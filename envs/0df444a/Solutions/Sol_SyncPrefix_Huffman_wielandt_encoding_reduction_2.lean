-- Prove2me | solution 2 for SyncPrefix.Huffman.wielandt_encoding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:14:28.097193+00:00
-- url     : https://prove2.me/submissions/ca74ee4e-14e2-4313-881a-98cba62ce049

import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Definitions.Def_SyncPrefix_Huffman_WielandtReduction
import Theorems.Thm_SyncPrefix_Huffman_wielandt_code
import Theorems.Thm_SyncPrefix_Huffman_composition_decoder
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_CookPvsNP_StackCompare
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_bounded_loop
import Theorems.Thm_CookPvsNP_stack_sync_pop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open SyncPrefix.Huffman CookPvsNP

namespace WielandtSolution

abbrev Sym := Option Bool
abbrev SaveSym := Option Sym × Bool

def unmaskFalse : Sym → Sym
  | some false => some true
  | x => x

/-! ### Part 1: Prefix-preserving wrapper around `Alg` (`SaveTMProof`) -/

namespace SaveTMProof

structure SaveCell (Γ : Type) where
  orig : Option Sym
  one : Option Γ
  isOut : Bool
  deriving DecidableEq

noncomputable instance instFintypeSaveCell {Γ : Type} [Fintype Γ] :
    Fintype (SaveCell Γ) :=
  Fintype.ofInjective
    (fun c : SaveCell Γ => (c.orig, c.one, c.isOut))
    (by
      intro a b h
      cases a; cases b
      simp_all)

def SaveCell.unpack {Γ : Type} : Option (SaveCell Γ) → SaveCell Γ
  | none => ⟨none, none, false⟩
  | some c => c

def saveInputEmbedding {Γ : Type} (ι₁ : Sym ↪ Γ) : Sym ↪ SaveCell Γ where
  toFun x := ⟨some x, some (ι₁ (unmaskFalse x)), false⟩
  inj' _ _ h := Option.some.inj (congrArg SaveCell.orig h)

def saveOutputEmbedding (Γ : Type) : SaveSym ↪ SaveCell Γ where
  toFun p := ⟨p.1, none, p.2⟩
  inj' a b h := by
    cases a; cases b
    have h1 := congrArg SaveCell.orig h
    have h2 := congrArg SaveCell.isOut h
    simp_all

inductive SaveQ (Q : Type) where
  | sim (q : Q)
  | markOut
  | scanLeft
  | haltAccept
  | haltReject
  deriving DecidableEq, Fintype

def saveMarkStep {Γ Q : Type} (c : SaveCell Γ) :
    SaveQ Q × Option (SaveCell Γ) × Move :=
  if c.one.isSome then
    (.markOut, some ⟨c.orig, none, true⟩, .right)
  else
    (.scanLeft, some ⟨c.orig, none, false⟩, .left)

def saveTM {Γ : Type} (M : TM Γ) : TM (SaveCell Γ) where
  Q := SaveQ M.Q
  q₀ := .sim M.q₀
  qaccept := .haltAccept
  qreject := .haltReject
  accept_ne_reject := by intro h; cases h
  δ := fun q s =>
    let c := SaveCell.unpack s
    match q with
    | .sim q₀ =>
        if q₀ = M.qaccept ∨ q₀ = M.qreject then
          saveMarkStep c
        else
          match M.δ q₀ c.one with
          | (q', w, m) => (.sim q', some ⟨c.orig, w, false⟩, m)
    | .markOut => saveMarkStep c
    | .scanLeft =>
        match s with
        | some _ => (.scanLeft, some ⟨c.orig, none, c.isOut⟩, .left)
        | none => (.haltAccept, none, .right)
    | .haltAccept => (.haltAccept, s, .right)
    | .haltReject => (.haltReject, s, .right)

structure SimCfg (Γ Q : Type) where
  state : Q
  left : List (Option Sym × Option Γ)
  head : Option (Option Sym × Option Γ)
  right : List (Option Sym × Option Γ)

def SimCfg.cellOf {Γ : Type} (p : Option Sym × Option Γ) : Option (SaveCell Γ) :=
  some ⟨p.1, p.2, false⟩

def SimCfg.encode {Γ : Type} {M : TM Γ} (d : SimCfg Γ M.Q) :
    Cfg (SaveCell Γ) (saveTM M).Q where
  state := .sim d.state
  left := d.left.map SimCfg.cellOf
  head := d.head.map (fun p => ⟨p.1, p.2, false⟩)
  right := d.right.map SimCfg.cellOf

def SimCfg.source {Γ Q : Type} (d : SimCfg Γ Q) : Cfg Γ Q where
  state := d.state
  left := d.left.map Prod.snd
  head := match d.head with | none => none | some p => p.2
  right := d.right.map Prod.snd

def SimCfg.origList {Γ Q : Type} (d : SimCfg Γ Q) : List Sym :=
  d.left.reverse.filterMap Prod.fst ++
    (match d.head with | none => [] | some p => p.1.toList) ++
    d.right.filterMap Prod.fst

def SimCfg.init {Γ : Type} (ι₁ : Sym ↪ Γ) (M : TM Γ) (w : List Sym) :
    SimCfg Γ M.Q where
  state := M.q₀
  left := []
  head := (w.map (fun x => (some x, some (ι₁ (unmaskFalse x))))).head?
  right := (w.map (fun x => (some x, some (ι₁ (unmaskFalse x))))).tail

lemma filterMap_fst_cons {α β : Type} (p : Option α × β) (xs : List (Option α × β)) :
    List.filterMap Prod.fst (p :: xs) = p.1.toList ++ xs.filterMap Prod.fst := by
  rcases p with ⟨o, b⟩
  cases o <;> simp

lemma filterMap_fst_map_some {Γ : Type} (ι₁ : Sym ↪ Γ) (w : List Sym) :
    (w.map (fun x => (some x, some (ι₁ (unmaskFalse x))))).filterMap Prod.fst = w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma simCfg_init_encode {Γ : Type} (ι₁ : Sym ↪ Γ) (M : TM Γ) (w : List Sym) :
    (SimCfg.init ι₁ M w).encode = (saveTM M).init (w.map (saveInputEmbedding ι₁)) := by
  cases w with
  | nil => rfl
  | cons x xs =>
    simp [SimCfg.init, SimCfg.encode, SimCfg.cellOf, TM.init,
      saveTM, saveInputEmbedding, Function.comp_def]
    exact ⟨rfl, fun _ _ => rfl⟩

lemma simCfg_init_source {Γ : Type} (ι₁ : Sym ↪ Γ) (M : TM Γ) (w : List Sym) :
    (SimCfg.init ι₁ M w).source = M.init ((w.map unmaskFalse).map ι₁) := by
  cases w <;> simp [SimCfg.init, SimCfg.source, TM.init, Function.comp_def]

lemma simCfg_init_origList {Γ : Type} (ι₁ : Sym ↪ Γ) (M : TM Γ) (w : List Sym) :
    (SimCfg.init ι₁ M w).origList = w := by
  cases w with
  | nil => rfl
  | cons x xs =>
    simp [SimCfg.init, SimCfg.origList, filterMap_fst_map_some]

def SimCfg.step {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) : SimCfg Γ M.Q :=
  if M.IsHalting d.source then d else
    let orig_h : Option Sym := match d.head with | none => none | some p => p.1
    let one_h : Option Γ := match d.head with | none => none | some p => p.2
    match M.δ d.state one_h with
    | (q', s', .right) =>
        { state := q'
          left := (orig_h, s') :: d.left
          head := d.right.head?
          right := d.right.tail }
    | (q', s', .left) =>
        match d.left with
        | [] =>
            { state := q'
              left := []
              head := none
              right := (orig_h, s') :: d.right }
        | a :: x' =>
            { state := q'
              left := x'
              head := some a
              right := (orig_h, s') :: d.right }

lemma simCfg_step_source {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) :
    (d.step M).source = M.step d.source := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.step, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;> cases head <;>
      simp [SimCfg.step, SimCfg.source, TM.step, TM.IsHalting, hq, hd]

lemma simCfg_step_encode {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q)
    (hn : ¬ M.IsHalting d.source) :
    (saveTM M).step d.encode = (d.step M).encode := by
  rcases d with ⟨q, left, head, right⟩
  have hq : ¬ (q = M.qaccept ∨ q = M.qreject) := hn
  rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
  have hnot_halt : ¬ (saveTM M).IsHalting
      (SimCfg.encode (M := M) ⟨q, left, head, right⟩) := by
    intro hh
    rcases hh with hh | hh <;> cases hh
  cases move <;> cases left <;> cases right <;> cases head <;>
    simp [SimCfg.step, SimCfg.encode, SimCfg.source, SimCfg.cellOf, TM.step, TM.IsHalting,
      saveTM, SaveCell.unpack, hq, hd, hnot_halt]

lemma simCfg_step_origList {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) :
    (d.step M).origList = d.origList := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;> cases head <;>
      simp [SimCfg.step, SimCfg.source, SimCfg.origList, TM.IsHalting, hq, hd,
        filterMap_fst_cons, List.append_assoc]

lemma simCfg_step_len {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) :
    (d.step M).left.length + (d.step M).right.length ≤ d.left.length + d.right.length + 1 := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;>
      simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq, hd] <;> omega

lemma simCfg_run_origList {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) (m : ℕ) :
    ((SimCfg.step M)^[m] d).origList = d.origList := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', simCfg_step_origList, ih]

lemma simCfg_run_len {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) (m : ℕ) :
    ((SimCfg.step M)^[m] d).left.length + ((SimCfg.step M)^[m] d).right.length ≤
      d.left.length + d.right.length + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h := simCfg_step_len M ((SimCfg.step M)^[m] d)
    omega

lemma simCfg_run_encode {Γ : Type} (M : TM Γ) (d : SimCfg Γ M.Q) (m : ℕ)
    (hm : ∀ i < m, ¬ M.IsHalting ((SimCfg.step M)^[i] d).source) :
    (saveTM M).run m d.encode = ((SimCfg.step M)^[m] d).encode := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold TM.run at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [ih (fun i hi => hm i (Nat.lt_succ_of_lt hi))]
    exact simCfg_step_encode M _ (hm m (Nat.lt_succ_self m))

lemma tm_run_eq_of_halting' {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q)
    (h : M.IsHalting c) (n : ℕ) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold TM.run at ih ⊢
    rw [Function.iterate_succ_apply', ih, TM.step, if_pos h]

lemma tm_join {Γ : Type} (M : TM Γ) {a b : ℕ} {c d e : Cfg Γ M.Q}
    (h : M.run a c = d) (g : M.run b d = e) : M.run (a + b) c = e := by
  unfold TM.run at h g ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  exact g

lemma simCfg_first_halt {Γ : Type} (M : TM Γ) (d₀ : SimCfg Γ M.Q) (n : ℕ)
    (hn : M.IsHalting (M.run n d₀.source)) :
    ∃ m ≤ n,
      (saveTM M).run m d₀.encode = ((SimCfg.step M)^[m] d₀).encode ∧
      ((SimCfg.step M)^[m] d₀).source = M.run n d₀.source ∧
      M.IsHalting ((SimCfg.step M)^[m] d₀).source := by
  classical
  have hs : Function.Semiconj (@SimCfg.source Γ M.Q) (SimCfg.step M) M.step :=
    simCfg_step_source M
  have hsource (k : ℕ) : ((SimCfg.step M)^[k] d₀).source = M.run k d₀.source :=
    hs.iterate_right k d₀
  let hex : ∃ m, M.IsHalting (M.run m d₀.source) := ⟨n, hn⟩
  let m := Nat.find hex
  have hm : m ≤ n := Nat.find_min' hex hn
  have hstop : M.IsHalting (M.run m d₀.source) := Nat.find_spec hex
  have heq : M.run n d₀.source = M.run m d₀.source := by
    conv_lhs => rw [show n = (n - m) + m by omega]
    change (M.step)^[(n - m) + m] d₀.source = _
    rw [Function.iterate_add_apply]
    exact tm_run_eq_of_halting' M _ hstop (n - m)
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · apply simCfg_run_encode
    intro i hi
    rw [hsource]
    exact Nat.find_min hex hi
  · exact (hsource m).trans heq.symm
  · rw [hsource]; exact hstop

/-! ### MarkOut and ScanLeft phases -/

def eOrig {Γ : Type} : Option (Option Sym × Option Γ) → Option Sym
  | none => none
  | some p => p.1

def eOne {Γ : Type} : Option (Option Sym × Option Γ) → Option Γ
  | none => none
  | some p => p.2

def eCell {Γ : Type} : Option (Option Sym × Option Γ) → Option (SaveCell Γ)
  | none => none
  | some p => some ⟨p.1, p.2, false⟩

def scanLeftCfg {Γ : Type} {M : TM Γ}
    (left : List (Option Sym × Option Γ × Bool))
    (right : List SaveSym) : Cfg (SaveCell Γ) (saveTM M).Q where
  state := .scanLeft
  left := left.tail.map (fun x => some ⟨x.1, x.2.1, x.2.2⟩)
  head := left.head?.map (fun x => ⟨x.1, x.2.1, x.2.2⟩)
  right := right.map (some ∘ saveOutputEmbedding Γ)

def haltSaveCfg {Γ : Type} {M : TM Γ} (outCells : List SaveSym) :
    Cfg (SaveCell Γ) (saveTM M).Q where
  state := .haltAccept
  left := [none]
  head := (outCells.map (some ∘ saveOutputEmbedding Γ)).headD none
  right := (outCells.map (some ∘ saveOutputEmbedding Γ)).tail

lemma step_scanLeft_cons {Γ : Type} (M : TM Γ)
    (x : Option Sym × Option Γ × Bool)
    (xs : List (Option Sym × Option Γ × Bool))
    (right : List SaveSym) :
    (saveTM M).step (scanLeftCfg (M := M) (x :: xs) right) =
      scanLeftCfg (M := M) xs ((x.1, x.2.2) :: right) := by
  cases xs <;> rfl

lemma run_scanLeft {Γ : Type} (M : TM Γ)
    (left : List (Option Sym × Option Γ × Bool))
    (right : List SaveSym) :
    (saveTM M).run left.length (scanLeftCfg (M := M) left right) =
      scanLeftCfg (M := M) [] (left.reverse.map (fun x => (x.1, x.2.2)) ++ right) := by
  induction left generalizing right with
  | nil => rfl
  | cons x xs ih =>
    have h1 : (saveTM M).run 1 (scanLeftCfg (M := M) (x :: xs) right) =
        scanLeftCfg (M := M) xs ((x.1, x.2.2) :: right) := step_scanLeft_cons M x xs right
    have h2 := ih ((x.1, x.2.2) :: right)
    have hj := tm_join (saveTM M) h1 h2
    rw [Nat.add_comm 1 xs.length] at hj
    simpa [List.append_assoc] using hj

lemma step_scanLeft_nil {Γ : Type} (M : TM Γ) (outCells : List SaveSym) :
    (saveTM M).run 1 (scanLeftCfg (M := M) [] outCells) = haltSaveCfg (M := M) outCells := rfl

lemma output_haltSaveCfg {Γ : Type} (M : TM Γ) (outCells : List SaveSym) :
    (saveTM M).output (haltSaveCfg (M := M) outCells) =
      outCells.map (some ∘ saveOutputEmbedding Γ) := by
  cases outCells with
  | nil => rfl
  | cons x xs =>
    have hdrop : ∀ l : List SaveSym,
        (l.map (some ∘ saveOutputEmbedding Γ)).dropWhile Option.isNone =
          l.map (some ∘ saveOutputEmbedding Γ) := by
      intro l; cases l <;> rfl
    simp only [TM.output, haltSaveCfg, List.map_cons, List.headD_cons, List.tail_cons]
    rw [← List.map_cons, ← List.map_reverse, hdrop, ← List.map_reverse, List.reverse_reverse]

def markRCfg {Γ : Type} {M : TM Γ} (q : SaveQ M.Q)
    (left : List (Option Sym × Option Γ × Bool))
    (R : List (Option (Option Sym × Option Γ))) : Cfg (SaveCell Γ) (saveTM M).Q where
  state := q
  left := left.map (fun x => some ⟨x.1, x.2.1, x.2.2⟩)
  head := (R.map eCell).headD none
  right := (R.map eCell).tail

def tailOutR {Γ : Type} : List (Option (Option Sym × Option Γ)) → List SaveSym
  | [] => [(none, false)]
  | e :: R' => (eOrig e, false) :: R'.map (fun x => (eOrig x, false))

def isMarkState {Γ : Type} (M : TM Γ) : SaveQ M.Q → Prop
  | .sim q₀ => q₀ = M.qaccept ∨ q₀ = M.qreject
  | .markOut => True
  | _ => False

lemma map_eCell_of_isSome_eOne_none {Γ : Type} :
    ∀ R' : List (Option (Option Sym × Option Γ)),
      (∀ e ∈ R', e.isSome = true) →
      (∀ e ∈ R', eOne e = none) →
      R'.map eCell = (R'.map (fun x => (eOrig x, false))).map (some ∘ saveOutputEmbedding Γ)
  | [], _, _ => rfl
  | e :: R', hsome, hnone => by
    have he_some := hsome e List.mem_cons_self
    have he_none := hnone e List.mem_cons_self
    cases e with
    | none => simp at he_some
    | some p =>
      rcases p with ⟨o, g⟩
      dsimp [eOne] at he_none
      subst he_none
      simp only [List.map_cons, eCell, eOrig, Function.comp_apply, saveOutputEmbedding]
      congr 1
      exact map_eCell_of_isSome_eOne_none R'
        (fun x hx => hsome x (List.mem_cons_of_mem _ hx))
        (fun x hx => hnone x (List.mem_cons_of_mem _ hx))

lemma step_markRCfg_zero {Γ : Type} (M : TM Γ) (q : SaveQ M.Q) (hq : isMarkState M q)
    (left : List (Option Sym × Option Γ × Bool))
    (R : List (Option (Option Sym × Option Γ)))
    (hsome : ∀ e ∈ R.tail, e.isSome = true)
    (hnone : ∀ e ∈ R, eOne e = none) :
    (saveTM M).run 1 (markRCfg (M := M) q left R) = scanLeftCfg (M := M) left (tailOutR R) := by
  change (saveTM M).step (markRCfg (M := M) q left R) = _
  cases R with
  | nil =>
    cases q <;> try contradiction
    · dsimp [isMarkState] at hq
      cases left <;> simp [TM.step, TM.IsHalting, saveTM, hq, saveMarkStep, markRCfg,
        SaveCell.unpack, scanLeftCfg, tailOutR, saveOutputEmbedding] <;> rfl
    · cases left <;> simp [TM.step, TM.IsHalting, saveTM, saveMarkStep, markRCfg,
        SaveCell.unpack, scanLeftCfg, tailOutR, saveOutputEmbedding] <;> rfl
  | cons e₀ R' =>
    have he0 : eOne e₀ = none := hnone e₀ List.mem_cons_self
    have hR' : R'.map eCell =
        (R'.map (fun x => (eOrig x, false))).map (some ∘ saveOutputEmbedding Γ) :=
      map_eCell_of_isSome_eOne_none R' hsome (fun x hx => hnone x (List.mem_cons_of_mem _ hx))
    have hunpack : SaveCell.unpack (eCell e₀) = ⟨eOrig e₀, none, false⟩ := by
      cases e₀ with
      | none => rfl
      | some p =>
        rcases p with ⟨o, g⟩
        dsimp [eOne] at he0
        subst he0
        rfl
    cases q <;> try contradiction
    · dsimp [isMarkState] at hq
      cases left <;> simp [TM.step, TM.IsHalting, saveTM, hq, saveMarkStep, markRCfg,
        hunpack, hR', scanLeftCfg, tailOutR, saveOutputEmbedding] <;> rfl
    · cases left <;> simp [TM.step, TM.IsHalting, saveTM, saveMarkStep, markRCfg,
        hunpack, hR', scanLeftCfg, tailOutR, saveOutputEmbedding] <;> rfl

lemma step_markRCfg_succ {Γ : Type} (M : TM Γ) (q : SaveQ M.Q) (hq : isMarkState M q)
    (left : List (Option Sym × Option Γ × Bool))
    (e₀ : Option (Option Sym × Option Γ)) (γ₀ : Γ) (he0 : eOne e₀ = some γ₀)
    (R' : List (Option (Option Sym × Option Γ))) :
    (saveTM M).run 1 (markRCfg (M := M) q left (e₀ :: R')) =
      markRCfg (M := M) .markOut ((eOrig e₀, none, true) :: left) R' := by
  change (saveTM M).step (markRCfg (M := M) q left (e₀ :: R')) = _
  have hunpack : SaveCell.unpack (eCell e₀) = ⟨eOrig e₀, some γ₀, false⟩ := by
    cases e₀ with
    | none => simp [eOne] at he0
    | some p =>
      rcases p with ⟨o, g⟩
      dsimp [eOne] at he0
      subst he0
      rfl
  cases q <;> try contradiction
  · dsimp [isMarkState] at hq
    simp [TM.step, TM.IsHalting, saveTM, hq, saveMarkStep, markRCfg, hunpack]
  · simp [TM.step, TM.IsHalting, saveTM, saveMarkStep, markRCfg, hunpack]

lemma run_markRCfg {Γ : Type} (M : TM Γ) :
    ∀ (L : ℕ) (q : SaveQ M.Q) (_hq : isMarkState M q)
      (left : List (Option Sym × Option Γ × Bool))
      (R : List (Option (Option Sym × Option Γ)))
      (γ₀ : Γ) (padding : ℕ)
      (_hsome : ∀ e ∈ R.tail, e.isSome = true)
      (_hmap : R.map eOne = List.replicate L (some γ₀) ++ List.replicate padding none),
      (saveTM M).run (L + 1) (markRCfg (M := M) q left R) =
        scanLeftCfg (M := M) ((R.take L).reverse.map (fun e => (eOrig e, none, true)) ++ left)
          (tailOutR (R.drop L))
  | 0, q, hq, left, R, _, padding, hsome, hmap => by
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, List.take_zero,
      List.reverse_nil, List.map_nil, List.drop_zero] at hmap ⊢
    apply step_markRCfg_zero M q hq left R hsome
    intro e he
    have hmem : eOne e ∈ R.map eOne := List.mem_map_of_mem he
    rw [hmap] at hmem
    exact List.eq_of_mem_replicate hmem
  | L + 1, q, hq, left, R, γ₀, padding, hsome, hmap => by
    cases R with
    | nil => simp [List.replicate_succ] at hmap
    | cons e₀ R' =>
      simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at hmap
      rcases hmap with ⟨he0, hmap'⟩
      have hsome' : ∀ e ∈ R'.tail, e.isSome = true := by
        intro e he
        exact hsome e (List.tail_subset R' he)
      have h1 := step_markRCfg_succ M q hq left e₀ γ₀ he0 R'
      have h2 := run_markRCfg M L .markOut trivial ((eOrig e₀, none, true) :: left)
        R' γ₀ padding hsome' hmap'
      have hj := tm_join (saveTM M) h1 h2
      rw [Nat.add_comm 1 (L + 1)] at hj
      simpa [List.take_succ_cons, List.drop_succ_cons, List.append_assoc] using hj

private lemma leading_blanks {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = List.replicate n none ++ xs.dropWhile Option.isNone := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    cases x with
    | none =>
      obtain ⟨n, h⟩ := ih
      refine ⟨n + 1, ?_⟩
      simpa [List.replicate_succ] using congrArg (List.cons none) h
    | some _ => exact ⟨0, by simp⟩

private lemma trailing_blanks {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = (xs.reverse.dropWhile Option.isNone).reverse ++ List.replicate n none := by
  obtain ⟨n, h⟩ := leading_blanks xs.reverse
  exact ⟨n, by simpa using congrArg List.reverse h⟩

def simCfgR {Γ Q : Type} (d : SimCfg Γ Q) : List (Option (Option Sym × Option Γ)) :=
  d.head :: d.right.map some

def saveOutList {Γ Q : Type} (d : SimCfg Γ Q) (L : ℕ) : List SaveSym :=
  d.left.reverse.map (fun p => (p.1, false)) ++
    ((simCfgR d).take L).map (fun e => (eOrig e, true)) ++
    tailOutR ((simCfgR d).drop L)

lemma filter_snd_tailOutR {Γ : Type} (S : List (Option (Option Sym × Option Γ))) :
    (tailOutR S).filter Prod.snd = [] := by
  cases S with
  | nil => rfl
  | cons e S' =>
    induction S' with
    | nil => rfl
    | cons _ _ ih => exact ih

lemma filter_snd_saveOutList {Γ Q : Type} (d : SimCfg Γ Q) (L : ℕ)
    (hL : L ≤ (simCfgR d).length) :
    ((saveOutList d L).filter Prod.snd).length = L := by
  unfold saveOutList
  rw [List.filter_append, List.filter_append, filter_snd_tailOutR, List.append_nil]
  have h1 : (d.left.reverse.map (fun p : Option Sym × Option Γ => (p.1, false))).filter Prod.snd = [] := by
    induction d.left.reverse <;> simp [*]
  have h2 : (((simCfgR d).take L).map (fun e => (eOrig e, true))).filter Prod.snd =
      ((simCfgR d).take L).map (fun e => (eOrig e, true)) := by
    induction ((simCfgR d).take L) <;> simp [*]
  rw [h1, List.nil_append, h2, List.length_map, List.length_take, Nat.min_eq_left hL]

lemma filterMap_fst_tailOutR {Γ : Type} (S : List (Option (Option Sym × Option Γ))) :
    (tailOutR S).filterMap Prod.fst = S.filterMap eOrig := by
  cases S with
  | nil => rfl
  | cons e S' =>
    simp only [tailOutR, List.filterMap_cons, List.filterMap_map]
    rfl

lemma filterMap_fst_saveOutList {Γ Q : Type} (d : SimCfg Γ Q) (L : ℕ) :
    (saveOutList d L).filterMap Prod.fst = d.origList := by
  unfold saveOutList
  rw [List.filterMap_append, List.filterMap_append, filterMap_fst_tailOutR]
  have h1 : (d.left.reverse.map (fun p : Option Sym × Option Γ => (p.1, false))).filterMap Prod.fst =
      d.left.reverse.filterMap Prod.fst := by
    rw [List.filterMap_map]; rfl
  have h2 : (((simCfgR d).take L).map (fun e => (eOrig e, true))).filterMap Prod.fst =
      ((simCfgR d).take L).filterMap eOrig := by
    rw [List.filterMap_map]; rfl
  rw [h1, h2, List.append_assoc, ← List.filterMap_append, List.take_append_drop]
  unfold simCfgR SimCfg.origList
  rw [List.filterMap_cons, List.filterMap_map]
  have h3 : (eOrig ∘ some : Option Sym × Option Γ → Option Sym) = Prod.fst := rfl
  rw [h3]
  rcases d.head with _ | ⟨_ | b, _⟩ <;> simp [eOrig, Option.toList, List.append_assoc]

lemma simCfg_encode_eq_markRCfg {Γ : Type} {M : TM Γ} (d : SimCfg Γ M.Q) :
    d.encode = markRCfg (M := M) (.sim d.state) (d.left.map (fun p => (p.1, p.2, false))) (simCfgR d) := by
  unfold SimCfg.encode markRCfg simCfgR
  simp only [List.map_map, List.map_cons, List.headD_cons, List.tail_cons]
  congr 1
  cases d.head <;> rfl

lemma map_some_unit {Γ : Type} (ι₂ : Unit ↪ Γ) (u : List Unit) :
    u.map (some ∘ ι₂) = List.replicate u.length (some (ι₂ ())) := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
    cases x
    simp [List.replicate_succ, ih]

lemma polyTimeComputable_save
    (F : List Sym → List Unit) (hF : PolyTimeComputable F) :
    ∃ f_save : List Sym → List SaveSym,
      PolyTimeComputable f_save ∧
      ∀ w : List Sym,
        (f_save w).filterMap Prod.fst = w ∧
        ((f_save w).filter Prod.snd).length = (F (w.map unmaskFalse)).length := by
  rcases hF with ⟨Γ, hfinΓ, ι₁, ι₂, M, k, hM⟩
  let _ : Fintype Γ := hfinΓ
  have hrun_save : ∀ w : List Sym,
      ∃ (outCells : List SaveSym) (t : ℕ),
        t ≤ 4 * (w.length + (w.length ^ k + k)) + 5 ∧
        (saveTM M).HaltsWithin t (w.map (saveInputEmbedding ι₁)) ∧
        (saveTM M).output ((saveTM M).run t
          ((saveTM M).init (w.map (saveInputEmbedding ι₁)))) =
          outCells.map (some ∘ saveOutputEmbedding Γ) ∧
        outCells.filterMap Prod.fst = w ∧
        (outCells.filter Prod.snd).length = (F (w.map unmaskFalse)).length := by
    intro w
    set n := w.length ^ k + k
    have hw_len : (w.map unmaskFalse).length ^ k + k = n := by simp [n]
    obtain ⟨hHalt_n, hOut_n⟩ := hM (w.map unmaskFalse)
    rw [hw_len] at hHalt_n hOut_n
    set d₀ := SimCfg.init ι₁ M w
    have hd₀_src : d₀.source = M.init ((w.map unmaskFalse).map ι₁) := simCfg_init_source ι₁ M w
    have hn' : M.IsHalting (M.run n d₀.source) := by rw [hd₀_src]; exact hHalt_n
    obtain ⟨m, hm_le, hm_run, hm_src, hm_halt⟩ := simCfg_first_halt M d₀ n hn'
    set d := (SimCfg.step M)^[m] d₀
    have hd_orig : d.origList = w :=
      (simCfg_run_origList M d₀ m).trans (simCfg_init_origList ι₁ M w)
    have hd_len : d.left.length + d.right.length ≤ w.length + m := by
      have h : d.left.length + d.right.length ≤ d₀.left.length + d₀.right.length + m :=
        simCfg_run_len M d₀ m
      have h0 : d₀.left.length + d₀.right.length ≤ w.length := by
        cases w <;> simp [d₀, SimCfg.init]
      omega
    set L := (F (w.map unmaskFalse)).length
    obtain ⟨padding, hpad⟩ := trailing_blanks (d.source.head :: d.source.right)
    change d.source.head :: d.source.right = M.output d.source ++ List.replicate padding none at hpad
    have hout_d : M.output d.source = List.replicate L (some (ι₂ ())) := by
      rw [hm_src, hd₀_src, hOut_n, map_some_unit ι₂ (F (w.map unmaskFalse))]
    rw [hout_d] at hpad
    have hR_map : (simCfgR d).map eOne =
        List.replicate L (some (ι₂ ())) ++ List.replicate padding none := by
      simpa [simCfgR, SimCfg.source, List.map_map, Function.comp_def, eOne] using hpad
    have hR_len : L ≤ (simCfgR d).length := by
      have hlen := congrArg List.length hR_map
      simp only [List.length_map, List.length_append, List.length_replicate] at hlen
      omega
    have hR_some : ∀ e ∈ (simCfgR d).tail, e.isSome = true := by
      intro e he
      simp only [simCfgR, List.tail_cons, List.mem_map] at he
      rcases he with ⟨p, _, rfl⟩
      rfl
    have hmark := run_markRCfg M L (.sim d.state) hm_halt
      (d.left.map (fun p => (p.1, p.2, false))) (simCfgR d) (ι₂ ()) padding hR_some hR_map
    rw [← simCfg_encode_eq_markRCfg d] at hmark
    set left₁ := ((simCfgR d).take L).reverse.map (fun e => (eOrig e, (none : Option Γ), true)) ++
      d.left.map (fun p => (p.1, p.2, false))
    have hscan := run_scanLeft M left₁ (tailOutR ((simCfgR d).drop L))
    have hout_eq : left₁.reverse.map (fun x => (x.1, x.2.2)) ++ tailOutR ((simCfgR d).drop L) =
        saveOutList d L := by
      simp [left₁, saveOutList, List.reverse_append, List.map_append, List.map_map,
        Function.comp_def, List.append_assoc]
    rw [hout_eq] at hscan
    have hfin := step_scanLeft_nil M (saveOutList d L)
    have hrun_init : (saveTM M).run m ((saveTM M).init (w.map (saveInputEmbedding ι₁))) =
        d.encode := by
      rw [← simCfg_init_encode ι₁ M w]
      exact hm_run
    have hrun_total := tm_join (saveTM M)
      (tm_join (saveTM M) (tm_join (saveTM M) hrun_init hmark) hscan) hfin
    set t := ((m + (L + 1)) + left₁.length) + 1
    have hleft₁_len : left₁.length ≤ L + d.left.length := by
      simp only [left₁, List.length_append, List.length_map, List.length_reverse, List.length_take]
      omega
    have hL_le : L ≤ w.length + m + 1 := by
      have : (simCfgR d).length = d.right.length + 1 := by simp [simCfgR]
      omega
    refine ⟨saveOutList d L, t, by omega, ?_, ?_, ?_, ?_⟩
    · change (saveTM M).IsHalting ((saveTM M).run t _)
      rw [hrun_total]
      exact Or.inl rfl
    · rw [hrun_total]
      exact output_haltSaveCfg M (saveOutList d L)
    · rw [filterMap_fst_saveOutList, hd_orig]
    · exact filter_snd_saveOutList d L hR_len
  classical
  let f_save : List Sym → List SaveSym :=
    fun w => Classical.choose (hrun_save w)
  have hpow : ∀ w : List Sym,
      4 * (w.length + (w.length ^ k + k)) + 5 ≤ 8 * (w.length + 1) ^ (k + 1) + (4 * k + 5) := by
    intro w
    set P := (w.length + 1) ^ (k + 1)
    have h1 : w.length ≤ P := by
      calc w.length ≤ w.length + 1 := Nat.le_succ _
        _ = (w.length + 1) ^ 1 := (Nat.pow_one _).symm
        _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : w.length ^ k ≤ P := by
      calc w.length ^ k ≤ (w.length + 1) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨k', hk'⟩ := polynomial_absorb 8 (k + 1) (4 * k + 5)
  refine ⟨f_save, ?_, fun w => ?_⟩
  · refine ⟨SaveCell Γ, inferInstance, saveInputEmbedding ι₁, saveOutputEmbedding Γ,
      saveTM M, k', fun w => ?_⟩
    obtain ⟨t, ht_le, hhalt, hout, -, -⟩ := Classical.choose_spec (hrun_save w)
    have htk' : t ≤ w.length ^ k' + k' := by
      have h1 := hpow w
      have h2 := hk' w.length
      omega
    have hrun_eq : (saveTM M).run (w.length ^ k' + k')
        ((saveTM M).init (w.map (saveInputEmbedding ι₁))) =
        (saveTM M).run t ((saveTM M).init (w.map (saveInputEmbedding ι₁))) := by
      conv_lhs => rw [← Nat.sub_add_cancel htk']
      change ((saveTM M).step)^[(w.length ^ k' + k' - t) + t] _ = _
      rw [Function.iterate_add_apply]
      exact tm_run_eq_of_halting' (saveTM M) _ hhalt _
    refine ⟨?_, ?_⟩
    · change (saveTM M).IsHalting ((saveTM M).run (w.length ^ k' + k') _)
      rw [hrun_eq]
      exact hhalt
    · rw [hrun_eq]
      exact hout
  · obtain ⟨_, _, _, _, h1, h2⟩ := Classical.choose_spec (hrun_save w)
    exact ⟨h1, h2⟩

end SaveTMProof

/-! ### Part 2: StackProgram Unary Division (`DivStackProof`) -/

namespace DivStackProof

inductive DKey where
  | ki
  | ko
  | L
  | M
  | Lrem
  | sc
  deriving DecidableEq

instance : Fintype DKey where
  elems := {.ki, .ko, .L, .M, .Lrem, .sc}
  complete x := by cases x <;> decide

abbrev DProg := StackProg DKey SaveSym
abbrev DStore := DKey → List SaveSym

def dTok : SaveSym := (none, true)

def isFalseOrig (p : SaveSym) : Bool :=
  decide (p.1 = some (some false))

def countL (cells : List SaveSym) : ℕ :=
  (cells.filter isFalseOrig).length

def countM (cells : List SaveSym) : ℕ :=
  (cells.filter Prod.snd).length

lemma exec_congr {p : DProg} {s t t' : DStore} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma exec_congr_left {p : DProg} {s s' t : DStore} {n : ℕ}
    (h : p.Exec s t n) (hs : s' = s) : p.Exec s' t n := hs ▸ h

lemma exec_seq_le {p q : DProg} {s t u : DStore} {B1 B2 : ℕ}
    (h1 : ∃ c1 ≤ B1, p.Exec s t c1) (h2 : ∃ c2 ≤ B2, q.Exec t u c2) :
    ∃ c ≤ B1 + 1 + B2, (p.seq q).Exec s u c := by
  rcases h1 with ⟨c1, hc1, e1⟩
  rcases h2 with ⟨c2, hc2, e2⟩
  exact ⟨c1 + 1 + c2, by omega, StackProg.Exec.seq e1 e2⟩

lemma exec_le_of_le {p : DProg} {s t : DStore} {B B' : ℕ}
    (h : ∃ c ≤ B, p.Exec s t c) (hB : B ≤ B') :
    ∃ c ≤ B', p.Exec s t c := by
  rcases h with ⟨c, hc, e⟩
  exact ⟨c, le_trans hc hB, e⟩

lemma exec_branch_true_le (test : (DKey → Option SaveSym) → Bool) (p q : DProg)
    {s t : DStore} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true)
    (hp : ∃ c ≤ B, p.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hp with ⟨c, hc, ep⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchTrue ht ep⟩

lemma exec_branch_false_le (test : (DKey → Option SaveSym) → Bool) (p q : DProg)
    {s t : DStore} {B : ℕ}
    (hf : test (fun k => (s k).head?) = false)
    (hq : ∃ c ≤ B, q.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hq with ⟨c, hc, eq⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchFalse hf eq⟩

lemma exec_bounded_loop (test : (DKey → Option SaveSym) → Bool) (p : DProg)
    (n : ℕ) (s : ℕ → DStore) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, ∃ c ≤ B, p.Exec (s i) (s (i + 1)) c) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by
  classical
  let cost : ℕ → ℕ := fun i => if h : i < n then Classical.choose (hb i h) else 0
  refine stack_bounded_loop test p n s cost B hg he ?_ ?_
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).2
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).1

lemma head?_replicate_isSome (n : ℕ) (a : SaveSym) (hn : 0 < n) :
    (List.replicate n a).head?.isSome = true := by
  cases n with
  | zero => omega
  | succ _ => rfl

lemma head?_replicate_isNone_false (n : ℕ) (a : SaveSym) (hn : 0 < n) :
    (List.replicate n a).head?.isNone = false := by
  cases n with
  | zero => omega
  | succ _ => rfl

def scanAct (h : DKey → Option SaveSym) (k : DKey) : StackAct SaveSym :=
  match k with
  | .ki => .pop
  | .L =>
      match h .ki with
      | some p => if isFalseOrig p then .push dTok else .keep
      | none => .keep
  | .M =>
      match h .ki with
      | some p => if p.2 then .push dTok else .keep
      | none => .keep
  | _ => .keep

def scanLoopProg : DProg :=
  .loop (fun h => (h .ki).isSome) (.act scanAct)

def scanStore (cells : List SaveSym) (i : ℕ) : DStore := fun k =>
  match k with
  | .ki => cells.drop i
  | .L => List.replicate (countL (cells.take i)) dTok
  | .M => List.replicate (countM (cells.take i)) dTok
  | _ => []

lemma exec_scanLoopProg (cells : List SaveSym) :
    ∃ c ≤ 3 * cells.length + 1,
      scanLoopProg.Exec (fun k => if k = .ki then cells else [])
        (scanStore cells cells.length) c := by
  have h0 : (fun k => if k = DKey.ki then cells else []) = scanStore cells 0 := by
    funext k
    cases k <;> rfl
  have hloop := exec_bounded_loop (fun h => (h .ki).isSome) (.act scanAct)
    cells.length (scanStore cells) 1
    (fun i hi => by
      show (cells.drop i).head?.isSome = true
      rw [List.drop_eq_getElem_cons hi]
      rfl)
    (by
      show (cells.drop cells.length).head?.isSome = false
      simp)
    (fun i hi => by
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act scanAct (scanStore cells i)) ?_⟩
      have hhead : (cells.drop i).head? = some cells[i] := by
        rw [List.drop_eq_getElem_cons hi]; rfl
      have htail : (cells.drop i).tail = cells.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi]; rfl
      have hcountL : countL (cells.take (i + 1)) =
          countL (cells.take i) + if isFalseOrig cells[i] then 1 else 0 := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]
        simp only [countL, Option.toList, List.filter_append, List.filter_cons,
          List.filter_nil, List.length_append]
        split_ifs <;> rfl
      have hcountM : countM (cells.take (i + 1)) =
          countM (cells.take i) + if cells[i].2 then 1 else 0 := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]
        simp only [countM, Option.toList, List.filter_append, List.filter_cons,
          List.filter_nil, List.length_append]
        split_ifs <;> rfl
      funext k
      cases k <;> simp [StackProg.applyAct, scanAct, scanStore, StackAct.apply, hhead, htail,
        hcountL, hcountM]
      · split_ifs <;> simp [List.replicate_succ]
      · split_ifs <;> simp [List.replicate_succ])
  rcases hloop with ⟨c, hc, eloop⟩
  exact ⟨c, by omega, exec_congr_left eloop h0⟩

def divBodyProg : DProg :=
  .seq (copyProg .L .Lrem .sc)
    (.seq (syncPopProg .Lrem .M)
      (.branch (fun h => (h .Lrem).isNone)
        (pushProg .ko dTok)
        (clearProg .Lrem)))

def divLoopProg : DProg :=
  .loop (fun h => (h .M).isSome) divBodyProg

def divMainProg : DProg :=
  .seq scanLoopProg
    (.branch (fun h => (h .L).isSome)
      divLoopProg
      (clearProg .M))

def divStore (L M i : ℕ) : DStore := fun k =>
  match k with
  | .L => List.replicate L dTok
  | .M => List.replicate (M - i * L) dTok
  | .ko => List.replicate (min i (M / L)) dTok
  | _ => []

lemma exec_divBodyProg (L M i : ℕ) (hL : 0 < L) (hi : i * L < M) :
    ∃ c ≤ 12 * L + 8,
      divBodyProg.Exec (divStore L M i) (divStore L M (i + 1)) c := by
  set s0 := divStore L M i
  have hc1 := stack_copy DKey.L DKey.Lrem DKey.sc (by decide) (by decide) (by decide) s0 rfl
  set s1 := Function.update s0 .Lrem (s0 .L ++ s0 .Lrem)
  have e1 : ∃ c ≤ 6 * L + 3, (copyProg .L .Lrem .sc).Exec s0 s1 c :=
    ⟨6 * (s0 .L).length + 3, by simp [s0, divStore], hc1⟩
  have hsync := stack_sync_pop DKey.Lrem DKey.M (by decide) s1
  set rem := M - i * L
  set s2 := Function.update
    (Function.update s1 .Lrem (List.replicate (L - min L rem) dTok))
    .M (List.replicate (rem - min L rem) dTok)
  have e2 : ∃ c ≤ 3 * L + 1, (syncPopProg .Lrem .M).Exec s1 s2 c := by
    refine ⟨3 * min (s1 .Lrem).length (s1 .M).length + 1, ?_, exec_congr hsync ?_⟩
    · have : (s1 .Lrem).length = L := by simp [s1, s0, divStore]
      omega
    · funext k
      cases k <;> simp [s2, s1, s0, divStore, rem, List.drop_replicate]
  have hrem_sub : rem - min L rem = M - (i + 1) * L := by
    rw [Nat.succ_mul]
    omega
  have e3 : ∃ c ≤ 3 * L + 2,
      (StackProg.branch (fun h => (h .Lrem).isNone)
        (pushProg .ko dTok)
        (clearProg .Lrem)).Exec s2 (divStore L M (i + 1)) c := by
    by_cases hle : L ≤ rem
    · have hmin_L : min L rem = L := Nat.min_eq_left hle
      have htest : (fun h : DKey → Option SaveSym => (h .Lrem).isNone) (fun k => (s2 k).head?) = true := by
        show (s2 .Lrem).head?.isNone = true
        simp [s2, hmin_L]
      have hdiv_ge : i + 1 ≤ M / L := by
        rw [Nat.le_div_iff_mul_le hL, Nat.succ_mul]
        omega
      have hmin_i : min (i + 1) (M / L) = min i (M / L) + 1 := by omega
      have hrem_L : rem - L = M - (i + 1) * L := by omega
      have hp := (stack_basic_macros DKey.ko s2).1 dTok
      have ep : ∃ c ≤ 1, (pushProg .ko dTok).Exec s2 (divStore L M (i + 1)) c := by
        refine ⟨1, le_rfl, exec_congr hp ?_⟩
        funext k
        cases k <;> simp [s2, s1, s0, divStore, hmin_L, hrem_L, hmin_i, List.replicate_succ]
      exact exec_le_of_le (exec_branch_true_le _ _ _ htest ep) (by omega)
    · have hlt : rem < L := by omega
      have hmin_r : min L rem = rem := Nat.min_eq_right (le_of_lt hlt)
      have htest : (fun h : DKey → Option SaveSym => (h .Lrem).isNone) (fun k => (s2 k).head?) = false := by
        show (s2 .Lrem).head?.isNone = false
        simp [s2, hmin_r, head?_replicate_isNone_false (L - rem) dTok (by omega)]
      have hdiv_lt : M / L ≤ i := by
        have h1 : M < (i + 1) * L := by rw [Nat.succ_mul]; omega
        have h2 : M / L < i + 1 := (Nat.div_lt_iff_lt_mul hL).mpr h1
        omega
      have hmin_i : min (i + 1) (M / L) = min i (M / L) := by omega
      have hcl := (stack_basic_macros DKey.Lrem s2).2.2
      have ecl : ∃ c ≤ 3 * L + 1, (clearProg .Lrem).Exec s2 (divStore L M (i + 1)) c := by
        refine ⟨3 * (s2 .Lrem).length + 1, ?_, exec_congr hcl ?_⟩
        · simp [s2]
        · funext k
          cases k <;> simp [s2, s1, s0, divStore, hrem_sub, hmin_i]
      exact exec_le_of_le (exec_branch_false_le _ _ _ htest ecl) (by omega)
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma mul_lt_of_lt_ceil_div (L M i : ℕ) (hL : 0 < L) (hi : i < (M + L - 1) / L) :
    i * L < M := by
  have h1 : i + 1 ≤ (M + L - 1) / L := hi
  rw [Nat.le_div_iff_mul_le hL, Nat.succ_mul] at h1
  omega

lemma ceil_div_mul_ge (L M : ℕ) (hL : 0 < L) :
    M ≤ ((M + L - 1) / L) * L := by
  have h := Nat.div_add_mod (M + L - 1) L
  have hmod : (M + L - 1) % L < L := Nat.mod_lt _ hL
  have hcomm : L * ((M + L - 1) / L) = ((M + L - 1) / L) * L := Nat.mul_comm _ _
  omega

lemma ceil_div_le (L M : ℕ) (hL : 0 < L) :
    (M + L - 1) / L ≤ M := by
  cases M with
  | zero =>
    have hlt : L - 1 < L := by omega
    simpa using Nat.div_eq_of_lt hlt
  | succ m =>
    have hle : m + 1 + L - 1 ≤ (m + 1) * L := by
      have hm : m * 1 ≤ m * L := Nat.mul_le_mul_left m hL
      rw [Nat.add_one_mul]
      omega
    calc (m + 1 + L - 1) / L ≤ ((m + 1) * L) / L := Nat.div_le_div_right hle
      _ = m + 1 := Nat.mul_div_cancel _ hL

lemma div_le_ceil_div (L M : ℕ) (hL : 0 < L) :
    M / L ≤ (M + L - 1) / L :=
  Nat.div_le_div_right (by omega)

lemma exec_divLoopProg (L M : ℕ) (hL : 0 < L) :
    ∃ c ≤ M * (12 * L + 10) + 1,
      divLoopProg.Exec (divStore L M 0) (divStore L M ((M + L - 1) / L)) c := by
  set n_iter := (M + L - 1) / L
  have hloop := exec_bounded_loop (fun h => (h .M).isSome) divBodyProg n_iter
    (divStore L M) (12 * L + 8)
    (fun i hi => by
      have hlt := mul_lt_of_lt_ceil_div L M i hL hi
      show (List.replicate (M - i * L) dTok).head?.isSome = true
      exact head?_replicate_isSome _ _ (by omega))
    (by
      have hge : M ≤ n_iter * L := ceil_div_mul_ge L M hL
      have hzero : M - n_iter * L = 0 := by omega
      show (List.replicate (M - n_iter * L) dTok).head?.isSome = false
      rw [hzero]
      rfl)
    (fun i hi => exec_divBodyProg L M i hL (mul_lt_of_lt_ceil_div L M i hL hi))
  rcases hloop with ⟨c, hc, eloop⟩
  have hn_le : n_iter ≤ M := ceil_div_le L M hL
  have hmul : n_iter * (12 * L + 8 + 2) ≤ M * (12 * L + 10) :=
    Nat.mul_le_mul_right (12 * L + 10) hn_le
  exact ⟨c, by omega, eloop⟩

def divFinalStore (cells : List SaveSym) : DStore := fun k =>
  let L := countL cells
  let M := countM cells
  match k with
  | .L => List.replicate L dTok
  | .ko => List.replicate (if L = 0 then 0 else M / L) dTok
  | _ => []

lemma countL_le_length (cells : List SaveSym) : countL cells ≤ cells.length :=
  List.length_filter_le _ _

lemma countM_le_length (cells : List SaveSym) : countM cells ≤ cells.length :=
  List.length_filter_le _ _

lemma exec_divMainProg (cells : List SaveSym) :
    ∃ c ≤ 12 * cells.length * cells.length + 16 * cells.length + 6,
      divMainProg.Exec (fun k => if k = .ki then cells else [])
        (divFinalStore cells) c := by
  have e1 := exec_scanLoopProg cells
  set L := countL cells
  set M := countM cells
  have hL_le : L ≤ cells.length := countL_le_length cells
  have hM_le : M ≤ cells.length := countM_le_length cells
  have hscan_eq : scanStore cells cells.length = divStore L M 0 := by
    funext k
    cases k <;> simp [scanStore, divStore, L, M]
  have e2 : ∃ c ≤ M * (12 * L + 10) + 3 * M + 3,
      (StackProg.branch (fun h => (h .L).isSome) divLoopProg (clearProg .M)).Exec
        (scanStore cells cells.length) (divFinalStore cells) c := by
    by_cases hL0 : 0 < L
    · have hL_ne : L ≠ 0 := by omega
      have htest : (fun h : DKey → Option SaveSym => (h .L).isSome)
          (fun k => (scanStore cells cells.length k).head?) = true := by
        rw [hscan_eq]
        show (List.replicate L dTok).head?.isSome = true
        exact head?_replicate_isSome L dTok hL0
      have elp := exec_divLoopProg L M hL0
      rcases elp with ⟨cl, hcl, eloop⟩
      have elp' : ∃ c ≤ M * (12 * L + 10) + 1,
          divLoopProg.Exec (scanStore cells cells.length) (divFinalStore cells) c := by
        refine ⟨cl, hcl, exec_congr (exec_congr_left eloop hscan_eq) ?_⟩
        have hge := ceil_div_mul_ge L M hL0
        have hzero : M - ((M + L - 1) / L) * L = 0 := by omega
        have hmin : min ((M + L - 1) / L) (M / L) = M / L :=
          Nat.min_eq_right (div_le_ceil_div L M hL0)
        funext k
        cases k <;> simp [divStore, divFinalStore, L, M, hzero, hmin, hL_ne]
      exact exec_le_of_le (exec_branch_true_le _ _ _ htest elp') (by omega)
    · have hL_eq : L = 0 := by omega
      have htest : (fun h : DKey → Option SaveSym => (h .L).isSome)
          (fun k => (scanStore cells cells.length k).head?) = false := by
        rw [hscan_eq]
        show (List.replicate L dTok).head?.isSome = false
        rw [hL_eq]
        rfl
      have hcl := (stack_basic_macros DKey.M (scanStore cells cells.length)).2.2
      have ecl : ∃ c ≤ 3 * M + 1,
          (clearProg .M).Exec (scanStore cells cells.length) (divFinalStore cells) c := by
        refine ⟨3 * (scanStore cells cells.length .M).length + 1, ?_, exec_congr hcl ?_⟩
        · simp [scanStore, M]
        · funext k
          cases k <;> simp [scanStore, divFinalStore, L, M, hL_eq]
      exact exec_le_of_le (exec_branch_false_le _ _ _ htest ecl) (by omega)
  have hmul : M * (12 * L + 10) ≤ cells.length * (12 * cells.length + 10) :=
    Nat.mul_le_mul hM_le (by omega)
  have hquad : cells.length * (12 * cells.length + 10) =
      12 * cells.length * cells.length + 10 * cells.length := by ring
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

def f_div_save (cells : List SaveSym) : List SaveSym :=
  divFinalStore cells .ko

def f_div_unit (cells : List SaveSym) : List Unit :=
  List.replicate (if countL cells = 0 then 0 else countM cells / countL cells) ()

lemma polyTimeComputable_div_unit :
    PolyTimeComputable f_div_unit ∧
    ∀ cells : List SaveSym, 0 < countL cells →
      (f_div_unit cells).length = countM cells / countL cells := by
  have hspec : ∀ cells : List SaveSym, 0 < countL cells →
      (f_div_unit cells).length = countM cells / countL cells := by
    intro cells hL
    have hne : countL cells ≠ 0 := by omega
    simp [f_div_unit, hne]
  refine ⟨?_, hspec⟩
  obtain ⟨k, hk⟩ := polynomial_absorb 34 2 0
  have hdiv_save : PolyTimeComputable f_div_save := by
    refine stack_program_polytime divMainProg .ki .ko f_div_save k (fun cells => ?_)
    obtain ⟨c, hc, hexec⟩ := exec_divMainProg cells
    have hbound : 12 * cells.length * cells.length + 16 * cells.length + 6 ≤
        34 * (cells.length + 1) ^ 2 + 0 := by nlinarith
    have hk_c := hk cells.length
    exact ⟨divFinalStore cells, c, by omega, hexec, rfl⟩
  rcases hdiv_save with ⟨Γ, hfinΓ, ι₁, ι₂, M_tm, k_tm, hM_tm⟩
  let ι₂' : Unit ↪ Γ := ⟨fun _ => ι₂ dTok, fun a b _ => Subsingleton.elim a b⟩
  refine ⟨Γ, hfinΓ, ι₁, ι₂', M_tm, k_tm, fun cells => ?_⟩
  obtain ⟨hhalt, hout⟩ := hM_tm cells
  refine ⟨hhalt, ?_⟩
  rw [hout]
  unfold f_div_save divFinalStore f_div_unit
  dsimp only
  set K := if countL cells = 0 then 0 else countM cells / countL cells
  clear_value K
  induction K with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.map_cons, Function.comp_apply, ih]
    rfl

end DivStackProof

section HeapWielandt

open SyncPrefix.Huffman

def valFlip : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 0 else 1) * 2 ^ w.length + valFlip w

lemma valFlip_lt (w : List Bool) : valFlip w < 2 ^ w.length := by
  induction w with
  | nil => simp [valFlip]
  | cons b w ih =>
    simp only [valFlip, List.length_cons, Nat.pow_add_one]
    split_ifs <;> omega

lemma valFlip_append_singleton (w : List Bool) (b : Bool) :
    valFlip (w ++ [b]) = 2 * valFlip w + (if b then 0 else 1) := by
  induction w with
  | nil =>
    simp only [List.nil_append, valFlip, List.length_nil, pow_zero]
    split_ifs <;> omega
  | cons a w ih =>
    simp only [List.cons_append, valFlip, List.length_append, List.length_singleton,
      Nat.pow_add_one, ih]
    split_ifs <;> ring

lemma valFlip_injective_of_length_eq :
    ∀ {w₁ w₂ : List Bool}, w₁.length = w₂.length → valFlip w₁ = valFlip w₂ → w₁ = w₂
  | [], [], _, _ => rfl
  | b₁ :: w₁, b₂ :: w₂, hlen, hval => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [valFlip, hlen] at hval
    have hlt₁ : valFlip w₁ < 2 ^ w₂.length := hlen ▸ valFlip_lt w₁
    have hlt₂ : valFlip w₂ < 2 ^ w₂.length := valFlip_lt w₂
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂
      · rfl
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, zero_mul, zero_add] at hval
        omega
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, zero_mul, zero_add] at hval
        omega
      · rfl
    subst hb
    congr 1
    exact valFlip_injective_of_length_eq hlen (by omega)

def heapIdx (w : List Bool) : ℕ :=
  2 ^ w.length - 1 + valFlip w

lemma heapIdx_nil : heapIdx [] = 0 := rfl

lemma heapIdx_bounds (w : List Bool) :
    2 ^ w.length - 1 ≤ heapIdx w ∧ heapIdx w < 2 ^ (w.length + 1) - 1 := by
  unfold heapIdx
  have hlt := valFlip_lt w
  have hpos : 1 ≤ 2 ^ w.length := Nat.one_le_two_pow
  rw [Nat.pow_add_one]
  omega

lemma heapIdx_append_singleton (w : List Bool) (b : Bool) :
    heapIdx (w ++ [b]) = 2 * heapIdx w + (if b then 1 else 2) := by
  unfold heapIdx
  rw [List.length_append, List.length_singleton, Nat.pow_add_one, valFlip_append_singleton]
  have hpos : 1 ≤ 2 ^ w.length := Nat.one_le_two_pow
  split_ifs <;> omega

lemma heapIdx_injective : Function.Injective heapIdx := by
  intro w₁ w₂ h
  have hb₁ := heapIdx_bounds w₁
  have hb₂ := heapIdx_bounds w₂
  have hlen : w₁.length = w₂.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpow : 2 ^ (w₁.length + 1) ≤ 2 ^ w₂.length :=
        Nat.pow_le_pow_right (by decide) hlt
      omega
    · have hpow : 2 ^ (w₂.length + 1) ≤ 2 ^ w₁.length :=
        Nat.pow_le_pow_right (by decide) hgt
      omega
  unfold heapIdx at h
  rw [hlen] at h
  exact valFlip_injective_of_length_eq hlen (by omega)

lemma mem_wielandtCode_iff (L : ℕ) (w : List Bool) :
    w ∈ wielandtCode L ↔
      (∃ u : List Bool, u.length = L - 1 ∧ w = false :: u) ∨
      (∃ u : List Bool, u.length = L ∧ w = true :: u) := by
  simp only [wielandtCode, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact Or.inl ⟨List.ofFn v, List.length_ofFn, rfl⟩
    · exact Or.inr ⟨List.ofFn v, List.length_ofFn, rfl⟩
  · rintro (⟨u, hlen, rfl⟩ | ⟨u, hlen, rfl⟩)
    · left
      refine ⟨fun i => u[i.val]'(by omega), ?_⟩
      congr 1
      exact List.ext_getElem (by simp [hlen]) (fun i h1 h2 => by simp)
    · right
      refine ⟨fun i => u[i.val]'(by omega), ?_⟩
      congr 1
      exact List.ext_getElem (by simp [hlen]) (fun i h1 h2 => by simp)

lemma mem_properPrefixes_wielandtCode_iff (L : ℕ) (hL : 1 ≤ L) (u : List Bool) :
    u ∈ properPrefixes (wielandtCode L) ↔
      u = [] ∨
      (∃ v : List Bool, v.length < L - 1 ∧ u = false :: v) ∨
      (∃ v : List Bool, v.length < L ∧ u = true :: v) := by
  simp only [properPrefixes, Finset.mem_insert, Finset.mem_filter, allPrefixes,
    Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  constructor
  · rintro (rfl | ⟨⟨z, hz, hpref⟩, hnot⟩)
    · exact Or.inl rfl
    · rcases u with _ | ⟨b, v⟩
      · exact Or.inl rfl
      · rw [mem_wielandtCode_iff] at hz hnot
        rcases hz with ⟨w, hwlen, rfl⟩ | ⟨w, hwlen, rfl⟩
        · simp only [List.cons_prefix_cons] at hpref
          rcases hpref with ⟨rfl, hpref⟩
          have hvlen : v.length ≤ L - 1 := hwlen ▸ hpref.length_le
          have hne : v.length ≠ L - 1 := fun heq => hnot (Or.inl ⟨v, heq, rfl⟩)
          exact Or.inr (Or.inl ⟨v, by omega, rfl⟩)
        · simp only [List.cons_prefix_cons] at hpref
          rcases hpref with ⟨rfl, hpref⟩
          have hvlen : v.length ≤ L := hwlen ▸ hpref.length_le
          have hne : v.length ≠ L := fun heq => hnot (Or.inr ⟨v, heq, rfl⟩)
          exact Or.inr (Or.inr ⟨v, by omega, rfl⟩)
  · rintro (rfl | ⟨v, hvlen, rfl⟩ | ⟨v, hvlen, rfl⟩)
    · exact Or.inl rfl
    · right
      refine ⟨⟨false :: (v ++ List.replicate (L - 1 - v.length) false), ?_, ?_⟩, ?_⟩
      · rw [mem_wielandtCode_iff]
        exact Or.inl ⟨v ++ List.replicate (L - 1 - v.length) false, by simp; omega, rfl⟩
      · simp only [List.cons_prefix_cons, true_and]
        exact List.prefix_append v _
      · rw [mem_wielandtCode_iff]
        rintro (⟨w, hwlen, hcons⟩ | ⟨w, _, hcons⟩)
        · injection hcons with _ hvw
          subst hvw
          omega
        · nomatch hcons
    · right
      refine ⟨⟨true :: (v ++ List.replicate (L - v.length) false), ?_, ?_⟩, ?_⟩
      · rw [mem_wielandtCode_iff]
        exact Or.inr ⟨v ++ List.replicate (L - v.length) false, by simp; omega, rfl⟩
      · simp only [List.cons_prefix_cons, true_and]
        exact List.prefix_append v _
      · rw [mem_wielandtCode_iff]
        rintro (⟨w, _, hcons⟩ | ⟨w, hwlen, hcons⟩)
        · nomatch hcons
        · injection hcons with _ hvw
          subst hvw
          omega

lemma append_mem_wielandtCode_or_properPrefixes (L : ℕ) (hL : 1 ≤ L)
    (u : List Bool) (hu : u ∈ properPrefixes (wielandtCode L)) (x : Bool) :
    u ++ [x] ∈ wielandtCode L ∨ u ++ [x] ∈ properPrefixes (wielandtCode L) := by
  rw [mem_properPrefixes_wielandtCode_iff L hL] at hu ⊢
  rw [mem_wielandtCode_iff]
  rcases hu with rfl | ⟨v, hvlen, rfl⟩ | ⟨v, hvlen, rfl⟩
  · cases x
    · by_cases h0 : L - 1 = 0
      · exact Or.inl (Or.inl ⟨[], by simp [h0], rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨[], by simp; omega, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨[], by simp; omega, rfl⟩))
  · by_cases heq : v.length + 1 = L - 1
    · exact Or.inl (Or.inl ⟨v ++ [x], by simp [heq], rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨v ++ [x], by simp; omega, rfl⟩))
  · by_cases heq : v.length + 1 = L
    · exact Or.inl (Or.inr ⟨v ++ [x], by simp [heq], rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨v ++ [x], by simp; omega, rfl⟩))

lemma properPrefixes_wielandtCode_card' (L : ℕ) (hL : 1 ≤ L) :
    (properPrefixes (wielandtCode L)).card = 3 * 2 ^ (L - 1) - 1 := by
  set Z := wielandtCode L
  obtain ⟨hMaxZ, hCardZ, -⟩ := wielandt_code L hL
  have hComp := (composition_decoder (fun (_ : Unit) (_ : Fin Z.card) => ()) Z hMaxZ
    (wielandtCodeEquiv L)).1
  simp only [Fintype.card_bool, Fintype.card_prod, Fintype.card_unit, Fintype.card_coe,
    one_mul] at hComp
  have hZ_pos : 0 < Z.card := by rw [hCardZ]; positivity
  have hZ_sub : Z ⊆ allPrefixes Z := by
    intro z hz
    simp only [allPrefixes, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
    exact ⟨z, hz, List.prefix_refl z⟩
  have hnil_all : [] ∈ allPrefixes Z := by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hZ_pos
    simp only [allPrefixes, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
    exact ⟨z, hz, List.nil_prefix⟩
  have hnil_not_Z : [] ∉ Z := hMaxZ.1.1
  have hpp_eq : properPrefixes Z = allPrefixes Z \ Z := by
    ext p
    simp only [properPrefixes, Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro (rfl | ⟨hp1, hp2⟩)
      · exact ⟨hnil_all, hnil_not_Z⟩
      · exact ⟨hp1, hp2⟩
    · rintro ⟨hp1, hp2⟩
      exact Or.inr ⟨hp1, hp2⟩
  have hcard_sdiff : (properPrefixes Z).card + Z.card = (allPrefixes Z).card := by
    rw [hpp_eq]
    exact Finset.card_sdiff_add_card_eq_card hZ_sub
  change Z.card = 3 * 2 ^ (L - 1) at hCardZ
  omega

lemma heapIdx_lt_of_mem_properPrefixes (L : ℕ) (hL : 1 ≤ L)
    (u : List Bool) (hu : u ∈ properPrefixes (wielandtCode L)) :
    heapIdx u < 3 * 2 ^ (L - 1) - 1 := by
  have hpowL : 2 ^ L = 2 * 2 ^ (L - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hL, Nat.pow_add_one]
    ring
  have hpos : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  rw [mem_properPrefixes_wielandtCode_iff L hL] at hu
  rcases hu with rfl | ⟨v, hvlen, rfl⟩ | ⟨v, hvlen, rfl⟩
  · simp only [heapIdx_nil]
    omega
  · have hb := (heapIdx_bounds (false :: v)).2
    have hle : (false :: v).length + 1 ≤ L := by simp; omega
    have hpow : 2 ^ ((false :: v).length + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hle
    omega
  · by_cases hv : v.length < L - 1
    · have hb := (heapIdx_bounds (true :: v)).2
      have hle : (true :: v).length + 1 ≤ L := by simp; omega
      have hpow : 2 ^ ((true :: v).length + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hle
      omega
    · have hveq : v.length = L - 1 := by omega
      have hvlt : valFlip v < 2 ^ (L - 1) := hveq ▸ valFlip_lt v
      unfold heapIdx valFlip
      simp only [List.length_cons, hveq, Nat.sub_add_cancel hL, ↓reduceIte, zero_mul, zero_add]
      omega

lemma heapIdx_bounds_of_mem_wielandtCode (L : ℕ) (hL : 1 ≤ L)
    (z : List Bool) (hz : z ∈ wielandtCode L) :
    3 * 2 ^ (L - 1) - 1 ≤ heapIdx z ∧
      heapIdx z - (3 * 2 ^ (L - 1) - 1) < (wielandtCode L).card := by
  have hCardZ : (wielandtCode L).card = 3 * 2 ^ (L - 1) := (wielandt_code L hL).2.1
  have hpowL : 2 ^ L = 2 * 2 ^ (L - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hL, Nat.pow_add_one]
    ring
  have hpowL1 : 2 ^ (L + 1) = 4 * 2 ^ (L - 1) := by
    rw [Nat.pow_add_one, hpowL]; ring
  have hpos : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  rw [mem_wielandtCode_iff] at hz
  rcases hz with ⟨u, hulen, rfl⟩ | ⟨u, hulen, rfl⟩
  · have hult : valFlip u < 2 ^ (L - 1) := hulen ▸ valFlip_lt u
    unfold heapIdx valFlip
    simp only [List.length_cons, hulen, Nat.sub_add_cancel hL, Bool.false_eq_true, ↓reduceIte,
      one_mul, hCardZ]
    omega
  · have hult : valFlip u < 2 ^ L := hulen ▸ valFlip_lt u
    unfold heapIdx valFlip
    simp only [List.length_cons, hulen, ↓reduceIte, zero_mul, zero_add, hCardZ]
    omega

noncomputable def heapProperPrefixEquiv (L : ℕ) (hL : 1 ≤ L) :
    {u // u ∈ properPrefixes (wielandtCode L)} ≃ Fin (properPrefixes (wielandtCode L)).card := by
  let f : {u // u ∈ properPrefixes (wielandtCode L)} → Fin (properPrefixes (wielandtCode L)).card :=
    fun u => ⟨heapIdx u.val, by
      rw [properPrefixes_wielandtCode_card' L hL]
      exact heapIdx_lt_of_mem_properPrefixes L hL u.val u.property⟩
  have hinj : Function.Injective f := by
    intro u₁ u₂ h
    apply Subtype.ext
    exact heapIdx_injective (Fin.ext_iff.mp h)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  exact Equiv.ofBijective f hbij

@[simp]
lemma heapProperPrefixEquiv_apply_val (L : ℕ) (hL : 1 ≤ L)
    (u : {u // u ∈ properPrefixes (wielandtCode L)}) :
    (heapProperPrefixEquiv L hL u).val = heapIdx u.val := rfl

noncomputable def heapWielandtCodeEquiv (L : ℕ) (hL : 1 ≤ L) :
    Fin (wielandtCode L).card ≃ {z // z ∈ wielandtCode L} := by
  let P := 3 * 2 ^ (L - 1) - 1
  let g : {z // z ∈ wielandtCode L} → Fin (wielandtCode L).card :=
    fun z => ⟨heapIdx z.val - P, (heapIdx_bounds_of_mem_wielandtCode L hL z.val z.property).2⟩
  have hinj : Function.Injective g := by
    intro z₁ z₂ h
    have hval : heapIdx z₁.val - P = heapIdx z₂.val - P := Fin.ext_iff.mp h
    have hb₁ := (heapIdx_bounds_of_mem_wielandtCode L hL z₁.val z₁.property).1
    have hb₂ := (heapIdx_bounds_of_mem_wielandtCode L hL z₂.val z₂.property).1
    apply Subtype.ext
    exact heapIdx_injective (by omega)
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  exact (Equiv.ofBijective g hbij).symm

@[simp]
lemma heapWielandtCodeEquiv_symm_apply_val (L : ℕ) (hL : 1 ≤ L)
    (z : {z // z ∈ wielandtCode L}) :
    ((heapWielandtCodeEquiv L hL).symm z).val = heapIdx z.val - (3 * 2 ^ (L - 1) - 1) := rfl

noncomputable def heapWielandtStateEquiv (n L : ℕ) (hL : 1 ≤ L) :
    DecoderState (Fin n) (wielandtCode L) ≃ Fin (n * (properPrefixes (wielandtCode L)).card) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (heapProperPrefixEquiv L hL)).trans finProdFinEquiv

noncomputable def heapWielandtAB (AH : Automaton) (hL : 1 ≤ wielandtL AH.k) : Automaton :=
  let L := wielandtL AH.k
  let Z := wielandtCode L
  let δY := dupTransition AH Z.card
  let e := heapWielandtCodeEquiv L hL
  let es := heapWielandtStateEquiv AH.n L hL
  { n := AH.n * (properPrefixes Z).card
    k := 2
    δ := fun s a => es (composeDecoder δY Z e (es.symm s) (fin2EquivBool a)) }

lemma heapWielandtStateEquiv_apply_val (n L : ℕ) (hL : 1 ≤ L)
    (q : Fin n) (u : {u // u ∈ properPrefixes (wielandtCode L)}) :
    (heapWielandtStateEquiv n L hL (q, u)).val =
      q.val * (properPrefixes (wielandtCode L)).card + heapIdx u.val := by
  simp [heapWielandtStateEquiv, finProdFinEquiv]
  ring

lemma heapWielandtStateEquiv_symm_fst_val (n L : ℕ) (hL : 1 ≤ L)
    (s : Fin (n * (properPrefixes (wielandtCode L)).card)) :
    ((heapWielandtStateEquiv n L hL).symm s).1.val =
      s.val / (properPrefixes (wielandtCode L)).card := by
  set p := (heapWielandtStateEquiv n L hL).symm s
  have hs : heapWielandtStateEquiv n L hL p = s := Equiv.apply_symm_apply _ s
  have hval : s.val = p.1.val * (properPrefixes (wielandtCode L)).card + (heapProperPrefixEquiv L hL p.2).val := by
    rw [← hs]
    exact heapWielandtStateEquiv_apply_val n L hL p.1 p.2
  have hlt : (heapProperPrefixEquiv L hL p.2).val < (properPrefixes (wielandtCode L)).card :=
    (heapProperPrefixEquiv L hL p.2).isLt
  have hP : 0 < (properPrefixes (wielandtCode L)).card := by omega
  rw [hval, Nat.mul_comm p.1.val, Nat.mul_add_div hP, Nat.div_eq_of_lt hlt, add_zero]

lemma heapWielandtStateEquiv_symm_snd_heapIdx (n L : ℕ) (hL : 1 ≤ L)
    (s : Fin (n * (properPrefixes (wielandtCode L)).card)) :
    heapIdx ((heapWielandtStateEquiv n L hL).symm s).2.val =
      s.val % (properPrefixes (wielandtCode L)).card := by
  set p := (heapWielandtStateEquiv n L hL).symm s
  have hs : heapWielandtStateEquiv n L hL p = s := Equiv.apply_symm_apply _ s
  have hval : s.val = p.1.val * (properPrefixes (wielandtCode L)).card + heapIdx p.2.val := by
    rw [← hs]
    exact heapWielandtStateEquiv_apply_val n L hL p.1 p.2
  have hlt : heapIdx p.2.val < (properPrefixes (wielandtCode L)).card :=
    (heapProperPrefixEquiv L hL p.2).isLt
  rw [hval, Nat.mul_comm p.1.val, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma heapWielandtAB_q_lt (AH : Automaton) (hL : 1 ≤ wielandtL AH.k)
    (s : Fin (heapWielandtAB AH hL).n) :
    s.val / (3 * 2 ^ (wielandtL AH.k - 1) - 1) < AH.n := by
  have hP_eq : (properPrefixes (wielandtCode (wielandtL AH.k))).card =
      3 * 2 ^ (wielandtL AH.k - 1) - 1 :=
    properPrefixes_wielandtCode_card' (wielandtL AH.k) hL
  have hs : s.val < AH.n * (properPrefixes (wielandtCode (wielandtL AH.k))).card := s.isLt
  rw [hP_eq, Nat.mul_comm] at hs
  exact Nat.div_lt_of_lt_mul hs

lemma heapWielandtAB_delta_val (AH : Automaton) (hk : 2 ≤ AH.k)
    (hL : 1 ≤ wielandtL AH.k)
    (s : Fin (heapWielandtAB AH hL).n) (a : Fin 2) :
    let L := wielandtL AH.k
    let P := 3 * 2 ^ (L - 1) - 1
    let q := s.val / P
    let p := s.val % P
    let child := 2 * p + (2 - a.val)
    ((heapWielandtAB AH hL).δ s a).val =
      if child < P then
        q * P + child
      else if hlt : child - P < AH.k then
        (AH.δ ⟨q, heapWielandtAB_q_lt AH hL s⟩ ⟨child - P, hlt⟩).val * P
      else
        (AH.δ ⟨q, heapWielandtAB_q_lt AH hL s⟩ ⟨0, by omega⟩).val * P := by
  intro L P q p child
  have hP_eq : (properPrefixes (wielandtCode L)).card = P :=
    properPrefixes_wielandtCode_card' L hL
  set Z := wielandtCode L
  set δY := dupTransition AH Z.card
  set e := heapWielandtCodeEquiv L hL
  set es := heapWielandtStateEquiv AH.n L hL
  let s' : Fin (AH.n * (properPrefixes Z).card) := s
  set su := es.symm s'
  have hq_val : su.1.val = q := by
    have h1 := heapWielandtStateEquiv_symm_fst_val AH.n L hL s'
    change su.1.val = s.val / (properPrefixes Z).card at h1
    rw [h1, hP_eq]
  have hp_val : heapIdx su.2.val = p := by
    have h1 := heapWielandtStateEquiv_symm_snd_heapIdx AH.n L hL s'
    change heapIdx su.2.val = s.val % (properPrefixes Z).card at h1
    rw [h1, hP_eq]
  set x := fin2EquivBool a
  have hchild : heapIdx (su.2.val ++ [x]) = child := by
    rw [heapIdx_append_singleton, hp_val]
    have ha : (if x then 1 else 2) = 2 - a.val := by
      fin_cases a <;> rfl
    omega
  change (es (composeDecoder δY Z e su x)).val = _
  unfold composeDecoder
  have hor := append_mem_wielandtCode_or_properPrefixes L hL su.2.val su.2.property x
  by_cases hz : su.2.val ++ [x] ∈ Z
  · have hchild_ge : P ≤ child := by
      rw [← hchild]
      exact (heapIdx_bounds_of_mem_wielandtCode L hL _ hz).1
    have hnot_lt : ¬ child < P := by omega
    simp only [hz, ↓reduceDIte, hnot_lt, ↓reduceIte]
    unfold rootState
    rw [heapWielandtStateEquiv_apply_val, heapIdx_nil, add_zero, hP_eq]
    have he_val : (e.symm ⟨su.2.val ++ [x], hz⟩).val = child - P := by
      rw [heapWielandtCodeEquiv_symm_apply_val, hchild]
    have hsu1 : su.1 = ⟨q, heapWielandtAB_q_lt AH hL s⟩ := Fin.ext hq_val
    unfold δY dupTransition
    have h0 : 0 < AH.k := by omega
    simp only [he_val, hsu1, h0, ↓reduceDIte]
    split_ifs <;> rfl
  · have hpp : su.2.val ++ [x] ∈ properPrefixes Z := by
      rcases hor with h1 | h2
      · exact absurd h1 hz
      · exact h2
    have hchild_lt : child < P := by
      rw [← hchild]
      exact heapIdx_lt_of_mem_properPrefixes L hL _ hpp
    simp only [hz, hpp, ↓reduceDIte, hchild_lt, ↓reduceIte]
    rw [heapWielandtStateEquiv_apply_val, hP_eq, hq_val, hchild]

end HeapWielandt

section WielandtStackProof

open SyncPrefix.Huffman CookPvsNP

inductive WKey where
  | ki
  | ko
  | outRev
  | N
  | K
  | L
  | M0
  | P
  | Nrem
  | QP
  | PI
  | Prem
  | CHD
  | VAL
  | W
  | C1
  | C2
  | sc
  deriving DecidableEq

instance : Fintype WKey where
  elems := {.ki, .ko, .outRev, .N, .K, .L, .M0, .P, .Nrem, .QP, .PI, .Prem, .CHD, .VAL, .W, .C1, .C2, .sc}
  complete x := by cases x <;> decide

abbrev WProg := StackProg WKey Sym
abbrev WStore := WKey → List Sym

lemma w_exec_congr {p : WProg} {s t t' : WStore} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma w_exec_congr_left {p : WProg} {s s' t : WStore} {n : ℕ}
    (h : p.Exec s t n) (hs : s' = s) : p.Exec s' t n := hs ▸ h

lemma w_exec_seq_le {p q : WProg} {s t u : WStore} {B1 B2 : ℕ}
    (h1 : ∃ c1 ≤ B1, p.Exec s t c1) (h2 : ∃ c2 ≤ B2, q.Exec t u c2) :
    ∃ c ≤ B1 + 1 + B2, (p.seq q).Exec s u c := by
  rcases h1 with ⟨c1, hc1, e1⟩
  rcases h2 with ⟨c2, hc2, e2⟩
  exact ⟨c1 + 1 + c2, by omega, StackProg.Exec.seq e1 e2⟩

lemma w_exec_le_of_le {p : WProg} {s t : WStore} {B B' : ℕ}
    (h : ∃ c ≤ B, p.Exec s t c) (hB : B ≤ B') :
    ∃ c ≤ B', p.Exec s t c := by
  rcases h with ⟨c, hc, e⟩
  exact ⟨c, le_trans hc hB, e⟩

lemma w_exec_branch_true_le (test : (WKey → Option Sym) → Bool) (p q : WProg)
    {s t : WStore} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true)
    (hp : ∃ c ≤ B, p.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hp with ⟨c, hc, ep⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchTrue ht ep⟩

lemma w_exec_branch_false_le (test : (WKey → Option Sym) → Bool) (p q : WProg)
    {s t : WStore} {B : ℕ}
    (hf : test (fun k => (s k).head?) = false)
    (hq : ∃ c ≤ B, q.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hq with ⟨c, hc, eq⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchFalse hf eq⟩

lemma w_exec_bounded_loop (test : (WKey → Option Sym) → Bool) (p : WProg)
    (n : ℕ) (s : ℕ → WStore) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, ∃ c ≤ B, p.Exec (s i) (s (i + 1)) c) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by
  classical
  let cost : ℕ → ℕ := fun i => if h : i < n then Classical.choose (hb i h) else 0
  refine stack_bounded_loop test p n s cost B hg he ?_ ?_
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).2
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).1

lemma w_head?_replicate_isSome (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isSome = true := by
  cases n with
  | zero => omega
  | succ _ => rfl

lemma w_head?_replicate_isNone_false (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isNone = false := by
  cases n with
  | zero => omega
  | succ _ => rfl

def encUnary (v : ℕ) : List Sym := List.replicate v (some true) ++ [none]

def emitUnaryTo (src dst : WKey) : WProg :=
  .seq (copyProg src dst .sc) (pushProg dst none)

lemma exec_emitUnaryTo (src dst : WKey) (hsd : src ≠ dst) (hst : src ≠ .sc) (hdt : dst ≠ .sc)
    (s : WStore) (v : ℕ) (hsrc : s src = List.replicate v (some true)) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 5,
      (emitUnaryTo src dst).Exec s
        (Function.update s dst ((encUnary v).reverse ++ s dst)) c := by
  have e1 := stack_copy src dst .sc hsd hst hdt s hsc
  set s1 := Function.update s dst (s src ++ s dst)
  have e2 := (stack_basic_macros dst s1).1 none
  refine ⟨(6 * (s src).length + 3) + 1 + 1, by simp [hsrc], ?_⟩
  refine w_exec_congr (StackProg.Exec.seq e1 e2) ?_
  funext k
  cases k <;> simp [s1, hsrc, encUnary, List.reverse_append]

def leadOnes : List Sym → ℕ
  | some true :: xs => leadOnes xs + 1
  | _ => 0

lemma leadOnes_le : ∀ w : List Sym, leadOnes w ≤ w.length
  | [] => by simp [leadOnes]
  | none :: _ => by simp [leadOnes]
  | some false :: _ => by simp [leadOnes]
  | some true :: xs => by
    simp only [leadOnes, List.length_cons]
    have := leadOnes_le xs
    omega

lemma head?_drop_of_lt_leadOnes : ∀ (w : List Sym) (i : ℕ), i < leadOnes w →
    (w.drop i).head? = some (some true)
  | some true :: _, 0, _ => rfl
  | some true :: xs, i + 1, hi => by
    simp only [leadOnes] at hi
    exact head?_drop_of_lt_leadOnes xs i (by omega)
  | [], _, hi => by simp [leadOnes] at hi
  | none :: _, _, hi => by simp [leadOnes] at hi
  | some false :: _, _, hi => by simp [leadOnes] at hi

lemma head?_drop_leadOnes : ∀ w : List Sym,
    (w.drop (leadOnes w)).head? ≠ some (some true)
  | [] => by simp [leadOnes]
  | none :: _ => by simp [leadOnes]
  | some false :: _ => by simp [leadOnes]
  | some true :: xs => by
    simp only [leadOnes, List.drop_succ_cons]
    exact head?_drop_leadOnes xs

lemma tail_drop_eq_drop_succ (w : List Sym) (i : ℕ) :
    (w.drop i).tail = w.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, add_comm]

def nextWord (w : List Sym) : List Sym := (w.drop (leadOnes w)).tail

def wordAt (w : List Sym) : ℕ → List Sym
  | 0 => w
  | i + 1 => nextWord (wordAt w i)

def valAt (w : List Sym) (i : ℕ) : ℕ := leadOnes (wordAt w i)

lemma wordAt_wordAt (w : List Sym) (a : ℕ) : ∀ b : ℕ,
    wordAt (wordAt w a) b = wordAt w (a + b)
  | 0 => rfl
  | b + 1 => by
    change nextWord (wordAt (wordAt w a) b) = nextWord (wordAt w (a + b))
    rw [wordAt_wordAt w a b]

lemma valAt_wordAt (w : List Sym) (a b : ℕ) :
    valAt (wordAt w a) b = valAt w (a + b) := by
  unfold valAt
  rw [wordAt_wordAt]

lemma length_nextWord_le (w : List Sym) : (nextWord w).length ≤ w.length := by
  simp [nextWord]

lemma length_wordAt_le (w : List Sym) : ∀ i : ℕ, (wordAt w i).length ≤ w.length
  | 0 => le_rfl
  | i + 1 => le_trans (length_nextWord_le (wordAt w i)) (length_wordAt_le w i)

lemma valAt_le_length (w : List Sym) (i : ℕ) : valAt w i ≤ w.length :=
  le_trans (leadOnes_le (wordAt w i)) (length_wordAt_le w i)

def readUnaryAct (src dst : WKey) (_h : WKey → Option Sym) (k : WKey) : StackAct Sym :=
  if k = src then .pop else if k = dst then .push (some true) else .keep

def readUnaryLoop (src dst : WKey) : WProg :=
  .loop (fun h => decide (h src = some (some true))) (.act (readUnaryAct src dst))

def readUnaryProg (src dst : WKey) : WProg :=
  .seq (readUnaryLoop src dst) (popProg src)

def sReadUnary (src dst : WKey) (s : WStore) (i : ℕ) : WStore :=
  Function.update (Function.update s src ((s src).drop i))
    dst (List.replicate i (some true))

lemma exec_readUnaryProg_raw (src dst : WKey) (hsd : src ≠ dst)
    (s : WStore) (hdst : s dst = []) :
    ∃ c ≤ 3 * leadOnes (s src) + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (nextWord (s src)))
          dst (List.replicate (leadOnes (s src)) (some true))) c := by
  have hloop : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec (sReadUnary src dst s 0)
        (sReadUnary src dst s (leadOnes (s src))) c1 := by
    refine w_exec_bounded_loop (fun h => decide (h src = some (some true)))
      (.act (readUnaryAct src dst)) (leadOnes (s src)) (sReadUnary src dst s) 1 ?_ ?_ ?_
    · intro i hi
      have hsrc_i : sReadUnary src dst s i src = (s src).drop i := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [decide_eq_true_eq, hsrc_i]
      exact head?_drop_of_lt_leadOnes (s src) i hi
    · have hsrc_n : sReadUnary src dst s (leadOnes (s src)) src = (s src).drop (leadOnes (s src)) := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [decide_eq_false_iff_not, hsrc_n]
      exact head?_drop_leadOnes (s src)
    · intro i _
      refine ⟨1, le_rfl, w_exec_congr (StackProg.Exec.act (readUnaryAct src dst) (sReadUnary src dst s i)) ?_⟩
      funext k
      by_cases hks : k = src
      · subst hks
        simp [StackProg.applyAct, readUnaryAct, sReadUnary, hsd, StackAct.apply, tail_drop_eq_drop_succ]
      · by_cases hkd : k = dst
        · subst hkd
          simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, StackAct.apply, List.replicate_succ]
        · simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, hkd, StackAct.apply]
  have h0 : s = sReadUnary src dst s 0 := by
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hdst]
      · simp [sReadUnary, hks, hkd]
  rcases hloop with ⟨c1, hc1, eloop⟩
  have hloop' : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec s
        (sReadUnary src dst s (leadOnes (s src))) c1 := ⟨c1, hc1, w_exec_congr_left eloop h0⟩
  have hpop : ∃ c2 ≤ 1, (popProg src).Exec (sReadUnary src dst s (leadOnes (s src)))
      (Function.update (Function.update s src (nextWord (s src)))
        dst (List.replicate (leadOnes (s src)) (some true))) c2 := by
    refine ⟨1, le_rfl, w_exec_congr (stack_basic_macros src (sReadUnary src dst s (leadOnes (s src)))).2.1 ?_⟩
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd, nextWord]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hks]
      · simp [sReadUnary, hks, hkd]
  exact w_exec_le_of_le (w_exec_seq_le hloop' hpop) (by omega)

lemma exec_readUnaryProg_wordAt (src dst : WKey) (hsd : src ≠ dst)
    (s : WStore) (w : List Sym) (idx : ℕ)
    (hsrc : s src = wordAt w idx) (hdst : s dst = []) :
    ∃ c ≤ 3 * w.length + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (wordAt w (idx + 1)))
          dst (List.replicate (valAt w idx) (some true))) c := by
  have hraw := exec_readUnaryProg_raw src dst hsd s hdst
  rw [hsrc] at hraw
  have hv : leadOnes (wordAt w idx) ≤ w.length := valAt_le_length w idx
  exact w_exec_le_of_le hraw (by omega)

def advanceWordsBody (wStack cntStack tmpStack : WKey) : WProg :=
  .seq (popProg cntStack)
    (.seq (readUnaryProg wStack tmpStack)
      (clearProg tmpStack))

def advanceWordsProg (wStack cntStack tmpStack : WKey) : WProg :=
  .loop (fun h => (h cntStack).isSome) (advanceWordsBody wStack cntStack tmpStack)

def sAdvanceWords (wStack cntStack : WKey) (s : WStore) (w : List Sym) (m i : ℕ) : WStore :=
  Function.update (Function.update s wStack (wordAt w i))
    cntStack (List.replicate (m - i) (some true))

lemma exec_advanceWordsProg (wStack cntStack tmpStack : WKey)
    (hwc : wStack ≠ cntStack) (hwt : wStack ≠ tmpStack) (hct : cntStack ≠ tmpStack)
    (s : WStore) (w : List Sym) (m : ℕ)
    (hw : s wStack = w) (hcnt : s cntStack = List.replicate m (some true))
    (htmp : s tmpStack = []) :
    ∃ c ≤ m * (6 * w.length + 10) + 1,
      (advanceWordsProg wStack cntStack tmpStack).Exec s
        (Function.update (Function.update s wStack (wordAt w m)) cntStack []) c := by
  have h0 : s = sAdvanceWords wStack cntStack s w m 0 := by
    funext k
    by_cases h1 : k = cntStack
    · subst h1; simp [sAdvanceWords, hcnt]
    · by_cases h2 : k = wStack
      · subst h2; simp [sAdvanceWords, h1, hw, wordAt]
      · simp [sAdvanceWords, h1, h2]
  have hloop := w_exec_bounded_loop (fun h => (h cntStack).isSome)
    (advanceWordsBody wStack cntStack tmpStack) m
    (sAdvanceWords wStack cntStack s w m) (6 * w.length + 8)
    (fun i hi => by
      dsimp only
      have hcnt_i : sAdvanceWords wStack cntStack s w m i cntStack = List.replicate (m - i) (some true) := by
        simp [sAdvanceWords]
      rw [hcnt_i]
      exact w_head?_replicate_isSome (m - i) (some true) (by omega))
    (by
      dsimp only
      have hcnt_m : sAdvanceWords wStack cntStack s w m m cntStack = [] := by
        simp [sAdvanceWords]
      rw [hcnt_m]
      rfl)
    (fun i hi => by
      set si := sAdvanceWords wStack cntStack s w m i
      have hp1 := (stack_basic_macros cntStack si).2.1
      set s1 := Function.update si cntStack (si cntStack).tail
      have e1 : ∃ c ≤ 1, (popProg cntStack).Exec si s1 c := ⟨1, le_rfl, hp1⟩
      have hs1_w : s1 wStack = wordAt w i := by
        simp [s1, si, sAdvanceWords, hwc]
      have hs1_tmp : s1 tmpStack = [] := by
        simp [s1, si, sAdvanceWords, hct.symm, hwt.symm, htmp]
      have e2 := exec_readUnaryProg_wordAt wStack tmpStack hwt s1 w i hs1_w hs1_tmp
      set s2 := Function.update (Function.update s1 wStack (wordAt w (i + 1)))
        tmpStack (List.replicate (valAt w i) (some true))
      have hcl := (stack_basic_macros tmpStack s2).2.2
      have hv_le : valAt w i ≤ w.length := valAt_le_length w i
      have e3 : ∃ c ≤ 3 * w.length + 1,
          (clearProg tmpStack).Exec s2 (sAdvanceWords wStack cntStack s w m (i + 1)) c := by
        refine ⟨3 * (s2 tmpStack).length + 1, ?_, w_exec_congr hcl ?_⟩
        · simp [s2]; omega
        · have hsub : m - i - 1 = m - (i + 1) := by omega
          funext k
          by_cases hk1 : k = cntStack
          · subst hk1
            simp [s2, s1, si, sAdvanceWords, hct, hwc.symm, List.tail_replicate, hsub]
          · by_cases hk2 : k = wStack
            · subst hk2
              simp [s2, s1, si, sAdvanceWords, hwt, hk1]
            · by_cases hk3 : k = tmpStack
              · subst hk3
                simp [s2, s1, si, sAdvanceWords, hk1, hk2, htmp]
              · simp [s2, s1, si, sAdvanceWords, hk1, hk2, hk3]
      exact w_exec_le_of_le (w_exec_seq_le e1 (w_exec_seq_le e2 e3)) (by omega))
  rcases hloop with ⟨c, hc, eloop⟩
  refine ⟨c, hc, w_exec_congr (w_exec_congr_left eloop h0) ?_⟩
  simp [sAdvanceWords]

lemma flatten_replicate_replicate (m P : ℕ) (a : Sym) :
    (List.replicate m (List.replicate P a)).flatten = List.replicate (m * P) a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, ← List.replicate_add]
    congr 1
    ring

def mulPEmb : Fin 4 ↪ WKey where
  toFun
    | ⟨0, _⟩ => .P
    | ⟨1, _⟩ => .VAL
    | ⟨2, _⟩ => .C2
    | ⟨_ + 3, _⟩ => .sc
  inj' i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | cases h

lemma exec_mulPEmb (s : WStore) (P v : ℕ)
    (hP : s .P = List.replicate P (some true))
    (hVAL : s .VAL = [])
    (hC2 : s .C2 = List.replicate v (some true))
    (hsc : s .sc = []) :
    ∃ c ≤ (6 * P + 7) * v + 1,
      (repeatCopyProg mulPEmb).Exec s
        (Function.update (Function.update s .C2 []) .VAL (List.replicate (v * P) (some true))) c := by
  have hm0 : mulPEmb 0 = .P := rfl
  have hm1 : mulPEmb 1 = .VAL := rfl
  have hm2 : mulPEmb 2 = .C2 := rfl
  have hm3 : mulPEmb 3 = .sc := rfl
  have hrep := stack_repeat_copy mulPEmb s (by rw [hm3, hsc])
  refine ⟨(6 * (s (mulPEmb 0)).length + 7) * (s (mulPEmb 2)).length + 1, ?_, w_exec_congr hrep ?_⟩
  · simp [hm0, hm2, hP, hC2]
  · simp [hm0, hm1, hm2, hP, hVAL, hC2, flatten_replicate_replicate]

def readMulPEmitProg : WProg :=
  .seq (readUnaryProg .W .C2)
    (.seq (repeatCopyProg mulPEmb)
      (.seq (emitUnaryTo .VAL .outRev)
        (.seq (clearProg .VAL)
          (clearProg .W))))

lemma exec_readMulPEmitProg (s : WStore) (u : List Sym) (P : ℕ)
    (hW : s .W = u)
    (hP : s .P = List.replicate P (some true))
    (hVAL : s .VAL = []) (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ (15 * P + 13) * u.length + 15,
      readMulPEmitProg.Exec s
        (Function.update (Function.update s .W [])
          .outRev ((encUnary (leadOnes u * P)).reverse ++ s .outRev)) c := by
  set v := leadOnes u
  have hv_le : v ≤ u.length := leadOnes_le u
  have e1 := exec_readUnaryProg_raw .W .C2 (by decide) s hC2
  rw [hW] at e1
  set s1 := Function.update (Function.update s .W (nextWord u)) .C2 (List.replicate v (some true))
  have e2 := exec_mulPEmb s1 P v (by simp [s1, hP]) (by simp [s1, hVAL])
    (by simp [s1]) (by simp [s1, hsc])
  set s2 := Function.update (Function.update s1 .C2 []) .VAL (List.replicate (v * P) (some true))
  have e3 := exec_emitUnaryTo .VAL .outRev (by decide) (by decide) (by decide) s2 (v * P)
    (by simp [s2]) (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .outRev ((encUnary (v * P)).reverse ++ s2 .outRev)
  have hcl4 := (stack_basic_macros WKey.VAL s3).2.2
  set s4 := Function.update s3 .VAL []
  have e4 : ∃ c ≤ 3 * (v * P) + 1, (clearProg .VAL).Exec s3 s4 c := by
    refine ⟨3 * (s3 .VAL).length + 1, ?_, hcl4⟩
    simp [s3, s2]
  have hcl5 := (stack_basic_macros WKey.W s4).2.2
  have hnw_le : (nextWord u).length ≤ u.length := length_nextWord_le u
  have e5 : ∃ c ≤ 3 * u.length + 1,
      (clearProg .W).Exec s4
        (Function.update (Function.update s .W [])
          .outRev ((encUnary (v * P)).reverse ++ s .outRev)) c := by
    refine ⟨3 * (s4 .W).length + 1, ?_, w_exec_congr hcl5 ?_⟩
    · simp [s4, s3, s2, s1]; omega
    · funext k
      cases k <;> simp [s4, s3, s2, s1, hVAL, hC2]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 e5)))
  refine w_exec_le_of_le e_all ?_
  have hmul1 : (6 * P + 7) * v ≤ (6 * P + 7) * u.length := Nat.mul_le_mul_left _ hv_le
  have hmul2 : v * P ≤ u.length * P := Nat.mul_le_mul_right P hv_le
  have h3v : 3 * leadOnes u ≤ 3 * u.length := by omega
  nlinarith

def transValU (u : List Sym) (k P q child : ℕ) : ℕ :=
  if child < P then
    q * P + child
  else if child - P < k then
    valAt u (child - P) * P
  else
    valAt u 0 * P

def emitChildLtProg : WProg :=
  .seq (clearProg .C1)
    (.seq (clearProg .C2)
      (.seq (copyProg .QP .VAL .sc)
        (.seq (copyProg .CHD .VAL .sc)
          (.seq (emitUnaryTo .VAL .outRev)
            (.seq (clearProg .VAL)
              (clearProg .CHD))))))

def emitChildGeLtKProg : WProg :=
  .seq (clearProg .VAL)
    (.seq (clearProg .C2)
      (.seq (copyProg .ki .W .sc)
        (.seq (advanceWordsProg .W .C1 .C2)
          readMulPEmitProg)))

def emitChildGeGeKProg : WProg :=
  .seq (clearProg .VAL)
    (.seq (clearProg .C2)
      (.seq (clearProg .C1)
        (.seq (copyProg .ki .W .sc)
          readMulPEmitProg)))

def emitChildGeProg : WProg :=
  .seq (clearProg .CHD)
    (.seq (copyProg .C1 .VAL .sc)
      (.seq (copyProg .K .C2 .sc)
        (.seq (syncPopProg .VAL .C2)
          (.branch (fun h => (h .C2).isSome)
            emitChildGeLtKProg
            emitChildGeGeKProg))))

def emitChildProg : WProg :=
  .seq (copyProg .CHD .C1 .sc)
    (.seq (copyProg .P .C2 .sc)
      (.seq (syncPopProg .C1 .C2)
        (.branch (fun h => (h .C2).isSome)
          emitChildLtProg
          emitChildGeProg)))

lemma exec_emitChildLtProg (s : WStore) (P q child : ℕ) (hlt : child < P)
    (hQP : s .QP = List.replicate (q * P) (some true))
    (hCHD : s .CHD = List.replicate child (some true))
    (hVAL : s .VAL = [])
    (hC1 : s .C1 = [])
    (hC2 : s .C2 = List.replicate (P - child) (some true))
    (hsc : s .sc = []) :
    ∃ c ≤ 15 * (q * P) + 21 * P + 21,
      emitChildLtProg.Exec s
        (Function.update (Function.update (Function.update s .C2 []) .CHD [])
          .outRev ((encUnary (q * P + child)).reverse ++ s .outRev)) c := by
  have hcl1 := (stack_basic_macros WKey.C1 s).2.2
  set s1 := Function.update s .C1 []
  have el1 : ∃ c ≤ 1, (clearProg .C1).Exec s s1 c := by
    refine ⟨3 * (s .C1).length + 1, ?_, hcl1⟩
    simp [hC1]
  have hcl2 := (stack_basic_macros WKey.C2 s1).2.2
  set s2 := Function.update s1 .C2 []
  have el2 : ∃ c ≤ 3 * P + 1, (clearProg .C2).Exec s1 s2 c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, hcl2⟩
    simp [s1, hC2]
  have hcp3 := stack_copy WKey.QP WKey.VAL WKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .VAL (List.replicate (q * P) (some true))
  have el3 : ∃ c ≤ 6 * (q * P) + 3, (copyProg .QP .VAL .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .QP).length + 3, ?_, w_exec_congr hcp3 ?_⟩
    · simp [s2, s1, hQP]
    · funext j; cases j <;> simp [s3, s2, s1, hQP, hVAL]
  have hcp4 := stack_copy WKey.CHD WKey.VAL WKey.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, hsc])
  set s4 := Function.update s3 .VAL (List.replicate (q * P + child) (some true))
  have el4 : ∃ c ≤ 6 * P + 3, (copyProg .CHD .VAL .sc).Exec s3 s4 c := by
    refine ⟨6 * (s3 .CHD).length + 3, ?_, w_exec_congr hcp4 ?_⟩
    · simp [s3, s2, s1, hCHD]; omega
    · have hadd : child + q * P = q * P + child := Nat.add_comm _ _
      funext j; cases j <;> simp [s4, s3, s2, s1, hCHD, ← List.replicate_add, hadd]
  have el5 := exec_emitUnaryTo .VAL .outRev (by decide) (by decide) (by decide) s4 (q * P + child)
    (by simp [s4]) (by simp [s4, s3, s2, s1, hsc])
  set s5 := Function.update s4 .outRev ((encUnary (q * P + child)).reverse ++ s4 .outRev)
  have hcl6 := (stack_basic_macros WKey.VAL s5).2.2
  set s6 := Function.update s5 .VAL []
  have el6 : ∃ c ≤ 3 * (q * P + P) + 1, (clearProg .VAL).Exec s5 s6 c := by
    refine ⟨3 * (s5 .VAL).length + 1, ?_, hcl6⟩
    simp [s5, s4]; omega
  have hcl7 := (stack_basic_macros WKey.CHD s6).2.2
  have el7 : ∃ c ≤ 3 * P + 1,
      (clearProg .CHD).Exec s6
        (Function.update (Function.update (Function.update s .C2 []) .CHD [])
          .outRev ((encUnary (q * P + child)).reverse ++ s .outRev)) c := by
    refine ⟨3 * (s6 .CHD).length + 1, ?_, w_exec_congr hcl7 ?_⟩
    · simp [s6, s5, s4, s3, s2, s1, hCHD]; omega
    · funext j; cases j <;> simp [s6, s5, s4, s3, s2, s1, hVAL, hC1]
  have e_all := w_exec_seq_le el1 (w_exec_seq_le el2 (w_exec_seq_le el3
    (w_exec_seq_le el4 (w_exec_seq_le el5 (w_exec_seq_le el6 el7)))))
  exact w_exec_le_of_le e_all (by omega)

lemma exec_emitChildGeLtKProg (s : WStore) (u : List Sym) (k P b : ℕ)
    (hb_le : b ≤ P + 2)
    (hki : s .ki = u)
    (hP : s .P = List.replicate P (some true))
    (hW : s .W = [])
    (hVAL : s .VAL = [])
    (hC1 : s .C1 = List.replicate b (some true))
    (hC2 : s .C2 = List.replicate (k - b) (some true))
    (hsc : s .sc = []) :
    ∃ c ≤ (21 * P + 31) * u.length + 3 * k + 10 * P + 50,
      emitChildGeLtKProg.Exec s
        (Function.update (Function.update (Function.update s .C1 []) .C2 [])
          .outRev ((encUnary (valAt u b * P)).reverse ++ s .outRev)) c := by
  have hcl1 := (stack_basic_macros WKey.VAL s).2.2
  set s1 := Function.update s .VAL []
  have e1 : ∃ c ≤ 1, (clearProg .VAL).Exec s s1 c := by
    refine ⟨3 * (s .VAL).length + 1, ?_, hcl1⟩
    simp [hVAL]
  have hcl2 := (stack_basic_macros WKey.C2 s1).2.2
  set s2 := Function.update s1 .C2 []
  have e2 : ∃ c ≤ 3 * k + 1, (clearProg .C2).Exec s1 s2 c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, hcl2⟩
    simp [s1, hC2]
  have hcp3 := stack_copy WKey.ki WKey.W WKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .W u
  have e3 : ∃ c ≤ 6 * u.length + 3, (copyProg .ki .W .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .ki).length + 3, ?_, w_exec_congr hcp3 ?_⟩
    · simp [s2, s1, hki]
    · funext j; cases j <;> simp [s3, s2, s1, hki, hW]
  have e4 := exec_advanceWordsProg .W .C1 .C2 (by decide) (by decide) (by decide) s3 u b
    (by simp [s3]) (by simp [s3, s2, s1, hC1]) (by simp [s3, s2])
  set s4 := Function.update (Function.update s3 .W (wordAt u b)) .C1 []
  have e5 := exec_readMulPEmitProg s4 (wordAt u b) P
    (by simp [s4]) (by simp [s4, s3, s2, s1, hP])
    (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2])
    (by simp [s4, s3, s2, s1, hsc])
  have e5' : ∃ c ≤ (15 * P + 13) * u.length + 15,
      readMulPEmitProg.Exec s4
        (Function.update (Function.update (Function.update s .C1 []) .C2 [])
          .outRev ((encUnary (valAt u b * P)).reverse ++ s .outRev)) c := by
    refine w_exec_le_of_le (by
      rcases e5 with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      funext j
      cases j <;> simp [s4, s3, s2, s1, hVAL, hW, valAt]) ?_
    have hlen_w : (wordAt u b).length ≤ u.length := length_wordAt_le u b
    have hmul : (15 * P + 13) * (wordAt u b).length ≤ (15 * P + 13) * u.length :=
      Nat.mul_le_mul_left _ hlen_w
    omega
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 e5')))
  refine w_exec_le_of_le e_all ?_
  have hmul_b : b * (6 * u.length + 10) ≤ (P + 2) * (6 * u.length + 10) :=
    Nat.mul_le_mul_right _ hb_le
  nlinarith

lemma exec_emitChildGeGeKProg (s : WStore) (u : List Sym) (k P b : ℕ)
    (hb_le : b ≤ P + 2)
    (hki : s .ki = u)
    (hP : s .P = List.replicate P (some true))
    (hW : s .W = [])
    (hVAL : s .VAL = List.replicate (b - k) (some true))
    (hC1 : s .C1 = List.replicate b (some true))
    (hC2 : s .C2 = [])
    (hsc : s .sc = []) :
    ∃ c ≤ (15 * P + 19) * u.length + 6 * P + 40,
      emitChildGeGeKProg.Exec s
        (Function.update (Function.update (Function.update s .VAL []) .C1 [])
          .outRev ((encUnary (valAt u 0 * P)).reverse ++ s .outRev)) c := by
  have hcl1 := (stack_basic_macros WKey.VAL s).2.2
  set s1 := Function.update s .VAL []
  have e1 : ∃ c ≤ 3 * P + 7, (clearProg .VAL).Exec s s1 c := by
    refine ⟨3 * (s .VAL).length + 1, ?_, hcl1⟩
    simp [hVAL]; omega
  have hcl2 := (stack_basic_macros WKey.C2 s1).2.2
  set s2 := Function.update s1 .C2 []
  have e2 : ∃ c ≤ 1, (clearProg .C2).Exec s1 s2 c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, hcl2⟩
    simp [s1, hC2]
  have hcl3 := (stack_basic_macros WKey.C1 s2).2.2
  set s3 := Function.update s2 .C1 []
  have e3 : ∃ c ≤ 3 * P + 7, (clearProg .C1).Exec s2 s3 c := by
    refine ⟨3 * (s2 .C1).length + 1, ?_, hcl3⟩
    simp [s2, s1, hC1]; omega
  have hcp4 := stack_copy WKey.ki WKey.W WKey.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, hsc])
  set s4 := Function.update s3 .W u
  have e4 : ∃ c ≤ 6 * u.length + 3, (copyProg .ki .W .sc).Exec s3 s4 c := by
    refine ⟨6 * (s3 .ki).length + 3, ?_, w_exec_congr hcp4 ?_⟩
    · simp [s3, s2, s1, hki]
    · funext j; cases j <;> simp [s4, s3, s2, s1, hki, hW]
  have e5 := exec_readMulPEmitProg s4 u P
    (by simp [s4]) (by simp [s4, s3, s2, s1, hP])
    (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2])
    (by simp [s4, s3, s2, s1, hsc])
  have e5' : ∃ c ≤ (15 * P + 13) * u.length + 15,
      readMulPEmitProg.Exec s4
        (Function.update (Function.update (Function.update s .VAL []) .C1 [])
          .outRev ((encUnary (valAt u 0 * P)).reverse ++ s .outRev)) c := by
    rcases e5 with ⟨c, hc, ec⟩
    refine ⟨c, hc, w_exec_congr ec ?_⟩
    funext j
    cases j <;> simp [s4, s3, s2, s1, hW, hC2, valAt, wordAt]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 e5')))
  have hring : 6 * u.length + (15 * P + 13) * u.length = (15 * P + 19) * u.length := by ring
  exact w_exec_le_of_le e_all (by omega)

lemma exec_emitChildGeProg (s : WStore) (u : List Sym) (k P q child : ℕ)
    (hge : P ≤ child) (hchd_le : child ≤ 2 * P + 2)
    (hki : s .ki = u)
    (hK : s .K = List.replicate k (some true))
    (hP : s .P = List.replicate P (some true))
    (hCHD : s .CHD = List.replicate child (some true))
    (hVAL : s .VAL = []) (hW : s .W = [])
    (hC1 : s .C1 = List.replicate (child - P) (some true))
    (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ (21 * P + 31) * u.length + 9 * k + 25 * P + 90,
      emitChildGeProg.Exec s
        (Function.update (Function.update (Function.update s .C1 []) .CHD [])
          .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
  set b := child - P
  have hb_le : b ≤ P + 2 := by omega
  have hnot_lt : ¬ child < P := by omega
  have hcl1 := (stack_basic_macros WKey.CHD s).2.2
  set s1 := Function.update s .CHD []
  have eg1 : ∃ c ≤ 6 * P + 7, (clearProg .CHD).Exec s s1 c := by
    refine ⟨3 * (s .CHD).length + 1, ?_, hcl1⟩
    simp [hCHD]; omega
  have hcp2 := stack_copy WKey.C1 WKey.VAL WKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 .VAL (List.replicate b (some true))
  have eg2 : ∃ c ≤ 6 * P + 15, (copyProg .C1 .VAL .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .C1).length + 3, ?_, w_exec_congr hcp2 ?_⟩
    · simp [s1, hC1]; omega
    · funext j; cases j <;> simp [s2, s1, hC1, hVAL, b]
  have hcp3 := stack_copy WKey.K WKey.C2 WKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .C2 (List.replicate k (some true))
  have eg3 : ∃ c ≤ 6 * k + 3, (copyProg .K .C2 .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .K).length + 3, ?_, w_exec_congr hcp3 ?_⟩
    · simp [s2, s1, hK]
    · funext j; cases j <;> simp [s3, s2, s1, hK, hC2]
  have hsync2 := stack_sync_pop WKey.VAL WKey.C2 (by decide) s3
  set s4 := Function.update
    (Function.update s3 .VAL (List.replicate (b - min b k) (some true)))
    .C2 (List.replicate (k - min b k) (some true))
  have eg4 : ∃ c ≤ 3 * P + 7, (syncPopProg .VAL .C2).Exec s3 s4 c := by
    refine ⟨3 * min (s3 .VAL).length (s3 .C2).length + 1, ?_, w_exec_congr hsync2 ?_⟩
    · have : (s3 .VAL).length = b := by simp [s3, s2]
      omega
    · funext j
      cases j <;> simp [s4, s3, s2, List.drop_replicate]
  by_cases hbk : b < k
  · have hmin_bk : min b k = b := Nat.min_eq_left (le_of_lt hbk)
    have htest2 : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s4 j).head?) = true := by
      show (s4 .C2).head?.isSome = true
      simp [s4, hmin_bk, w_head?_replicate_isSome (k - b) (some true) (by omega)]
    have e_sub := exec_emitChildGeLtKProg s4 u k P b hb_le
      (by simp [s4, s3, s2, s1, hki])
      (by simp [s4, s3, s2, s1, hP])
      (by simp [s4, s3, s2, s1, hW])
      (by simp [s4, hmin_bk])
      (by simp [s4, s3, s2, s1, hC1, b])
      (by simp [s4, hmin_bk])
      (by simp [s4, s3, s2, s1, hsc])
    have e_sub' : ∃ c ≤ (21 * P + 31) * u.length + 3 * k + 10 * P + 50,
        emitChildGeLtKProg.Exec s4
          (Function.update (Function.update (Function.update s .C1 []) .CHD [])
            .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
      rcases e_sub with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      funext j
      cases j <;> simp [s4, s3, s2, s1, hmin_bk, hVAL, hC2, transValU, hnot_lt, hbk, b]
    have e_br2 := w_exec_branch_true_le (fun h => (h .C2).isSome) emitChildGeLtKProg emitChildGeGeKProg htest2 e_sub'
    have e_ge := w_exec_seq_le eg1 (w_exec_seq_le eg2 (w_exec_seq_le eg3 (w_exec_seq_le eg4 e_br2)))
    exact w_exec_le_of_le e_ge (by omega)
  · have hmin_bk : min b k = k := Nat.min_eq_right (by omega)
    have htest2 : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s4 j).head?) = false := by
      show (s4 .C2).head?.isSome = false
      simp [s4, hmin_bk]
    have e_sub := exec_emitChildGeGeKProg s4 u k P b hb_le
      (by simp [s4, s3, s2, s1, hki])
      (by simp [s4, s3, s2, s1, hP])
      (by simp [s4, s3, s2, s1, hW])
      (by simp [s4, hmin_bk])
      (by simp [s4, s3, s2, s1, hC1, b])
      (by simp [s4, hmin_bk])
      (by simp [s4, s3, s2, s1, hsc])
    have e_sub' : ∃ c ≤ (15 * P + 19) * u.length + 6 * P + 40,
        emitChildGeGeKProg.Exec s4
          (Function.update (Function.update (Function.update s .C1 []) .CHD [])
            .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
      rcases e_sub with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      funext j
      cases j <;> simp [s4, s3, s2, s1, hmin_bk, hVAL, hC2, transValU, hnot_lt, hbk, b]
    have e_br2 := w_exec_branch_false_le (fun h => (h .C2).isSome) emitChildGeLtKProg emitChildGeGeKProg htest2 e_sub'
    have e_ge := w_exec_seq_le eg1 (w_exec_seq_le eg2 (w_exec_seq_le eg3 (w_exec_seq_le eg4 e_br2)))
    refine w_exec_le_of_le e_ge ?_
    have hmul_u : (15 * P + 19) * u.length ≤ (21 * P + 31) * u.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

lemma exec_emitChildProg (s : WStore) (u : List Sym) (k P q child : ℕ)
    (hchd_le : child ≤ 2 * P + 2)
    (hki : s .ki = u)
    (hK : s .K = List.replicate k (some true))
    (hP : s .P = List.replicate P (some true))
    (hQP : s .QP = List.replicate (q * P) (some true))
    (hCHD : s .CHD = List.replicate child (some true))
    (hVAL : s .VAL = []) (hW : s .W = [])
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ (21 * P + 31) * u.length + 15 * (q * P) + 9 * k + 50 * P + 120,
      emitChildProg.Exec s
        (Function.update (Function.update s .CHD [])
          .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
  have hc1 := stack_copy WKey.CHD WKey.C1 WKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .C1 (s .CHD ++ s .C1)
  have e1 : ∃ c ≤ 12 * P + 15, (copyProg .CHD .C1 .sc).Exec s s1 c := by
    refine ⟨6 * (s .CHD).length + 3, ?_, hc1⟩
    simp [hCHD]; omega
  have hc2 := stack_copy WKey.P WKey.C2 WKey.sc (by decide) (by decide) (by decide) s1 (by simp [s1, hsc])
  set s2 := Function.update s1 .C2 (s1 .P ++ s1 .C2)
  have e2 : ∃ c ≤ 6 * P + 3, (copyProg .P .C2 .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .P).length + 3, ?_, hc2⟩
    simp [s1, hP]
  have hsync := stack_sync_pop WKey.C1 WKey.C2 (by decide) s2
  set s3 := Function.update
    (Function.update s2 .C1 (List.replicate (child - min child P) (some true)))
    .C2 (List.replicate (P - min child P) (some true))
  have e3 : ∃ c ≤ 3 * P + 1, (syncPopProg .C1 .C2).Exec s2 s3 c := by
    refine ⟨3 * min (s2 .C1).length (s2 .C2).length + 1, ?_, w_exec_congr hsync ?_⟩
    · have : (s2 .C2).length = P := by simp [s2, s1, hP, hC2]
      omega
    · funext j
      cases j <;> simp [s3, s2, s1, hCHD, hP, hC1, hC2, List.drop_replicate]
  by_cases hlt : child < P
  · have hmin : min child P = child := Nat.min_eq_left (le_of_lt hlt)
    have htest : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s3 j).head?) = true := by
      show (s3 .C2).head?.isSome = true
      simp [s3, hmin, w_head?_replicate_isSome (P - child) (some true) (by omega)]
    have elt := exec_emitChildLtProg s3 P q child hlt
      (by simp [s3, s2, s1, hQP]) (by simp [s3, s2, s1, hCHD])
      (by simp [s3, s2, s1, hVAL]) (by simp [s3, hmin])
      (by simp [s3, hmin]) (by simp [s3, s2, s1, hsc])
    have elt' : ∃ c ≤ 15 * (q * P) + 21 * P + 21,
        emitChildLtProg.Exec s3
          (Function.update (Function.update s .CHD [])
            .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
      rcases elt with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      funext j
      cases j <;> simp [s3, s2, s1, hmin, hC1, hC2, transValU, hlt]
    have e_br := w_exec_branch_true_le (fun h => (h .C2).isSome) emitChildLtProg emitChildGeProg htest elt'
    have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 e_br))
    exact w_exec_le_of_le e_all (by omega)
  · have hge : P ≤ child := by omega
    have hmin : min child P = P := Nat.min_eq_right hge
    have htest : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s3 j).head?) = false := by
      show (s3 .C2).head?.isSome = false
      simp [s3, hmin]
    have ege := exec_emitChildGeProg s3 u k P q child hge hchd_le
      (by simp [s3, s2, s1, hki]) (by simp [s3, s2, s1, hK])
      (by simp [s3, s2, s1, hP]) (by simp [s3, s2, s1, hCHD])
      (by simp [s3, s2, s1, hVAL]) (by simp [s3, s2, s1, hW])
      (by simp [s3, hmin]) (by simp [s3, hmin]) (by simp [s3, s2, s1, hsc])
    have ege' : ∃ c ≤ (21 * P + 31) * u.length + 9 * k + 25 * P + 90,
        emitChildGeProg.Exec s3
          (Function.update (Function.update s .CHD [])
            .outRev ((encUnary (transValU u k P q child)).reverse ++ s .outRev)) c := by
      rcases ege with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      funext j
      cases j <;> simp [s3, s2, s1, hmin, hC1, hC2]
    have e_br := w_exec_branch_false_le (fun h => (h .C2).isSome) emitChildLtProg emitChildGeProg htest ege'
    have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 e_br))
    exact w_exec_le_of_le e_all (by omega)

def buildChildProg (addTwo : Bool) : WProg :=
  .seq (copyProg .PI .CHD .sc)
    (.seq (copyProg .PI .CHD .sc)
      (if addTwo then
        .seq (pushProg .CHD (some true)) (pushProg .CHD (some true))
      else
        pushProg .CHD (some true)))

lemma exec_buildChildProg (addTwo : Bool) (s : WStore) (P p : ℕ) (hp : p ≤ P)
    (hPI : s .PI = List.replicate p (some true))
    (hCHD : s .CHD = []) (hsc : s .sc = []) :
    ∃ c ≤ 12 * P + 12,
      (buildChildProg addTwo).Exec s
        (Function.update s .CHD (List.replicate (2 * p + if addTwo then 2 else 1) (some true))) c := by
  have hc1 := stack_copy WKey.PI WKey.CHD WKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .CHD (s .PI ++ s .CHD)
  have e1 : ∃ c ≤ 6 * P + 3, (copyProg .PI .CHD .sc).Exec s s1 c := by
    refine ⟨6 * (s .PI).length + 3, ?_, hc1⟩
    simp [hPI]; omega
  have hc2 := stack_copy WKey.PI WKey.CHD WKey.sc (by decide) (by decide) (by decide) s1 (by simp [s1, hsc])
  set s2 := Function.update s1 .CHD (s1 .PI ++ s1 .CHD)
  have e2 : ∃ c ≤ 6 * P + 3, (copyProg .PI .CHD .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .PI).length + 3, ?_, hc2⟩
    simp [s1, hPI]; omega
  have h2p : p + p = 2 * p := by ring
  cases addTwo
  · have hp3 := (stack_basic_macros WKey.CHD s2).1 (some true)
    have e3 : ∃ c ≤ 1,
        (pushProg .CHD (some true)).Exec s2
          (Function.update s .CHD (List.replicate (2 * p + 1) (some true))) c := by
      refine ⟨1, le_rfl, w_exec_congr hp3 ?_⟩
      funext j
      cases j <;> simp [s2, s1, hPI, hCHD, ← List.replicate_add, h2p, List.replicate_succ]
    exact w_exec_le_of_le (w_exec_seq_le e1 (w_exec_seq_le e2 e3)) (by omega)
  · have hp3 := (stack_basic_macros WKey.CHD s2).1 (some true)
    set s3 := Function.update s2 .CHD (some true :: s2 .CHD)
    have e3 : ∃ c ≤ 1, (pushProg .CHD (some true)).Exec s2 s3 c := ⟨1, le_rfl, hp3⟩
    have hp4 := (stack_basic_macros WKey.CHD s3).1 (some true)
    have e4 : ∃ c ≤ 1,
        (pushProg .CHD (some true)).Exec s3
          (Function.update s .CHD (List.replicate (2 * p + 2) (some true))) c := by
      refine ⟨1, le_rfl, w_exec_congr hp4 ?_⟩
      funext j
      cases j <;> simp [s3, s2, s1, hPI, hCHD, ← List.replicate_add, h2p, List.replicate_succ]
    exact w_exec_le_of_le (w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 e4))) (by omega)

def onePOut (u : List Sym) (k P q p : ℕ) : List Sym :=
  encUnary (transValU u k P q (2 * p + 2)) ++ encUnary (transValU u k P q (2 * p + 1))

def pBlockOut (u : List Sym) (k P q : ℕ) : ℕ → List Sym
  | 0 => []
  | p + 1 => pBlockOut u k P q p ++ onePOut u k P q p

def qAllOut (body : List Sym) (k P : ℕ) : ℕ → List Sym
  | 0 => []
  | q + 1 => qAllOut body k P q ++ pBlockOut (wordAt body (q * k)) k P q P

def pStore (n k L M0 P : ℕ) (body : List Sym) (q p : ℕ) : WStore := fun j =>
  match j with
  | .ki => wordAt body (q * k)
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .L => List.replicate L (some false)
  | .M0 => List.replicate M0 (some true)
  | .P => List.replicate P (some true)
  | .Nrem => List.replicate (n - (q + 1)) (some true)
  | .QP => List.replicate (q * P) (some true)
  | .PI => List.replicate p (some true)
  | .Prem => List.replicate (P - p) (some true)
  | .outRev =>
      (pBlockOut (wordAt body (q * k)) k P q p).reverse ++
        (qAllOut body k P q).reverse ++
        (encUnary 2).reverse ++ (encUnary (n * P)).reverse
  | _ => []

def pBodyProg : WProg :=
  .seq (popProg .Prem)
    (.seq (buildChildProg true)
      (.seq emitChildProg
        (.seq (buildChildProg false)
          (.seq emitChildProg
            (pushProg .PI (some true))))))

def pLoopProg : WProg :=
  .loop (fun h => (h .Prem).isSome) pBodyProg

lemma exec_pBodyProg (n k L M0 P : ℕ) (body : List Sym) (q p : ℕ) (hp : p < P) :
    ∃ c ≤ (42 * P + 62) * body.length + 30 * (q * P) + 18 * k + 124 * P + 275,
      pBodyProg.Exec (pStore n k L M0 P body q p) (pStore n k L M0 P body q (p + 1)) c := by
  set u := wordAt body (q * k)
  have hu_le : u.length ≤ body.length := length_wordAt_le body (q * k)
  set s0 := pStore n k L M0 P body q p
  have hp1 := (stack_basic_macros WKey.Prem s0).2.1
  set s1 := Function.update s0 .Prem (s0 .Prem).tail
  have e1 : ∃ c ≤ 1, (popProg .Prem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have e2 := exec_buildChildProg true s1 P p (le_of_lt hp)
    (by simp [s1, s0, pStore]) (by simp [s1, s0, pStore]) (by simp [s1, s0, pStore])
  set s2 := Function.update s1 .CHD (List.replicate (2 * p + 2) (some true))
  have e3 := exec_emitChildProg s2 u k P q (2 * p + 2) (by omega)
    (by simp [s2, s1, s0, pStore, u]) (by simp [s2, s1, s0, pStore])
    (by simp [s2, s1, s0, pStore]) (by simp [s2, s1, s0, pStore])
    (by simp [s2]) (by simp [s2, s1, s0, pStore]) (by simp [s2, s1, s0, pStore])
    (by simp [s2, s1, s0, pStore]) (by simp [s2, s1, s0, pStore]) (by simp [s2, s1, s0, pStore])
  set s3 := Function.update (Function.update s2 .CHD [])
    .outRev ((encUnary (transValU u k P q (2 * p + 2))).reverse ++ s2 .outRev)
  have e4 := exec_buildChildProg false s3 P p (le_of_lt hp)
    (by simp [s3, s2, s1, s0, pStore]) (by simp [s3]) (by simp [s3, s2, s1, s0, pStore])
  set s4 := Function.update s3 .CHD (List.replicate (2 * p + 1) (some true))
  have e5 := exec_emitChildProg s4 u k P q (2 * p + 1) (by omega)
    (by simp [s4, s3, s2, s1, s0, pStore, u]) (by simp [s4, s3, s2, s1, s0, pStore])
    (by simp [s4, s3, s2, s1, s0, pStore]) (by simp [s4, s3, s2, s1, s0, pStore])
    (by simp [s4]) (by simp [s4, s3, s2, s1, s0, pStore]) (by simp [s4, s3, s2, s1, s0, pStore])
    (by simp [s4, s3, s2, s1, s0, pStore]) (by simp [s4, s3, s2, s1, s0, pStore])
    (by simp [s4, s3, s2, s1, s0, pStore])
  set s5 := Function.update (Function.update s4 .CHD [])
    .outRev ((encUnary (transValU u k P q (2 * p + 1))).reverse ++ s4 .outRev)
  have hp6 := (stack_basic_macros WKey.PI s5).1 (some true)
  have e6 : ∃ c ≤ 1, (pushProg .PI (some true)).Exec s5 (pStore n k L M0 P body q (p + 1)) c := by
    refine ⟨1, le_rfl, w_exec_congr hp6 ?_⟩
    have hsub : P - p - 1 = P - (p + 1) := by omega
    funext j
    cases j <;> simp [s5, s4, s3, s2, s1, s0, pStore, u, pBlockOut, onePOut,
      List.reverse_append, List.append_assoc, List.replicate_succ, hsub]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 (w_exec_seq_le e5 e6))))
  refine w_exec_le_of_le e_all ?_
  have hmul : (21 * P + 31) * u.length ≤ (21 * P + 31) * body.length :=
    Nat.mul_le_mul_left _ hu_le
  have h2u : 2 * ((21 * P + 31) * body.length) = (42 * P + 62) * body.length := by ring
  omega

lemma exec_pLoopProg (n k L M0 P : ℕ) (body : List Sym) (q : ℕ) :
    ∃ c ≤ P * ((42 * P + 62) * body.length + 30 * (q * P) + 18 * k + 124 * P + 277) + 1,
      pLoopProg.Exec (pStore n k L M0 P body q 0) (pStore n k L M0 P body q P) c := by
  refine w_exec_bounded_loop (fun h => (h .Prem).isSome) pBodyProg P
    (pStore n k L M0 P body q)
    ((42 * P + 62) * body.length + 30 * (q * P) + 18 * k + 124 * P + 275)
    (fun p hp => by
      show (List.replicate (P - p) (some true)).head?.isSome = true
      exact w_head?_replicate_isSome (P - p) (some true) (by omega))
    (by
      show (List.replicate (P - P) (some true)).head?.isSome = false
      simp)
    (fun p hp => exec_pBodyProg n k L M0 P body q p hp)

def qStore (n k L M0 P : ℕ) (body : List Sym) (q : ℕ) : WStore := fun j =>
  match j with
  | .ki => wordAt body (q * k)
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .L => List.replicate L (some false)
  | .M0 => List.replicate M0 (some true)
  | .P => List.replicate P (some true)
  | .Nrem => List.replicate (n - q) (some true)
  | .QP => List.replicate (q * P) (some true)
  | .outRev =>
      (qAllOut body k P q).reverse ++
        (encUnary 2).reverse ++ (encUnary (n * P)).reverse
  | _ => []

def qBodyProg : WProg :=
  .seq (popProg .Nrem)
    (.seq (copyProg .P .Prem .sc)
      (.seq pLoopProg
        (.seq (clearProg .PI)
          (.seq (copyProg .K .C1 .sc)
            (.seq (advanceWordsProg .ki .C1 .C2)
              (copyProg .P .QP .sc))))))

def qLoopProg : WProg :=
  .loop (fun h => (h .Nrem).isSome) qBodyProg

lemma exec_qBodyProg (n k L M0 P : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ P * ((42 * P + 62) * body.length + 30 * (n * P) + 18 * k + 124 * P + 277) +
        k * (6 * body.length + 10) + 6 * k + 15 * P + 20,
      qBodyProg.Exec (qStore n k L M0 P body q) (qStore n k L M0 P body (q + 1)) c := by
  set s0 := qStore n k L M0 P body q
  have hp1 := (stack_basic_macros WKey.Nrem s0).2.1
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hcp2 := stack_copy WKey.P WKey.Prem WKey.sc (by decide) (by decide) (by decide) s1 rfl
  have e2 : ∃ c ≤ 6 * P + 3, (copyProg .P .Prem .sc).Exec s1 (pStore n k L M0 P body q 0) c := by
    refine ⟨6 * (s1 .P).length + 3, ?_, w_exec_congr hcp2 ?_⟩
    · simp [s1, s0, qStore]
    · have hsub : n - q - 1 = n - (q + 1) := by omega
      funext j
      cases j <;> simp [s1, s0, qStore, pStore, pBlockOut, hsub]
  have e3 := exec_pLoopProg n k L M0 P body q
  set s3 := pStore n k L M0 P body q P
  have hcl4 := (stack_basic_macros WKey.PI s3).2.2
  set s4 := Function.update s3 .PI []
  have e4 : ∃ c ≤ 3 * P + 1, (clearProg .PI).Exec s3 s4 c := by
    refine ⟨3 * (s3 .PI).length + 1, ?_, hcl4⟩
    simp [s3, pStore]
  have hcp5 := stack_copy WKey.K WKey.C1 WKey.sc (by decide) (by decide) (by decide) s4
    (by simp [s4, s3, pStore])
  set s5 := Function.update s4 .C1 (List.replicate k (some true))
  have e5 : ∃ c ≤ 6 * k + 3, (copyProg .K .C1 .sc).Exec s4 s5 c := by
    refine ⟨6 * (s4 .K).length + 3, ?_, w_exec_congr hcp5 ?_⟩
    · simp [s4, s3, pStore]
    · funext j
      cases j <;> simp [s5, s4, s3, pStore]
  have e6 := exec_advanceWordsProg .ki .C1 .C2 (by decide) (by decide) (by decide) s5
    (wordAt body (q * k)) k (by simp [s5, s4, s3, pStore]) (by simp [s5]) (by simp [s5, s4, s3, pStore])
  set s6 := Function.update (Function.update s5 .ki (wordAt (wordAt body (q * k)) k)) .C1 []
  have e6' : ∃ c ≤ k * (6 * body.length + 10) + 1,
      (advanceWordsProg .ki .C1 .C2).Exec s5 s6 c := by
    refine w_exec_le_of_le e6 ?_
    have hlen : (wordAt body (q * k)).length ≤ body.length := length_wordAt_le body (q * k)
    have hmul : k * (6 * (wordAt body (q * k)).length + 10) ≤ k * (6 * body.length + 10) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  have hcp7 := stack_copy WKey.P WKey.QP WKey.sc (by decide) (by decide) (by decide) s6
    (by simp [s6, s5, s4, s3, pStore])
  have e7 : ∃ c ≤ 6 * P + 3, (copyProg .P .QP .sc).Exec s6 (qStore n k L M0 P body (q + 1)) c := by
    refine ⟨6 * (s6 .P).length + 3, ?_, w_exec_congr hcp7 ?_⟩
    · simp [s6, s5, s4, s3, pStore]
    · have hqk : q * k + k = (q + 1) * k := by ring
      have hqp : P + q * P = (q + 1) * P := by ring
      funext j
      cases j <;> simp [s6, s5, s4, s3, pStore, qStore, qAllOut, wordAt_wordAt, hqk,
        ← List.replicate_add, hqp, List.reverse_append, List.append_assoc]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 (w_exec_seq_le e5 (w_exec_seq_le e6' e7)))))
  refine w_exec_le_of_le e_all ?_
  have hqP : q * P ≤ n * P := Nat.mul_le_mul_right P (le_of_lt hq)
  have hmulP : P * ((42 * P + 62) * body.length + 30 * (q * P) + 18 * k + 124 * P + 277) ≤
      P * ((42 * P + 62) * body.length + 30 * (n * P) + 18 * k + 124 * P + 277) :=
    Nat.mul_le_mul_left P (by omega)
  omega

lemma exec_qLoopProg (n k L M0 P : ℕ) (body : List Sym) :
    ∃ c ≤ n * (P * ((42 * P + 62) * body.length + 30 * (n * P) + 18 * k + 124 * P + 277) +
        k * (6 * body.length + 10) + 6 * k + 15 * P + 22) + 1,
      qLoopProg.Exec (qStore n k L M0 P body 0) (qStore n k L M0 P body n) c := by
  refine w_exec_bounded_loop (fun h => (h .Nrem).isSome) qBodyProg n
    (qStore n k L M0 P body)
    (P * ((42 * P + 62) * body.length + 30 * (n * P) + 18 * k + 124 * P + 277) +
      k * (6 * body.length + 10) + 6 * k + 15 * P + 20)
    (fun q hq => by
      show (List.replicate (n - q) (some true)).head?.isSome = true
      exact w_head?_replicate_isSome (n - q) (some true) (by omega))
    (by
      show (List.replicate (n - n) (some true)).head?.isSome = false
      simp)
    (fun q hq => exec_qBodyProg n k L M0 P body q hq)

lemma two_mul_pow_min_lt_iff (k i : ℕ) :
    2 * 2 ^ (min i (Nat.log 2 (k - 1))) < k ↔ i < Nat.log 2 (k - 1) := by
  set m := Nat.log 2 (k - 1)
  by_cases hi : i < m
  · have hmin : min i m = i := Nat.min_eq_left (le_of_lt hi)
    rw [hmin]
    have hk1 : k - 1 ≠ 0 := by
      intro h0
      have : m = 0 := by simp [m, h0]
      omega
    have hpow_m : 2 ^ m ≤ k - 1 := Nat.pow_log_le_self 2 hk1
    have hpow_i : 2 ^ (i + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hi
    have h2 : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
    omega
  · have hmin : min i m = m := Nat.min_eq_right (by omega)
    rw [hmin]
    have hlt_pow : k - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) (k - 1)
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

lemma pow_min_log_le (k i : ℕ) :
    2 ^ (min i (Nat.log 2 (k - 1))) ≤ k + 1 := by
  have hle : 2 ^ (min i (Nat.log 2 (k - 1))) ≤ 2 ^ (Nat.log 2 (k - 1)) :=
    Nat.pow_le_pow_right (by decide) (Nat.min_le_right i _)
  by_cases hk1 : k - 1 = 0
  · have hm0 : Nat.log 2 (k - 1) = 0 := by simp [hk1]
    have hmin0 : min i (Nat.log 2 (k - 1)) = 0 := by omega
    rw [hmin0]
    omega
  · have hpow : 2 ^ (Nat.log 2 (k - 1)) ≤ k - 1 := Nat.pow_log_le_self 2 hk1
    omega

lemma log_sub_one_le (k : ℕ) : Nat.log 2 (k - 1) ≤ k := by
  have h : Nat.log 2 (k - 1) ≤ k - 1 := Nat.log_le_self 2 (k - 1)
  omega

def lStore (n k : ℕ) (body : List Sym) (i : ℕ) : WStore := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .L => List.replicate (min i (Nat.log 2 (k - 1)) + 1) (some false)
  | .M0 => List.replicate (2 ^ (min i (Nat.log 2 (k - 1)))) (some true)
  | .Prem => List.replicate (k - i) (some true)
  | _ => []

def initReadProg : WProg :=
  .seq (readUnaryProg .ki .N)
    (.seq (readUnaryProg .ki .K)
      (.seq (pushProg .L (some false))
        (.seq (pushProg .M0 (some true))
          (copyProg .K .Prem .sc))))

lemma exec_initReadProg (w : List Sym) :
    ∃ c ≤ 12 * w.length + 18,
      initReadProg.Exec (fun j => if j = .ki then w else [])
        (lStore (valAt w 0) (valAt w 1) (wordAt w 2) 0) c := by
  set n := valAt w 0
  set k := valAt w 1
  set body := wordAt w 2
  set s0 : WStore := fun j => if j = .ki then w else []
  have e1 := exec_readUnaryProg_wordAt .ki .N (by decide) s0 w 0 rfl rfl
  set s1 := Function.update (Function.update s0 .ki (wordAt w 1)) .N (List.replicate n (some true))
  have e2 := exec_readUnaryProg_wordAt .ki .K (by decide) s1 w 1 (by simp [s1]) (by simp [s1, s0])
  set s2 := Function.update (Function.update s1 .ki body) .K (List.replicate k (some true))
  have hp3 := (stack_basic_macros WKey.L s2).1 (some false)
  set s3 := Function.update s2 .L (some false :: s2 .L)
  have e3 : ∃ c ≤ 1, (pushProg .L (some false)).Exec s2 s3 c := ⟨1, le_rfl, hp3⟩
  have hp4 := (stack_basic_macros WKey.M0 s3).1 (some true)
  set s4 := Function.update s3 .M0 (some true :: s3 .M0)
  have e4 : ∃ c ≤ 1, (pushProg .M0 (some true)).Exec s3 s4 c := ⟨1, le_rfl, hp4⟩
  have hcp5 := stack_copy WKey.K WKey.Prem WKey.sc (by decide) (by decide) (by decide) s4
    (by simp [s4, s3, s2, s1, s0])
  have hk_le : k ≤ w.length := valAt_le_length w 1
  have e5 : ∃ c ≤ 6 * w.length + 3, (copyProg .K .Prem .sc).Exec s4 (lStore n k body 0) c := by
    refine ⟨6 * (s4 .K).length + 3, ?_, w_exec_congr hcp5 ?_⟩
    · simp [s4, s3, s2]; omega
    · funext j
      cases j <;> simp [s4, s3, s2, s1, s0, lStore]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 e5)))
  exact w_exec_le_of_le e_all (by omega)

def lBodyTrueProg : WProg :=
  .seq (clearProg .C1)
    (.seq (clearProg .C2)
      (.seq (pushProg .L (some false))
        (.seq (copyProg .M0 .C1 .sc)
          (transferProg .C1 (fun j => decide (j = .M0))))))

def lBodyFalseProg : WProg :=
  .seq (clearProg .C1) (clearProg .C2)

def lBodyProg : WProg :=
  .seq (popProg .Prem)
    (.seq (copyProg .M0 .C1 .sc)
      (.seq (copyProg .M0 .C1 .sc)
        (.seq (copyProg .K .C2 .sc)
          (.seq (syncPopProg .C1 .C2)
            (.branch (fun h => (h .C2).isSome)
              lBodyTrueProg
              lBodyFalseProg)))))

def lLoopProg : WProg :=
  .loop (fun h => (h .Prem).isSome) lBodyProg

lemma exec_lBodyTrueProg (s : WStore) (k l mi : ℕ) (hmi : mi ≤ k + 1)
    (hL : s .L = List.replicate l (some false))
    (hM0 : s .M0 = List.replicate mi (some true))
    (hC1 : s .C1 = [])
    (hC2 : s .C2 = List.replicate (k - 2 * mi) (some true))
    (hsc : s .sc = []) :
    ∃ c ≤ 12 * k + 25,
      lBodyTrueProg.Exec s
        (Function.update (Function.update (Function.update s .C2 []) .L (List.replicate (l + 1) (some false)))
          .M0 (List.replicate (mi + mi) (some true))) c := by
  have hcl1 := (stack_basic_macros WKey.C1 s).2.2
  set s1 := Function.update s .C1 []
  have et1 : ∃ c ≤ 1, (clearProg .C1).Exec s s1 c := by
    refine ⟨3 * (s .C1).length + 1, ?_, hcl1⟩
    simp [hC1]
  have hcl2 := (stack_basic_macros WKey.C2 s1).2.2
  set s2 := Function.update s1 .C2 []
  have et2 : ∃ c ≤ 3 * k + 1, (clearProg .C2).Exec s1 s2 c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, hcl2⟩
    simp [s1, hC2]
  have hp3 := (stack_basic_macros WKey.L s2).1 (some false)
  set s3 := Function.update s2 .L (List.replicate (l + 1) (some false))
  have et3 : ∃ c ≤ 1, (pushProg .L (some false)).Exec s2 s3 c := by
    refine ⟨1, le_rfl, w_exec_congr hp3 ?_⟩
    funext j; cases j <;> simp [s3, s2, s1, hL, List.replicate_succ]
  have hcp4 := stack_copy WKey.M0 WKey.C1 WKey.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, hsc])
  set s4 := Function.update s3 .C1 (List.replicate mi (some true))
  have et4 : ∃ c ≤ 6 * k + 9, (copyProg .M0 .C1 .sc).Exec s3 s4 c := by
    refine ⟨6 * (s3 .M0).length + 3, ?_, w_exec_congr hcp4 ?_⟩
    · simp [s3, s2, s1, hM0]; omega
    · funext j; cases j <;> simp [s4, s3, s2, s1, hM0]
  have htr5 := stack_transfer WKey.C1 (fun j => decide (j = .M0)) s4
  have et5 : ∃ c ≤ 3 * k + 4,
      (transferProg .C1 (fun j => decide (j = .M0))).Exec s4
        (Function.update (Function.update (Function.update s .C2 []) .L (List.replicate (l + 1) (some false)))
          .M0 (List.replicate (mi + mi) (some true))) c := by
    refine ⟨3 * (s4 .C1).length + 1, ?_, w_exec_congr htr5 ?_⟩
    · simp [s4]; omega
    · funext j
      cases j <;> simp [transferStore, s4, s3, s2, s1, hM0, hC1, ← List.replicate_add]
  have e_all := w_exec_seq_le et1 (w_exec_seq_le et2 (w_exec_seq_le et3 (w_exec_seq_le et4 et5)))
  exact w_exec_le_of_le e_all (by omega)

lemma exec_lBodyProg (n k : ℕ) (body : List Sym) (i : ℕ) (hi : i < k) :
    ∃ c ≤ 36 * k + 60,
      lBodyProg.Exec (lStore n k body i) (lStore n k body (i + 1)) c := by
  have hmi_le : 2 ^ (min i (Nat.log 2 (k - 1))) ≤ k + 1 := pow_min_log_le k i
  set s0 := lStore n k body i
  have hp1 := (stack_basic_macros WKey.Prem s0).2.1
  set s1 := Function.update s0 .Prem (s0 .Prem).tail
  have e1 : ∃ c ≤ 1, (popProg .Prem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hcp2 := stack_copy WKey.M0 WKey.C1 WKey.sc (by decide) (by decide) (by decide) s1 rfl
  set s2 := Function.update s1 .C1 (s1 .M0 ++ s1 .C1)
  have e2 : ∃ c ≤ 6 * k + 9, (copyProg .M0 .C1 .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .M0).length + 3, ?_, hcp2⟩
    simp [s1, s0, lStore]; omega
  have hcp3 := stack_copy WKey.M0 WKey.C1 WKey.sc (by decide) (by decide) (by decide) s2 (by simp [s2, s1, s0, lStore])
  set s3 := Function.update s2 .C1 (List.replicate (2 * 2 ^ (min i (Nat.log 2 (k - 1)))) (some true))
  have e3 : ∃ c ≤ 6 * k + 9, (copyProg .M0 .C1 .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .M0).length + 3, ?_, w_exec_congr hcp3 ?_⟩
    · simp [s2, s1, s0, lStore]; omega
    · have h2mi : 2 ^ (min i (Nat.log 2 (k - 1))) + 2 ^ (min i (Nat.log 2 (k - 1))) =
          2 * 2 ^ (min i (Nat.log 2 (k - 1))) := by ring
      funext j
      cases j <;> simp [s3, s2, s1, s0, lStore, ← List.replicate_add, h2mi]
  have hcp4 := stack_copy WKey.K WKey.C2 WKey.sc (by decide) (by decide) (by decide) s3 (by simp [s3, s2, s1, s0, lStore])
  set s4 := Function.update s3 .C2 (List.replicate k (some true))
  have e4 : ∃ c ≤ 6 * k + 3, (copyProg .K .C2 .sc).Exec s3 s4 c := by
    refine ⟨6 * (s3 .K).length + 3, ?_, w_exec_congr hcp4 ?_⟩
    · simp [s3, s2, s1, s0, lStore]
    · funext j
      cases j <;> simp [s4, s3, s2, s1, s0, lStore]
  have hsync := stack_sync_pop WKey.C1 WKey.C2 (by decide) s4
  set mi := 2 ^ (min i (Nat.log 2 (k - 1)))
  set s5 := Function.update
    (Function.update s4 .C1 (List.replicate (2 * mi - min (2 * mi) k) (some true)))
    .C2 (List.replicate (k - min (2 * mi) k) (some true))
  have e5 : ∃ c ≤ 3 * k + 1, (syncPopProg .C1 .C2).Exec s4 s5 c := by
    refine ⟨3 * min (s4 .C1).length (s4 .C2).length + 1, ?_, w_exec_congr hsync ?_⟩
    · have : (s4 .C2).length = k := by simp [s4]
      omega
    · funext j
      cases j <;> simp [s5, s4, s3, mi, List.drop_replicate]
  by_cases him : i < Nat.log 2 (k - 1)
  · have hlt_k : 2 * mi < k := (two_mul_pow_min_lt_iff k i).mpr him
    have hmin_k : min (2 * mi) k = 2 * mi := Nat.min_eq_left (le_of_lt hlt_k)
    have htest : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s5 j).head?) = true := by
      show (s5 .C2).head?.isSome = true
      simp [s5, hmin_k, w_head?_replicate_isSome (k - 2 * mi) (some true) (by omega)]
    have et := exec_lBodyTrueProg s5 k (min i (Nat.log 2 (k - 1)) + 1) mi hmi_le
      (by simp [s5, s4, s3, s2, s1, s0, lStore])
      (by simp [s5, s4, s3, s2, s1, s0, lStore, mi])
      (by simp [s5, hmin_k])
      (by simp [s5, hmin_k])
      (by simp [s5, s4, s3, s2, s1, s0, lStore])
    have et' : ∃ c ≤ 12 * k + 25,
        lBodyTrueProg.Exec s5 (lStore n k body (i + 1)) c := by
      rcases et with ⟨c, hc, ec⟩
      refine ⟨c, hc, w_exec_congr ec ?_⟩
      have hmin_i : min i (Nat.log 2 (k - 1)) = i := Nat.min_eq_left (le_of_lt him)
      have hmin_i1 : min (i + 1) (Nat.log 2 (k - 1)) = i + 1 := Nat.min_eq_left him
      have hpow_succ : mi + mi = 2 ^ (i + 1) := by
        dsimp [mi]
        rw [hmin_i, Nat.pow_add_one]
        ring
      have hsub : k - i - 1 = k - (i + 1) := by omega
      funext j
      cases j <;> simp [s5, s4, s3, s2, s1, s0, lStore,
        hmin_k, hmin_i, hmin_i1, hpow_succ, List.tail_replicate, hsub]
    have e_br := w_exec_branch_true_le (fun h => (h .C2).isSome) lBodyTrueProg lBodyFalseProg htest et'
    have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 (w_exec_seq_le e5 e_br))))
    exact w_exec_le_of_le e_all (by omega)
  · have hge_k : k ≤ 2 * mi := by
      have h := mt (two_mul_pow_min_lt_iff k i).mp him
      omega
    have hmin_k : min (2 * mi) k = k := Nat.min_eq_right hge_k
    have htest : (fun h : WKey → Option Sym => (h .C2).isSome) (fun j => (s5 j).head?) = false := by
      show (s5 .C2).head?.isSome = false
      simp [s5, hmin_k]
    have hcl1 := (stack_basic_macros WKey.C1 s5).2.2
    set s6 := Function.update s5 .C1 []
    have ef1 : ∃ c ≤ 6 * k + 7, (clearProg .C1).Exec s5 s6 c := by
      refine ⟨3 * (s5 .C1).length + 1, ?_, hcl1⟩
      simp [s5]; omega
    have hcl2 := (stack_basic_macros WKey.C2 s6).2.2
    have ef2 : ∃ c ≤ 1, (clearProg .C2).Exec s6 (lStore n k body (i + 1)) c := by
      refine ⟨3 * (s6 .C2).length + 1, ?_, w_exec_congr hcl2 ?_⟩
      · simp [s6, s5, hmin_k]
      · have hmin_i : min i (Nat.log 2 (k - 1)) = Nat.log 2 (k - 1) := Nat.min_eq_right (by omega)
        have hmin_i1 : min (i + 1) (Nat.log 2 (k - 1)) = Nat.log 2 (k - 1) := Nat.min_eq_right (by omega)
        have hsub : k - i - 1 = k - (i + 1) := by omega
        funext j
        cases j <;> simp [s6, s5, s4, s3, s2, s1, s0, lStore, hmin_i, hmin_i1, List.tail_replicate, hsub]
    have e_f := w_exec_seq_le ef1 ef2
    have e_br := w_exec_branch_false_le (fun h => (h .C2).isSome) lBodyTrueProg lBodyFalseProg htest e_f
    have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 (w_exec_seq_le e5 e_br))))
    exact w_exec_le_of_le e_all (by omega)

lemma exec_lLoopProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ k * (36 * k + 62) + 1,
      lLoopProg.Exec (lStore n k body 0) (lStore n k body k) c := by
  refine w_exec_bounded_loop (fun h => (h .Prem).isSome) lBodyProg k
    (lStore n k body) (36 * k + 60)
    (fun i hi => by
      show (List.replicate (k - i) (some true)).head?.isSome = true
      exact w_head?_replicate_isSome (k - i) (some true) (by omega))
    (by
      show (List.replicate (k - k) (some true)).head?.isSome = false
      simp)
    (fun i hi => exec_lBodyProg n k body i hi)

def buildPProg : WProg :=
  .seq (copyProg .M0 .P .sc)
    (.seq (copyProg .M0 .P .sc)
      (.seq (copyProg .M0 .P .sc)
        (popProg .P)))

lemma exec_buildPProg (s : WStore) (M0 : ℕ)
    (hM0 : s .M0 = List.replicate M0 (some true))
    (hP : s .P = []) (hsc : s .sc = []) :
    ∃ c ≤ 18 * M0 + 15,
      buildPProg.Exec s
        (Function.update s .P (List.replicate (3 * M0 - 1) (some true))) c := by
  have hc1 := stack_copy WKey.M0 WKey.P WKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .P (List.replicate M0 (some true))
  have e1 : ∃ c ≤ 6 * M0 + 3, (copyProg .M0 .P .sc).Exec s s1 c := by
    refine ⟨6 * (s .M0).length + 3, ?_, w_exec_congr hc1 ?_⟩
    · simp [hM0]
    · funext j; cases j <;> simp [s1, hM0, hP]
  have hc2 := stack_copy WKey.M0 WKey.P WKey.sc (by decide) (by decide) (by decide) s1 (by simp [s1, hsc])
  set s2 := Function.update s1 .P (List.replicate (2 * M0) (some true))
  have e2 : ∃ c ≤ 6 * M0 + 3, (copyProg .M0 .P .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .M0).length + 3, ?_, w_exec_congr hc2 ?_⟩
    · simp [s1, hM0]
    · have h2 : M0 + M0 = 2 * M0 := by ring
      funext j; cases j <;> simp [s2, s1, hM0, ← List.replicate_add, h2]
  have hc3 := stack_copy WKey.M0 WKey.P WKey.sc (by decide) (by decide) (by decide) s2 (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .P (List.replicate (3 * M0) (some true))
  have e3 : ∃ c ≤ 6 * M0 + 3, (copyProg .M0 .P .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .M0).length + 3, ?_, w_exec_congr hc3 ?_⟩
    · simp [s2, s1, hM0]
    · have h3 : M0 + 2 * M0 = 3 * M0 := by ring
      funext j; cases j <;> simp [s3, s2, s1, hM0, ← List.replicate_add, h3]
  have hp4 := (stack_basic_macros WKey.P s3).2.1
  have e4 : ∃ c ≤ 1, (popProg .P).Exec s3
      (Function.update s .P (List.replicate (3 * M0 - 1) (some true))) c := by
    refine ⟨1, le_rfl, w_exec_congr hp4 ?_⟩
    funext j; cases j <;> simp [s3, s2, s1, List.tail_replicate]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 e4))
  exact w_exec_le_of_le e_all (by omega)

def emitHeader1Prog : WProg :=
  .seq (copyProg .N .C2 .sc)
    (.seq (repeatCopyProg mulPEmb)
      (.seq (emitUnaryTo .VAL .outRev)
        (clearProg .VAL)))

def emitHeader2Prog : WProg :=
  .seq (pushProg .VAL (some true))
    (.seq (pushProg .VAL (some true))
      (.seq (emitUnaryTo .VAL .outRev)
        (.seq (clearProg .VAL)
          (copyProg .N .Nrem .sc))))

def emitHeaderProg : WProg :=
  .seq emitHeader1Prog emitHeader2Prog

def initHeaderProg : WProg :=
  .seq buildPProg emitHeaderProg

lemma exec_emitHeader1Prog (s : WStore) (n P : ℕ)
    (hN : s .N = List.replicate n (some true))
    (hP : s .P = List.replicate P (some true))
    (hC2 : s .C2 = []) (hVAL : s .VAL = []) (hsc : s .sc = []) :
    ∃ c ≤ (15 * P + 13) * n + 15,
      emitHeader1Prog.Exec s
        (Function.update s .outRev ((encUnary (n * P)).reverse ++ s .outRev)) c := by
  have hc1 := stack_copy WKey.N WKey.C2 WKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .C2 (List.replicate n (some true))
  have eh1 : ∃ c ≤ 6 * n + 3, (copyProg .N .C2 .sc).Exec s s1 c := by
    refine ⟨6 * (s .N).length + 3, ?_, w_exec_congr hc1 ?_⟩
    · simp [hN]
    · funext j; cases j <;> simp [s1, hN, hC2]
  have eh2 := exec_mulPEmb s1 P n (by simp [s1, hP]) (by simp [s1, hVAL])
    (by simp [s1]) (by simp [s1, hsc])
  set s2 := Function.update (Function.update s1 .C2 []) .VAL (List.replicate (n * P) (some true))
  have eh3 := exec_emitUnaryTo .VAL .outRev (by decide) (by decide) (by decide) s2 (n * P)
    (by simp [s2]) (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .outRev ((encUnary (n * P)).reverse ++ s2 .outRev)
  have hcl4 := (stack_basic_macros WKey.VAL s3).2.2
  have eh4 : ∃ c ≤ 3 * (n * P) + 1,
      (clearProg .VAL).Exec s3
        (Function.update s .outRev ((encUnary (n * P)).reverse ++ s .outRev)) c := by
    refine ⟨3 * (s3 .VAL).length + 1, ?_, w_exec_congr hcl4 ?_⟩
    · simp [s3, s2]
    · funext j; cases j <;> simp [s3, s2, s1, hC2, hVAL]
  have e_all := w_exec_seq_le eh1 (w_exec_seq_le eh2 (w_exec_seq_le eh3 eh4))
  have hring : 6 * n + (6 * P + 7) * n + 6 * (n * P) + 3 * (n * P) = (15 * P + 13) * n := by ring
  exact w_exec_le_of_le e_all (by omega)

lemma exec_emitHeader2Prog (s : WStore) (n : ℕ)
    (hN : s .N = List.replicate n (some true))
    (hNrem : s .Nrem = []) (hVAL : s .VAL = []) (hsc : s .sc = []) :
    ∃ c ≤ 6 * n + 35,
      emitHeader2Prog.Exec s
        (Function.update (Function.update s .outRev ((encUnary 2).reverse ++ s .outRev))
          .Nrem (List.replicate n (some true))) c := by
  have hp5 := (stack_basic_macros WKey.VAL s).1 (some true)
  set s1 := Function.update s .VAL [some true]
  have eh5 : ∃ c ≤ 1, (pushProg .VAL (some true)).Exec s s1 c := by
    refine ⟨1, le_rfl, w_exec_congr hp5 ?_⟩
    funext j; cases j <;> simp [s1, hVAL]
  have hp6 := (stack_basic_macros WKey.VAL s1).1 (some true)
  set s2 := Function.update s1 .VAL (List.replicate 2 (some true))
  have eh6 : ∃ c ≤ 1, (pushProg .VAL (some true)).Exec s1 s2 c := ⟨1, le_rfl, hp6⟩
  have eh7 := exec_emitUnaryTo .VAL .outRev (by decide) (by decide) (by decide) s2 2
    (by simp [s2]) (by simp [s2, s1, hsc])
  set s3 := Function.update s2 .outRev ((encUnary 2).reverse ++ s2 .outRev)
  have hcl8 := (stack_basic_macros WKey.VAL s3).2.2
  set s4 := Function.update s3 .VAL []
  have eh8 : ∃ c ≤ 7, (clearProg .VAL).Exec s3 s4 c := by
    refine ⟨3 * (s3 .VAL).length + 1, ?_, hcl8⟩
    simp [s3, s2]
  have hc9 := stack_copy WKey.N WKey.Nrem WKey.sc (by decide) (by decide) (by decide) s4
    (by simp [s4, s3, s2, s1, hsc])
  have eh9 : ∃ c ≤ 6 * n + 3,
      (copyProg .N .Nrem .sc).Exec s4
        (Function.update (Function.update s .outRev ((encUnary 2).reverse ++ s .outRev))
          .Nrem (List.replicate n (some true))) c := by
    refine ⟨6 * (s4 .N).length + 3, ?_, w_exec_congr hc9 ?_⟩
    · simp [s4, s3, s2, s1, hN]
    · funext j; cases j <;> simp [s4, s3, s2, s1, hN, hNrem, hVAL]
  have e_all := w_exec_seq_le eh5 (w_exec_seq_le eh6 (w_exec_seq_le eh7 (w_exec_seq_le eh8 eh9)))
  exact w_exec_le_of_le e_all (by omega)

lemma exec_initHeaderProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 18 * (2 ^ (wielandtL k - 1)) + (15 * (3 * 2 ^ (wielandtL k - 1) - 1) + 19) * n + 70,
      initHeaderProg.Exec (lStore n k body k)
        (qStore n k (wielandtL k) (2 ^ (wielandtL k - 1)) (3 * 2 ^ (wielandtL k - 1) - 1) body 0) c := by
  set L := wielandtL k
  set M0 := 2 ^ (L - 1)
  set P := 3 * M0 - 1
  have hmin_k : min k (Nat.log 2 (k - 1)) = L - 1 :=
    Nat.min_eq_right (log_sub_one_le k)
  have hL_sub : L - 1 + 1 = L := rfl
  set s0 := lStore n k body k
  have e_p := exec_buildPProg s0 M0
    (by simp [s0, lStore, hmin_k, M0]) (by simp [s0, lStore]) (by simp [s0, lStore])
  set s1 := Function.update s0 .P (List.replicate P (some true))
  have eh1 := exec_emitHeader1Prog s1 n P
    (by simp [s1, s0, lStore]) (by simp [s1])
    (by simp [s1, s0, lStore]) (by simp [s1, s0, lStore]) (by simp [s1, s0, lStore])
  set s2 := Function.update s1 .outRev ((encUnary (n * P)).reverse ++ s1 .outRev)
  have eh2 := exec_emitHeader2Prog s2 n
    (by simp [s2, s1, s0, lStore]) (by simp [s2, s1, s0, lStore])
    (by simp [s2, s1, s0, lStore]) (by simp [s2, s1, s0, lStore])
  have eh2' : ∃ c ≤ 6 * n + 35,
      emitHeader2Prog.Exec s2 (qStore n k L M0 P body 0) c := by
    rcases eh2 with ⟨c, hc, ec⟩
    refine ⟨c, hc, w_exec_congr ec ?_⟩
    funext j
    cases j <;> simp [s2, s1, s0, lStore, qStore, qAllOut, wordAt, hmin_k, hL_sub, M0]
  have e_emit := w_exec_seq_le eh1 eh2'
  have e_all := w_exec_seq_le e_p e_emit
  have hring : (15 * P + 13) * n + 6 * n = (15 * P + 19) * n := by ring
  exact w_exec_le_of_le e_all (by omega)

def rawOut (w : List Sym) : List Sym :=
  let n := valAt w 0
  let k := valAt w 1
  let body := wordAt w 2
  let L := wielandtL k
  let M0 := 2 ^ (L - 1)
  let P := 3 * M0 - 1
  encUnary (n * P) ++ encUnary 2 ++ qAllOut body k P n

def f_prep (w : List Sym) : List Sym :=
  let L := wielandtL (valAt w 1)
  List.replicate L (some false) ++ (rawOut w).drop L

def finalizeProg : WProg :=
  .seq (transferProg .outRev (fun j => decide (j = .ko)))
    (.seq (copyProg .L .C1 .sc)
      (.seq (syncPopProg .C1 .ko)
        (transferProg .L (fun j => decide (j = .ko)))))

lemma drop_min_length {α : Type} (l : List α) (n : ℕ) :
    l.drop (min n l.length) = l.drop n := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_of_length_le (by omega),
      List.drop_of_length_le (by omega)]

lemma reverse_replicate {α : Type} (n : ℕ) (a : α) :
    (List.replicate n a).reverse = List.replicate n a := by
  simp

lemma exec_finalizeProg (w : List Sym) :
    ∃ s_fin : WStore, ∃ c ≤ 3 * (rawOut w).length + 12 * (wielandtL (valAt w 1)) + 12,
      finalizeProg.Exec
        (qStore (valAt w 0) (valAt w 1) (wielandtL (valAt w 1))
          (2 ^ (wielandtL (valAt w 1) - 1)) (3 * 2 ^ (wielandtL (valAt w 1) - 1) - 1)
          (wordAt w 2) (valAt w 0)) s_fin c ∧
      s_fin .ko = f_prep w := by
  set n := valAt w 0
  set k := valAt w 1
  set body := wordAt w 2
  set L := wielandtL k
  set M0 := 2 ^ (L - 1)
  set P := 3 * M0 - 1
  set s0 := qStore n k L M0 P body n
  have hout_eq : s0 .outRev = (rawOut w).reverse := by
    simp [s0, qStore, rawOut, n, k, body, L, M0, P, List.reverse_append, List.append_assoc]
  have htr1 := stack_transfer WKey.outRev (fun j => decide (j = .ko)) s0
  set s1 := transferStore WKey.outRev (fun j => decide (j = .ko)) s0
  have e1 : ∃ c ≤ 3 * (rawOut w).length + 1,
      (transferProg .outRev (fun j => decide (j = .ko))).Exec s0 s1 c := by
    refine ⟨3 * (s0 .outRev).length + 1, ?_, htr1⟩
    rw [hout_eq, List.length_reverse]
  have hcp2 := stack_copy WKey.L WKey.C1 WKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, transferStore, s0, qStore])
  set s2 := Function.update s1 .C1 (List.replicate L (some false))
  have e2 : ∃ c ≤ 6 * L + 3, (copyProg .L .C1 .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .L).length + 3, ?_, w_exec_congr hcp2 ?_⟩
    · simp [s1, transferStore, s0, qStore]
    · funext j; cases j <;> simp [s2, s1, transferStore, s0, qStore]
  have hsync3 := stack_sync_pop WKey.C1 WKey.ko (by decide) s2
  set s3 := Function.update
    (Function.update s2 .C1 ((s2 .C1).drop (min (s2 .C1).length (s2 .ko).length)))
    .ko ((s2 .ko).drop (min (s2 .C1).length (s2 .ko).length))
  have e3 : ∃ c ≤ 3 * L + 1, (syncPopProg .C1 .ko).Exec s2 s3 c := by
    refine ⟨3 * min (s2 .C1).length (s2 .ko).length + 1, ?_, hsync3⟩
    have : (s2 .C1).length = L := by simp [s2]
    omega
  have htr4 := stack_transfer WKey.L (fun j => decide (j = .ko)) s3
  set s4 := transferStore WKey.L (fun j => decide (j = .ko)) s3
  have e4 : ∃ c ≤ 3 * L + 1,
      (transferProg .L (fun j => decide (j = .ko))).Exec s3 s4 c := by
    refine ⟨3 * (s3 .L).length + 1, ?_, htr4⟩
    simp [s3, s2, s1, transferStore, s0, qStore]
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 e4))
  rcases e_all with ⟨c, hc, ec⟩
  refine ⟨s4, c, by omega, ec, ?_⟩
  have hs2_ko : s2 .ko = rawOut w := by
    have h1 : s1 .ko = rawOut w := by
      dsimp [s1, transferStore]
      rw [hout_eq, List.reverse_reverse]
      have hko0 : s0 .ko = [] := rfl
      rw [hko0, List.append_nil]
    simp [s2, h1]
  have hs2_C1 : (s2 .C1).length = L := by simp [s2]
  have hs3_ko : s3 .ko = (rawOut w).drop L := by
    simp [s3, hs2_ko, hs2_C1, drop_min_length]
  have hs3_L : s3 .L = List.replicate L (some false) := by
    simp [s3, s2, s1, transferStore, s0, qStore]
  simp [s4, transferStore, hs3_L, hs3_ko, f_prep, L, k]

lemma transValU_le (u : List Sym) (k P q child : ℕ) (hchd : child ≤ 2 * P + 2) :
    transValU u k P q child ≤ (q + u.length + 2) * P + 2 := by
  unfold transValU
  split_ifs with h1 h2
  · calc q * P + child ≤ q * P + (2 * P + 2) := by omega
      _ ≤ (q + u.length + 2) * P + 2 := by nlinarith
  · have hv : valAt u (child - P) ≤ u.length := valAt_le_length u (child - P)
    have hmul : valAt u (child - P) * P ≤ u.length * P := Nat.mul_le_mul_right P hv
    nlinarith
  · have hv : valAt u 0 ≤ u.length := valAt_le_length u 0
    have hmul : valAt u 0 * P ≤ u.length * P := Nat.mul_le_mul_right P hv
    nlinarith

lemma length_encUnary (v : ℕ) : (encUnary v).length = v + 1 := by
  simp [encUnary]

lemma length_onePOut_le (u : List Sym) (k P q p : ℕ) (hp : p < P) :
    (onePOut u k P q p).length ≤ 2 * (q + u.length + 2) * P + 6 := by
  unfold onePOut
  rw [List.length_append, length_encUnary, length_encUnary]
  have h1 := transValU_le u k P q (2 * p + 2) (by omega)
  have h2 := transValU_le u k P q (2 * p + 1) (by omega)
  have hring : 2 * (q + u.length + 2) * P = 2 * ((q + u.length + 2) * P) := by ring
  omega

lemma length_pBlockOut_le (u : List Sym) (k P q : ℕ) :
    ∀ p ≤ P, (pBlockOut u k P q p).length ≤ p * (2 * (q + u.length + 2) * P + 6)
  | 0, _ => by simp [pBlockOut]
  | p + 1, hp => by
    simp only [pBlockOut, List.length_append]
    have ih := length_pBlockOut_le u k P q p (by omega)
    have h1 := length_onePOut_le u k P q p (by omega)
    rw [Nat.succ_mul]
    omega

lemma length_qAllOut_le (body : List Sym) (k P n : ℕ) :
    ∀ q ≤ n, (qAllOut body k P q).length ≤ q * (P * (2 * (n + body.length + 2) * P + 6))
  | 0, _ => by simp [qAllOut]
  | q + 1, hq => by
    simp only [qAllOut, List.length_append]
    have ih := length_qAllOut_le body k P n q (by omega)
    have hp := length_pBlockOut_le (wordAt body (q * k)) k P q P le_rfl
    have hu : (wordAt body (q * k)).length ≤ body.length := length_wordAt_le body (q * k)
    have hle_in : 2 * (q + (wordAt body (q * k)).length + 2) * P + 6 ≤
        2 * (n + body.length + 2) * P + 6 := by
      have : q + (wordAt body (q * k)).length + 2 ≤ n + body.length + 2 := by omega
      nlinarith
    have hmul_P : P * (2 * (q + (wordAt body (q * k)).length + 2) * P + 6) ≤
        P * (2 * (n + body.length + 2) * P + 6) :=
      Nat.mul_le_mul_left P hle_in
    rw [Nat.succ_mul]
    omega

def wielandtProg : WProg :=
  .seq initReadProg
    (.seq lLoopProg
      (.seq initHeaderProg
        (.seq qLoopProg
          finalizeProg)))

lemma wielandt_step_bound (M w_len n k b_len L M0 P raw_len c : ℕ)
    (hM_eq : M = w_len + 1)
    (hn : n ≤ M) (hk : k ≤ M) (hb : b_len ≤ M)
    (hL : L ≤ 2 * M) (hM0 : M0 ≤ 2 * M) (hP : P ≤ 6 * M)
    (hraw : raw_len ≤ (n * P + 1) + 3 + n * (P * (2 * (n + b_len + 2) * P + 6)))
    (hc : c ≤ (12 * w_len + 18) + 1 + ((k * (36 * k + 62) + 1) + 1 +
      ((18 * M0 + (15 * P + 19) * n + 70) + 1 +
      ((n * (P * ((42 * P + 62) * b_len + 30 * (n * P) + 18 * k + 124 * P + 277) +
        k * (6 * b_len + 10) + 6 * k + 15 * P + 22) + 1) + 1 +
      (3 * raw_len + 12 * L + 12))))) :
    c ≤ 15000 * M ^ 4 := by
  have h1M : 1 ≤ M := by omega
  have hM2 : M ≤ M ^ 2 := by
    have := Nat.mul_le_mul_left M h1M
    nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by
    have := Nat.mul_le_mul_left (M ^ 2) h1M
    linarith [show M ^ 2 * M = M ^ 3 by ring, show M ^ 2 * 1 = M ^ 2 by ring]
  have hM4 : M ^ 3 ≤ M ^ 4 := by
    have := Nat.mul_le_mul_left (M ^ 3) h1M
    linarith [show M ^ 3 * M = M ^ 4 by ring, show M ^ 3 * 1 = M ^ 3 by ring]
  have hnP : n * P ≤ 6 * M ^ 2 := by
    have := Nat.mul_le_mul hn hP
    linarith [show M * (6 * M) = 6 * M ^ 2 by ring]
  have hraw1 : 2 * (n + b_len + 2) * P + 6 ≤ 54 * M ^ 2 := by
    have hnb : 2 * (n + b_len + 2) ≤ 8 * M := by omega
    have := Nat.mul_le_mul hnb hP
    linarith [show (8 * M) * (6 * M) = 48 * M ^ 2 by ring]
  have hraw2 : P * (2 * (n + b_len + 2) * P + 6) ≤ 324 * M ^ 3 := by
    have := Nat.mul_le_mul hP hraw1
    linarith [show (6 * M) * (54 * M ^ 2) = 324 * M ^ 3 by ring]
  have hraw3 : n * (P * (2 * (n + b_len + 2) * P + 6)) ≤ 324 * M ^ 4 := by
    have := Nat.mul_le_mul hn hraw2
    linarith [show M * (324 * M ^ 3) = 324 * M ^ 4 by ring]
  have hraw_tot : raw_len ≤ 334 * M ^ 4 := by omega
  have he2 : k * (36 * k + 62) ≤ 98 * M ^ 2 := by
    have hk2 : 36 * k + 62 ≤ 98 * M := by omega
    have := Nat.mul_le_mul hk hk2
    linarith [show M * (98 * M) = 98 * M ^ 2 by ring]
  have he3 : (15 * P + 19) * n ≤ 109 * M ^ 2 := by
    have hP2 : 15 * P + 19 ≤ 109 * M := by omega
    have := Nat.mul_le_mul hP2 hn
    linarith [show (109 * M) * M = 109 * M ^ 2 by ring]
  have hq1 : (42 * P + 62) * b_len ≤ 314 * M ^ 2 := by
    have hP3 : 42 * P + 62 ≤ 314 * M := by omega
    have := Nat.mul_le_mul hP3 hb
    linarith [show (314 * M) * M = 314 * M ^ 2 by ring]
  have hq2 : (42 * P + 62) * b_len + 30 * (n * P) + 18 * k + 124 * P + 277 ≤ 1533 * M ^ 2 := by
    omega
  have hq3 : P * ((42 * P + 62) * b_len + 30 * (n * P) + 18 * k + 124 * P + 277) ≤ 9198 * M ^ 3 := by
    have := Nat.mul_le_mul hP hq2
    linarith [show (6 * M) * (1533 * M ^ 2) = 9198 * M ^ 3 by ring]
  have hq4 : k * (6 * b_len + 10) ≤ 16 * M ^ 2 := by
    have hb2 : 6 * b_len + 10 ≤ 16 * M := by omega
    have := Nat.mul_le_mul hk hb2
    linarith [show M * (16 * M) = 16 * M ^ 2 by ring]
  have hq5 : P * ((42 * P + 62) * b_len + 30 * (n * P) + 18 * k + 124 * P + 277) +
      k * (6 * b_len + 10) + 6 * k + 15 * P + 22 ≤ 9332 * M ^ 3 := by
    linarith
  have he4 : n * (P * ((42 * P + 62) * b_len + 30 * (n * P) + 18 * k + 124 * P + 277) +
      k * (6 * b_len + 10) + 6 * k + 15 * P + 22) ≤ 9332 * M ^ 4 := by
    have := Nat.mul_le_mul hn hq5
    linarith [show M * (9332 * M ^ 3) = 9332 * M ^ 4 by ring]
  linarith

lemma exec_wielandtProg (w : List Sym) :
    ∃ s_fin : WStore, ∃ c ≤ 15000 * (w.length + 1) ^ 4,
      wielandtProg.Exec (fun j => if j = .ki then w else []) s_fin c ∧
      s_fin .ko = f_prep w := by
  set n := valAt w 0
  set k := valAt w 1
  set body := wordAt w 2
  set L := wielandtL k
  set M0 := 2 ^ (L - 1)
  set P := 3 * M0 - 1
  have hn_le : n ≤ w.length + 1 := Nat.le_succ_of_le (valAt_le_length w 0)
  have hk_le : k ≤ w.length + 1 := Nat.le_succ_of_le (valAt_le_length w 1)
  have hb_le : body.length ≤ w.length + 1 := Nat.le_succ_of_le (length_wordAt_le w 2)
  have hL_le : L ≤ 2 * (w.length + 1) := by
    have : Nat.log 2 (k - 1) ≤ k := log_sub_one_le k
    dsimp [L, wielandtL]
    omega
  have hM0_le : M0 ≤ 2 * (w.length + 1) := by
    have h1 := pow_min_log_le k k
    have hmin : min k (Nat.log 2 (k - 1)) = L - 1 :=
      Nat.min_eq_right (log_sub_one_le k)
    rw [hmin] at h1
    change M0 ≤ k + 1 at h1
    omega
  have hP_le : P ≤ 6 * (w.length + 1) := by omega
  have e1 := exec_initReadProg w
  have e2 := exec_lLoopProg n k body
  have e3 := exec_initHeaderProg n k body
  have e4 := exec_qLoopProg n k L M0 P body
  obtain ⟨s_fin, c5, hc5, ec5, hko⟩ := exec_finalizeProg w
  have e5 : ∃ c ≤ 3 * (rawOut w).length + 12 * L + 12,
      finalizeProg.Exec (qStore n k L M0 P body n) s_fin c := ⟨c5, hc5, ec5⟩
  have e_all := w_exec_seq_le e1 (w_exec_seq_le e2 (w_exec_seq_le e3 (w_exec_seq_le e4 e5)))
  rcases e_all with ⟨c, hc, ec⟩
  refine ⟨s_fin, c, ?_, ec, hko⟩
  have hraw_len : (rawOut w).length ≤ (n * P + 1) + 3 + n * (P * (2 * (n + body.length + 2) * P + 6)) := by
    change (encUnary (n * P) ++ encUnary 2 ++ qAllOut body k P n).length ≤ _
    simp only [List.length_append, length_encUnary]
    have hq := length_qAllOut_le body k P n n le_rfl
    omega
  exact wielandt_step_bound (w.length + 1) w.length n k body.length L M0 P (rawOut w).length c
    rfl hn_le hk_le hb_le hL_le hM0_le hP_le hraw_len hc

lemma polyTimeComputable_prep : PolyTimeComputable f_prep := by
  obtain ⟨k, hk⟩ := polynomial_absorb 15000 4 0
  refine stack_program_polytime wielandtProg .ki .ko f_prep k (fun w => ?_)
  obtain ⟨s_fin, c, hc, hexec, hko⟩ := exec_wielandtProg w
  have hk_w := hk w.length
  exact ⟨s_fin, c, by omega, hexec, hko⟩

/-! ### Part 5: Connecting `f_prep AH.encode` to `(heapWielandtAB AH hL).encode` -/

lemma leadOnes_replicate_append (n : ℕ) (xs : List Sym) :
    leadOnes (List.replicate n (some true) ++ none :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leadOnes, ih]

lemma nextWord_replicate_append (n : ℕ) (xs : List Sym) :
    nextWord (List.replicate n (some true) ++ none :: xs) = xs := by
  unfold nextWord
  rw [leadOnes_replicate_append]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

lemma drop_flatMap_encUnary :
    ∀ (L : List ℕ) (j : ℕ), j < L.length →
      (L.drop j).flatMap encUnary =
        List.replicate (L.getD j 0) (some true) ++ none :: (L.drop (j + 1)).flatMap encUnary
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by
    simp [encUnary]
  | _ :: xs, j + 1, hj => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
    simpa [List.drop_succ_cons] using drop_flatMap_encUnary xs j hj

def transVals (A : Automaton) : List ℕ :=
  (List.finRange A.n).flatMap fun q =>
    (List.finRange A.k).map fun a => (A.δ q a).val

def bodyA (A : Automaton) : List Sym :=
  (transVals A).flatMap encUnary

lemma encode_eq_bodyA (A : Automaton) :
    A.encode =
      List.replicate A.n (some true) ++ none ::
        (List.replicate A.k (some true) ++ none :: bodyA A) := by
  unfold Automaton.encode bodyA transVals
  simp only [encUnary, List.append_assoc, List.cons_append]
  congr 4
  induction (List.finRange A.n) with
  | nil => rfl
  | cons q qs ih =>
    simp [List.flatMap_cons, List.flatMap_append, List.flatMap_map, encUnary, ih]

lemma wordAt_zero_encode (A : Automaton) :
    wordAt A.encode 0 =
      List.replicate A.n (some true) ++ none ::
        (List.replicate A.k (some true) ++ none :: bodyA A) :=
  encode_eq_bodyA A

lemma wordAt_one_encode (A : Automaton) :
    wordAt A.encode 1 = List.replicate A.k (some true) ++ none :: bodyA A := by
  change nextWord (wordAt A.encode 0) = _
  rw [wordAt_zero_encode, nextWord_replicate_append]

lemma wordAt_two_encode (A : Automaton) :
    wordAt A.encode 2 = bodyA A := by
  change nextWord (wordAt A.encode 1) = _
  rw [wordAt_one_encode, nextWord_replicate_append]

lemma valAt_zero_encode (A : Automaton) :
    valAt A.encode 0 = A.n := by
  unfold valAt
  rw [wordAt_zero_encode, leadOnes_replicate_append]

lemma valAt_one_encode (A : Automaton) :
    valAt A.encode 1 = A.k := by
  unfold valAt
  rw [wordAt_one_encode, leadOnes_replicate_append]

lemma wordAt_succ_eq_wordAt_nextWord (w : List Sym) (idx : ℕ) :
    wordAt w (idx + 1) = wordAt (nextWord w) idx := by
  induction idx generalizing w with
  | zero => rfl
  | succ idx ih =>
    change nextWord (wordAt w (idx + 1)) = nextWord (wordAt (nextWord w) idx)
    rw [ih w]

lemma wordAt_flatMap_encUnary :
    ∀ (L : List ℕ) (idx : ℕ),
      wordAt (L.flatMap encUnary) idx = (L.drop idx).flatMap encUnary
  | L, 0 => by simp [wordAt]
  | [], idx + 1 => by
    rw [wordAt_succ_eq_wordAt_nextWord]
    have h0 : nextWord (([] : List ℕ).flatMap encUnary) = ([] : List ℕ).flatMap encUnary := rfl
    rw [h0, wordAt_flatMap_encUnary [] idx]
    simp
  | x :: xs, idx + 1 => by
    rw [wordAt_succ_eq_wordAt_nextWord, List.flatMap_cons]
    have h1 : encUnary x ++ xs.flatMap encUnary =
        List.replicate x (some true) ++ none :: xs.flatMap encUnary := by
      simp [encUnary]
    rw [h1, nextWord_replicate_append, List.drop_succ_cons]
    exact wordAt_flatMap_encUnary xs idx

lemma valAt_flatMap_encUnary (L : List ℕ) (idx : ℕ) (h : idx < L.length) :
    valAt (L.flatMap encUnary) idx = L.getD idx 0 := by
  unfold valAt
  rw [wordAt_flatMap_encUnary, drop_flatMap_encUnary L idx h, leadOnes_replicate_append]

lemma length_flatMap_const {α β : Type} (k : ℕ) (f : α → List β) (hf : ∀ x, (f x).length = k) :
    ∀ xs : List α, (xs.flatMap f).length = xs.length * k
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, hf x, length_flatMap_const k f hf xs,
      List.length_cons, Nat.succ_mul, add_comm]

lemma drop_flatMap_const {α β : Type} (k : ℕ) (f : α → List β) (hf : ∀ x, (f x).length = k) :
    ∀ (xs : List α) (q : ℕ), (xs.flatMap f).drop (q * k) = (xs.drop q).flatMap f
  | xs, 0 => by simp
  | [], _ + 1 => by simp
  | x :: xs, q + 1 => by
    have h1 : (f x ++ xs.flatMap f).drop k = xs.flatMap f := by
      rw [← hf x, List.drop_left]
    rw [List.flatMap_cons, Nat.succ_mul, add_comm (q * k) k, ← List.drop_drop, h1,
      List.drop_succ_cons]
    exact drop_flatMap_const k f hf xs q

lemma length_transVals (A : Automaton) : (transVals A).length = A.n * A.k := by
  unfold transVals
  rw [length_flatMap_const A.k (fun q => (List.finRange A.k).map fun a => (A.δ q a).val)
    (fun _ => by simp), List.length_finRange]

lemma getD_drop_zero (L : List ℕ) (i : ℕ) :
    (L.drop i).getD 0 0 = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp [List.drop_succ_cons, ih i]

lemma drop_finRange_eq_cons {n : ℕ} (q : Fin n) :
    (List.finRange n).drop q.val = q :: (List.finRange n).drop (q.val + 1) := by
  have hlt : q.val < (List.finRange n).length := by simp [q.isLt]
  rw [List.drop_eq_getElem_cons hlt]
  simp

lemma getD_transVals (A : Automaton) (q : Fin A.n) (a : Fin A.k) :
    (transVals A).getD (q.val * A.k + a.val) 0 = (A.δ q a).val := by
  rw [← getD_drop_zero (transVals A) (q.val * A.k + a.val), ← List.drop_drop]
  unfold transVals
  rw [drop_flatMap_const A.k (fun q => (List.finRange A.k).map fun a => (A.δ q a).val)
    (fun _ => by simp) (List.finRange A.n) q.val, drop_finRange_eq_cons q, List.flatMap_cons]
  have hlen : a.val ≤ ((List.finRange A.k).map fun b => (A.δ q b).val).length := by
    simp [le_of_lt a.isLt]
  rw [List.drop_append_of_le_length hlen]
  have hmap_drop : ((List.finRange A.k).map fun b => (A.δ q b).val).drop a.val =
      (A.δ q a).val :: (((List.finRange A.k).drop (a.val + 1)).map fun b => (A.δ q b).val) := by
    rw [← List.map_drop, drop_finRange_eq_cons a, List.map_cons]
  rw [hmap_drop]
  rfl

lemma valAt_bodyA (A : Automaton) (q : Fin A.n) (a : Fin A.k) :
    valAt (bodyA A) (q.val * A.k + a.val) = (A.δ q a).val := by
  have hlt : q.val * A.k + a.val < (transVals A).length := by
    rw [length_transVals]
    calc q.val * A.k + a.val < q.val * A.k + A.k := Nat.add_lt_add_left a.isLt _
      _ = (q.val + 1) * A.k := by ring
      _ ≤ A.n * A.k := Nat.mul_le_mul_right A.k (Nat.succ_le_of_lt q.isLt)
  unfold bodyA
  rw [valAt_flatMap_encUnary (transVals A) (q.val * A.k + a.val) hlt, getD_transVals]

lemma valAt_wordAt_bodyA (AH : Automaton) (q : ℕ) (hq : q < AH.n) (a : ℕ) (ha : a < AH.k) :
    valAt (wordAt (bodyA AH) (q * AH.k)) a = (AH.δ ⟨q, hq⟩ ⟨a, ha⟩).val := by
  rw [valAt_wordAt]
  exact valAt_bodyA AH ⟨q, hq⟩ ⟨a, ha⟩

lemma heapWielandtAB_delta_eq_transValU (AH : Automaton) (hk : 2 ≤ AH.k)
    (hL : 1 ≤ wielandtL AH.k)
    (s : Fin (heapWielandtAB AH hL).n) (a : Fin 2) :
    let L := wielandtL AH.k
    let P := 3 * 2 ^ (L - 1) - 1
    let q := s.val / P
    let p := s.val % P
    let child := 2 * p + (2 - a.val)
    ((heapWielandtAB AH hL).δ s a).val =
      transValU (wordAt (bodyA AH) (q * AH.k)) AH.k P q child := by
  intro L P q p child
  rw [heapWielandtAB_delta_val AH hk hL s a]
  unfold transValU
  have hq : q < AH.n := heapWielandtAB_q_lt AH hL s
  split_ifs with h1 h2
  · rfl
  · rw [valAt_wordAt_bodyA AH q hq (child - P) h2]
  · rw [valAt_wordAt_bodyA AH q hq 0 (by omega)]

lemma finRange_two_flatMap_delta (AH : Automaton) (hk : 2 ≤ AH.k)
    (hL : 1 ≤ wielandtL AH.k) (s : Fin (heapWielandtAB AH hL).n) :
    let P := 3 * 2 ^ (wielandtL AH.k - 1) - 1
    ((List.finRange (heapWielandtAB AH hL).k).flatMap fun a =>
      List.replicate ((heapWielandtAB AH hL).δ s a).val (some true) ++ [none]) =
      onePOut (wordAt (bodyA AH) ((s.val / P) * AH.k)) AH.k P (s.val / P) (s.val % P) := by
  intro P
  let a0 : Fin 2 := ⟨0, by decide⟩
  let a1 : Fin 2 := ⟨1, by decide⟩
  change ((List.finRange 2).flatMap fun a : Fin 2 =>
    List.replicate ((heapWielandtAB AH hL).δ s a).val (some true) ++ [none]) = _
  have h2 : List.finRange 2 = [a0, a1] := rfl
  rw [h2, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change encUnary ((heapWielandtAB AH hL).δ s a0).val ++
      encUnary ((heapWielandtAB AH hL).δ s a1).val = _
  rw [heapWielandtAB_delta_eq_transValU AH hk hL s a0,
      heapWielandtAB_delta_eq_transValU AH hk hL s a1]
  rfl

lemma flatMap_range_q_P (body : List Sym) (k P q : ℕ) :
    ∀ p : ℕ, p ≤ P →
      ((List.range p).map (q * P + ·)).flatMap (fun s =>
        onePOut (wordAt body ((s / P) * k)) k P (s / P) (s % P)) =
      pBlockOut (wordAt body (q * k)) k P q p
  | 0, _ => rfl
  | p + 1, hp => by
    have hp_lt : p < P := by omega
    have hP_pos : 0 < P := by omega
    have hdiv : (q * P + p) / P = q := by
      rw [Nat.mul_comm q P, Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hp_lt, add_zero]
    have hmod : (q * P + p) % P = p := by
      rw [Nat.mul_comm q P, Nat.mul_add_mod, Nat.mod_eq_of_lt hp_lt]
    simp [List.range_succ, pBlockOut, flatMap_range_q_P body k P q p (by omega), hdiv, hmod]

lemma qAllOut_eq_flatMap_range (body : List Sym) (k P : ℕ) :
    ∀ q : ℕ, qAllOut body k P q =
      (List.range (q * P)).flatMap (fun s =>
        onePOut (wordAt body ((s / P) * k)) k P (s / P) (s % P))
  | 0 => by simp [qAllOut]
  | q + 1 => by
    simp only [qAllOut, qAllOut_eq_flatMap_range body k P q]
    rw [Nat.succ_mul, List.range_add, List.flatMap_append,
      flatMap_range_q_P body k P q P le_rfl]

lemma map_val_finRange : ∀ m : ℕ, (List.finRange m).map Fin.val = List.range m
  | 0 => rfl
  | m + 1 => by
    rw [List.finRange_succ, List.map_cons, List.range_succ_eq_map]
    congr 1
    rw [← map_val_finRange m, List.map_map, List.map_map]
    rfl

lemma flatMap_finRange_eq_flatMap_range {α : Type} (m : ℕ) (g : ℕ → List α) :
    ((List.finRange m).flatMap fun s => g s.val) = (List.range m).flatMap g := by
  rw [← map_val_finRange m, List.flatMap_map]

lemma rawOut_encode_eq (AH : Automaton) (hk : 2 ≤ AH.k) (hL : 1 ≤ wielandtL AH.k) :
    rawOut AH.encode = (heapWielandtAB AH hL).encode := by
  set L := wielandtL AH.k
  set M0 := 2 ^ (L - 1)
  set P := 3 * M0 - 1
  have hP_eq : (properPrefixes (wielandtCode L)).card = P :=
    properPrefixes_wielandtCode_card' L hL
  unfold rawOut
  rw [valAt_zero_encode, valAt_one_encode, wordAt_two_encode]
  dsimp only
  change encUnary (AH.n * P) ++ encUnary 2 ++ qAllOut (bodyA AH) AH.k P AH.n = _
  rw [qAllOut_eq_flatMap_range (bodyA AH) AH.k P AH.n]
  unfold Automaton.encode
  have hAB_n : (heapWielandtAB AH hL).n = AH.n * P := by
    show AH.n * (properPrefixes (wielandtCode L)).card = AH.n * P
    rw [hP_eq]
  have hAB_k : (heapWielandtAB AH hL).k = 2 := rfl
  have hbody : ((List.finRange (heapWielandtAB AH hL).n).flatMap fun s =>
      (List.finRange (heapWielandtAB AH hL).k).flatMap fun a =>
        List.replicate ((heapWielandtAB AH hL).δ s a).val (some true) ++ [none]) =
      (List.range (AH.n * P)).flatMap (fun s =>
        onePOut (wordAt (bodyA AH) ((s / P) * AH.k)) AH.k P (s / P) (s % P)) := by
    have hstep : ∀ s : Fin (heapWielandtAB AH hL).n,
        ((List.finRange (heapWielandtAB AH hL).k).flatMap fun a =>
          List.replicate ((heapWielandtAB AH hL).δ s a).val (some true) ++ [none]) =
        onePOut (wordAt (bodyA AH) ((s.val / P) * AH.k)) AH.k P (s.val / P) (s.val % P) :=
      finRange_two_flatMap_delta AH hk hL
    simp only [hstep]
    rw [flatMap_finRange_eq_flatMap_range (heapWielandtAB AH hL).n
      (fun s => onePOut (wordAt (bodyA AH) ((s / P) * AH.k)) AH.k P (s / P) (s % P)), hAB_n]
  rw [hbody, hAB_n, hAB_k]
  simp [encUnary, List.append_assoc]

def isSomeFalse (x : Sym) : Bool := decide (x = some false)

lemma map_unmaskFalse_encUnary (v : ℕ) : (encUnary v).map unmaskFalse = encUnary v := by
  simp [encUnary, unmaskFalse]

lemma map_unmaskFalse_onePOut (u : List Sym) (k P q p : ℕ) :
    (onePOut u k P q p).map unmaskFalse = onePOut u k P q p := by
  simp [onePOut, map_unmaskFalse_encUnary]

lemma map_unmaskFalse_pBlockOut (u : List Sym) (k P q : ℕ) :
    ∀ p, (pBlockOut u k P q p).map unmaskFalse = pBlockOut u k P q p
  | 0 => rfl
  | p + 1 => by simp [pBlockOut, map_unmaskFalse_onePOut, map_unmaskFalse_pBlockOut u k P q p]

lemma map_unmaskFalse_qAllOut (body : List Sym) (k P : ℕ) :
    ∀ q, (qAllOut body k P q).map unmaskFalse = qAllOut body k P q
  | 0 => rfl
  | q + 1 => by simp [qAllOut, map_unmaskFalse_pBlockOut, map_unmaskFalse_qAllOut body k P q]

lemma filter_isSomeFalse_encUnary (v : ℕ) : (encUnary v).filter isSomeFalse = [] := by
  simp [encUnary, isSomeFalse]

lemma filter_isSomeFalse_onePOut (u : List Sym) (k P q p : ℕ) :
    (onePOut u k P q p).filter isSomeFalse = [] := by
  simp [onePOut, filter_isSomeFalse_encUnary]

lemma filter_isSomeFalse_pBlockOut (u : List Sym) (k P q : ℕ) :
    ∀ p, (pBlockOut u k P q p).filter isSomeFalse = []
  | 0 => rfl
  | p + 1 => by simp [pBlockOut, filter_isSomeFalse_onePOut, filter_isSomeFalse_pBlockOut u k P q p]

lemma filter_isSomeFalse_qAllOut (body : List Sym) (k P : ℕ) :
    ∀ q, (qAllOut body k P q).filter isSomeFalse = []
  | 0 => rfl
  | q + 1 => by simp [qAllOut, filter_isSomeFalse_pBlockOut, filter_isSomeFalse_qAllOut body k P q]

lemma wielandtL_le_n_mul_P (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    L ≤ n * (3 * 2 ^ (L - 1) - 1) := by
  have hpow : L - 1 < 2 ^ (L - 1) := Nat.lt_two_pow_self
  have hL_le : L ≤ 3 * 2 ^ (L - 1) - 1 := by omega
  calc L ≤ 3 * 2 ^ (L - 1) - 1 := hL_le
    _ = 1 * (3 * 2 ^ (L - 1) - 1) := (Nat.one_mul _).symm
    _ ≤ n * (3 * 2 ^ (L - 1) - 1) := Nat.mul_le_mul_right _ hn

lemma rawOut_encode_split (AH : Automaton) (hn : 2 ≤ AH.n) (hL : 1 ≤ wielandtL AH.k) :
    let L := wielandtL AH.k
    let P := 3 * 2 ^ (L - 1) - 1
    rawOut AH.encode =
      List.replicate L (some true) ++
        (List.replicate (AH.n * P - L) (some true) ++
          [none] ++ encUnary 2 ++ qAllOut (bodyA AH) AH.k P AH.n) := by
  intro L P
  have hLP : L ≤ AH.n * P := wielandtL_le_n_mul_P AH.n L (by omega) hL
  unfold rawOut
  rw [valAt_zero_encode, valAt_one_encode, wordAt_two_encode]
  dsimp only
  change List.replicate (AH.n * P) (some true) ++ [none] ++ encUnary 2 ++
      qAllOut (bodyA AH) AH.k P AH.n = _
  have hrep : List.replicate (AH.n * P) (some true) =
      List.replicate L (some true) ++ List.replicate (AH.n * P - L) (some true) := by
    rw [← List.replicate_add, Nat.add_sub_of_le hLP]
  rw [hrep]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma drop_rawOut_encode (AH : Automaton) (hn : 2 ≤ AH.n) (hL : 1 ≤ wielandtL AH.k) :
    let L := wielandtL AH.k
    let P := 3 * 2 ^ (L - 1) - 1
    (rawOut AH.encode).drop L =
      List.replicate (AH.n * P - L) (some true) ++
        [none] ++ encUnary 2 ++ qAllOut (bodyA AH) AH.k P AH.n := by
  intro L P
  rw [rawOut_encode_split AH hn hL]
  have hlen : (List.replicate L (some true)).length = L := by simp
  exact List.drop_left' hlen

lemma map_unmaskFalse_f_prep_encode (AH : Automaton) (hn : 2 ≤ AH.n) (hk : 2 ≤ AH.k)
    (hL : 1 ≤ wielandtL AH.k) :
    (f_prep AH.encode).map unmaskFalse = (heapWielandtAB AH hL).encode := by
  unfold f_prep
  rw [valAt_one_encode]
  dsimp only
  rw [drop_rawOut_encode AH hn hL]
  simp only [List.map_append, List.map_replicate, unmaskFalse, List.map_cons, List.map_nil,
    map_unmaskFalse_encUnary, map_unmaskFalse_qAllOut]
  rw [← rawOut_encode_split AH hn hL, rawOut_encode_eq AH hk hL]

lemma filter_isSomeFalse_f_prep_encode (AH : Automaton) (hn : 2 ≤ AH.n)
    (hL : 1 ≤ wielandtL AH.k) :
    ((f_prep AH.encode).filter isSomeFalse).length = wielandtL AH.k := by
  unfold f_prep
  rw [valAt_one_encode]
  dsimp only
  rw [drop_rawOut_encode AH hn hL]
  simp [isSomeFalse, filter_isSomeFalse_encUnary, filter_isSomeFalse_qAllOut]

end WielandtStackProof

lemma countL_eq_filter_filterMap (cells : List SaveSym) :
    DivStackProof.countL cells =
      ((cells.filterMap Prod.fst).filter isSomeFalse).length := by
  unfold DivStackProof.countL
  induction cells with
  | nil => rfl
  | cons p cs ih =>
    rcases p with ⟨_ | _ | (_ | _), m⟩ <;>
      simp [DivStackProof.isFalseOrig, isSomeFalse, ih]

theorem heap_wielandtAB_encode_polyTime (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg_H : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg_H ∧
      ∀ AH : Automaton, IsHuffmanDecoder AH.δ → IsSynchronizing AH.δ → 2 ≤ AH.n → 2 ≤ AH.k →
        ∀ hL : 1 ≤ wielandtL AH.k,
          (Alg_H AH.encode).length = (Alg (heapWielandtAB AH hL).encode).length / wielandtL AH.k := by
  obtain ⟨f_save, hf_save_poly, hf_save_spec⟩ := SaveTMProof.polyTimeComputable_save Alg hAlg
  obtain ⟨hf_div_poly, hf_div_spec⟩ := DivStackProof.polyTimeComputable_div_unit
  have hf_prep_poly := polyTimeComputable_prep
  have hcomp1 := CookPvsNP.polyTimeComputable_comp f_prep f_save
    hf_prep_poly hf_save_poly
  have hcomp2 := CookPvsNP.polyTimeComputable_comp (f_save ∘ f_prep)
    DivStackProof.f_div_unit hcomp1 hf_div_poly
  refine ⟨DivStackProof.f_div_unit ∘ f_save ∘ f_prep, hcomp2,
    fun AH _ _ hn2 hk2 hL => ?_⟩
  set w_prep := f_prep AH.encode
  set cells := f_save w_prep
  obtain ⟨horig, hout⟩ := hf_save_spec w_prep
  have hcountL : DivStackProof.countL cells = wielandtL AH.k := by
    rw [countL_eq_filter_filterMap, horig]
    exact filter_isSomeFalse_f_prep_encode AH hn2 hL
  have hcountM : DivStackProof.countM cells = (Alg (heapWielandtAB AH hL).encode).length := by
    unfold DivStackProof.countM
    rw [hout, map_unmaskFalse_f_prep_encode AH hn2 hk2 hL]
  have hdiv := hf_div_spec cells (by rw [hcountL]; omega)
  change (DivStackProof.f_div_unit cells).length = _
  rw [hdiv, hcountM, hcountL]

/-! ### Part 6: Reduction properties and top-level `theorem solution` -/

lemma run_nil {σ α : Type} (δ : σ → α → σ) (q : σ) : run δ q [] = q := rfl

lemma run_cons {σ α : Type} (δ : σ → α → σ) (q : σ) (a : α) (w : List α) :
    run δ q (a :: w) = run δ (δ q a) w := rfl

lemma finite_words_length_le (k B : ℕ) :
    {w : List (Fin k) | w.length ≤ B}.Finite := by
  let S : Finset (List (Fin k)) :=
    (Finset.range (B + 1)).biUnion (fun m =>
      (Finset.univ : Finset (Fin m → Fin k)).image List.ofFn)
  refine S.finite_toSet.subset (fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw
  simp only [S, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨w.length, by omega, fun i => w.get i, List.ofFn_get w⟩

lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2⁻¹)
  rw [Real.log_inv] at h1
  linarith

lemma wielandtL_bounds (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ wielandtL k ∧
      2 ^ (wielandtL k - 1) ≤ k - 1 ∧
      k ≤ 2 * 2 ^ (wielandtL k - 1) ∧
      (wielandtL k : ℝ) ≤ 2 * Real.log k + 2 := by
  unfold wielandtL
  set m := Nat.log 2 (k - 1)
  have hk1 : k - 1 ≠ 0 := by omega
  have hpow_le : 2 ^ m ≤ k - 1 := Nat.pow_log_le_self 2 hk1
  have hlt_pow : k - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) (k - 1)
  have hpow_succ : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, hpow_le, by omega, ?_⟩
  have hpow_le_k : 2 ^ m ≤ k := by omega
  have hpow_real : ((2 : ℝ) ^ m) ≤ (k : ℝ) := by exact_mod_cast hpow_le_k
  have hlog_le : Real.log ((2 : ℝ) ^ m) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by positivity) hpow_real
  rw [Real.log_pow] at hlog_le
  have hlog2 := half_le_log_two
  have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm_half : (m : ℝ) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hm_nonneg
  push_cast
  linarith

def dupProj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (b : Fin K) : Fin AH.k :=
  if h : b.val < AH.k then ⟨b.val, h⟩ else ⟨0, by omega⟩

def dupInj (AH : Automaton) (K : ℕ) (hK : AH.k ≤ K) (a : Fin AH.k) : Fin K :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt hK⟩

lemma dupTransition_eq_proj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    (q : Fin AH.n) (b : Fin K) :
    dupTransition AH K q b = AH.δ q (dupProj AH K hk b) := by
  unfold dupTransition dupProj
  have h0 : 0 < AH.k := by omega
  split_ifs with h
  · rfl
  · rfl

lemma dupProj_dupInj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (a : Fin AH.k) :
    dupProj AH K hk (dupInj AH K hK a) = a := by
  unfold dupProj dupInj
  simp [a.isLt]

lemma run_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    (q : Fin AH.n) (y : List (Fin K)) :
    run (dupTransition AH K) q y = run AH.δ q (y.map (dupProj AH K hk)) := by
  induction y generalizing q with
  | nil => rfl
  | cons b y ih =>
    simp only [List.map_cons, run_cons, dupTransition_eq_proj AH K hk]
    exact ih _

lemma map_dupProj_dupInj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (w : List (Fin AH.k)) :
    (w.map (dupInj AH K hK)).map (dupProj AH K hk) = w := by
  rw [List.map_map]
  have hcomp : dupProj AH K hk ∘ dupInj AH K hK = id := funext (dupProj_dupInj AH K hk hK)
  rw [hcomp, List.map_id]

lemma run_dupTransition_map_inj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (q : Fin AH.n) (w : List (Fin AH.k)) :
    run (dupTransition AH K) q (w.map (dupInj AH K hK)) = run AH.δ q w := by
  rw [run_dupTransition AH K hk, map_dupProj_dupInj AH K hk hK]

lemma isFirstReturn_map_dupProj (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k)
    {r : Fin AH.n} {y : List (Fin K)} (hy : IsFirstReturn (dupTransition AH K) r y) :
    IsFirstReturn AH.δ r (y.map (dupProj AH K hk)) := by
  rcases hy with ⟨hne, hret, hmin⟩
  refine ⟨by simpa using hne, ?_, ?_⟩
  · rw [← run_dupTransition AH K hk]
    exact hret
  · intro i hi0 hi_lt
    rw [List.length_map] at hi_lt
    rw [← List.map_take, ← run_dupTransition AH K hk]
    exact hmin i hi0 hi_lt

lemma isHuffmanDecoder_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (hHuff : IsHuffmanDecoder AH.δ) :
    IsHuffmanDecoder (dupTransition AH K) := by
  rcases hHuff with ⟨hSC, r, hfin⟩
  refine ⟨fun q q' => ?_, r, ?_⟩
  · obtain ⟨w, hw⟩ := hSC q q'
    exact ⟨w.map (dupInj AH K hK), by rw [run_dupTransition_map_inj AH K hk hK, hw]⟩
  · let B := hfin.toFinset.sup List.length
    refine (finite_words_length_le K B).subset (fun y hy => ?_)
    simp only [Set.mem_setOf_eq] at hy ⊢
    have hmap : y.map (dupProj AH K hk) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr (isFirstReturn_map_dupProj AH K hk hy)
    have hle := Finset.le_sup (f := List.length) hmap
    simpa using hle

lemma sync_dupTransition (AH : Automaton) (K : ℕ) (hk : 2 ≤ AH.k) (hK : AH.k ≤ K)
    (hSync : IsSynchronizing AH.δ) :
    IsSynchronizing (dupTransition AH K) ∧ syncLength (dupTransition AH K) = syncLength AH.δ := by
  have hset_eq :
      {ℓ | ∃ y : List (Fin K), y.length = ℓ ∧ IsSyncWord (dupTransition AH K) y} =
        {ℓ | ∃ w : List (Fin AH.k), w.length = ℓ ∧ IsSyncWord AH.δ w} := by
    ext ℓ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, rfl, q, hq⟩
      refine ⟨y.map (dupProj AH K hk), List.length_map .., q, fun q' => ?_⟩
      rw [← run_dupTransition AH K hk]
      exact hq q'
    · rintro ⟨w, rfl, q, hq⟩
      refine ⟨w.map (dupInj AH K hK), List.length_map .., q, fun q' => ?_⟩
      rw [run_dupTransition_map_inj AH K hk hK]
      exact hq q'
  refine ⟨?_, ?_⟩
  · rcases hSync with ⟨w, q, hq⟩
    exact ⟨w.map (dupInj AH K hK), q, fun q' => by
      rw [run_dupTransition_map_inj AH K hk hK]
      exact hq q'⟩
  · unfold syncLength
    rw [hset_eq]

lemma run_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (s : σ₂) (w : List α₂) :
    run (fun q a => es (δ₁ (es.symm q) (ea a))) s w =
      es (run δ₁ (es.symm s) (w.map ea)) := by
  induction w generalizing s with
  | nil => simp [run_nil]
  | cons a w ih =>
    simp only [List.map_cons, run_cons]
    rw [ih]
    simp

lemma isHuffmanDecoder_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (hHuff : IsHuffmanDecoder δ₁) :
    IsHuffmanDecoder (fun q a => es (δ₁ (es.symm q) (ea a))) := by
  rcases hHuff with ⟨hSC, r, hfin⟩
  refine ⟨fun s s' => ?_, es r, ?_⟩
  · obtain ⟨w₁, hw₁⟩ := hSC (es.symm s) (es.symm s')
    refine ⟨w₁.map ea.symm, ?_⟩
    rw [run_reindex, List.map_map]
    have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
    rw [hcomp, List.map_id, hw₁, es.apply_symm_apply]
  · refine (hfin.image (List.map ea.symm)).subset (fun w hw => ?_)
    simp only [Set.mem_setOf_eq] at hw
    rcases hw with ⟨hne, hret, hmin⟩
    refine ⟨w.map ea, ⟨by simpa using hne, ?_, ?_⟩, ?_⟩
    · rw [run_reindex, es.symm_apply_apply, es.injective.eq_iff] at hret
      exact hret
    · intro i hi0 hi_lt
      rw [List.length_map] at hi_lt
      have hmin_i := hmin i hi0 hi_lt
      rw [run_reindex, es.symm_apply_apply, Ne, es.injective.eq_iff, List.map_take] at hmin_i
      exact hmin_i
    · rw [List.map_map]
      have hcomp : (ea.symm ∘ ea : α₂ → α₂) = id := funext ea.symm_apply_apply
      rw [hcomp, List.map_id]

lemma isSynchronizing_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) (hSync : IsSynchronizing δ₁) :
    IsSynchronizing (fun q a => es (δ₁ (es.symm q) (ea a))) := by
  rcases hSync with ⟨w₁, q, hq⟩
  refine ⟨w₁.map ea.symm, es q, fun s => ?_⟩
  rw [run_reindex, List.map_map]
  have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
  rw [hcomp, List.map_id, hq]

lemma syncLength_reindex {σ₁ σ₂ α₁ α₂ : Type} (δ₁ : σ₁ → α₁ → σ₁)
    (es : σ₁ ≃ σ₂) (ea : α₂ ≃ α₁) :
    syncLength (fun q a => es (δ₁ (es.symm q) (ea a))) = syncLength δ₁ := by
  have hset_eq :
      {ℓ | ∃ w : List α₂, w.length = ℓ ∧ IsSyncWord (fun q a => es (δ₁ (es.symm q) (ea a))) w} =
        {ℓ | ∃ w₁ : List α₁, w₁.length = ℓ ∧ IsSyncWord δ₁ w₁} := by
    ext ℓ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, rfl, s₀, hs₀⟩
      refine ⟨w.map ea, List.length_map .., es.symm s₀, fun q₁ => ?_⟩
      have h := hs₀ (es q₁)
      rw [run_reindex, es.symm_apply_apply] at h
      exact (es.symm_apply_eq.mpr h.symm).symm
    · rintro ⟨w₁, rfl, q₀, hq₀⟩
      refine ⟨w₁.map ea.symm, List.length_map .., es q₀, fun s => ?_⟩
      rw [run_reindex, List.map_map]
      have hcomp : (ea ∘ ea.symm : α₁ → α₁) = id := funext ea.apply_symm_apply
      rw [hcomp, List.map_id, hq₀]
  unfold syncLength
  rw [hset_eq]

end WielandtSolution

theorem solution (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg_H : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg_H ∧
      ∀ AH : Automaton, IsHuffmanDecoder AH.δ → IsSynchronizing AH.δ → 2 ≤ AH.n → 2 ≤ AH.k →
        ∃ (L : ℕ) (δY : Fin AH.n → Fin (wielandtCode L).card → Fin AH.n)
          (e : Fin (wielandtCode L).card ≃ {z // z ∈ wielandtCode L}) (AB : Automaton),
          1 ≤ L ∧ (L : ℝ) ≤ 2 * Real.log AH.k + 2 ∧
          IsHuffmanDecoder δY ∧ IsSynchronizing δY ∧ syncLength δY = syncLength AH.δ ∧
          AB.k = 2 ∧ AH.n ≤ AB.n ∧ AB.n ≤ 6 * AH.n * AH.k ∧
          (IsHuffmanDecoder (composeDecoder δY (wielandtCode L) e) → IsHuffmanDecoder AB.δ) ∧
          (IsSynchronizing (composeDecoder δY (wielandtCode L) e) → IsSynchronizing AB.δ) ∧
          syncLength AB.δ = syncLength (composeDecoder δY (wielandtCode L) e) ∧
          (Alg_H AH.encode).length = (Alg AB.encode).length / L := by
  obtain ⟨Alg_H, hAlg_H, hAlg_H_spec⟩ := WielandtSolution.heap_wielandtAB_encode_polyTime Alg hAlg
  refine ⟨Alg_H, hAlg_H, fun AH hHuff hSync hn2 hk2 => ?_⟩
  have ⟨hL1, hpow_le, hk_le_pow, hL_real⟩ := WielandtSolution.wielandtL_bounds AH.k hk2
  set L := wielandtL AH.k
  obtain ⟨-, hCardZ, -⟩ := wielandt_code L hL1
  have hK : AH.k ≤ (wielandtCode L).card := by
    rw [hCardZ]
    omega
  let δY := dupTransition AH (wielandtCode L).card
  let e := WielandtSolution.heapWielandtCodeEquiv L hL1
  let AB := WielandtSolution.heapWielandtAB AH hL1
  have hHuffY : IsHuffmanDecoder δY := WielandtSolution.isHuffmanDecoder_dupTransition AH _ hk2 hK hHuff
  have ⟨hSyncY, hLenY⟩ := WielandtSolution.sync_dupTransition AH _ hk2 hK hSync
  have hpp_card := WielandtSolution.properPrefixes_wielandtCode_card' L hL1
  have hpp_ge1 : 1 ≤ (properPrefixes (wielandtCode L)).card := by
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  have hpp_le : (properPrefixes (wielandtCode L)).card ≤ 6 * AH.k := by
    omega
  refine ⟨L, δY, e, AB, hL1, hL_real, hHuffY, hSyncY, hLenY, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show AH.n ≤ AH.n * (properPrefixes (wielandtCode L)).card
    exact Nat.le_mul_of_pos_right AH.n hpp_ge1
  · show AH.n * (properPrefixes (wielandtCode L)).card ≤ 6 * AH.n * AH.k
    calc AH.n * (properPrefixes (wielandtCode L)).card
        ≤ AH.n * (6 * AH.k) := Nat.mul_le_mul_left AH.n hpp_le
      _ = 6 * AH.n * AH.k := by ring
  · exact WielandtSolution.isHuffmanDecoder_reindex (composeDecoder δY (wielandtCode L) e)
      (WielandtSolution.heapWielandtStateEquiv AH.n L hL1) fin2EquivBool
  · exact WielandtSolution.isSynchronizing_reindex (composeDecoder δY (wielandtCode L) e)
      (WielandtSolution.heapWielandtStateEquiv AH.n L hL1) fin2EquivBool
  · exact WielandtSolution.syncLength_reindex (composeDecoder δY (wielandtCode L) e)
      (WielandtSolution.heapWielandtStateEquiv AH.n L hL1) fin2EquivBool
  · exact hAlg_H_spec AH hHuff hSync hn2 hk2 hL1
