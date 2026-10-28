-- Prove2me | solution 1 for SyncPrefix.Huffman.scDisjointCopies_encode_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T20:35:41.535889+00:00
-- url     : https://prove2.me/submissions/a5cd1d73-7fbe-4935-9e47-525e257ff2a2

import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Definitions.Def_SyncPrefix_Huffman_DisjointCopies
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_bounded_loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open SyncPrefix.Huffman SetCoverThreshold.SetCover CookPvsNP

namespace SaveTMProof

structure SaveCell (Sym₁ Γ : Type) where
  orig : Option Sym₁
  one : Option Γ
  isOut : Bool
  deriving DecidableEq

noncomputable instance instFintypeSaveCell {Sym₁ Γ : Type} [Fintype Sym₁] [Fintype Γ] :
    Fintype (SaveCell Sym₁ Γ) :=
  Fintype.ofInjective
    (fun c : SaveCell Sym₁ Γ => (c.orig, c.one, c.isOut))
    (by
      intro a b h
      cases a; cases b
      simp_all)

def SaveCell.unpack {Sym₁ Γ : Type} : Option (SaveCell Sym₁ Γ) → SaveCell Sym₁ Γ
  | none => ⟨none, none, false⟩
  | some c => c

def saveInputEmbedding {Sym₁ Γ : Type} (ι₁ : Sym₁ ↪ Γ) : Sym₁ ↪ SaveCell Sym₁ Γ where
  toFun x := ⟨some x, some (ι₁ x), false⟩
  inj' _ _ h := Option.some.inj (congrArg SaveCell.orig h)

def saveOutputEmbedding (Sym₁ Γ : Type) : (Option Sym₁ × Bool) ↪ SaveCell Sym₁ Γ where
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

def saveMarkStep {Sym₁ Γ Q : Type} (c : SaveCell Sym₁ Γ) :
    SaveQ Q × Option (SaveCell Sym₁ Γ) × Move :=
  if c.one.isSome then
    (.markOut, some ⟨c.orig, none, true⟩, .right)
  else
    (.scanLeft, some ⟨c.orig, none, false⟩, .left)

def saveTM (Sym₁ : Type) {Γ : Type} (M : TM Γ) : TM (SaveCell Sym₁ Γ) where
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

structure SimCfg (Sym₁ Γ Q : Type) where
  state : Q
  left : List (Option Sym₁ × Option Γ)
  head : Option (Option Sym₁ × Option Γ)
  right : List (Option Sym₁ × Option Γ)

def SimCfg.cellOf {Sym₁ Γ : Type} (p : Option Sym₁ × Option Γ) : Option (SaveCell Sym₁ Γ) :=
  some ⟨p.1, p.2, false⟩

def SimCfg.encode {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) :
    Cfg (SaveCell Sym₁ Γ) (SaveQ Q) where
  state := .sim d.state
  left := d.left.map SimCfg.cellOf
  head := d.head.map (fun p => ⟨p.1, p.2, false⟩)
  right := d.right.map SimCfg.cellOf

def SimCfg.source {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) : Cfg Γ Q where
  state := d.state
  left := d.left.map Prod.snd
  head := match d.head with | none => none | some p => p.2
  right := d.right.map Prod.snd

def SimCfg.origList {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) : List Sym₁ :=
  d.left.reverse.filterMap Prod.fst ++
    (match d.head with | none => [] | some p => p.1.toList) ++
    d.right.filterMap Prod.fst

def SimCfg.init {Sym₁ Γ Q : Type} (ι₁ : Sym₁ ↪ Γ) (q₀ : Q) (w : List Sym₁) :
    SimCfg Sym₁ Γ Q where
  state := q₀
  left := []
  head := (w.map (fun x => (some x, some (ι₁ x)))).head?
  right := (w.map (fun x => (some x, some (ι₁ x)))).tail

lemma filterMap_fst_cons {α β : Type} (p : Option α × β) (xs : List (Option α × β)) :
    List.filterMap Prod.fst (p :: xs) = p.1.toList ++ xs.filterMap Prod.fst := by
  rcases p with ⟨o, b⟩
  cases o <;> rfl

lemma filterMap_fst_map_some {Sym₁ Γ : Type} (ι₁ : Sym₁ ↪ Γ) (w : List Sym₁) :
    (w.map (fun x => (some x, some (ι₁ x)))).filterMap Prod.fst = w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma simCfg_init_encode {Sym₁ Γ : Type} (ι₁ : Sym₁ ↪ Γ) (M : TM Γ) (w : List Sym₁) :
    (SimCfg.init ι₁ M.q₀ w).encode = (saveTM Sym₁ M).init (w.map (saveInputEmbedding ι₁)) := by
  cases w with
  | nil => rfl
  | cons x xs =>
    simp only [SimCfg.init, SimCfg.encode, SimCfg.cellOf, TM.init, saveTM,
      List.map_cons, List.head?_cons, List.tail_cons, List.map_nil, List.map_map]
    rfl

lemma simCfg_init_source {Sym₁ Γ : Type} (ι₁ : Sym₁ ↪ Γ) (M : TM Γ) (w : List Sym₁) :
    (SimCfg.init ι₁ M.q₀ w).source = M.init (w.map ι₁) := by
  cases w <;> simp [SimCfg.init, SimCfg.source, TM.init, Function.comp_def]

lemma simCfg_init_origList {Sym₁ Γ : Type} (ι₁ : Sym₁ ↪ Γ) (M : TM Γ) (w : List Sym₁) :
    (SimCfg.init ι₁ M.q₀ w).origList = w := by
  cases w with
  | nil => rfl
  | cons x xs =>
    simp [SimCfg.init, SimCfg.origList, filterMap_fst_map_some]

def SimCfg.step {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) : SimCfg Sym₁ Γ M.Q :=
  if M.IsHalting d.source then d else
    let orig_h : Option Sym₁ := match d.head with | none => none | some p => p.1
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

lemma simCfg_step_source {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) :
    (d.step M).source = M.step d.source := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.step, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;> cases head <;>
      simp [SimCfg.step, SimCfg.source, TM.step, TM.IsHalting, hq, hd]

lemma simCfg_step_encode {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q)
    (hn : ¬ M.IsHalting d.source) :
    (saveTM Sym₁ M).step d.encode = (d.step M).encode := by
  rcases d with ⟨q, left, head, right⟩
  have hq : ¬ (q = M.qaccept ∨ q = M.qreject) := hn
  rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
  have hnot_halt : ¬ (saveTM Sym₁ M).IsHalting
      (SimCfg.encode ⟨q, left, head, right⟩) := by
    intro hh
    rcases hh with hh | hh <;> cases hh
  cases move <;> cases left <;> cases right <;> cases head <;>
    simp [SimCfg.step, SimCfg.encode, SimCfg.source, SimCfg.cellOf, TM.step, TM.IsHalting,
      saveTM, SaveCell.unpack, hq, hd, hnot_halt]

lemma simCfg_step_origList {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) :
    (d.step M).origList = d.origList := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;> cases head <;>
      simp [SimCfg.step, SimCfg.source, SimCfg.origList, TM.IsHalting, hq, hd,
        filterMap_fst_cons, List.append_assoc]

lemma simCfg_step_len {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) :
    (d.step M).left.length + (d.step M).right.length ≤ d.left.length + d.right.length + 1 := by
  rcases d with ⟨q, left, head, right⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq]
  · rcases hd : M.δ q (match head with | none => none | some p => p.2) with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;>
      simp [SimCfg.step, SimCfg.source, TM.IsHalting, hq, hd] <;> omega

lemma simCfg_run_origList {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) (m : ℕ) :
    ((SimCfg.step M)^[m] d).origList = d.origList := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', simCfg_step_origList, ih]

lemma simCfg_run_len {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) (m : ℕ) :
    ((SimCfg.step M)^[m] d).left.length + ((SimCfg.step M)^[m] d).right.length ≤
      d.left.length + d.right.length + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h := simCfg_step_len M ((SimCfg.step M)^[m] d)
    omega

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

lemma simCfg_run_encode {Sym₁ Γ : Type} (M : TM Γ) (d : SimCfg Sym₁ Γ M.Q) (m : ℕ)
    (hm : ∀ i < m, ¬ M.IsHalting ((SimCfg.step M)^[i] d).source) :
    (saveTM Sym₁ M).run m d.encode = ((SimCfg.step M)^[m] d).encode := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 := ih (fun i hi => hm i (Nat.lt_succ_of_lt hi))
    have h2 : (saveTM Sym₁ M).run 1 ((SimCfg.step M)^[m] d).encode =
        (SimCfg.step M ((SimCfg.step M)^[m] d)).encode :=
      simCfg_step_encode M _ (hm m (Nat.lt_succ_self m))
    have hj := tm_join (saveTM Sym₁ M) h1 h2
    simpa [Function.iterate_succ_apply'] using hj

lemma simCfg_first_halt {Sym₁ Γ : Type} (M : TM Γ) (d₀ : SimCfg Sym₁ Γ M.Q) (n : ℕ)
    (hn : M.IsHalting (M.run n d₀.source)) :
    ∃ m ≤ n,
      (saveTM Sym₁ M).run m d₀.encode = ((SimCfg.step M)^[m] d₀).encode ∧
      ((SimCfg.step M)^[m] d₀).source = M.run n d₀.source ∧
      M.IsHalting ((SimCfg.step M)^[m] d₀).source := by
  classical
  have hs : Function.Semiconj (SimCfg.source (Sym₁ := Sym₁)) (SimCfg.step M) M.step :=
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

def eOrig {Sym₁ Γ : Type} : Option (Option Sym₁ × Option Γ) → Option Sym₁
  | none => none
  | some p => p.1

def eOne {Sym₁ Γ : Type} : Option (Option Sym₁ × Option Γ) → Option Γ
  | none => none
  | some p => p.2

def eCell {Sym₁ Γ : Type} : Option (Option Sym₁ × Option Γ) → Option (SaveCell Sym₁ Γ)
  | none => none
  | some p => some ⟨p.1, p.2, false⟩

def scanLeftCfg {Sym₁ Γ Q : Type}
    (left : List (Option Sym₁ × Option Γ × Bool))
    (right : List (Option Sym₁ × Bool)) : Cfg (SaveCell Sym₁ Γ) (SaveQ Q) where
  state := .scanLeft
  left := left.tail.map (fun x => some ⟨x.1, x.2.1, x.2.2⟩)
  head := left.head?.map (fun x => ⟨x.1, x.2.1, x.2.2⟩)
  right := right.map (some ∘ saveOutputEmbedding Sym₁ Γ)

def haltSaveCfg {Sym₁ Γ Q : Type} (outCells : List (Option Sym₁ × Bool)) :
    Cfg (SaveCell Sym₁ Γ) (SaveQ Q) where
  state := .haltAccept
  left := [none]
  head := (outCells.map (some ∘ saveOutputEmbedding Sym₁ Γ)).headD none
  right := (outCells.map (some ∘ saveOutputEmbedding Sym₁ Γ)).tail

lemma step_scanLeft_cons {Sym₁ Γ : Type} (M : TM Γ)
    (x : Option Sym₁ × Option Γ × Bool)
    (xs : List (Option Sym₁ × Option Γ × Bool))
    (right : List (Option Sym₁ × Bool)) :
    (saveTM Sym₁ M).step (scanLeftCfg (x :: xs) right) =
      scanLeftCfg xs ((x.1, x.2.2) :: right) := by
  cases xs <;> rfl

lemma run_scanLeft {Sym₁ Γ : Type} (M : TM Γ)
    (left : List (Option Sym₁ × Option Γ × Bool))
    (right : List (Option Sym₁ × Bool)) :
    (saveTM Sym₁ M).run left.length (scanLeftCfg left right) =
      scanLeftCfg [] (left.reverse.map (fun x => (x.1, x.2.2)) ++ right) := by
  induction left generalizing right with
  | nil => rfl
  | cons x xs ih =>
    have h1 : (saveTM Sym₁ M).run 1 (scanLeftCfg (x :: xs) right) =
        scanLeftCfg xs ((x.1, x.2.2) :: right) := step_scanLeft_cons M x xs right
    have h2 := ih ((x.1, x.2.2) :: right)
    have hj := tm_join (saveTM Sym₁ M) h1 h2
    rw [Nat.add_comm 1 xs.length] at hj
    simpa [List.append_assoc] using hj

lemma step_scanLeft_nil {Sym₁ Γ : Type} (M : TM Γ) (outCells : List (Option Sym₁ × Bool)) :
    (saveTM Sym₁ M).run 1 (scanLeftCfg [] outCells) = haltSaveCfg outCells := rfl

lemma output_haltSaveCfg {Sym₁ Γ : Type} (M : TM Γ) (outCells : List (Option Sym₁ × Bool)) :
    (saveTM Sym₁ M).output (haltSaveCfg outCells) =
      outCells.map (some ∘ saveOutputEmbedding Sym₁ Γ) := by
  cases outCells with
  | nil => rfl
  | cons x xs =>
    have hdrop : ∀ l : List (Option Sym₁ × Bool),
        (l.map (some ∘ saveOutputEmbedding Sym₁ Γ)).dropWhile Option.isNone =
          l.map (some ∘ saveOutputEmbedding Sym₁ Γ) := by
      intro l; cases l <;> rfl
    simp only [TM.output, haltSaveCfg, List.map_cons, List.headD_cons, List.tail_cons]
    rw [← List.map_cons, ← List.map_reverse, hdrop, ← List.map_reverse, List.reverse_reverse]

def markRCfg {Sym₁ Γ Q : Type} (q : SaveQ Q)
    (left : List (Option Sym₁ × Option Γ × Bool))
    (R : List (Option (Option Sym₁ × Option Γ))) : Cfg (SaveCell Sym₁ Γ) (SaveQ Q) where
  state := q
  left := left.map (fun x => some ⟨x.1, x.2.1, x.2.2⟩)
  head := (R.map eCell).headD none
  right := (R.map eCell).tail

def tailOutR {Sym₁ Γ : Type} : List (Option (Option Sym₁ × Option Γ)) → List (Option Sym₁ × Bool)
  | [] => [(none, false)]
  | e :: R' => (eOrig e, false) :: R'.map (fun x => (eOrig x, false))

def isMarkState {Γ : Type} (M : TM Γ) : SaveQ M.Q → Prop
  | .sim q₀ => q₀ = M.qaccept ∨ q₀ = M.qreject
  | .markOut => True
  | _ => False

lemma map_eCell_of_isSome_eOne_none {Sym₁ Γ : Type} :
    ∀ R' : List (Option (Option Sym₁ × Option Γ)),
      (∀ e ∈ R', e.isSome = true) →
      (∀ e ∈ R', eOne e = none) →
      R'.map eCell = (R'.map (fun x => (eOrig x, false))).map (some ∘ saveOutputEmbedding Sym₁ Γ)
  | [], _, _ => rfl
  | e :: R', hsome, hnone => by
    have he_some := hsome e (by simp)
    have he_none := hnone e (by simp)
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

lemma step_markRCfg_zero {Sym₁ Γ : Type} (M : TM Γ) (q : SaveQ M.Q) (hq : isMarkState M q)
    (left : List (Option Sym₁ × Option Γ × Bool))
    (R : List (Option (Option Sym₁ × Option Γ)))
    (hsome : ∀ e ∈ R.tail, e.isSome = true)
    (hnone : ∀ e ∈ R, eOne e = none) :
    (saveTM Sym₁ M).run 1 (markRCfg q left R) = scanLeftCfg left (tailOutR R) := by
  change (saveTM Sym₁ M).step (markRCfg q left R) = _
  have hnot_halt : ¬ (saveTM Sym₁ M).IsHalting (markRCfg q left R) := by
    intro hh
    rcases hh with hh | hh <;> simp [markRCfg] at hh <;> subst hh <;> exact hq
  cases R with
  | nil =>
    cases q <;> try contradiction
    · dsimp [isMarkState] at hq
      cases left <;> simp [TM.step, TM.IsHalting, saveTM, hnot_halt, hq, saveMarkStep, markRCfg,
        SaveCell.unpack, scanLeftCfg, tailOutR] <;> rfl
    · cases left <;> simp [TM.step, TM.IsHalting, saveTM, hnot_halt, saveMarkStep, markRCfg,
        SaveCell.unpack, scanLeftCfg, tailOutR] <;> rfl
  | cons e₀ R' =>
    have he0 : eOne e₀ = none := hnone e₀ (by simp)
    have hR' : R'.map eCell =
        (R'.map (fun x => (eOrig x, false))).map (some ∘ saveOutputEmbedding Sym₁ Γ) :=
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
      cases left <;> simp [TM.step, TM.IsHalting, saveTM, hnot_halt, hq, saveMarkStep, markRCfg,
        hunpack, hR', scanLeftCfg, tailOutR] <;> rfl
    · cases left <;> simp [TM.step, TM.IsHalting, saveTM, hnot_halt, saveMarkStep, markRCfg,
        hunpack, hR', scanLeftCfg, tailOutR] <;> rfl

lemma step_markRCfg_succ {Sym₁ Γ : Type} (M : TM Γ) (q : SaveQ M.Q) (hq : isMarkState M q)
    (left : List (Option Sym₁ × Option Γ × Bool))
    (e₀ : Option (Option Sym₁ × Option Γ)) (γ₀ : Γ) (he0 : eOne e₀ = some γ₀)
    (R' : List (Option (Option Sym₁ × Option Γ))) :
    (saveTM Sym₁ M).run 1 (markRCfg q left (e₀ :: R')) =
      markRCfg .markOut ((eOrig e₀, none, true) :: left) R' := by
  change (saveTM Sym₁ M).step (markRCfg q left (e₀ :: R')) = _
  have hnot_halt : ¬ (saveTM Sym₁ M).IsHalting (markRCfg q left (e₀ :: R')) := by
    intro hh
    rcases hh with hh | hh <;> simp [markRCfg] at hh <;> subst hh <;> exact hq
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
    simp [TM.step, TM.IsHalting, saveTM, hnot_halt, hq, saveMarkStep, markRCfg, hunpack]
  · simp [TM.step, TM.IsHalting, saveTM, hnot_halt, saveMarkStep, markRCfg, hunpack]

lemma run_markRCfg {Sym₁ Γ : Type} (M : TM Γ) (γ₀ : Γ) (padding : ℕ) :
    ∀ (L : ℕ) (q : SaveQ M.Q), isMarkState M q →
      ∀ (left : List (Option Sym₁ × Option Γ × Bool))
        (R : List (Option (Option Sym₁ × Option Γ))),
        (∀ e ∈ R.tail, e.isSome = true) →
        R.map eOne = List.replicate L (some γ₀) ++ List.replicate padding none →
        (saveTM Sym₁ M).run (L + 1) (markRCfg q left R) =
          scanLeftCfg ((R.take L).reverse.map (fun e => (eOrig e, none, true)) ++ left)
            (tailOutR (R.drop L))
  | 0, q, hq, left, R, hsome, hmap => by
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, List.take_zero,
      List.reverse_nil, List.map_nil, List.drop_zero] at hmap ⊢
    apply step_markRCfg_zero M q hq left R hsome
    intro e he
    have hmem : eOne e ∈ R.map eOne := List.mem_map_of_mem he
    rw [hmap] at hmem
    exact List.eq_of_mem_replicate hmem
  | L + 1, q, hq, left, R, hsome, hmap => by
    cases R with
    | nil => simp [List.replicate_succ] at hmap
    | cons e₀ R' =>
      simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at hmap
      rcases hmap with ⟨he0, hmap'⟩
      have hsome' : ∀ e ∈ R'.tail, e.isSome = true := by
        intro e he
        exact hsome e (List.tail_subset R' he)
      have h1 := step_markRCfg_succ M q hq left e₀ γ₀ he0 R'
      have h2 := run_markRCfg M γ₀ padding L .markOut trivial ((eOrig e₀, none, true) :: left)
        R' hsome' hmap'
      have hj := tm_join (saveTM Sym₁ M) h1 h2
      rw [Nat.add_comm 1 (L + 1)] at hj
      simpa [List.take_succ_cons, List.drop_succ_cons, List.append_assoc] using hj

/-! ### Output structure and `polyTimeComputable_save` -/

lemma leading_blanks {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = List.replicate n none ++ xs.dropWhile Option.isNone := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    cases x with
    | none =>
      obtain ⟨n, h⟩ := ih
      exact ⟨n + 1, by simpa [List.replicate_succ] using congrArg (List.cons none) h⟩
    | some a => exact ⟨0, by simp⟩

lemma trailing_blanks {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = (xs.reverse.dropWhile Option.isNone).reverse ++ List.replicate n none := by
  obtain ⟨n, h⟩ := leading_blanks xs.reverse
  exact ⟨n, by simpa using congrArg List.reverse h⟩

def simCfgR {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) : List (Option (Option Sym₁ × Option Γ)) :=
  d.head :: d.right.map some

def saveOutList {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) (L : ℕ) : List (Option Sym₁ × Bool) :=
  d.left.reverse.map (fun p => (p.1, false)) ++
    ((simCfgR d).take L).map (fun e => (eOrig e, true)) ++
    tailOutR ((simCfgR d).drop L)

lemma filter_snd_tailOutR {Sym₁ Γ : Type} (S : List (Option (Option Sym₁ × Option Γ))) :
    (tailOutR S).filter Prod.snd = [] := by
  cases S with
  | nil => rfl
  | cons e S' =>
    induction S' with
    | nil => rfl
    | cons x xs ih => exact ih

lemma filter_snd_saveOutList {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) (L : ℕ)
    (hL : L ≤ (simCfgR d).length) :
    ((saveOutList d L).filter Prod.snd).length = L := by
  unfold saveOutList
  rw [List.filter_append, List.filter_append, filter_snd_tailOutR, List.append_nil]
  have h1 : (d.left.reverse.map (fun p : Option Sym₁ × Option Γ => (p.1, false))).filter Prod.snd = [] := by
    induction d.left.reverse <;> simp [*]
  have h2 : (((simCfgR d).take L).map (fun e => (eOrig e, true))).filter Prod.snd =
      ((simCfgR d).take L).map (fun e => (eOrig e, true)) := by
    induction ((simCfgR d).take L) <;> simp [*]
  rw [h1, List.nil_append, h2, List.length_map, List.length_take, Nat.min_eq_left hL]

lemma filterMap_fst_tailOutR {Sym₁ Γ : Type} (S : List (Option (Option Sym₁ × Option Γ))) :
    (tailOutR S).filterMap Prod.fst = S.filterMap eOrig := by
  cases S with
  | nil => rfl
  | cons e S' =>
    simp only [tailOutR, List.filterMap_cons, List.filterMap_map]
    rfl

lemma filterMap_fst_saveOutList {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) (L : ℕ) :
    (saveOutList d L).filterMap Prod.fst = d.origList := by
  unfold saveOutList
  rw [List.filterMap_append, List.filterMap_append, filterMap_fst_tailOutR]
  have h1 : (d.left.reverse.map (fun p : Option Sym₁ × Option Γ => (p.1, false))).filterMap Prod.fst =
      d.left.reverse.filterMap Prod.fst := by
    rw [List.filterMap_map]; rfl
  have h2 : (((simCfgR d).take L).map (fun e => (eOrig e, true))).filterMap Prod.fst =
      ((simCfgR d).take L).filterMap eOrig := by
    rw [List.filterMap_map]; rfl
  rw [h1, h2, List.append_assoc, ← List.filterMap_append, List.take_append_drop]
  unfold simCfgR SimCfg.origList
  rw [List.filterMap_cons, List.filterMap_map]
  have h3 : (eOrig ∘ some : Option Sym₁ × Option Γ → Option Sym₁) = Prod.fst := rfl
  rw [h3]
  cases d.head with
  | none => simp [eOrig]
  | some p => rcases p with ⟨o, g⟩; cases o <;> simp [eOrig]

lemma simCfg_encode_eq_markRCfg {Sym₁ Γ Q : Type} (d : SimCfg Sym₁ Γ Q) :
    d.encode = markRCfg (.sim d.state) (d.left.map (fun p => (p.1, p.2, false))) (simCfgR d) := by
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

lemma polyTimeComputable_save {Sym₁ : Type} [Fintype Sym₁]
    (F : List Sym₁ → List Unit) (hF : PolyTimeComputable F) :
    ∃ f_save : List Sym₁ → List (Option Sym₁ × Bool),
      PolyTimeComputable f_save ∧
      ∀ w : List Sym₁,
        (f_save w).filterMap Prod.fst = w ∧
        ((f_save w).filter Prod.snd).length = (F w).length := by
  rcases hF with ⟨Γ, hfinΓ, ι₁, ι₂, M, k, hM⟩
  let _ : Fintype Γ := hfinΓ
  have hrun_save : ∀ w : List Sym₁,
      ∃ (outCells : List (Option Sym₁ × Bool)) (t : ℕ),
        t ≤ 4 * (w.length + (w.length ^ k + k)) + 5 ∧
        (saveTM Sym₁ M).HaltsWithin t (w.map (saveInputEmbedding ι₁)) ∧
        (saveTM Sym₁ M).output ((saveTM Sym₁ M).run t
          ((saveTM Sym₁ M).init (w.map (saveInputEmbedding ι₁)))) =
          outCells.map (some ∘ saveOutputEmbedding Sym₁ Γ) ∧
        outCells.filterMap Prod.fst = w ∧
        (outCells.filter Prod.snd).length = (F w).length := by
    intro w
    set n := w.length ^ k + k
    obtain ⟨hHalt_n, hOut_n⟩ := hM w
    set d₀ := SimCfg.init ι₁ M.q₀ w
    have hd₀_src : d₀.source = M.init (w.map ι₁) := simCfg_init_source ι₁ M w
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
    set L := (F w).length
    obtain ⟨padding, hpad⟩ := trailing_blanks (d.source.head :: d.source.right)
    change d.source.head :: d.source.right = M.output d.source ++ List.replicate padding none at hpad
    have hout_d : M.output d.source = List.replicate L (some (ι₂ ())) := by
      rw [hm_src, hd₀_src, hOut_n, map_some_unit ι₂ (F w)]
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
    have hmark := run_markRCfg M (ι₂ ()) padding L (.sim d.state) hm_halt
      (d.left.map (fun p => (p.1, p.2, false))) (simCfgR d) hR_some hR_map
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
    have hrun_init : (saveTM Sym₁ M).run m ((saveTM Sym₁ M).init (w.map (saveInputEmbedding ι₁))) =
        d.encode := by
      rw [← simCfg_init_encode ι₁ M w]
      exact hm_run
    have hrun_total := tm_join (saveTM Sym₁ M)
      (tm_join (saveTM Sym₁ M) (tm_join (saveTM Sym₁ M) hrun_init hmark) hscan) hfin
    set t := ((m + (L + 1)) + left₁.length) + 1
    have hleft₁_len : left₁.length ≤ L + d.left.length := by
      simp only [left₁, List.length_append, List.length_map, List.length_reverse, List.length_take]
      omega
    have hL_le : L ≤ w.length + m + 1 := by
      have : (simCfgR d).length = d.right.length + 1 := by simp [simCfgR]
      omega
    refine ⟨saveOutList d L, t, by omega, ?_, ?_, ?_, ?_⟩
    · change (saveTM Sym₁ M).IsHalting ((saveTM Sym₁ M).run t _)
      rw [hrun_total]
      exact Or.inl rfl
    · rw [hrun_total]
      exact output_haltSaveCfg M (saveOutList d L)
    · rw [filterMap_fst_saveOutList, hd_orig]
    · exact filter_snd_saveOutList d L hR_len
  classical
  let f_save : List Sym₁ → List (Option Sym₁ × Bool) :=
    fun w => Classical.choose (hrun_save w)
  have hpow : ∀ w : List Sym₁,
      4 * (w.length + (w.length ^ k + k)) + 5 ≤ (4 * k + 13) * (w.length + 1) ^ (k + 1) := by
    intro w
    set P := (w.length + 1) ^ (k + 1)
    have h1 : w.length ≤ P := by
      calc w.length ≤ w.length + 1 := Nat.le_succ _
        _ = (w.length + 1) ^ 1 := (Nat.pow_one _).symm
        _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : w.length ^ k ≤ P := by
      calc w.length ^ k ≤ (w.length + 1) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    have h4 : k ≤ k * P := Nat.le_mul_of_pos_right k h3
    have h5 : (4 * k + 13) * P = 4 * (k * P) + 13 * P := by ring
    omega
  obtain ⟨k', hk'⟩ := polynomial_absorb (4 * k + 13) (k + 1) 0
  refine ⟨f_save, ?_, fun w => ?_⟩
  · refine ⟨SaveCell Sym₁ Γ, inferInstance, saveInputEmbedding ι₁, saveOutputEmbedding Sym₁ Γ,
      saveTM Sym₁ M, k', fun w => ?_⟩
    obtain ⟨t, ht_le, hhalt, hout, -, -⟩ := Classical.choose_spec (hrun_save w)
    have htk' : t ≤ w.length ^ k' + k' := by
      have h1 := hpow w
      have h2 := hk' w.length
      omega
    have hrun_eq : (saveTM Sym₁ M).run (w.length ^ k' + k')
        ((saveTM Sym₁ M).init (w.map (saveInputEmbedding ι₁))) =
        (saveTM Sym₁ M).run t ((saveTM Sym₁ M).init (w.map (saveInputEmbedding ι₁))) := by
      conv_lhs => rw [← Nat.sub_add_cancel htk']
      change ((saveTM Sym₁ M).step)^[(w.length ^ k' + k' - t) + t] _ = _
      rw [Function.iterate_add_apply]
      exact tm_run_eq_of_halting' (saveTM Sym₁ M) _ hhalt _
    refine ⟨?_, ?_⟩
    · change (saveTM Sym₁ M).IsHalting ((saveTM Sym₁ M).run (w.length ^ k' + k') _)
      rw [hrun_eq]
      exact hhalt
    · rw [hrun_eq]
      exact hout
  · obtain ⟨_, _, _, _, h1, h2⟩ := Classical.choose_spec (hrun_save w)
    exact ⟨h1, h2⟩

end SaveTMProof

/-! ## Part 3: Stack Program for Unary Division by `leadOnes` -/

namespace DivStackProg

abbrev Sym := Option Bool
abbrev DSym := Option Sym × Bool

inductive DKey where
  | ki
  | ko
  | U
  | Wrev
  | W
  | P
  | Psc
  | sc
  deriving DecidableEq

instance : Fintype DKey where
  elems := {.ki, .ko, .U, .Wrev, .W, .P, .Psc, .sc}
  complete x := by cases x <;> decide

abbrev DProg := StackProg DKey DSym
abbrev DStore := DKey → List DSym

def tok : DSym := (none, true)
def wrapSym (x : Sym) : DSym := (some x, false)

lemma exec_congr {p : DProg} {s t t' : DStore} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

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

lemma exec_branch_true_le (test : (DKey → Option DSym) → Bool) (p q : DProg)
    {s t : DStore} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true)
    (hp : ∃ c ≤ B, p.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hp with ⟨c, hc, ep⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchTrue ht ep⟩

lemma exec_branch_false_le (test : (DKey → Option DSym) → Bool) (p q : DProg)
    {s t : DStore} {B : ℕ}
    (hf : test (fun k => (s k).head?) = false)
    (hq : ∃ c ≤ B, q.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hq with ⟨c, hc, eq⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchFalse hf eq⟩

lemma exec_bounded_loop (test : (DKey → Option DSym) → Bool) (p : DProg)
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

lemma tail_drop_eq_drop_succ {α : Type} (w : List α) (i : ℕ) :
    (w.drop i).tail = w.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, add_comm]

/-! ### Stage 1: Scan input `u` into `.U` and `.W` -/

def scanUAct (h : DKey → Option DSym) (k : DKey) : StackAct DSym :=
  if k = .ki then .pop
  else if k = .U then
    match h .ki with
    | some (_, true) => .push tok
    | _ => .keep
  else if k = .Wrev then
    match h .ki with
    | some (some x, _) => .push (wrapSym x)
    | _ => .keep
  else .keep

def scanULoop : DProg :=
  .loop (fun h => (h .ki).isSome) (.act scanUAct)

def scanUProg : DProg :=
  .seq scanULoop (transferProg .Wrev (fun k => decide (k = .W)))

def sScanU (u : List DSym) (i : ℕ) : DStore := fun k =>
  if k = .ki then u.drop i
  else if k = .U then List.replicate ((u.take i).filter Prod.snd).length tok
  else if k = .Wrev then ((u.take i).filterMap Prod.fst).reverse.map wrapSym
  else []

def sAfterScanU (u : List DSym) : DStore := fun k =>
  if k = .U then List.replicate (u.filter Prod.snd).length tok
  else if k = .W then (u.filterMap Prod.fst).map wrapSym
  else []

lemma take_succ_filter_snd (u : List DSym) (i : ℕ) (hi : i < u.length) :
    ((u.take (i + 1)).filter Prod.snd).length =
      ((u.take i).filter Prod.snd).length + (if u[i].2 then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append]
  rcases h : u[i] with ⟨o, b⟩
  cases b <;> simp

lemma take_succ_filterMap_fst (u : List DSym) (i : ℕ) (hi : i < u.length) :
    ((u.take (i + 1)).filterMap Prod.fst).reverse.map wrapSym =
      match u[i].1 with
      | some x => wrapSym x :: ((u.take i).filterMap Prod.fst).reverse.map wrapSym
      | none => ((u.take i).filterMap Prod.fst).reverse.map wrapSym := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filterMap_append]
  rcases h : u[i] with ⟨o, b⟩
  cases o <;> simp

lemma exec_scanUProg (u : List DSym) :
    ∃ c ≤ 6 * u.length + 3,
      scanUProg.Exec (fun k => if k = .ki then u else []) (sAfterScanU u) c := by
  have hloop : ∃ c1 ≤ u.length * 3 + 1,
      scanULoop.Exec (sScanU u 0) (sScanU u u.length) c1 := by
    refine exec_bounded_loop (fun h => (h .ki).isSome) (.act scanUAct) u.length (sScanU u) 1
      (fun i hi => by
        dsimp [sScanU]
        rw [List.drop_eq_getElem_cons hi]
        rfl)
      (by simp [sScanU])
      (fun i hi => by
        refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act scanUAct (sScanU u i)) ?_⟩
        have h1 := take_succ_filter_snd u i hi
        have h2 := take_succ_filterMap_fst u i hi
        funext k
        cases k <;> simp [StackProg.applyAct, scanUAct, sScanU, StackAct.apply,
          List.getElem?_eq_getElem hi, tail_drop_eq_drop_succ, h1, h2]
        · rcases hui : u[i] with ⟨o, b⟩
          cases b <;> simp [List.replicate_succ]
        · rcases hui : u[i] with ⟨o, b⟩
          cases o <;> simp)
  have h0 : (fun k => if k = .ki then u else []) = sScanU u 0 := by
    funext k; cases k <;> rfl
  rw [h0]
  have htr_exec := stack_transfer DKey.Wrev (fun k => decide (k = .W)) (sScanU u u.length)
  have hlen_wrev : (sScanU u u.length .Wrev).length ≤ u.length := by
    dsimp [sScanU]
    rw [List.take_length, List.length_map, List.length_reverse]
    exact List.length_filterMap_le Prod.fst u
  have htr : ∃ c2 ≤ 3 * u.length + 1,
      (transferProg .Wrev (fun k => decide (k = .W))).Exec (sScanU u u.length) (sAfterScanU u) c2 := by
    refine ⟨3 * (sScanU u u.length .Wrev).length + 1, by omega, exec_congr htr_exec ?_⟩
    funext k
    cases k <;> simp [transferStore, sScanU, sAfterScanU, ← List.map_reverse]
  exact exec_le_of_le (exec_seq_le hloop htr) (by omega)

/-! ### Stage 2: Read `leadOnes` from `.W` into `.P` -/

def divReadPAct (_h : DKey → Option DSym) (k : DKey) : StackAct DSym :=
  if k = .W then .pop
  else if k = .P then .push tok
  else .keep

def divReadPLoop : DProg :=
  .loop (fun h => decide (h .W = some (wrapSym (some true)))) (.act divReadPAct)

def sDivReadP (w : List Sym) (L i : ℕ) : DStore := fun k =>
  if k = .U then List.replicate L tok
  else if k = .W then (w.drop i).map wrapSym
  else if k = .P then List.replicate i tok
  else []

lemma exec_divReadPLoop (w : List Sym) (L : ℕ) :
    ∃ c ≤ 3 * w.length + 1,
      divReadPLoop.Exec (sDivReadP w L 0) (sDivReadP w L (leadOnes w)) c := by
  have hloop : ∃ c ≤ leadOnes w * 3 + 1,
      divReadPLoop.Exec (sDivReadP w L 0) (sDivReadP w L (leadOnes w)) c := by
    refine exec_bounded_loop (fun h => decide (h .W = some (wrapSym (some true))))
      (.act divReadPAct) (leadOnes w) (sDivReadP w L) 1 ?_ ?_ ?_
    · intro i hi
      rw [decide_eq_true_eq]
      dsimp [sDivReadP]
      rw [List.head?_map, head?_drop_of_lt_leadOnes w i hi]
      rfl
    · rw [decide_eq_false_iff_not]
      dsimp [sDivReadP]
      rw [List.head?_map]
      intro h
      apply head?_drop_leadOnes w
      cases h' : (w.drop (leadOnes w)).head? with
      | none => simp [h'] at h
      | some x =>
        simp [h', wrapSym] at h
        simp [h]
    · intro i _
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act divReadPAct (sDivReadP w L i)) ?_⟩
      funext k
      cases k <;> simp [StackProg.applyAct, divReadPAct, sDivReadP, StackAct.apply,
        ← List.map_tail, tail_drop_eq_drop_succ, List.replicate_succ]
  have hle := leadOnes_le w
  exact exec_le_of_le hloop (by omega)

/-! ### Stage 3: Divide `.U` (`L`) by `.P` (`p`) into `.ko` -/

def divBodyProg : DProg :=
  .seq (copyProg .P .Psc .sc)
    (.seq (popProg .Psc)
      (.seq (consumeProg .Psc (fun k => decide (k = .U)))
        (.branch (fun h => (h .U).isSome)
          (.seq (popProg .U) (pushProg .ko tok))
          (popProg .sc))))

def divLoop : DProg :=
  .loop (fun h => (h .U).isSome) divBodyProg

def divStage3Prog : DProg :=
  .branch (fun h => (h .P).isSome) divLoop (popProg .sc)

def divN (L p : ℕ) : ℕ := L / p + if L % p = 0 then 0 else 1

def sDiv (w : List Sym) (L p i : ℕ) : DStore := fun k =>
  if k = .U then List.replicate (L - i * p) tok
  else if k = .ko then List.replicate (min i (L / p)) tok
  else if k = .P then List.replicate p tok
  else if k = .W then (w.drop p).map wrapSym
  else []

lemma divN_guard {L p i : ℕ} (hp : 1 ≤ p) (hi : i < divN L p) : i * p < L := by
  have hdiv := Nat.div_add_mod L p
  rw [mul_comm p (L / p)] at hdiv
  unfold divN at hi
  split_ifs at hi with hmod
  · have h1 : (i + 1) * p ≤ (L / p) * p := Nat.mul_le_mul_right p (by omega)
    have h2 : i * p + p = (i + 1) * p := by ring
    omega
  · have h1 : i * p ≤ (L / p) * p := Nat.mul_le_mul_right p (by omega)
    omega

lemma divN_exit (L p : ℕ) (hp : 1 ≤ p) : L - divN L p * p = 0 := by
  have hdiv := Nat.div_add_mod L p
  rw [mul_comm p (L / p)] at hdiv
  have hlt : L % p < p := Nat.mod_lt L (by omega)
  unfold divN
  split_ifs with hmod
  · simp [hmod] at hdiv
    simp [hdiv]
  · have h1 : (L / p + 1) * p = (L / p) * p + p := by ring
    omega

lemma exec_divBodyProg (w : List Sym) (L p i : ℕ) (hp : 1 ≤ p) (hi : i < divN L p) :
    ∃ c ≤ 9 * p + 12,
      divBodyProg.Exec (sDiv w L p i) (sDiv w L p (i + 1)) c := by
  set s0 := sDiv w L p i
  have hcopy := stack_copy DKey.P DKey.Psc DKey.sc (by decide) (by decide) (by decide) s0 rfl
  set s1 := Function.update s0 .Psc (s0 .P ++ s0 .Psc)
  have e1 : ∃ c ≤ 6 * p + 3, (copyProg .P .Psc .sc).Exec s0 s1 c :=
    ⟨6 * (s0 .P).length + 3, by simp [s0, sDiv], hcopy⟩
  have hpop1 := (stack_basic_macros DKey.Psc s1).2.1
  set s2 := Function.update s1 .Psc (s1 .Psc).tail
  have e2 : ∃ c ≤ 1, (popProg .Psc).Exec s1 s2 c := ⟨1, le_rfl, hpop1⟩
  have hs2_Psc : s2 .Psc = List.replicate (p - 1) tok := by
    simp [s2, s1, s0, sDiv]
  have hcons := stack_consume DKey.Psc (fun k => decide (k = .U)) s2
  set s3 : DStore := consumeStore DKey.Psc (fun k => decide (k = .U)) s2
  have e3 : ∃ c ≤ 3 * (p - 1) + 1,
      (consumeProg .Psc (fun k => decide (k = .U))).Exec s2 s3 c := by
    refine ⟨3 * (s2 .Psc).length + 1, by simp [hs2_Psc], hcons⟩
  have hs3_U : s3 .U = List.replicate (L - i * p - (p - 1)) tok := by
    simp [s3, consumeStore, hs2_Psc, s2, s1, s0, sDiv]
  have hdiv := Nat.div_add_mod L p
  rw [mul_comm p (L / p)] at hdiv
  have hlt : L % p < p := Nat.mod_lt L (by omega)
  by_cases hi_q : i < L / p
  · have hmul : (i + 1) * p ≤ (L / p) * p := Nat.mul_le_mul_right p (by omega)
    have hmul_eq : (i + 1) * p = i * p + p := by ring
    have hrem : 1 ≤ L - i * p - (p - 1) := by omega
    have hguard : ((s3 .U).head?).isSome = true := by
      rw [hs3_U]
      obtain ⟨m, hm⟩ : ∃ m, L - i * p - (p - 1) = m + 1 := ⟨L - i * p - p, by omega⟩
      rw [hm, List.replicate_succ]
      rfl
    have hpopU := (stack_basic_macros DKey.U s3).2.1
    set s4 := Function.update s3 .U (s3 .U).tail
    have hpushKo := (stack_basic_macros DKey.ko s4).1 tok
    have e4_inner : ∃ c ≤ 1 + 1 + 1,
        ((popProg .U).seq (pushProg .ko tok)).Exec s3 (sDiv w L p (i + 1)) c := by
      refine ⟨1 + 1 + 1, le_rfl, exec_congr (StackProg.Exec.seq hpopU hpushKo) ?_⟩
      have hrem2 : L - i * p - (p - 1) - 1 = L - (i + 1) * p := by omega
      have hmin1 : min i (L / p) + 1 = min (i + 1) (L / p) := by omega
      funext k
      cases k <;> simp [s4, s3, consumeStore, hs3_U, s2, s1, s0, sDiv, hrem2, ← List.replicate_succ, hmin1]
    have e4 := exec_branch_true_le (fun h => (h .U).isSome)
      ((popProg .U).seq (pushProg .ko tok)) (popProg .sc) hguard e4_inner
    exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))) (by omega)
  · have hi_eq : i = L / p := by
      unfold divN at hi
      split_ifs at hi <;> omega
    have hrem0 : L - i * p - (p - 1) = 0 := by
      subst hi_eq
      omega
    have hguard : ((s3 .U).head?).isSome = false := by
      rw [hs3_U, hrem0]
      rfl
    have hpopSc := (stack_basic_macros DKey.sc s3).2.1
    have e4_inner : ∃ c ≤ 1, (popProg .sc).Exec s3 (sDiv w L p (i + 1)) c := by
      refine ⟨1, le_rfl, exec_congr hpopSc ?_⟩
      have hrem2 : L - (i + 1) * p = 0 := by
        subst hi_eq
        have : (L / p + 1) * p = (L / p) * p + p := by ring
        omega
      have hmin1 : min i (L / p) = min (i + 1) (L / p) := by omega
      funext k
      cases k <;> simp [s3, consumeStore, hs3_U, hrem0, hrem2, s2, s1, s0, sDiv, hmin1]
    have e4 := exec_branch_false_le (fun h => (h .U).isSome)
      ((popProg .U).seq (pushProg .ko tok)) (popProg .sc) hguard e4_inner
    exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))) (by omega)

def divMainProg : DProg :=
  .seq scanUProg (.seq divReadPLoop divStage3Prog)

def f_div (u : List DSym) : List DSym :=
  let w := u.filterMap Prod.fst
  let L := (u.filter Prod.snd).length
  let p := leadOnes w
  if 1 ≤ p then List.replicate (L / p) tok else []

lemma exec_divMainProg (u : List DSym) :
    ∃ s : DStore, ∃ c ≤ 26 * (u.length + 1) ^ 2,
      divMainProg.Exec (fun k => if k = .ki then u else []) s c ∧
      s .ko = f_div u := by
  set w := u.filterMap Prod.fst
  set L := (u.filter Prod.snd).length
  set p := leadOnes w
  have hw_le : w.length ≤ u.length := List.length_filterMap_le Prod.fst u
  have hL_le : L ≤ u.length := List.length_filter_le Prod.snd u
  have hp_le : p ≤ u.length := le_trans (leadOnes_le w) hw_le
  have e1 := exec_scanUProg u
  have hs1 : sAfterScanU u = sDivReadP w L 0 := by
    funext k; cases k <;> simp [sAfterScanU, sDivReadP, w, L]
  rw [hs1] at e1
  have e2 := exec_le_of_le (exec_divReadPLoop w L) (show 3 * w.length + 1 ≤ 3 * u.length + 1 by omega)
  by_cases hp : 1 ≤ p
  · have hs2 : sDivReadP w L p = sDiv w L p 0 := by
      funext k; cases k <;> simp [sDivReadP, sDiv, p]
    rw [hs2] at e2
    have hloop := exec_bounded_loop (fun h => (h .U).isSome) divBodyProg
      (divN L p) (sDiv w L p) (9 * p + 12)
      (fun i hi => by
        dsimp [sDiv]
        have hlt := divN_guard hp hi
        obtain ⟨m, hm⟩ : ∃ m, L - i * p = m + 1 := ⟨L - i * p - 1, by omega⟩
        rw [hm, List.replicate_succ]
        rfl)
      (by
        dsimp [sDiv]
        rw [divN_exit L p hp]
        rfl)
      (fun i hi => exec_divBodyProg w L p i hp hi)
    have hguardP : ((sDiv w L p 0 .P).head?).isSome = true := by
      dsimp [sDiv]
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      rw [hm, List.replicate_succ]
      rfl
    have e3 := exec_branch_true_le (fun h => (h .P).isSome) divLoop (popProg .sc) hguardP hloop
    have e_all := exec_seq_le e1 (exec_seq_le e2 e3)
    rcases e_all with ⟨c, hc, e_exec⟩
    have hdivN_le : divN L p ≤ u.length + 1 := by
      have : L / p ≤ L := Nat.div_le_self L p
      unfold divN
      split_ifs <;> omega
    have hcost : c ≤ 26 * (u.length + 1) ^ 2 := by
      have hmul : divN L p * (9 * p + 12 + 2) ≤ (u.length + 1) * (9 * u.length + 14) :=
        Nat.mul_le_mul hdivN_le (by omega)
      nlinarith
    refine ⟨sDiv w L p (divN L p), c, hcost, e_exec, ?_⟩
    have hmin : min (divN L p) (L / p) = L / p := by
      unfold divN
      split_ifs <;> omega
    simp [sDiv, f_div, w, L, p, hp, hmin]
  · have hp0 : p = 0 := by omega
    have hguardP : ((sDivReadP w L p .P).head?).isSome = false := by
      simp [sDivReadP, hp0]
    have hpopSc := (stack_basic_macros DKey.sc (sDivReadP w L p)).2.1
    have e3_inner : ∃ c ≤ 1, (popProg .sc).Exec (sDivReadP w L p) (sDivReadP w L p) c := by
      refine ⟨1, le_rfl, exec_congr hpopSc ?_⟩
      funext k; cases k <;> simp [sDivReadP]
    have e3 := exec_branch_false_le (fun h => (h .P).isSome) divLoop (popProg .sc) hguardP e3_inner
    have e_all := exec_seq_le e1 (exec_seq_le e2 e3)
    rcases e_all with ⟨c, hc, e_exec⟩
    refine ⟨sDivReadP w L p, c, by nlinarith, e_exec, ?_⟩
    simp [sDivReadP, f_div, w, L, p, hp]

lemma polyTimeComputable_f_div : PolyTimeComputable f_div := by
  obtain ⟨k, hk⟩ := polynomial_absorb 26 2 0
  refine stack_program_polytime divMainProg .ki .ko f_div k (fun u => ?_)
  obtain ⟨s, c, hc, he, ho⟩ := exec_divMainProg u
  have hk_u := hk u.length
  exact ⟨s, c, by omega, he, ho⟩

lemma f_div_eq_replicate_length (u : List DSym) :
    f_div u = List.replicate (f_div u).length tok := by
  unfold f_div
  dsimp only
  split_ifs <;> simp

lemma map_replicate_tok {Γ : Type} (ι₂ : DSym ↪ Γ) (ι₂' : Unit ↪ Γ)
    (hι : ι₂' () = ι₂ tok) (n : ℕ) :
    (List.replicate n tok).map (some ∘ ι₂) =
      (List.replicate n ()).map (some ∘ ι₂') := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, hι]

lemma polyTimeComputable_unit_of_tok {Sym₁ : Type} [Fintype Sym₁]
    (G : List Sym₁ → List DSym) (hG : PolyTimeComputable G)
    (hrep : ∀ w, G w = List.replicate (G w).length tok) :
    PolyTimeComputable (fun w => List.replicate (G w).length ()) := by
  rcases hG with ⟨Γ, hfinΓ, ι₁, ι₂, M, k, hM⟩
  let ι₂' : Unit ↪ Γ :=
    { toFun := fun _ => ι₂ tok
      inj' := fun a b _ => by cases a; cases b; rfl }
  refine ⟨Γ, hfinΓ, ι₁, ι₂', M, k, fun w => ?_⟩
  obtain ⟨hhalt, hout⟩ := hM w
  refine ⟨hhalt, ?_⟩
  rw [hout, hrep w]
  exact map_replicate_tok ι₂ ι₂' rfl (G w).length

end DivStackProg

/-! ## Part 1: Stack Program for `scDisjointCopies` Encoding -/

namespace ScDisjointCopiesEncodeMap

open DivStackProg (Sym leadOnes leadOnes_le head?_drop_of_lt_leadOnes head?_drop_leadOnes
  tail_drop_eq_drop_succ)

inductive SKey where
  | ki
  | ko
  | outRev
  | P
  | PF
  | PP
  | M
  | Rrem
  | Pre
  | Post
  | W
  | Msc
  | Psc
  | sc
  deriving DecidableEq

instance : Fintype SKey where
  elems := {.ki, .ko, .outRev, .P, .PF, .PP, .M, .Rrem, .Pre, .Post, .W, .Msc, .Psc, .sc}
  complete x := by cases x <;> decide

abbrev Prog := StackProg SKey Sym
abbrev Store := SKey → List Sym

lemma exec_congr {p : Prog} {s t t' : Store} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma exec_seq_le {p q : Prog} {s t u : Store} {B1 B2 : ℕ}
    (h1 : ∃ c1 ≤ B1, p.Exec s t c1) (h2 : ∃ c2 ≤ B2, q.Exec t u c2) :
    ∃ c ≤ B1 + 1 + B2, (p.seq q).Exec s u c := by
  rcases h1 with ⟨c1, hc1, e1⟩
  rcases h2 with ⟨c2, hc2, e2⟩
  exact ⟨c1 + 1 + c2, by omega, StackProg.Exec.seq e1 e2⟩

lemma exec_le_of_le {p : Prog} {s t : Store} {B B' : ℕ}
    (h : ∃ c ≤ B, p.Exec s t c) (hB : B ≤ B') :
    ∃ c ≤ B', p.Exec s t c := by
  rcases h with ⟨c, hc, e⟩
  exact ⟨c, le_trans hc hB, e⟩

lemma exec_bounded_loop (test : (SKey → Option Sym) → Bool) (p : Prog)
    (n : ℕ) (s : ℕ → Store) (B : ℕ)
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

def emitUnary (src : SKey) : Prog :=
  .seq (copyProg src .outRev .sc) (pushProg .outRev none)

lemma exec_emitUnary (src : SKey) (hsd : src ≠ .outRev) (hst : src ≠ .sc)
    (s : Store) (v : ℕ) (hsrc : s src = List.replicate v (some true)) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 5,
      (emitUnary src).Exec s
        (Function.update s .outRev ((List.replicate v (some true) ++ [none]).reverse ++ s .outRev)) c := by
  have e1 := stack_copy src .outRev .sc hsd hst (by decide) s hsc
  set s1 := Function.update s .outRev (s src ++ s .outRev)
  have e2 := (stack_basic_macros .outRev s1).1 none
  refine ⟨(6 * (s src).length + 3) + 1 + 1, by simp [hsrc], ?_⟩
  refine exec_congr (StackProg.Exec.seq e1 e2) ?_
  funext k
  cases k <;> simp [s1, hsrc, List.reverse_append]

/-! ### Stage 1: Parse `p` leading `some true`s into `.P` and `.PF`, and pop separator -/

def readPAct (_h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = .ki then .pop
  else if k = .P then .push (some true)
  else if k = .PF then .push (some false)
  else .keep

def readPLoop : Prog :=
  .loop (fun h => decide (h .ki = some (some true))) (.act readPAct)

def readPProg : Prog :=
  .seq readPLoop (popProg .ki)

def sReadP (w : List Sym) (i : ℕ) : Store := fun k =>
  if k = .ki then w.drop i
  else if k = .P then List.replicate i (some true)
  else if k = .PF then List.replicate i (some false)
  else []

def storeAfterStage1 (w : List Sym) : Store := fun k =>
  if k = .ki then (w.drop (leadOnes w)).tail
  else if k = .P then List.replicate (leadOnes w) (some true)
  else if k = .PF then List.replicate (leadOnes w) (some false)
  else []

lemma exec_readPProg (w : List Sym) :
    ∃ c ≤ 3 * w.length + 3,
      readPProg.Exec (fun k => if k = .ki then w else []) (storeAfterStage1 w) c := by
  have hloop : ∃ c1 ≤ leadOnes w * 3 + 1,
      readPLoop.Exec (sReadP w 0) (sReadP w (leadOnes w)) c1 := by
    refine exec_bounded_loop (fun h => decide (h .ki = some (some true)))
      (.act readPAct) (leadOnes w) (sReadP w) 1 ?_ ?_ ?_
    · intro i hi
      rw [decide_eq_true_eq]
      dsimp [sReadP]
      exact head?_drop_of_lt_leadOnes w i hi
    · rw [decide_eq_false_iff_not]
      dsimp [sReadP]
      exact head?_drop_leadOnes w
    · intro i _
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act readPAct (sReadP w i)) ?_⟩
      funext k
      cases k <;> simp [StackProg.applyAct, readPAct, sReadP, StackAct.apply,
        tail_drop_eq_drop_succ, List.replicate_succ]
  have h0 : (fun k => if k = .ki then w else []) = sReadP w 0 := by
    funext k; cases k <;> rfl
  rw [h0]
  have hpop : ∃ c2 ≤ 1, (popProg .ki).Exec (sReadP w (leadOnes w)) (storeAfterStage1 w) c2 := by
    refine ⟨1, le_rfl, exec_congr (stack_basic_macros .ki (sReadP w (leadOnes w))).2.1 ?_⟩
    funext k
    cases k <;> simp [sReadP, storeAfterStage1]
  have hle := leadOnes_le w
  exact exec_le_of_le (exec_seq_le hloop hpop) (by omega)

/-! ### Stage 2: Count `none`s in `body` into `.M` -/

def countMAct (h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = .W then .pop
  else if k = .M then
    match h .W with
    | some none => .push (some true)
    | _ => .keep
  else .keep

def countMLoop : Prog :=
  .loop (fun h => (h .W).isSome) (.act countMAct)

def countMProg : Prog :=
  .seq (copyProg .ki .W .sc) countMLoop

def sCountM (p : ℕ) (body : List Sym) (i : ℕ) : Store := fun k =>
  if k = .ki then body
  else if k = .P then List.replicate p (some true)
  else if k = .PF then List.replicate p (some false)
  else if k = .W then body.drop i
  else if k = .M then List.replicate ((body.take i).count none) (some true)
  else []

def storeAfterStage2 (p : ℕ) (body : List Sym) : Store := fun k =>
  if k = .ki then body
  else if k = .P then List.replicate p (some true)
  else if k = .PF then List.replicate p (some false)
  else if k = .M then List.replicate (body.count none) (some true)
  else []

lemma take_succ_count_none (body : List Sym) (i : ℕ) (hi : i < body.length) :
    (body.take (i + 1)).count none =
      (body.take i).count none + (if body[i] = none then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.count_append]
  cases h : body[i] with
  | none => simp
  | some b => cases b <;> simp

lemma exec_countMProg (p : ℕ) (body : List Sym) (s : Store)
    (hs : s = fun k =>
      if k = .ki then body
      else if k = .P then List.replicate p (some true)
      else if k = .PF then List.replicate p (some false)
      else []) :
    ∃ c ≤ 9 * body.length + 5,
      countMProg.Exec s (storeAfterStage2 p body) c := by
  have e1 : ∃ c1 ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s (sCountM p body 0) c1 := by
    have hc := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s
      (by simp [hs])
    refine ⟨6 * (s .ki).length + 3, by simp [hs], exec_congr hc ?_⟩
    funext k
    cases k <;> simp [hs, sCountM]
  have e2 : ∃ c2 ≤ body.length * 3 + 1,
      countMLoop.Exec (sCountM p body 0) (storeAfterStage2 p body) c2 := by
    have hloop := exec_bounded_loop (fun h => (h .W).isSome) (.act countMAct)
      body.length (sCountM p body) 1
      (fun i hi => by
        dsimp [sCountM]
        rw [List.drop_eq_getElem_cons hi]
        rfl)
      (by simp [sCountM])
      (fun i hi => by
        refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act countMAct (sCountM p body i)) ?_⟩
        have hcnt := take_succ_count_none body i hi
        funext k
        cases k <;> simp [StackProg.applyAct, countMAct, sCountM, StackAct.apply,
          List.getElem?_eq_getElem hi, tail_drop_eq_drop_succ, hcnt]
        · cases hbi : body[i] with
          | none => simp [List.replicate_succ]
          | some b => cases b <;> simp)
    rcases hloop with ⟨c2, hc2, eloop⟩
    refine ⟨c2, hc2, exec_congr eloop ?_⟩
    funext k
    cases k <;> simp [sCountM, storeAfterStage2]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

/-! ### Stage 3: Initialize `.PP`, `.Post`, `.Rrem` and emit header -/

def repPortsT : Fin 4 ↪ SKey where
  toFun
    | ⟨0, _⟩ => .P
    | ⟨1, _⟩ => .PP
    | ⟨2, _⟩ => .Psc
    | ⟨_ + 3, _⟩ => .sc
  inj' := by decide

def repPortsF : Fin 4 ↪ SKey where
  toFun
    | ⟨0, _⟩ => .PF
    | ⟨1, _⟩ => .Post
    | ⟨2, _⟩ => .Psc
    | ⟨_ + 3, _⟩ => .sc
  inj' := by decide

def initDupProg : Prog :=
  .seq (copyProg .P .Psc .sc)
    (.seq (repeatCopyProg repPortsT)
      (.seq (emitUnary .PP)
        (.seq (copyProg .P .Psc .sc)
          (.seq (repeatCopyProg repPortsF)
            (copyProg .P .Rrem .sc)))))

lemma flatten_replicate_replicate (a b : ℕ) (x : Sym) :
    (List.replicate a (List.replicate b x)).flatten = List.replicate (a * b) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, add_comm, List.replicate_add]

def dupHeaderRev (p : ℕ) : List Sym :=
  (List.replicate (p * p) (some true) ++ [none]).reverse

def encodeOneSet (p : ℕ) (body : List Sym) (r a : ℕ) : List Sym :=
  List.replicate (r * p) (some false) ++
    (body.drop (a * (p + 1))).take p ++
    List.replicate ((p - 1 - r) * p) (some false) ++
    [none]

def encodeBlockPart (p : ℕ) (body : List Sym) (r aBound : ℕ) : List Sym :=
  (List.range aBound).flatMap (encodeOneSet p body r)

def encodeAllBlocks (p m : ℕ) (body : List Sym) (rBound : ℕ) : List Sym :=
  (List.range rBound).flatMap (fun r => encodeBlockPart p body r m)

lemma encodeBlockPart_zero (p : ℕ) (body : List Sym) (r : ℕ) :
    encodeBlockPart p body r 0 = [] := rfl

lemma encodeBlockPart_succ (p : ℕ) (body : List Sym) (r a : ℕ) :
    (encodeBlockPart p body r (a + 1)).reverse =
      (encodeOneSet p body r a).reverse ++ (encodeBlockPart p body r a).reverse := by
  simp [encodeBlockPart, List.range_succ, List.reverse_append]

lemma encodeAllBlocks_zero (p m : ℕ) (body : List Sym) :
    encodeAllBlocks p m body 0 = [] := rfl

lemma encodeAllBlocks_succ (p m : ℕ) (body : List Sym) (r : ℕ) :
    (encodeAllBlocks p m body (r + 1)).reverse =
      (encodeBlockPart p body r m).reverse ++ (encodeAllBlocks p m body r).reverse := by
  simp [encodeAllBlocks, List.range_succ, List.reverse_append]

def rStore (p m : ℕ) (body : List Sym) (r : ℕ) : Store := fun k =>
  match k with
  | .ki => body
  | .P => List.replicate p (some true)
  | .PF => List.replicate p (some false)
  | .PP => List.replicate (p * p) (some true)
  | .M => List.replicate m (some true)
  | .Rrem => List.replicate (p - r) (some true)
  | .Pre => List.replicate (r * p) (some false)
  | .Post => List.replicate ((p - r) * p) (some false)
  | .outRev => (encodeAllBlocks p m body r).reverse ++ dupHeaderRev p
  | .ko | .W | .Msc | .Psc | .sc => []

lemma exec_initDupProg (p : ℕ) (body : List Sym) :
    let m := body.count none
    ∃ c ≤ 18 * p * p + 32 * p + 25,
      initDupProg.Exec (storeAfterStage2 p body) (rStore p m body 0) c := by
  intro m
  set s0 := storeAfterStage2 p body
  have h1 := stack_copy SKey.P SKey.Psc SKey.sc (by decide) (by decide) (by decide) s0 rfl
  set s1 := Function.update s0 .Psc (s0 .P ++ s0 .Psc)
  have e1 : ∃ c ≤ 6 * p + 3, (copyProg .P .Psc .sc).Exec s0 s1 c :=
    ⟨6 * (s0 .P).length + 3, by simp [s0, storeAfterStage2], h1⟩
  have h2 := stack_repeat_copy repPortsT s1 (by simp [s1, s0, storeAfterStage2, repPortsT])
  set s2 := Function.update (Function.update s1 .Psc []) .PP
    ((List.replicate (s1 .Psc).length (s1 .P)).flatten ++ s1 .PP)
  have e2 : ∃ c ≤ (6 * p + 7) * p + 1, (repeatCopyProg repPortsT).Exec s1 s2 c := by
    refine ⟨((6 * (s1 .P).length + 7) * (s1 .Psc).length + 1), ?_, h2⟩
    simp [s1, s0, storeAfterStage2]
  have hs2_PP : s2 .PP = List.replicate (p * p) (some true) := by
    simp [s2, s1, s0, storeAfterStage2, flatten_replicate_replicate]
  have hs2_sc : s2 .sc = [] := by
    simp [s2, s1, s0, storeAfterStage2]
  have e3 := exec_emitUnary .PP (by decide) (by decide) s2 (p * p) hs2_PP hs2_sc
  set s3 := Function.update s2 .outRev
    ((List.replicate (p * p) (some true) ++ [none]).reverse ++ s2 .outRev)
  have hs3_P : s3 .P = List.replicate p (some true) := by
    simp [s3, s2, s1, s0, storeAfterStage2]
  have hs3_sc : s3 .sc = [] := by
    simp [s3, s2, s1, s0, storeAfterStage2]
  have h4 := stack_copy SKey.P SKey.Psc SKey.sc (by decide) (by decide) (by decide) s3 hs3_sc
  set s4 := Function.update s3 .Psc (s3 .P ++ s3 .Psc)
  have e4 : ∃ c ≤ 6 * p + 3, (copyProg .P .Psc .sc).Exec s3 s4 c :=
    ⟨6 * (s3 .P).length + 3, by simp [hs3_P], h4⟩
  have h5 := stack_repeat_copy repPortsF s4 (by simp [s4, s3, s2, s1, s0, storeAfterStage2, repPortsF])
  set s5 := Function.update (Function.update s4 .Psc []) .Post
    ((List.replicate (s4 .Psc).length (s4 .PF)).flatten ++ s4 .Post)
  have e5 : ∃ c ≤ (6 * p + 7) * p + 1, (repeatCopyProg repPortsF).Exec s4 s5 c := by
    refine ⟨((6 * (s4 .PF).length + 7) * (s4 .Psc).length + 1), ?_, h5⟩
    simp [s4, s3, s2, s1, s0, storeAfterStage2]
  have hs5_Post : s5 .Post = List.replicate (p * p) (some false) := by
    simp [s5, s4, s3, s2, s1, s0, storeAfterStage2, flatten_replicate_replicate]
  have hs5_sc : s5 .sc = [] := by
    simp [s5, s4, s3, s2, s1, s0, storeAfterStage2]
  have h6 := stack_copy SKey.P SKey.Rrem SKey.sc (by decide) (by decide) (by decide) s5 hs5_sc
  set s6 := Function.update s5 .Rrem (s5 .P ++ s5 .Rrem)
  have e6 : ∃ c ≤ 6 * p + 3, (copyProg .P .Rrem .sc).Exec s5 (rStore p m body 0) c := by
    refine ⟨6 * (s5 .P).length + 3, by simp [s5, s4, hs3_P], exec_congr h6 ?_⟩
    funext k
    cases k <;> simp [s6, hs5_Post, s5, s4, s3, hs2_PP, s2, s1, s0, storeAfterStage2,
      rStore, encodeAllBlocks, dupHeaderRev, m]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 (exec_seq_le e5 e6))))
  refine exec_le_of_le e_all ?_
  nlinarith

/-! ### Stage 4: Nested Loops over `r < p`, `a < m`, and slice copy of `p` bits -/

def copySliceAct (h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = .Psc then .pop
  else if k = .W then .pop
  else if k = .outRev then
    match h .W with
    | some x => .push x
    | none => .keep
  else .keep

def copySliceLoop : Prog :=
  .loop (fun h => (h .Psc).isSome) (.act copySliceAct)

lemma take_succ_rev_head?_drop (L : List Sym) (i : ℕ) (acc : List Sym) :
    (match (L.drop i).head? with
      | some x => x :: ((L.take i).reverse ++ acc)
      | none => (L.take i).reverse ++ acc) =
      (L.take (i + 1)).reverse ++ acc := by
  rw [List.take_add_one, ← List.head?_drop]
  cases (L.drop i).head? <;> simp

def sSlice (s : Store) (p : ℕ) (L : List Sym) (acc : List Sym) (i : ℕ) : Store := fun k =>
  if k = .Psc then List.replicate (p - i) (some true)
  else if k = .W then L.drop i
  else if k = .outRev then (L.take i).reverse ++ acc
  else s k

lemma exec_copySliceLoop (s : Store) (p : ℕ) (L acc : List Sym)
    (hPsc : s .Psc = List.replicate p (some true))
    (hW : s .W = L)
    (hout : s .outRev = acc) :
    ∃ c ≤ 3 * p + 1,
      copySliceLoop.Exec s (sSlice s p L acc p) c := by
  have hs0 : s = sSlice s p L acc 0 := by
    funext k
    cases k <;> simp [sSlice, hPsc, hW, hout]
  have hloop := exec_bounded_loop (fun h => (h .Psc).isSome) (.act copySliceAct)
    p (sSlice s p L acc) 1
    (fun i hi => by
      dsimp [sSlice]
      obtain ⟨d, hd⟩ : ∃ d, p - i = d + 1 := ⟨p - 1 - i, by omega⟩
      rw [hd, List.replicate_succ]
      rfl)
    (by simp [sSlice])
    (fun i hi => by
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act copySliceAct (sSlice s p L acc i)) ?_⟩
      have hsub : p - i - 1 = p - (i + 1) := by omega
      have htake := take_succ_rev_head?_drop L i acc
      funext k
      cases k <;> simp [StackProg.applyAct, copySliceAct, sSlice, StackAct.apply,
        tail_drop_eq_drop_succ, hsub]
      · rw [← List.head?_drop]
        cases hhead : (L.drop i).head? <;> simp [hhead] at htake ⊢ <;> exact htake)
  rcases hloop with ⟨c, hc, eloop⟩
  rw [← hs0] at eloop
  exact ⟨c, by omega, eloop⟩

def aBodyProg : Prog :=
  .seq (popProg .Msc)
    (.seq (copyProg .Pre .outRev .sc)
      (.seq (copyProg .P .Psc .sc)
        (.seq copySliceLoop
          (.seq (popProg .W)
            (.seq (copyProg .Post .outRev .sc)
              (pushProg .outRev none))))))

def aLoopProg : Prog :=
  .loop (fun h => (h .Msc).isSome) aBodyProg

def aStore (p m : ℕ) (body : List Sym) (r a : ℕ) : Store := fun k =>
  match k with
  | .ki => body
  | .P => List.replicate p (some true)
  | .PF => List.replicate p (some false)
  | .PP => List.replicate (p * p) (some true)
  | .M => List.replicate m (some true)
  | .Rrem => List.replicate (p - (r + 1)) (some true)
  | .Pre => List.replicate (r * p) (some false)
  | .Post => List.replicate ((p - 1 - r) * p) (some false)
  | .W => body.drop (a * (p + 1))
  | .Msc => List.replicate (m - a) (some true)
  | .outRev =>
      (encodeBlockPart p body r a).reverse ++
        (encodeAllBlocks p m body r).reverse ++ dupHeaderRev p
  | .ko | .Psc | .sc => []

lemma exec_aBodyProg (p m : ℕ) (body : List Sym) (r a : ℕ) (hr : r < p) (_ha : a < m) :
    ∃ c ≤ 12 * p * p + 9 * p + 19,
      aBodyProg.Exec (aStore p m body r a) (aStore p m body r (a + 1)) c := by
  set s0 := aStore p m body r a
  have h1 := (stack_basic_macros SKey.Msc s0).2.1
  set s1 := Function.update s0 .Msc (s0 .Msc).tail
  have e1 : ∃ c ≤ 1, (popProg .Msc).Exec s0 s1 c := ⟨1, le_rfl, h1⟩
  have h2 := stack_copy SKey.Pre SKey.outRev SKey.sc (by decide) (by decide) (by decide) s1 rfl
  set s2 := Function.update s1 .outRev (s1 .Pre ++ s1 .outRev)
  have hrp : r * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  have e2 : ∃ c ≤ 6 * (p * p) + 3, (copyProg .Pre .outRev .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .Pre).length + 3, ?_, h2⟩
    simp [s1, s0, aStore]
    omega
  have h3 := stack_copy SKey.P SKey.Psc SKey.sc (by decide) (by decide) (by decide) s2 rfl
  set s3 := Function.update s2 .Psc (s2 .P ++ s2 .Psc)
  have e3 : ∃ c ≤ 6 * p + 3, (copyProg .P .Psc .sc).Exec s2 s3 c :=
    ⟨6 * (s2 .P).length + 3, by simp [s2, s1, s0, aStore], h3⟩
  set L := body.drop (a * (p + 1))
  set acc1 := List.replicate (r * p) (some false) ++ s0 .outRev
  have hs3_Psc : s3 .Psc = List.replicate p (some true) := by
    simp [s3, s2, s1, s0, aStore]
  have hs3_W : s3 .W = L := by
    simp [s3, s2, s1, s0, aStore, L]
  have hs3_out : s3 .outRev = acc1 := by
    simp [s3, s2, s1, s0, aStore, acc1]
  have e4 := exec_copySliceLoop s3 p L acc1 hs3_Psc hs3_W hs3_out
  set s4 := sSlice s3 p L acc1 p
  have h5 := (stack_basic_macros SKey.W s4).2.1
  set s5 := Function.update s4 .W (s4 .W).tail
  have e5 : ∃ c ≤ 1, (popProg .W).Exec s4 s5 c := ⟨1, le_rfl, h5⟩
  have hs5_sc : s5 .sc = [] := by
    simp [s5, s4, sSlice, s3, s2, s1, s0, aStore]
  have h6 := stack_copy SKey.Post SKey.outRev SKey.sc (by decide) (by decide) (by decide) s5 hs5_sc
  set s6 := Function.update s5 .outRev (s5 .Post ++ s5 .outRev)
  have hpost_le : (p - 1 - r) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  have e6 : ∃ c ≤ 6 * (p * p) + 3, (copyProg .Post .outRev .sc).Exec s5 s6 c := by
    refine ⟨6 * (s5 .Post).length + 3, ?_, h6⟩
    simp [s5, s4, sSlice, s3, s2, s1, s0, aStore]
    omega
  have h7 := (stack_basic_macros SKey.outRev s6).1 none
  have e7 : ∃ c ≤ 1, (pushProg .outRev none).Exec s6 (aStore p m body r (a + 1)) c := by
    refine ⟨1, le_rfl, exec_congr h7 ?_⟩
    have hm_sub : m - a - 1 = m - (a + 1) := by omega
    funext k
    cases k <;> simp [s6, s5, s4, sSlice, s3, s2, s1, s0, aStore, hm_sub,
      acc1, L, encodeBlockPart_succ, encodeOneSet, List.reverse_append]
    · congr 1; ring
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3
    (exec_seq_le e4 (exec_seq_le e5 (exec_seq_le e6 e7)))))
  refine exec_le_of_le e_all ?_
  nlinarith

lemma exec_aLoopProg (p m : ℕ) (body : List Sym) (r : ℕ) (hr : r < p) :
    ∃ c ≤ m * (12 * p * p + 9 * p + 21) + 1,
      aLoopProg.Exec (aStore p m body r 0) (aStore p m body r m) c := by
  refine exec_bounded_loop (fun h => (h .Msc).isSome) aBodyProg
    m (aStore p m body r) (12 * p * p + 9 * p + 19)
    (fun a ha => by
      dsimp [aStore]
      obtain ⟨d, hd⟩ : ∃ d, m - a = d + 1 := ⟨m - 1 - a, by omega⟩
      rw [hd, List.replicate_succ]
      rfl)
    (by simp [aStore])
    (fun a ha => exec_aBodyProg p m body r a hr ha)

def rBodyProg : Prog :=
  .seq (popProg .Rrem)
    (.seq (copyProg .P .Psc .sc)
      (.seq (consumeProg .Psc (fun k => decide (k = .Post)))
        (.seq (copyProg .ki .W .sc)
          (.seq (copyProg .M .Msc .sc)
            (.seq aLoopProg
              (.seq (clearProg .W)
                (copyProg .PF .Pre .sc)))))))

def rLoopProg : Prog :=
  .loop (fun h => (h .Rrem).isSome) rBodyProg

lemma exec_rBodyProg (p m : ℕ) (body : List Sym) (r : ℕ) (hr : r < p) :
    ∃ c ≤ m * (12 * p * p + 9 * p + 21) + 9 * body.length + 6 * m + 15 * p + 25,
      rBodyProg.Exec (rStore p m body r) (rStore p m body (r + 1)) c := by
  set s0 := rStore p m body r
  have h1 := (stack_basic_macros SKey.Rrem s0).2.1
  set s1 := Function.update s0 .Rrem (s0 .Rrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Rrem).Exec s0 s1 c := ⟨1, le_rfl, h1⟩
  have h2 := stack_copy SKey.P SKey.Psc SKey.sc (by decide) (by decide) (by decide) s1 rfl
  set s2 := Function.update s1 .Psc (s1 .P ++ s1 .Psc)
  have e2 : ∃ c ≤ 6 * p + 3, (copyProg .P .Psc .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .P).length + 3, by simp [s1, s0, rStore], h2⟩
  have h3 := stack_consume SKey.Psc (fun k => decide (k = .Post)) s2
  set s3 := consumeStore SKey.Psc (fun k => decide (k = .Post)) s2
  have e3 : ∃ c ≤ 3 * p + 1,
      (consumeProg .Psc (fun k => decide (k = .Post))).Exec s2 s3 c := by
    refine ⟨3 * (s2 .Psc).length + 1, by simp [s2, s1, s0, rStore], h3⟩
  have hs3_sc : s3 .sc = [] := by
    simp [s3, consumeStore, s2, s1, s0, rStore]
  have h4 := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s3 hs3_sc
  set s4 := Function.update s3 .W (s3 .ki ++ s3 .W)
  have e4 : ∃ c ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s3 s4 c :=
    ⟨6 * (s3 .ki).length + 3, by simp [s3, consumeStore, s2, s1, s0, rStore], h4⟩
  have hs4_sc : s4 .sc = [] := by
    simp [s4, hs3_sc]
  have h5 := stack_copy SKey.M SKey.Msc SKey.sc (by decide) (by decide) (by decide) s4 hs4_sc
  have e5 : ∃ c ≤ 6 * m + 3, (copyProg .M .Msc .sc).Exec s4 (aStore p m body r 0) c := by
    refine ⟨6 * (s4 .M).length + 3, by simp [s4, s3, consumeStore, s2, s1, s0, rStore],
      exec_congr h5 ?_⟩
    have hr_sub : p - r - 1 = p - (r + 1) := by omega
    have hpost_sub : (p - r) * p - p = (p - 1 - r) * p := by
      have : p - r = (p - 1 - r) + 1 := by omega
      rw [this, Nat.succ_mul]
      omega
    funext k
    cases k <;> simp [s4, s3, consumeStore, s2, s1, s0, rStore, aStore,
      hr_sub, hpost_sub, encodeBlockPart_zero]
  have e6 := exec_aLoopProg p m body r hr
  set s6 := aStore p m body r m
  have h7 := stack_transfer SKey.W (fun _ => false) s6
  set s7 := transferStore SKey.W (fun _ => false) s6
  have e7 : ∃ c ≤ 3 * body.length + 1, (clearProg .W).Exec s6 s7 c := by
    refine ⟨3 * (s6 .W).length + 1, ?_, h7⟩
    dsimp [s6, aStore]
    simp only [List.length_drop]
    omega
  have hs7_sc : s7 .sc = [] := by
    simp [s7, transferStore, s6, aStore]
  have h8 := stack_copy SKey.PF SKey.Pre SKey.sc (by decide) (by decide) (by decide) s7 hs7_sc
  have e8 : ∃ c ≤ 6 * p + 3, (copyProg .PF .Pre .sc).Exec s7 (rStore p m body (r + 1)) c := by
    refine ⟨6 * (s7 .PF).length + 3, by simp [s7, transferStore, s6, aStore], exec_congr h8 ?_⟩
    have hpre_add : p + r * p = (r + 1) * p := by ring
    have hpost_eq : p - 1 - r = p - (r + 1) := by omega
    funext k
    cases k <;> simp [s7, transferStore, s6, aStore, rStore,
      ← List.replicate_add, hpre_add, hpost_eq, encodeAllBlocks_succ]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 (exec_seq_le e7 e8))))))
  refine exec_le_of_le e_all ?_
  omega

lemma exec_rLoopProg (p m : ℕ) (body : List Sym) :
    ∃ c ≤ p * (m * (12 * p * p + 9 * p + 21) + 9 * body.length + 6 * m + 15 * p + 27) + 1,
      rLoopProg.Exec (rStore p m body 0) (rStore p m body p) c := by
  refine exec_bounded_loop (fun h => (h .Rrem).isSome) rBodyProg
    p (rStore p m body)
    (m * (12 * p * p + 9 * p + 21) + 9 * body.length + 6 * m + 15 * p + 25)
    (fun r hr => by
      dsimp [rStore]
      obtain ⟨d, hd⟩ : ∃ d, p - r = d + 1 := ⟨p - 1 - r, by omega⟩
      rw [hd, List.replicate_succ]
      rfl)
    (by simp [rStore])
    (fun r hr => exec_rBodyProg p m body r hr)

/-! ### Stage 5: Transfer `.outRev` to `.ko` and full program execution -/

def dupMainProg : Prog :=
  .seq readPProg
    (.seq countMProg
      (.seq initDupProg
        (.seq rLoopProg
          (transferProg .outRev (fun k => decide (k = .ko))))))

def f_dup (w : List Sym) : List Sym :=
  let p := leadOnes w
  let body := (w.drop p).tail
  let m := body.count none
  (dupHeaderRev p).reverse ++ encodeAllBlocks p m body p

lemma length_encodeOneSet_le (p : ℕ) (body : List Sym) (r a : ℕ) (hr : r < p) :
    (encodeOneSet p body r a).length ≤ p * p + 1 := by
  simp only [encodeOneSet, List.length_append, List.length_replicate, List.length_take,
    List.length_singleton]
  have h1 : min p (body.drop (a * (p + 1))).length ≤ p := Nat.min_le_left _ _
  have h2 : r * p + p + (p - 1 - r) * p = p * p := by
    have : r + 1 + (p - 1 - r) = p := by omega
    calc r * p + p + (p - 1 - r) * p = (r + 1 + (p - 1 - r)) * p := by ring
      _ = p * p := by rw [this]
  omega

lemma length_encodeBlockPart_le (p : ℕ) (body : List Sym) (r : ℕ) (hr : r < p) :
    ∀ a : ℕ, (encodeBlockPart p body r a).length ≤ a * (p * p + 1)
  | 0 => by simp [encodeBlockPart]
  | a + 1 => by
    have h1 := length_encodeBlockPart_le p body r hr a
    have h2 := length_encodeOneSet_le p body r a hr
    have h3 : (encodeBlockPart p body r (a + 1)).length =
        (encodeBlockPart p body r a).length + (encodeOneSet p body r a).length := by
      simp [encodeBlockPart, List.range_succ]
    have h4 : (a + 1) * (p * p + 1) = a * (p * p + 1) + (p * p + 1) := by ring
    omega

lemma length_encodeAllBlocks_le (p m : ℕ) (body : List Sym) :
    ∀ r : ℕ, r ≤ p → (encodeAllBlocks p m body r).length ≤ r * (m * (p * p + 1))
  | 0, _ => by simp [encodeAllBlocks]
  | r + 1, hr => by
    have h1 := length_encodeAllBlocks_le p m body r (by omega)
    have h2 := length_encodeBlockPart_le p body r (by omega) m
    have h3 : (encodeAllBlocks p m body (r + 1)).length =
        (encodeAllBlocks p m body r).length + (encodeBlockPart p body r m).length := by
      simp [encodeAllBlocks, List.range_succ]
    have h4 : (r + 1) * (m * (p * p + 1)) = r * (m * (p * p + 1)) + m * (p * p + 1) := by ring
    omega

lemma count_none_le_length (l : List Sym) : l.count none ≤ l.length :=
  List.count_le_length

lemma exec_dupMainProg (w : List Sym) :
    ∃ s : Store, ∃ c ≤ 200 * (w.length + 1) ^ 4,
      dupMainProg.Exec (fun k => if k = .ki then w else []) s c ∧
      s .ko = f_dup w := by
  set p := leadOnes w
  set body := (w.drop p).tail
  set m := body.count none
  have hp_le : p ≤ w.length := leadOnes_le w
  have hbody_le : body.length ≤ w.length := by
    simp only [body, List.length_tail, List.length_drop]
    omega
  have hm_le : m ≤ body.length := count_none_le_length body
  have e1 := exec_readPProg w
  have e2 := exec_countMProg p body (storeAfterStage1 w) rfl
  have e3 := exec_initDupProg p body
  have e4 := exec_rLoopProg p m body
  set s4 := rStore p m body p
  have h5 := stack_transfer SKey.outRev (fun k => decide (k = .ko)) s4
  set s5 := transferStore SKey.outRev (fun k => decide (k = .ko)) s4
  have hout_len : (s4 .outRev).length ≤ p * (m * (p * p + 1)) + p * p + 1 := by
    dsimp [s4, rStore, dupHeaderRev]
    simp only [List.length_append, List.length_reverse, List.length_replicate, List.length_singleton]
    have htab := length_encodeAllBlocks_le p m body p le_rfl
    omega
  have e5 : ∃ c ≤ 3 * (p * (m * (p * p + 1)) + p * p + 1) + 1,
      (transferProg .outRev (fun k => decide (k = .ko))).Exec s4 s5 c := by
    refine ⟨3 * (s4 .outRev).length + 1, by omega, h5⟩
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 e5)))
  rcases e_all with ⟨c, hc, e_exec⟩
  refine ⟨s5, c, ?_, e_exec, ?_⟩
  · set M := w.length + 1
    have h1_M : 1 ≤ M := by omega
    have hwM : w.length ≤ M := by omega
    have hpM : p ≤ M := by omega
    have hbM : body.length ≤ M := by omega
    have hmM : m ≤ M := by omega
    set M2 := M * M
    set M3 := M * M2
    set M4 := M * M3
    have hM_M2 : M ≤ M2 := Nat.le_mul_of_pos_right M h1_M
    have h1_M2 : 1 ≤ M2 := le_trans h1_M hM_M2
    have hM2_M3 : M2 ≤ M3 := Nat.le_mul_of_pos_left M2 h1_M
    have hM_M3 : M ≤ M3 := le_trans hM_M2 hM2_M3
    have h1_M3 : 1 ≤ M3 := le_trans h1_M2 hM2_M3
    have hM3_M4 : M3 ≤ M4 := Nat.le_mul_of_pos_left M3 h1_M
    have hM2_M4 : M2 ≤ M4 := le_trans hM2_M3 hM3_M4
    have hM_M4 : M ≤ M4 := le_trans hM_M3 hM3_M4
    have h1_M4 : 1 ≤ M4 := le_trans h1_M3 hM3_M4
    have hp2 : p * p ≤ M2 := Nat.mul_le_mul hpM hpM
    have hp12 : 12 * p * p = 12 * (p * p) := by ring
    have hp18 : 18 * p * p = 18 * (p * p) := by ring
    have h_in1 : 12 * p * p + 9 * p + 21 ≤ 42 * M2 := by omega
    have hm_in1 : m * (12 * p * p + 9 * p + 21) ≤ 42 * M3 := by
      have hmul := Nat.mul_le_mul hmM h_in1
      have heq : M * (42 * M2) = 42 * M3 := by dsimp [M3]; ring
      omega
    have hB_le : m * (12 * p * p + 9 * p + 21) + 9 * body.length + 6 * m + 15 * p + 27 ≤
        99 * M3 := by omega
    have h_loop_le : p * (m * (12 * p * p + 9 * p + 21) + 9 * body.length + 6 * m + 15 * p + 27) ≤
        99 * M4 := by
      have hmul := Nat.mul_le_mul hpM hB_le
      have heq : M * (99 * M3) = 99 * M4 := by dsimp [M4]; ring
      omega
    have hp2_1 : p * p + 1 ≤ 2 * M2 := by omega
    have hm_p2_1 : m * (p * p + 1) ≤ 2 * M3 := by
      have hmul := Nat.mul_le_mul hmM hp2_1
      have heq : M * (2 * M2) = 2 * M3 := by dsimp [M3]; ring
      omega
    have h_tab_le : p * (m * (p * p + 1)) ≤ 2 * M4 := by
      have hmul := Nat.mul_le_mul hpM hm_p2_1
      have heq : M * (2 * M3) = 2 * M4 := by dsimp [M4]; ring
      omega
    have hpow4 : M ^ 4 = M4 := by dsimp [M4, M3, M2]; ring
    rw [hpow4]
    omega
  · simp [s5, transferStore, s4, rStore, f_dup, p, body, m, List.reverse_append]

lemma polyTimeComputable_f_dup : PolyTimeComputable f_dup := by
  obtain ⟨k, hk⟩ := polynomial_absorb 200 4 0
  refine stack_program_polytime dupMainProg .ki .ko f_dup k (fun w => ?_)
  obtain ⟨s, c, hc, he, ho⟩ := exec_dupMainProg w
  have hk_w := hk w.length
  exact ⟨s, c, by omega, he, ho⟩

/-! ### Correctness on `I.encode`: `f_dup I.encode = (scDisjointCopies I).encode` -/

def scBlock {n : ℕ} (S : Finset (Fin n)) : List Sym :=
  List.ofFn (fun x : Fin n => some (decide (x ∈ S))) ++ [none]

lemma leadOnes_replicate_append (n : ℕ) (xs : List Sym) :
    leadOnes (List.replicate n (some true) ++ none :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, leadOnes, ih]

lemma drop_replicate_append (n : ℕ) (xs : List Sym) :
    ((List.replicate n (some true) ++ none :: xs).drop n).tail = xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, ih]

lemma count_none_ofFn_some {n : ℕ} (S : Finset (Fin n)) :
    (List.ofFn (fun x : Fin n => some (decide (x ∈ S)))).count none = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  rw [List.mem_ofFn] at hmem
  rcases hmem with ⟨i, hi⟩
  cases hi

lemma count_none_flatMap_scBlock {n : ℕ} :
    ∀ L : List (Finset (Fin n)), (L.flatMap scBlock).count none = L.length
  | [] => rfl
  | S :: L => by
    simp [List.flatMap_cons, scBlock, List.count_append, count_none_ofFn_some,
      count_none_flatMap_scBlock L]

lemma length_scBlock {n : ℕ} (S : Finset (Fin n)) :
    (scBlock S).length = n + 1 := by
  simp [scBlock]

lemma drop_flatMap_scBlock {n : ℕ} :
    ∀ (L : List (Finset (Fin n))) (a : ℕ),
      (L.flatMap scBlock).drop (a * (n + 1)) = (L.drop a).flatMap scBlock
  | L, 0 => by simp
  | [], a + 1 => by simp
  | S :: L, a + 1 => by
    have h1 : (scBlock S ++ L.flatMap scBlock).drop (n + 1) = L.flatMap scBlock := by
      rw [← length_scBlock S, List.drop_left]
    rw [List.flatMap_cons, Nat.succ_mul, add_comm (a * (n + 1)) (n + 1),
      ← List.drop_drop, h1, List.drop_succ_cons]
    exact drop_flatMap_scBlock L a

lemma take_drop_flatMap_scBlock {n : ℕ} (L : List (Finset (Fin n))) (a : Fin L.length) :
    ((L.flatMap scBlock).drop (a.val * (n + 1))).take n =
      List.ofFn (fun x : Fin n => some (decide (x ∈ L.get a))) := by
  rw [drop_flatMap_scBlock L a.val, List.drop_eq_getElem_cons a.isLt, List.flatMap_cons]
  unfold scBlock
  rw [List.append_assoc]
  set v := List.ofFn (fun x : Fin n => some (decide (x ∈ L[a.val])))
  rw [List.take_append_of_le_length (by simp [v]), List.take_of_length_le (by simp [v])]
  rfl

lemma ofFn_scCopySet (n : ℕ) (r : Fin n) (S : Finset (Fin n)) :
    List.ofFn (fun z : Fin (n ^ 2) => some (decide (z ∈ scCopySet n r S))) =
      List.replicate (r.val * n) (some false) ++
        List.ofFn (fun x : Fin n => some (decide (x ∈ S))) ++
        List.replicate ((n - 1 - r.val) * n) (some false) := by
  have hr := r.isLt
  have hlen_rhs : r.val * n + n + (n - 1 - r.val) * n = n ^ 2 := by
    have : r.val + 1 + (n - 1 - r.val) = n := by omega
    calc r.val * n + n + (n - 1 - r.val) * n = (r.val + 1 + (n - 1 - r.val)) * n := by ring
      _ = n * n := by rw [this]
      _ = n ^ 2 := by ring
  apply List.ext_getElem
  · simp; omega
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    have hi : i < n ^ 2 := by simpa using hi1
    by_cases h1 : i < r.val * n
    · have h1' : i < (List.replicate (r.val * n) (some false) ++
          List.ofFn (fun x : Fin n => some (decide (x ∈ S)))).length := by
        simp; omega
      rw [List.getElem_append_left h1', List.getElem_append_left (by simp [h1]),
        List.getElem_replicate]
      suffices ¬ (⟨i, hi⟩ : Fin (n ^ 2)) ∈ scCopySet n r S by simp [this]
      intro hmem
      simp only [scCopySet, Finset.mem_image, scCopyPoint, Fin.ext_iff] at hmem
      rcases hmem with ⟨x, _, hx_eq⟩
      omega
    · by_cases h2 : i < r.val * n + n
      · have h2' : i < (List.replicate (r.val * n) (some false) ++
            List.ofFn (fun x : Fin n => some (decide (x ∈ S)))).length := by
          simp [h2]
        have h1_le : (List.replicate (r.val * n) (some false)).length ≤ i := by
          simp; omega
        rw [List.getElem_append_left h2', List.getElem_append_right h1_le]
        simp only [List.length_replicate, List.getElem_ofFn]
        congr 2
        apply propext
        simp only [scCopySet, Finset.mem_image, scCopyPoint, Fin.ext_iff]
        constructor
        · rintro ⟨x, hxS, hx_eq⟩
          have hxeq : x = ⟨i - r.val * n, by omega⟩ := by
            ext; dsimp; omega
          rwa [← hxeq]
        · intro hxS
          exact ⟨⟨i - r.val * n, by omega⟩, hxS, by dsimp; omega⟩
      · have h2_le : (List.replicate (r.val * n) (some false) ++
            List.ofFn (fun x : Fin n => some (decide (x ∈ S)))).length ≤ i := by
          simp; omega
        rw [List.getElem_append_right h2_le, List.getElem_replicate]
        suffices ¬ (⟨i, hi⟩ : Fin (n ^ 2)) ∈ scCopySet n r S by simp [this]
        intro hmem
        simp only [scCopySet, Finset.mem_image, scCopyPoint, Fin.ext_iff] at hmem
        rcases hmem with ⟨x, _, hx_eq⟩
        have hxlt := x.isLt
        omega

lemma flatMap_finRange_eq_flatMap_range {α : Type} (n : ℕ) (g : ℕ → List α) :
    (List.finRange n).flatMap (fun x : Fin n => g x.val) = (List.range n).flatMap g := by
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← List.flatMap_map, hmap]

lemma map_get_finRange {α : Type} (L : List α) :
    (List.finRange L.length).map L.get = L := by
  apply List.ext_getElem <;> simp

lemma flatMap_flatMap_eq {α β γ : Type} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap (fun x => (f x).flatMap g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma f_dup_encode (I : SCInstance) :
    f_dup I.encode = (scDisjointCopies I).encode := by
  unfold f_dup SCInstance.encode scDisjointCopies
  have hp : leadOnes (List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock) = I.n :=
    leadOnes_replicate_append I.n (I.sets.flatMap scBlock)
  have hbody : ((List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock).drop I.n).tail =
      I.sets.flatMap scBlock :=
    drop_replicate_append I.n (I.sets.flatMap scBlock)
  have hm : (I.sets.flatMap scBlock).count none = I.sets.length :=
    count_none_flatMap_scBlock I.sets
  change (let p := leadOnes (List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock)
    let body := ((List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock).drop p).tail
    let m := body.count none
    (dupHeaderRev p).reverse ++ encodeAllBlocks p m body p) = _
  dsimp only
  rw [hp, hbody, hm]
  have hpow2 : I.n * I.n = I.n ^ 2 := (sq I.n).symm
  have hblocks : encodeAllBlocks I.n I.sets.length (I.sets.flatMap scBlock) I.n =
      ((List.finRange I.n).flatMap fun r => I.sets.map (scCopySet I.n r)).flatMap scBlock := by
    rw [flatMap_flatMap_eq]
    have hinner : ∀ r : Fin I.n,
        (I.sets.map (scCopySet I.n r)).flatMap scBlock =
          encodeBlockPart I.n (I.sets.flatMap scBlock) r.val I.sets.length := by
      intro r
      conv_lhs => rw [← map_get_finRange I.sets]
      rw [List.map_map, List.flatMap_map]
      dsimp only [Function.comp_def]
      have hset : ∀ a : Fin I.sets.length,
          scBlock (scCopySet I.n r (I.sets.get a)) =
            encodeOneSet I.n (I.sets.flatMap scBlock) r.val a.val := by
        intro a
        dsimp only [encodeOneSet]
        rw [take_drop_flatMap_scBlock I.sets a, ← ofFn_scCopySet I.n r (I.sets.get a)]
        rfl
      simp_rw [hset]
      exact flatMap_finRange_eq_flatMap_range I.sets.length
        (encodeOneSet I.n (I.sets.flatMap scBlock) r.val)
    simp_rw [hinner]
    exact (flatMap_finRange_eq_flatMap_range I.n
      (fun r => encodeBlockPart I.n (I.sets.flatMap scBlock) r I.sets.length)).symm
  rw [hblocks]
  simp [dupHeaderRev, hpow2]
  rfl

end ScDisjointCopiesEncodeMap

theorem solution (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg' : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg' ∧
      ∀ I : SCInstance, I.Coverable → 1 ≤ I.n →
        (Alg' I.encode).length = (Alg (scDisjointCopies I).encode).length / I.n := by
  have hF : PolyTimeComputable (Alg ∘ ScDisjointCopiesEncodeMap.f_dup) :=
    polyTimeComputable_comp ScDisjointCopiesEncodeMap.f_dup Alg
      ScDisjointCopiesEncodeMap.polyTimeComputable_f_dup hAlg
  obtain ⟨f_save, h_save, h_save_spec⟩ :=
    SaveTMProof.polyTimeComputable_save (Alg ∘ ScDisjointCopiesEncodeMap.f_dup) hF
  set G : List (Option Bool) → List DivStackProg.DSym := DivStackProg.f_div ∘ f_save
  have hG : PolyTimeComputable G :=
    polyTimeComputable_comp f_save DivStackProg.f_div h_save DivStackProg.polyTimeComputable_f_div
  have hG_rep : ∀ w, G w = List.replicate (G w).length DivStackProg.tok :=
    fun w => DivStackProg.f_div_eq_replicate_length (f_save w)
  let Alg' : List (Option Bool) → List Unit := fun w => List.replicate (G w).length ()
  refine ⟨Alg', DivStackProg.polyTimeComputable_unit_of_tok G hG hG_rep, ?_⟩
  intro I _ hIn
  obtain ⟨h_fst, h_snd⟩ := h_save_spec I.encode
  have hp : DivStackProg.leadOnes I.encode = I.n :=
    ScDisjointCopiesEncodeMap.leadOnes_replicate_append I.n
      (I.sets.flatMap ScDisjointCopiesEncodeMap.scBlock)
  dsimp [Alg', G, DivStackProg.f_div]
  rw [h_fst, h_snd, hp, if_pos hIn]
  simp [Function.comp_apply, ScDisjointCopiesEncodeMap.f_dup_encode]


