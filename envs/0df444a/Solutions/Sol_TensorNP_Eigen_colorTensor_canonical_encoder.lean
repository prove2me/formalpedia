-- Prove2me | solution 1 for TensorNP.Eigen.colorTensor_canonical_encoder
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T14:59:06.234294+00:00
-- url     : https://prove2.me/submissions/c366c93e-c543-4588-a769-0427e6cc5576

import Mathlib
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_StackProgPortLift
import Definitions.Def_TensorNP_Eigen_Construction
import Definitions.Def_TensorNP_Eigen_Defs
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_unary_to_encNat_stack
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Theorems.Thm_TensorAdjacencyLookup8_lookupProg_exec


/- Inlined module: UnaryCompare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def compareStore (x y left right : ℕ) (flags : List BSym) : Fin 6 → List BSym :=
  fun k => if k = 0 then List.replicate x .one else if k = 1 then List.replicate y .one
    else if k = 2 then List.replicate left .one else if k = 3 then List.replicate right .one
    else if k = 5 then flags else []

private def cancelGuard (h : Fin 6 → Option BSym) : Bool := (h 2).isSome && (h 3).isSome
private def cancelAct (_ : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 2 ∨ k = 3 then .pop else .keep
private def cancelLoop : StackProg (Fin 6) BSym := .loop cancelGuard (.act cancelAct)

private lemma cancel_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct cancelAct (compareStore x y (left + 1) (right + 1) flags) =
      compareStore x y left right flags := by
  funext k
  fin_cases k <;> rfl

private lemma cancel_exec (x y left right : ℕ) (flags : List BSym) :
    cancelLoop.Exec (compareStore x y left right flags)
      (compareStore x y (left - right) (right - left) flags) (3 * min left right + 1) := by
  induction left generalizing right with
  | zero =>
      simpa [cancelLoop, cancelGuard, compareStore] using
        (StackProg.Exec.loopFalse (p := .act cancelAct)
          (s := compareStore x y 0 right flags) (by simp [cancelGuard, compareStore]))
  | succ left ih =>
      cases right with
      | zero =>
          simpa [cancelLoop, cancelGuard, compareStore] using
            (StackProg.Exec.loopFalse (p := .act cancelAct)
              (s := compareStore x y (left + 1) 0 flags) (by simp [cancelGuard, compareStore]))
      | succ right =>
          have hg : cancelGuard (fun k => (compareStore x y (left + 1) (right + 1) flags k).head?) = true := by rfl
          have ha : (StackProg.act cancelAct).Exec (compareStore x y (left + 1) (right + 1) flags)
              (compareStore x y left right flags) 1 := by
            simpa only [cancel_step] using (StackProg.Exec.act cancelAct
              (compareStore x y (left + 1) (right + 1) flags))
          have he := StackProg.Exec.loopTrue hg ha (ih right)
          simpa [cancelLoop, Nat.succ_sub_succ_eq_sub, Nat.succ_min_succ, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

private def ltFlag (left right : ℕ) : BSym :=
  if left = 0 ∧ 0 < right then .one else .zero

private def eqFlag (left right : ℕ) : BSym :=
  if left = 0 ∧ right = 0 then .one else .zero

private def ltAct (h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push (if (h 2).isNone && (h 3).isSome then .one else .zero) else .keep

private def eqAct (h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push (if (h 2).isNone && (h 3).isNone then .one else .zero) else .keep

private lemma lt_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct ltAct (compareStore x y left right flags) =
      compareStore x y left right (ltFlag left right :: flags) := by
  cases left <;> cases right <;> funext k <;> fin_cases k <;> rfl

private lemma eq_step (x y left right : ℕ) (flags : List BSym) :
    StackProg.applyAct eqAct (compareStore x y left right flags) =
      compareStore x y left right (eqFlag left right :: flags) := by
  cases left <;> cases right <;> funext k <;> fin_cases k <;> rfl

private def compareProgram : StackProg (Fin 6) BSym :=
  .seq (copyProg 0 2 4) (.seq (copyProg 1 3 4)
    (.seq cancelLoop (.seq (.act ltAct) (.act eqAct))))

theorem unary_compare_machine : ∃ p : StackProg (Fin 6) BSym, ∀ x y : ℕ, ∃ steps,
    p.Exec (compareStore x y 0 0 [])
      (compareStore x y (x-y) (y-x)
        [if x=y then BSym.one else .zero, if x<y then BSym.one else .zero]) steps ∧
    steps ≤ 10 * (x + y + 2) := by
  refine ⟨compareProgram, ?_⟩
  intro x y
  have he1 : (copyProg 0 2 4).Exec (compareStore x y 0 0 [])
      (compareStore x y x 0 []) (6 * x + 3) := by
    have he := stack_copy (0 : Fin 6) 2 4 (by decide) (by decide) (by decide)
      (compareStore x y 0 0 []) (by rfl)
    have heq : Function.update (compareStore x y 0 0 []) 2
        ((compareStore x y 0 0 []) 0 ++ (compareStore x y 0 0 []) 2) =
        compareStore x y x 0 [] := by
      funext k
      fin_cases k <;> simp [compareStore, Function.update]
    rw [heq] at he
    simpa [compareStore] using he
  have he2 : (copyProg 1 3 4).Exec (compareStore x y x 0 [])
      (compareStore x y x y []) (6 * y + 3) := by
    have he := stack_copy (1 : Fin 6) 3 4 (by decide) (by decide) (by decide)
      (compareStore x y x 0 []) (by rfl)
    have heq : Function.update (compareStore x y x 0 []) 3
        ((compareStore x y x 0 []) 1 ++ (compareStore x y x 0 []) 3) =
        compareStore x y x y [] := by
      funext k
      fin_cases k <;> simp [compareStore, Function.update]
    rw [heq] at he
    simpa [compareStore] using he
  have he3 := cancel_exec x y x y []
  have he4 : (StackProg.act ltAct).Exec (compareStore x y (x-y) (y-x) [])
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)]) 1 := by
    simpa only [lt_step] using (StackProg.Exec.act ltAct (compareStore x y (x-y) (y-x) []))
  have he5 : (StackProg.act eqAct).Exec
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)])
      (compareStore x y (x-y) (y-x) [eqFlag (x-y) (y-x), ltFlag (x-y) (y-x)]) 1 := by
    simpa only [eq_step] using (StackProg.Exec.act eqAct
      (compareStore x y (x-y) (y-x) [ltFlag (x-y) (y-x)]))
  have hflags : [eqFlag (x-y) (y-x), ltFlag (x-y) (y-x)] =
      [if x = y then BSym.one else .zero, if x < y then BSym.one else .zero] := by
    have heq : (x-y = 0 ∧ y-x = 0) ↔ x = y := by omega
    have hlt : (x-y = 0 ∧ 0 < y-x) ↔ x < y := by omega
    simp only [eqFlag, ltFlag, heq, hlt]
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2
    (StackProg.Exec.seq he3 (StackProg.Exec.seq he4 he5)))
  refine ⟨6*x + 3 + 1 + (6*y + 3 + 1 + (3*min x y + 1 + 1 + (1 + 1 + 1))), ?_, ?_⟩
  · simpa only [compareProgram, hflags] using he
  · have hmin := Nat.min_le_left x y
    omega

end TensorNP.Encoder
end


/- Inlined module: RegisterCompare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma register_write_at {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (k : Fin 6) :
    StackProgPortLift.write r t frame (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma register_write_outside {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (l : Fin M)
    (h : ∀ k, r k ≠ l) : StackProgPortLift.write r t frame l = frame l := by
  classical
  have hex : ¬ ∃ k, r k = l := by
    rintro ⟨k, hk⟩
    exact h k hk
  simp [StackProgPortLift.write, hex]

lemma register_project_write {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) :
    StackProgPortLift.project r (StackProgPortLift.write r t frame) = t := by
  funext k
  exact register_write_at r t frame k

lemma register_write_overwrite {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (u t : Fin 6 → List A) (frame : Fin M → List A) :
    StackProgPortLift.write r u (StackProgPortLift.write r t frame) =
      StackProgPortLift.write r u frame := by
  funext l
  by_cases h : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := h
    rw [register_write_at, register_write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact h ⟨k, hk⟩
    rw [register_write_outside r u _ l hout, register_write_outside r t frame l hout,
      register_write_outside r u frame l hout]

noncomputable def registerDecode {M : ℕ} (r : Fin 6 ↪ Fin M) (l : Fin M) : Option (Fin 6) := by
  classical
  exact if h : ∃ k, r k = l then some (Classical.choose h) else none

lemma registerDecode_spec {M : ℕ} (r : Fin 6 ↪ Fin M) (l : Fin M) (k : Fin 6) :
    registerDecode r l = some k ↔ r k = l := by
  classical
  unfold registerDecode
  split
  · rename_i h
    constructor
    · intro hk
      have hchoose : Classical.choose h = k := Option.some.inj hk
      simpa only [hchoose] using Classical.choose_spec h
    · intro hk
      have hchoose : Classical.choose h = k := r.injective ((Classical.choose_spec h).trans hk.symm)
      simp only [hchoose]
  · rename_i h
    constructor
    · intro hk
      contradiction
    · intro hk
      exact False.elim (h ⟨k, hk⟩)

theorem unary_compare_framed (M : ℕ) (r : Fin 6 ↪ Fin M) :
    ∃ p : StackProg (Fin M) BSym, ∀ (x y : ℕ) (frame : Fin M → List BSym), ∃ steps,
      p.Exec (StackProgPortLift.write r (compareStore x y 0 0 []) frame)
        (StackProgPortLift.write r (compareStore x y (x - y) (y - x)
          [if x = y then BSym.one else .zero, if x < y then BSym.one else .zero]) frame) steps ∧
      steps ≤ 10 * (x + y + 2) := by
  obtain ⟨p, hp⟩ := unary_compare_machine
  refine ⟨StackProgPortLift.liftProgC r (registerDecode r) p, ?_⟩
  intro x y frame
  obtain ⟨steps, he, hb⟩ := hp x y
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec r (registerDecode r)
    (registerDecode_spec r) he (StackProgPortLift.write r (compareStore x y 0 0 []) frame)
    (register_project_write r (compareStore x y 0 0 []) frame)
  rw [register_write_overwrite] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: RegisterSpec -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

/-- Twenty-one unary registers, disjoint from immutable lists and seven work ports. -/
def regPorts : Fin 21 ↪ Fin 32 :=
  ⟨![1,2,3,6,8,9,10,11,12,13,14,15,16,17,23,24,27,28,29,30,31], by decide⟩

def regScratch (l : Fin 32) : Prop := l=18 ∨ l=19 ∨ l=20 ∨ l=21 ∨ l=22 ∨ l=25 ∨ l=26
instance (l : Fin 32) : Decidable (regScratch l) := inferInstanceAs (Decidable (_ ∨ _))

def regBase (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun l => if regScratch l then [] else frame l

noncomputable def regStore (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) : Fin 32 → List BSym :=
  StackProgPortLift.write regPorts (fun r => List.replicate (R r) .one) (regBase frame)

lemma port_write_at {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) (k : K) :
    StackProgPortLift.write r t s (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    rw [r.injective (Classical.choose_spec h)]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma port_write_outside {K L A : Type} (r : K ↪ L) (t : K → List A) (s : L → List A) (l : L)
    (h : ∀ k, r k ≠ l) : StackProgPortLift.write r t s l = s l := by
  classical
  have hn : ¬ ∃ k, r k = l := by rintro ⟨k, hk⟩; exact h k hk
  simp [StackProgPortLift.write, hn]

@[simp] lemma regStore_at (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    regStore frame R (regPorts r) = List.replicate (R r) .one :=
  port_write_at regPorts _ _ r

lemma regPorts_not_scratch (r : Fin 21) : ¬ regScratch (regPorts r) := by
  fin_cases r <;> decide

lemma regScratch_outside (l : Fin 32) (h : regScratch l) (r : Fin 21) : regPorts r ≠ l := by
  intro he
  exact regPorts_not_scratch r (he.symm ▸ h)

lemma regStore_scratch (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (l : Fin 32)
    (h : regScratch l) : regStore frame R l = [] := by
  rw [regStore, port_write_outside _ _ _ _ (regScratch_outside l h)]
  simp [regBase, h]

lemma regStore_update (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    regStore frame (Function.update R r n) =
      Function.update (regStore frame R) (regPorts r) (List.replicate n .one) := by
  classical
  funext l
  by_cases h : ∃ k, regPorts k = l
  · obtain ⟨k, rfl⟩ := h
    rw [regStore_at]
    by_cases hk : k = r
    · subst k
      simp
    · have hp : regPorts k ≠ regPorts r := fun he => hk (regPorts.injective he)
      simp [hk, hp]
  · have hout : ∀ k, regPorts k ≠ l := by rintro k hk; exact h ⟨k, hk⟩
    have hl : l ≠ regPorts r := fun he => h ⟨r, he.symm⟩
    simp only [regStore, port_write_outside _ _ _ _ hout]
    simp only [Function.update_of_ne hl]
    rw [port_write_outside _ _ _ _ hout]

def regSize (R : Fin 21 → ℕ) : ℕ := ∑ r, R r

lemma reg_le_size (R : Fin 21 → ℕ) (r : Fin 21) : R r ≤ regSize R := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

end TensorNP.Encoder
end


/- Inlined module: CounterLanguage -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

abbrev RegFile := Fin 21 → ℕ

def regCharge (R : RegFile) : ℕ := 100*(regSize R+1)

def regCompare (less : Bool) (r s : Fin 21) (R : RegFile) : Bool :=
  if less then decide (R r < R s) else decide (R r = R s)

def regNeighbor (data : List BSym) (R : RegFile) : Bool :=
  decide (data.getD (R 3*R 0+R 8) .zero = .one)

/-- A finite counter language; the sole graph operation reads the immutable adjacency table. -/
inductive RegCmd where
  | skip
  | reset (r : Fin 21)
  | inc (r : Fin 21)
  | assign (dst src : Fin 21)
  | add (dst src : Fin 21) (h : dst ≠ src)
  | sub (dst src : Fin 21) (h : dst ≠ src)
  | seq (p q : RegCmd)
  | branch (less : Bool) (r s : Fin 21) (yes no : RegCmd)
  | neighbor (yes no : RegCmd)
  | down (r : Fin 21) (body : RegCmd)

/-- The cost bounds every source action, including unary work, guards and program transfers. -/
inductive RegExec (data : List BSym) : RegCmd → RegFile → RegFile → ℕ → Prop where
  | skip (R) : RegExec data .skip R R 1
  | reset (R r) : RegExec data (.reset r) R (Function.update R r 0) (regCharge R)
  | inc (R r) : RegExec data (.inc r) R (Function.update R r (R r+1)) (regCharge R)
  | assign (R dst src) : RegExec data (.assign dst src) R (Function.update R dst (R src)) (regCharge R)
  | add (R dst src h) : RegExec data (.add dst src h) R
      (Function.update R dst (R src+R dst)) (regCharge R)
  | sub (R dst src h) : RegExec data (.sub dst src h) R
      (Function.update R dst (R dst-R src)) (regCharge R)
  | seq {p q R T U n m} : RegExec data p R T n → RegExec data q T U m →
      RegExec data (.seq p q) R U (n+1+m)
  | branch {less r s yes no R T n} :
      RegExec data (if regCompare less r s R then yes else no) R T n →
      RegExec data (.branch less r s yes no) R T (regCharge R+n)
  | neighbor {yes no R T n} : R 3 < R 0 → R 8 < R 0 → data.length = R 0*R 0 →
      RegExec data (if regNeighbor data R then yes else no) R T n →
      RegExec data (.neighbor yes no) R T (100*(R 0+1)^2+n)
  | downFalse {r body R} : R r = 0 → RegExec data (.down r body) R R 1
  | downTrue {r body R T U n m} : 0 < R r →
      RegExec data body (Function.update R r (R r-1)) T n →
      RegExec data (.down r body) T U m →
      RegExec data (.down r body) R U (n+m+5)

/-- Each field is an independently checkable implementation of one counter instruction. -/
structure RegBackend where
  keep : StackProg (Fin 32) BSym
  reset : Fin 21 → StackProg (Fin 32) BSym
  inc : Fin 21 → StackProg (Fin 32) BSym
  assign : Fin 21 → Fin 21 → StackProg (Fin 32) BSym
  add : (dst src : Fin 21) → dst ≠ src → StackProg (Fin 32) BSym
  sub : (dst src : Fin 21) → dst ≠ src → StackProg (Fin 32) BSym
  branch : Bool → Fin 21 → Fin 21 → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym
  neighbor : StackProg (Fin 32) BSym → StackProg (Fin 32) BSym → StackProg (Fin 32) BSym
  keep_ok : ∀ frame R, keep.Exec (regStore frame R) (regStore frame R) 1
  reset_ok : ∀ frame R r, ∃ n, (reset r).Exec (regStore frame R)
    (regStore frame (Function.update R r 0)) n ∧ n ≤ regCharge R
  inc_ok : ∀ frame R r, ∃ n, (inc r).Exec (regStore frame R)
    (regStore frame (Function.update R r (R r+1))) n ∧ n ≤ regCharge R
  assign_ok : ∀ frame R dst src, ∃ n, (assign dst src).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R src))) n ∧ n ≤ regCharge R
  add_ok : ∀ frame R dst src h, ∃ n, (add dst src h).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R src+R dst))) n ∧ n ≤ regCharge R
  sub_ok : ∀ frame R dst src h, ∃ n, (sub dst src h).Exec (regStore frame R)
    (regStore frame (Function.update R dst (R dst-R src))) n ∧ n ≤ regCharge R
  pop_ok : ∀ frame R r, (popProg (regPorts r)).Exec (regStore frame R)
    (regStore frame (Function.update R r (R r-1))) 1
  branch_ok : ∀ less r s yes no frame R T n,
    (if regCompare less r s R then yes else no).Exec (regStore frame R) T n →
    ∃ m, (branch less r s yes no).Exec (regStore frame R) T m ∧ m ≤ regCharge R+n
  neighbor_ok : ∀ yes no frame R T n, R 3<R 0 → R 8<R 0 → (frame 7).length=R 0*R 0 →
    (if regNeighbor (frame 7) R then yes else no).Exec (regStore frame R) T n →
    ∃ m, (neighbor yes no).Exec (regStore frame R) T m ∧ m ≤ 100*(R 0+1)^2+n

noncomputable def compileReg (B : RegBackend) : RegCmd → StackProg (Fin 32) BSym
  | .skip => B.keep
  | .reset r => B.reset r
  | .inc r => B.inc r
  | .assign dst src => B.assign dst src
  | .add dst src h => B.add dst src h
  | .sub dst src h => B.sub dst src h
  | .seq p q => .seq (compileReg B p) (compileReg B q)
  | .branch less r s yes no => B.branch less r s (compileReg B yes) (compileReg B no)
  | .neighbor yes no => B.neighbor (compileReg B yes) (compileReg B no)
  | .down r body => .loop (fun h => (h (regPorts r)).isSome)
      (.seq (popProg (regPorts r)) (compileReg B body))

private theorem regStore_guard (frame : Fin 32 → List BSym) (R : RegFile) (r : Fin 21) :
    ((regStore frame R (regPorts r)).head?).isSome = decide (0<R r) := by
  rw [regStore_at]
  cases h : R r <;> simp [List.replicate_succ]

theorem compileReg_sound (B : RegBackend) {data : List BSym} {p : RegCmd} {R T : RegFile} {n : ℕ}
    (h : RegExec data p R T n) (frame : Fin 32 → List BSym) (hdata : frame 7 = data) :
    ∃ m, (compileReg B p).Exec (regStore frame R) (regStore frame T) m ∧ m ≤ n := by
  induction h with
  | skip R => exact ⟨1, B.keep_ok frame R, le_rfl⟩
  | reset R r => exact B.reset_ok frame R r
  | inc R r => exact B.inc_ok frame R r
  | assign R dst src => exact B.assign_ok frame R dst src
  | add R dst src h => exact B.add_ok frame R dst src h
  | sub R dst src h => exact B.sub_ok frame R dst src h
  | seq hp hq ihp ihq =>
      obtain ⟨u, hu, hub⟩ := ihp
      obtain ⟨v, hv, hvb⟩ := ihq
      exact ⟨u+1+v, StackProg.Exec.seq hu hv, by omega⟩
  | @branch less r s yes no R T n hp ih =>
      obtain ⟨u, hu, hub⟩ := ih
      have hu' : (if regCompare less r s R then compileReg B yes else compileReg B no).Exec
          (regStore frame R) (regStore frame T) u := by
        split <;> simp_all
      obtain ⟨v, hv, hvb⟩ := B.branch_ok less r s _ _ frame R _ u hu'
      exact ⟨v, hv, by omega⟩
  | @neighbor yes no R T n hr hc hlen hp ih =>
      obtain ⟨u, hu, hub⟩ := ih
      have hu' : (if regNeighbor (frame 7) R then compileReg B yes else compileReg B no).Exec
          (regStore frame R) (regStore frame T) u := by
        rw [hdata]
        split <;> simp_all
      obtain ⟨v, hv, hvb⟩ := B.neighbor_ok _ _ frame R _ u hr hc (by simpa [hdata] using hlen) hu'
      exact ⟨v, hv, by omega⟩
  | @downFalse r body R hz =>
      refine ⟨1, ?_, le_rfl⟩
      apply StackProg.Exec.loopFalse
      rw [regStore_guard]
      simp [hz]
  | @downTrue r body R T U n m hpos hp hl ihp ihl =>
      obtain ⟨u, hu, hub⟩ := ihp
      obtain ⟨v, hv, hvb⟩ := ihl
      have hg : ((regStore frame R (regPorts r)).head?).isSome = true := by
        rw [regStore_guard]
        exact decide_eq_true hpos
      refine ⟨1+(1+1+u)+1+v, ?_, by omega⟩
      exact StackProg.Exec.loopTrue hg (StackProg.Exec.seq (B.pop_ok frame R r) hu) hv

end TensorNP.Encoder
end


/- Inlined module: Entries -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen Matrix Finset

namespace TensorNP.Encoder

def monomialEntry (row col a b : ℕ) : ℤ := if row = a ∧ col = b then 1 else 0

noncomputable def colorEntryInt {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) : ℤ := by
  classical
  exact ![monomialEntry p.2.val (v+p.2.val) a.val b.val - monomialEntry (2*v) (2*v) a.val b.val,
    monomialEntry (v+p.2.val) (2*v) a.val b.val - monomialEntry p.2.val p.2.val a.val b.val,
    monomialEntry p.2.val (2*v) a.val b.val - monomialEntry (v+p.2.val) (v+p.2.val) a.val b.val,
    ∑ j : Fin v, if G.Adj p.2 j then
      monomialEntry p.2.val p.2.val a.val b.val +
      monomialEntry p.2.val j.val a.val b.val + monomialEntry j.val j.val a.val b.val else 0] p.1

theorem monomialEntry_cast (v : ℕ) (row col a b : Fin (2*v+1)) :
    (monomialEntry row.val col.val a.val b.val : ℚ) = Matrix.single row col 1 a b := by
  simp [monomialEntry, Matrix.single_apply, Fin.ext_iff]

theorem colorEntryInt_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) :
    (colorEntryInt G p a b : ℚ) = colorEncoding G p a b := by
  classical
  rcases p with ⟨f, i⟩
  fin_cases f <;> simp [colorEntryInt, colorEncoding, monomialEntry,
    Matrix.single_apply, Matrix.sub_apply, Matrix.sum_apply,
    Finset.sum_filter, xVar, yVar, zVar, Fin.ext_iff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : G.Adj i j <;> simp [hij, Matrix.add_apply, Matrix.single_apply, Fin.ext_iff]

theorem realSplit_map_intCast {m n : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℤ)
    (q : Fin (m+m)) (a b : Fin (n+n)) :
    ((realSplit A q a b : ℤ) : ℚ) =
      realSplit (fun k i j => (A k i j : ℚ)) q a b := by
  cases hq : finSumFinEquiv.symm q <;>
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
        simp [realSplit, Matrix.reindex_apply, Matrix.fromBlocks, Matrix.neg_apply, hq, ha, hb]
  rfl

theorem padSystem_map_intCast {m n : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℤ) (r s : ℕ)
    (q : Fin r) (a b : Fin s) :
    ((padSystem A r s q a b : ℤ) : ℚ) =
      padSystem (fun k i j => (A k i j : ℚ)) r s q a b := by
  unfold padSystem
  split_ifs <;> simp

noncomputable def intColorEncodingFin {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (4*v) → Matrix (Fin (2*v+1)) (Fin (2*v+1)) ℤ :=
  fun q a b => colorEntryInt G (finProdFinEquiv.symm q) a b

noncomputable def intColorTensor {v : ℕ} (G : SimpleGraph (Fin v)) :
    Fin (colorSize v) → Fin (colorSize v) → Fin (colorSize v) → ℤ :=
  fun i j k => padSystem (realSplit (intColorEncodingFin G)) (colorSize v) (colorSize v) k i j

theorem intColorTensor_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    (intColorTensor G i j k : ℚ) = colorTensor G i j k := by
  have hA : (fun q a b => (intColorEncodingFin G q a b : ℚ)) = colorEncodingFin G := by
    funext q a b
    exact colorEntryInt_cast G _ a b
  have hB : (fun q a b => ((realSplit (intColorEncodingFin G) q a b : ℤ) : ℚ)) =
      realSplit (colorEncodingFin G) := by
    funext q a b
    rw [realSplit_map_intCast, hA]
  unfold intColorTensor colorTensor squareSystem
  rw [padSystem_map_intCast, hB]

end TensorNP.Encoder
end


/- Inlined module: Prefix -/
section
set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

structure PrefixResult where
  patternRest : List BSym
  inputRest : List BSym
  matched : ℕ

def prefixResult : List BSym → List BSym → PrefixResult
  | [], input => ⟨[], input, 0⟩
  | a :: pattern, [] => ⟨a :: pattern, [], 0⟩
  | a :: pattern, b :: input =>
      if a = b then
        let r := prefixResult pattern input
        ⟨r.patternRest, r.inputRest, r.matched + 1⟩
      else ⟨a :: pattern, b :: input, 0⟩

def prefixStore (pattern input status : List BSym) : Fin 3 → List BSym :=
  fun k => if k = 0 then pattern else if k = 1 then input else status

def prefixGuard (h : Fin 3 → Option BSym) : Bool :=
  (h 0).isSome && decide (h 0 = h 1)

def prefixPop (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop else .keep

def prefixLoop : StackProg (Fin 3) BSym := .loop prefixGuard (.act prefixPop)

def prefixMark (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push (if (h 0).isNone then .one else .zero) else .keep

def prefixProg : StackProg (Fin 3) BSym := .seq prefixLoop (.act prefixMark)

theorem prefixPop_step (a b : BSym) (pattern input status : List BSym) :
    StackProg.applyAct prefixPop (prefixStore (a :: pattern) (b :: input) status) =
      prefixStore pattern input status := by
  funext k
  fin_cases k <;> rfl

theorem prefixLoop_exec (pattern input status : List BSym) :
    prefixLoop.Exec (prefixStore pattern input status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest status)
      (3 * (prefixResult pattern input).matched + 1) := by
  induction pattern generalizing input with
  | nil =>
      exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore])
  | cons a pattern ih =>
      cases input with
      | nil =>
          exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore])
      | cons b input =>
          by_cases hab : a = b
          · simp only [prefixResult, if_pos hab]
            convert StackProg.Exec.loopTrue
              (test := prefixGuard) (p := .act prefixPop)
              (s := prefixStore (a :: pattern) (b :: input) status)
              (by simp [prefixGuard, prefixStore, hab])
              (show (StackProg.act prefixPop).Exec
                  (prefixStore (a :: pattern) (b :: input) status)
                  (prefixStore pattern input status) 1 from
                by simpa only [prefixPop_step] using
                  (StackProg.Exec.act prefixPop
                    (prefixStore (a :: pattern) (b :: input) status)))
              (ih input) using 1 <;> first | rfl | omega
          · simp only [prefixResult, if_neg hab]
            exact StackProg.Exec.loopFalse (by simp [prefixGuard, prefixStore, hab])

theorem prefixMark_step (pattern input status : List BSym) :
    StackProg.applyAct prefixMark (prefixStore pattern input status) =
      prefixStore pattern input ((if pattern = [] then BSym.one else .zero) :: status) := by
  cases pattern <;> funext k <;> fin_cases k <;> rfl

theorem prefixProg_exec (pattern input status : List BSym) :
    prefixProg.Exec (prefixStore pattern input status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status))
      (3 * (prefixResult pattern input).matched + 3) := by
  exact StackProg.Exec.seq (prefixLoop_exec pattern input status)
    (show (StackProg.act prefixMark).Exec
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest status)
      (prefixStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status)) 1 from
      by simpa only [prefixMark_step] using
        (StackProg.Exec.act prefixMark
          (prefixStore (prefixResult pattern input).patternRest
            (prefixResult pattern input).inputRest status)))

theorem prefixResult_matched_le (pattern input : List BSym) :
    (prefixResult pattern input).matched ≤ pattern.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simpa [prefixResult, hab] using Nat.succ_le_succ (ih input)
          · simp [prefixResult, hab]

theorem prefixResult_append (pattern tail : List BSym) :
    prefixResult pattern (pattern ++ tail) = ⟨[], tail, pattern.length⟩ := by
  induction pattern with
  | nil => rfl
  | cons a pattern ih => simp [prefixResult, ih]

theorem prefixResult_sound (pattern input : List BSym)
    (h : (prefixResult pattern input).patternRest = []) :
    input = pattern ++ (prefixResult pattern input).inputRest := by
  induction pattern generalizing input with
  | nil => rfl
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult] at h
      | cons b input =>
          by_cases hab : a = b
          · subst b
            simpa [prefixResult] using congrArg (List.cons a) (ih input (by simpa [prefixResult] using h))
          · simp [prefixResult, hab] at h

theorem prefixResult_success_iff (pattern input : List BSym) :
    (prefixResult pattern input).patternRest = [] ↔ ∃ tail, input = pattern ++ tail := by
  constructor
  · intro h
    exact ⟨_, prefixResult_sound pattern input h⟩
  · rintro ⟨tail, rfl⟩
    rw [prefixResult_append]

theorem prefixProg_complete (pattern tail status : List BSym) :
    prefixProg.Exec (prefixStore pattern (pattern ++ tail) status)
      (prefixStore [] tail (BSym.one :: status)) (3 * pattern.length + 3) := by
  simpa [prefixResult_append] using
    (prefixProg_exec pattern (pattern ++ tail) status)

theorem prefixResult_matched_le_input (pattern input : List BSym) :
    (prefixResult pattern input).matched ≤ input.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simpa [prefixResult, hab] using Nat.succ_le_succ (ih input)
          · simp [prefixResult, hab]

end TensorNP.Encoder
end


/- Inlined module: HeaderSearch -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- A successful search retains the dimension, unused fuel, and suffix. -/
structure HeaderResult where
  dimension : ℕ
  fuel : ℕ
  suffix : List BSym
  found : Bool

/-- At most fuel candidates, starting at dimension n. -/
def boundedHeader : ℕ → ℕ → List BSym → HeaderResult
  | n, 0, _ => ⟨n, 0, [], false⟩
  | n, fuel + 1, input =>
      let r := prefixResult (encNat n) input
      if r.patternRest = [] then ⟨n, fuel + 1, r.inputRest, true⟩
      else boundedHeader (n + 1) fuel input

/-- Writer ports 0--4; original input5, working suffix6, fuel7, status8; scratch9--11. -/
def headerStore (n fuel : ℕ) (input suffix : List BSym) (found : Bool) : Fin 12 → List BSym :=
  fun k => if k = 0 then List.replicate n .one else if k = 5 then input
    else if k = 6 then suffix else if k = 7 then List.replicate fuel .one
    else if k = 8 then (if found then [.one] else []) else []

def headerResultStore (r : HeaderResult) (input : List BSym) : Fin 12 → List BSym :=
  headerStore r.dimension r.fuel input r.suffix r.found

def headerGuard (h : Fin 12 → Option BSym) : Bool :=
  (h 7).isSome && !(h 8 == some BSym.one)

def headerStepResult (n fuel : ℕ) (input : List BSym) : Fin 12 → List BSym :=
  let r := prefixResult (encNat n) input
  if r.patternRest = [] then headerStore n fuel input r.inputRest true
  else headerStore (n+1) (fuel-1) input [] false

theorem headerGuard_searching (n fuel : ℕ) (input : List BSym) :
    headerGuard (fun k => (headerStore n (fuel+1) input [] false k).head?) = true := by
  simp [headerGuard, headerStore, List.replicate_succ]

theorem headerGuard_found (n fuel : ℕ) (input suffix : List BSym) :
    headerGuard (fun k => (headerStore n fuel input suffix true k).head?) = false := by
  simp [headerGuard, headerStore]

/-- A bounded candidate step yields a bounded complete search, even on malformed inputs. -/
theorem headerLoop_exec (body : StackProg (Fin 12) BSym) (B : ℕ) (input : List BSym)
    (hstep : ∀ n fuel : ℕ, 0 < fuel → n + fuel ≤ input.length + 1 →
      ∃ steps, body.Exec (headerStore n fuel input [] false)
        (headerStepResult n fuel input) steps ∧ steps ≤ B) :
    ∀ fuel n : ℕ, n + fuel ≤ input.length + 1 →
      ∃ steps, (StackProg.loop headerGuard body).Exec
        (headerStore n fuel input [] false) (headerResultStore (boundedHeader n fuel input) input) steps ∧
        steps ≤ fuel * (B + 2) + 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro n _
      refine ⟨1, ?_, by simp⟩
      exact StackProg.Exec.loopFalse (by simp [headerGuard, headerStore])
  | succ fuel ih =>
      intro n hbudget
      obtain ⟨m, hm, hmB⟩ := hstep n (fuel+1) (by omega) hbudget
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · have hm' : body.Exec (headerStore n (fuel+1) input [] false)
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true) m := by
          simpa [headerStepResult, hmatch] using hm
        have hstop : (StackProg.loop headerGuard body).Exec
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true)
            (headerStore n (fuel+1) input (prefixResult (encNat n) input).inputRest true) 1 :=
          StackProg.Exec.loopFalse (headerGuard_found _ _ _ _)
        refine ⟨1 + m + 1 + 1, ?_, ?_⟩
        · simpa [boundedHeader, hmatch, headerResultStore] using
            (StackProg.Exec.loopTrue (headerGuard_searching n fuel input) hm' hstop)
        · nlinarith
      · have hm' : body.Exec (headerStore n (fuel+1) input [] false)
            (headerStore (n+1) fuel input [] false) m := by
          simpa [headerStepResult, hmatch] using hm
        obtain ⟨r, hr, hrB⟩ := ih (n+1) (by omega)
        refine ⟨1 + m + 1 + r, ?_, ?_⟩
        · simpa [boundedHeader, hmatch] using
            (StackProg.Exec.loopTrue (headerGuard_searching n fuel input) hm' hr)
        · nlinarith

theorem boundedHeader_sound (n fuel : ℕ) (input : List BSym)
    (hfound : (boundedHeader n fuel input).found = true) :
    n ≤ (boundedHeader n fuel input).dimension ∧
      (boundedHeader n fuel input).dimension < n + fuel ∧
      input = encNat (boundedHeader n fuel input).dimension ++ (boundedHeader n fuel input).suffix := by
  induction fuel generalizing n with
  | zero => simp [boundedHeader] at hfound
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp only [boundedHeader, if_pos hmatch]
        exact ⟨le_rfl, by omega, prefixResult_sound _ _ hmatch⟩
      · have hfound' : (boundedHeader (n+1) fuel input).found = true := by
          simpa [boundedHeader, hmatch] using hfound
        obtain ⟨hlo, hhi, heq⟩ := ih (n+1) hfound'
        simp only [boundedHeader, if_neg hmatch]
        exact ⟨by omega, by omega, heq⟩

theorem boundedHeader_complete (n fuel v : ℕ) (input tail : List BSym)
    (hvlo : n ≤ v) (hvhi : v < n + fuel) (hinput : input = encNat v ++ tail) :
    (boundedHeader n fuel input).found = true := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp [boundedHeader, hmatch]
      · have hvne : v ≠ n := by
          intro heq
          subst v
          exact hmatch ((prefixResult_success_iff _ _).mpr ⟨tail, hinput⟩)
        simpa [boundedHeader, hmatch] using ih (n+1) (by omega) (by omega)

end TensorNP.Encoder
end


/- Inlined module: HeaderCodes -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def digitValue : List BSym → ℕ
  | [] => 0
  | b :: rest => 2 * digitValue rest + if b = .one then 1 else 0

theorem digitValue_bits (n : ℕ) :
    digitValue ((Nat.bits n).map (fun b => if b then BSym.one else .zero)) = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b <;> simp [digitValue, ih, Nat.bit]

theorem terminated_prefix_unique (xs ys s t : List BSym)
    (hx : ∀ a ∈ xs, a ≠ BSym.sep) (hy : ∀ a ∈ ys, a ≠ BSym.sep)
    (h : xs ++ BSym.sep :: s = ys ++ BSym.sep :: t) : xs = ys ∧ s = t := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨rfl, (List.cons.inj h).2⟩
      | cons b ys =>
          exact False.elim ((hy b (by simp)) (List.cons.inj h).1.symm)
  | cons a xs ih =>
      cases ys with
      | nil => exact False.elim ((hx a (by simp)) (List.cons.inj h).1)
      | cons b ys =>
          have hab := (List.cons.inj h).1
          subst b
          obtain ⟨hxs, hst⟩ := ih ys
            (fun b hb => hx b (by simp [hb]))
            (fun b hb => hy b (by simp [hb])) (List.cons.inj h).2
          exact ⟨congrArg (List.cons a) hxs, hst⟩

theorem encNat_prefix_unique (n m : ℕ) (s t : List BSym)
    (h : encNat n ++ s = encNat m ++ t) : n = m ∧ s = t := by
  have hdigit : ∀ n : ℕ, ∀ a ∈ (Nat.bits n).map (fun b => if b then BSym.one else .zero),
      a ≠ BSym.sep := by
    intro n a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    cases b <;> decide
  obtain ⟨hd, hst⟩ := terminated_prefix_unique
    ((Nat.bits n).map (fun b => if b then BSym.one else .zero))
    ((Nat.bits m).map (fun b => if b then BSym.one else .zero)) s t
    (hdigit n) (hdigit m) (by simpa [encNat, List.append_assoc] using h)
  exact ⟨by simpa only [digitValue_bits] using congrArg digitValue hd, hst⟩

theorem boundedHeader_canonical (n fuel v : ℕ) (input tail : List BSym)
    (hvlo : n ≤ v) (hvhi : v < n + fuel) (hinput : input = encNat v ++ tail) :
    (boundedHeader n fuel input).dimension = v ∧
      (boundedHeader n fuel input).suffix = tail ∧
      (boundedHeader n fuel input).found = true := by
  have hf := boundedHeader_complete n fuel v input tail hvlo hvhi hinput
  have hs := boundedHeader_sound n fuel input hf
  have hu := encNat_prefix_unique _ _ _ _ (hs.2.2.symm.trans hinput)
  exact ⟨hu.1, hu.2, hf⟩

end TensorNP.Encoder
end


/- Inlined module: GraphCode -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem encNats_length_ge (xs : List ℕ) : xs.length ≤ (encNats xs).length := by
  induction xs with
  | nil => simp [encNats]
  | cons n xs ih =>
      simp only [List.length_cons, encNats, List.flatMap_cons, List.length_append,
        encNat, List.length_map] at *
      omega

theorem graphCode_dimension_sq_le {v : ℕ} (G : SimpleGraph (Fin v)) :
    v * v + 1 ≤ (TensorNP.Eigen.graphCode G).length := by
  classical
  have h := encNats_length_ge ([v] ++ (List.ofFn fun i : Fin v =>
    List.ofFn fun j : Fin v => if G.Adj i j then 1 else 0).flatten)
  simpa [TensorNP.Eigen.graphCode, List.length_flatten, Function.comp_def, List.sum_ofFn] using h

theorem graphCode_dimension_le {v : ℕ} (G : SimpleGraph (Fin v)) :
    v ≤ (TensorNP.Eigen.graphCode G).length := by
  have h := graphCode_dimension_sq_le G
  have hv := Nat.le_mul_self v
  omega

open Classical in
noncomputable def graphTail {v : ℕ} (G : SimpleGraph (Fin v)) : List BSym :=
  encNats ((List.ofFn fun i : Fin v =>
    List.ofFn fun j : Fin v => if G.Adj i j then 1 else 0).flatten)

theorem graphCode_header {v : ℕ} (G : SimpleGraph (Fin v)) :
    TensorNP.Eigen.graphCode G = encNat v ++ graphTail G := by
  classical
  simp [TensorNP.Eigen.graphCode, graphTail, encNats]

theorem boundedHeader_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) :
    let w := TensorNP.Eigen.graphCode G
    (boundedHeader 0 (w.length+1) w).dimension = v ∧
      (boundedHeader 0 (w.length+1) w).suffix = graphTail G ∧
      (boundedHeader 0 (w.length+1) w).found = true := by
  exact boundedHeader_canonical _ _ v _ _ (Nat.zero_le _) (by
    have h := graphCode_dimension_le G
    omega) (graphCode_header G)

end TensorNP.Encoder
end


/- Inlined module: Bits -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

def bitCode (b : Bool) : List BSym := if b then [.one, .sep] else [.sep]

def bitsCode (bs : List Bool) : List BSym := bs.flatMap bitCode

def parseBits : ℕ → List BSym → Option (List Bool × List BSym)
  | 0, input => some ([], input)
  | k + 1, .sep :: rest => (parseBits k rest).map fun p => (false :: p.1, p.2)
  | k + 1, .one :: .sep :: rest => (parseBits k rest).map fun p => (true :: p.1, p.2)
  | _ + 1, _ => none

theorem parseBits_sound (count : ℕ) (input : List BSym) (bs : List Bool)
    (tail : List BSym) (h : parseBits count input = some (bs, tail)) :
    bs.length = count ∧ input = bitsCode bs ++ tail := by
  induction count generalizing input bs tail with
  | zero =>
      simp [parseBits] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [bitsCode]
  | succ count ih =>
      cases input with
      | nil => simp [parseBits] at h
      | cons a rest =>
          cases a with
          | zero => simp [parseBits] at h
          | minus => simp [parseBits] at h
          | sep =>
              cases hp : parseBits count rest with
              | none => simp [parseBits, hp] at h
              | some p =>
                  rcases p with ⟨bs', tail'⟩
                  simp [parseBits, hp] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨hlen, hinput⟩ := ih rest bs' tail' hp
                  simp [bitsCode, bitCode, hlen, hinput]
          | one =>
              cases rest with
              | nil => simp [parseBits] at h
              | cons a rest =>
                  cases a with
                  | zero => simp [parseBits] at h
                  | one => simp [parseBits] at h
                  | minus => simp [parseBits] at h
                  | sep =>
                      cases hp : parseBits count rest with
                      | none => simp [parseBits, hp] at h
                      | some p =>
                          rcases p with ⟨bs', tail'⟩
                          simp [parseBits, hp] at h
                          obtain ⟨rfl, rfl⟩ := h
                          obtain ⟨hlen, hinput⟩ := ih rest bs' tail' hp
                          simp [bitsCode, bitCode, hlen, hinput]

theorem bitCode_eq_encNat (b : Bool) : bitCode b = encNat (if b then 1 else 0) := by
  cases b <;> decide

theorem parseBits_complete (bs : List Bool) (tail : List BSym) :
    parseBits bs.length (bitsCode bs ++ tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bitsCode] at ih
      cases b <;> simp [bitsCode, bitCode, parseBits, ih]

theorem bitsCode_length_bounds (bs : List Bool) :
    bs.length ≤ (bitsCode bs).length ∧ (bitsCode bs).length ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [bitsCode]
  | cons b bs ih =>
      cases b <;> simp [bitsCode, bitCode] at * <;> omega

theorem bitsCode_eq_encNats (bs : List Bool) :
    bitsCode bs = encNats (bs.map (fun b => if b then 1 else 0)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bitsCode, encNats] at ih
      simp [bitsCode, encNats, bitCode_eq_encNat, ih]

end TensorNP.Encoder
end


/- Inlined module: GraphMatrix -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def flattenMatrix {n : ℕ} (f : Fin n → Fin n → Bool) : List Bool :=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem flattenMatrix_ofFn {n : ℕ} (f : Fin n → Fin n → Bool) :
    flattenMatrix f = List.ofFn (fun k : Fin (n*n) =>
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul']
  unfold flattenMatrix
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have heq : (⟨n * i.val + j.val, by nlinarith [Nat.mul_le_mul_left n i.isLt, j.isLt]⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem flattenMatrix_getD {n : ℕ} (f : Fin n → Fin n → Bool) (i j : Fin n) :
    (flattenMatrix f).getD (i.val*n+j.val) false = f i j := by
  rw [flattenMatrix_ofFn]
  have hidx : i.val*n+j.val < n*n := by
    nlinarith [Nat.mul_le_mul_left n i.isLt, j.isLt]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hidx), List.getElem_ofFn]
  have heq : (⟨i.val*n+j.val, hidx⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem flattenMatrix_length {n : ℕ} (f : Fin n → Fin n → Bool) :
    (flattenMatrix f).length = n*n := by
  rw [flattenMatrix_ofFn, List.length_ofFn]

def ValidMatrix (n : ℕ) (bs : List Bool) : Prop :=
  bs.length = n*n ∧
    (∀ i : Fin n, bs.getD (i.val*n+i.val) false = false) ∧
    ∀ i j : Fin n, bs.getD (i.val*n+j.val) false = bs.getD (j.val*n+i.val) false

def matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) : SimpleGraph (Fin n) where
  Adj i j := bs.getD (i.val*n+j.val) false = true
  symm := by
    constructor
    intro i j hij
    rw [← h.2.2 i j]
    exact hij
  loopless := by
    constructor
    intro i hi
    exact Bool.noConfusion ((h.2.1 i).symm.trans hi)

noncomputable def graphBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact flattenMatrix (fun i j => decide (G.Adj i j))

theorem graphBits_valid {n : ℕ} (G : SimpleGraph (Fin n)) : ValidMatrix n (graphBits G) := by
  classical
  refine ⟨flattenMatrix_length _, ?_, ?_⟩
  · intro i
    rw [graphBits, flattenMatrix_getD]
    simp
  · intro i j
    rw [graphBits, flattenMatrix_getD, flattenMatrix_getD]
    simp [G.adj_comm]

theorem graphTail_eq_bitsCode {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphTail G = bitsCode (graphBits G) := by
  classical
  rw [bitsCode_eq_encNats]
  simp [graphTail, graphBits, flattenMatrix, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem flattenMatrix_inverse (n : ℕ) (bs : List Bool) (hlen : bs.length = n*n) :
    flattenMatrix (fun i j : Fin n => bs.getD (i.val*n+j.val) false) = bs := by
  rw [flattenMatrix_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn, hlen]
  · intro k hk hk'
    rw [List.getElem_ofFn]
    let q : Fin (n*n) := ⟨k, by simpa only [List.length_ofFn] using hk⟩
    have heq := congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
    change (finProdFinEquiv.symm q).2.val + n*(finProdFinEquiv.symm q).1.val = k at heq
    have hidx : (finProdFinEquiv.symm q).1.val*n + (finProdFinEquiv.symm q).2.val = k := by
      nlinarith
    change bs.getD ((finProdFinEquiv.symm q).1.val*n + (finProdFinEquiv.symm q).2.val) false = bs[k]
    rw [hidx]
    exact List.getD_eq_getElem bs false hk'

theorem graphBits_matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) :
    graphBits (matrixGraph n bs h) = bs := by
  classical
  unfold graphBits
  have hf : (fun i j => decide ((matrixGraph n bs h).Adj i j)) =
      (fun i j : Fin n => bs.getD (i.val*n+j.val) false) := by
    funext i j
    simp [matrixGraph]
  rw [hf]
  exact flattenMatrix_inverse n bs h.1

theorem graphCode_matrixGraph (n : ℕ) (bs : List Bool) (h : ValidMatrix n bs) :
    TensorNP.Eigen.graphCode (matrixGraph n bs h) = encNat n ++ bitsCode bs := by
  rw [graphCode_header, graphTail_eq_bitsCode, graphBits_matrixGraph]

theorem canonicalGraph_iff (input : List BSym) :
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G) ↔
      let r := boundedHeader 0 (input.length+1) input
      r.found = true ∧ ∃ bs : List Bool,
        parseBits (r.dimension*r.dimension) r.suffix = some (bs, []) ∧ ValidMatrix r.dimension bs := by
  constructor
  · rintro ⟨n, G, rfl⟩
    obtain ⟨hdim, hsuffix, hfound⟩ := boundedHeader_graphCode G
    refine ⟨hfound, graphBits G, ?_, ?_⟩
    · rw [hdim, hsuffix, graphTail_eq_bitsCode, ← (graphBits_valid G).1]
      simpa only [List.append_nil] using parseBits_complete (graphBits G) []
    · rw [hdim]
      exact graphBits_valid G
  · rintro ⟨hfound, bs, hparse, hvalid⟩
    have hheader := (boundedHeader_sound 0 (input.length+1) input hfound).2.2
    have hbits := (parseBits_sound _ _ _ _ hparse).2
    refine ⟨_, matrixGraph _ bs hvalid, ?_⟩
    rw [graphCode_matrixGraph]
    simpa only [List.append_nil] using hheader.trans
      (congrArg (fun tail => encNat (boundedHeader 0 (input.length+1) input).dimension ++ tail) hbits)

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckSpec -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

def symmetryPrefix (n : ℕ) (data : List BSym) (i : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => decide (data.getD (i*n+j) .zero = data.getD (j*n+i) .zero) && symmetryPrefix n data i j

def matrixCheckPrefix (n : ℕ) (data : List BSym) : ℕ → Bool
  | 0 => true
  | i+1 => decide (data.getD (i*n+i) .zero = BSym.zero) &&
      symmetryPrefix n data i n && matrixCheckPrefix n data i

def checkerStore (n row col : ℕ) (data : List BSym) (good : Bool) : Fin 12 → List BSym :=
  fun k => if k = 0 then data else if k = 1 then List.replicate n .one
    else if k = 2 then List.replicate row .one else if k = 3 then List.replicate col .one
    else if k = 8 then (if good then [] else [.zero]) else []

end TensorNP.Encoder
end


/- Inlined module: BitMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def boolSym (b : Bool) : BSym := if b then .one else .zero

def bitParserStore (input fuel data status : List BSym) : Fin 4 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then fuel else if k = 2 then data else status

def bitGuard (h : Fin 4 → Option BSym) : Bool := (h 1).isSome && (h 3).isNone
def bitIsSep (h : Fin 4 → Option BSym) : Bool := h 0 == some .sep
def bitIsOne (h : Fin 4 → Option BSym) : Bool := h 0 == some .one
def bitStatusEmpty (h : Fin 4 → Option BSym) : Bool := (h 3).isNone

def bitTake (b : BSym) (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .pop else if k = 2 then .push b else .keep
def bitPop (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else .keep
def bitMark (b : BSym) (_ : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push b else .keep

def bitBody : StackProg (Fin 4) BSym :=
  .branch bitIsSep (.act (bitTake .zero))
    (.branch bitIsOne
      (.seq (.act bitPop) (.branch bitIsSep (.act (bitTake .one)) (.act (bitMark .zero))))
      (.act (bitMark .zero)))

def bitLoop : StackProg (Fin 4) BSym := .loop bitGuard bitBody

def bitProgram : StackProg (Fin 4) BSym :=
  .seq bitLoop (.branch bitStatusEmpty (.act (bitMark .one)) (.act (fun _ _ => .keep)))

lemma bitTake_apply (b a : BSym) (i f d st : List BSym) :
    StackProg.applyAct (bitTake b) (bitParserStore (a :: i) (.one :: f) d st) =
      bitParserStore i f (b :: d) st := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitTake, bitParserStore, StackAct.apply]

lemma bitPop_apply (a : BSym) (i f d st : List BSym) :
    StackProg.applyAct bitPop (bitParserStore (a :: i) f d st) = bitParserStore i f d st := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitPop, bitParserStore, StackAct.apply]

lemma bitMark_apply (b : BSym) (i f d st : List BSym) :
    StackProg.applyAct (bitMark b) (bitParserStore i f d st) =
      bitParserStore i f d (b :: st) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, bitMark, bitParserStore, StackAct.apply]

lemma bitKeep_apply (s : Fin 4 → List BSym) :
    StackProg.applyAct (fun _ _ => .keep) s = s := by
  funext k
  rfl

lemma bitBody_sep (i f d : List BSym) :
    bitBody.Exec (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.zero :: d) []) 2 := by
  have ha : (StackProg.act (bitTake .zero)).Exec
      (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.zero :: d) []) 1 := by
    simpa only [bitTake_apply] using StackProg.Exec.act (bitTake .zero)
      (bitParserStore (.sep :: i) (.one :: f) d [])
  exact StackProg.Exec.branchTrue (by simp [bitIsSep, bitParserStore]) ha

lemma bitBody_one (i f d : List BSym) :
    bitBody.Exec (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
      (bitParserStore i f (.one :: d) []) 6 := by
  have hp : (StackProg.act bitPop).Exec
      (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
      (bitParserStore (.sep :: i) (.one :: f) d []) 1 := by
    simpa only [bitPop_apply] using StackProg.Exec.act bitPop
      (bitParserStore (.one :: .sep :: i) (.one :: f) d [])
  have ht : (StackProg.act (bitTake .one)).Exec
      (bitParserStore (.sep :: i) (.one :: f) d [])
      (bitParserStore i f (.one :: d) []) 1 := by
    simpa only [bitTake_apply] using StackProg.Exec.act (bitTake .one)
      (bitParserStore (.sep :: i) (.one :: f) d [])
  have hb := StackProg.Exec.branchTrue (test := bitIsSep) (q := .act (bitMark .zero))
    (by simp [bitIsSep, bitParserStore]) ht
  have hs := StackProg.Exec.seq hp hb
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore])
    (StackProg.Exec.branchTrue (by simp [bitIsOne, bitParserStore]) hs)

lemma bitBody_bad (i f d : List BSym) (hs : i.head? ≠ some .sep)
    (ho : i.head? ≠ some .one) :
    bitBody.Exec (bitParserStore i (.one :: f) d [])
      (bitParserStore i (.one :: f) d [.zero]) 3 := by
  have ha : (StackProg.act (bitMark .zero)).Exec
      (bitParserStore i (.one :: f) d []) (bitParserStore i (.one :: f) d [.zero]) 1 := by
    simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .zero)
      (bitParserStore i (.one :: f) d [])
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore, hs])
    (StackProg.Exec.branchFalse (by simp [bitIsOne, bitParserStore, ho]) ha)

lemma bitBody_one_bad (i f d : List BSym) (hs : i.head? ≠ some .sep) :
    bitBody.Exec (bitParserStore (.one :: i) (.one :: f) d [])
      (bitParserStore i (.one :: f) d [.zero]) 6 := by
  have hp : (StackProg.act bitPop).Exec (bitParserStore (.one :: i) (.one :: f) d [])
      (bitParserStore i (.one :: f) d []) 1 := by
    simpa only [bitPop_apply] using StackProg.Exec.act bitPop
      (bitParserStore (.one :: i) (.one :: f) d [])
  have ha : (StackProg.act (bitMark .zero)).Exec
      (bitParserStore i (.one :: f) d []) (bitParserStore i (.one :: f) d [.zero]) 1 := by
    simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .zero)
      (bitParserStore i (.one :: f) d [])
  have hb := StackProg.Exec.branchFalse (test := bitIsSep) (p := .act (bitTake .one))
    (by simp [bitIsSep, bitParserStore, hs]) ha
  have hh := StackProg.Exec.seq hp hb
  exact StackProg.Exec.branchFalse (by simp [bitIsSep, bitParserStore])
    (StackProg.Exec.branchTrue (by simp [bitIsOne, bitParserStore]) hh)

def bitOutcome (r : Option (List Bool × List BSym)) (d : List BSym)
    (s : Fin 4 → List BSym) : Prop :=
  match r with
  | some (bs, tail) => s = bitParserStore tail [] ((bs.map boolSym).reverse ++ d) []
  | none => s 3 = [.zero]

def bitLoopSpec (count : ℕ) (input d : List BSym) : Prop :=
  ∃ s steps, bitLoop.Exec (bitParserStore input (List.replicate count .one) d []) s steps ∧
    steps ≤ 8 * count + 1 ∧ bitOutcome (parseBits count input) d s

lemma bitLoop_step (count : ℕ) (input d : List BSym) (b : Bool)
    (ih : bitLoopSpec count input (boolSym b :: d)) :
    bitLoopSpec (count + 1) (bitCode b ++ input) d := by
  obtain ⟨s, n, he, hn, hr⟩ := ih
  have hbody : bitBody.Exec
      (bitParserStore (bitCode b ++ input) (.one :: List.replicate count .one) d [])
      (bitParserStore input (List.replicate count .one) (boolSym b :: d) [])
      (if b then 6 else 2) := by
    cases b <;> simp [bitCode, boolSym, bitBody_sep, bitBody_one]
  have hg : bitGuard (fun k =>
      (bitParserStore (bitCode b ++ input) (.one :: List.replicate count .one) d [] k).head?) = true := by
    simp [bitGuard, bitParserStore]
  have hex := StackProg.Exec.loopTrue hg hbody he
  refine ⟨s, 1 + (if b then 6 else 2) + 1 + n, ?_, ?_, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using hex
  · cases b <;> simp_all <;> omega
  · cases hp : parseBits count input with
    | none =>
        cases b <;> simpa [bitOutcome, bitCode, parseBits, hp] using hr
    | some p =>
        rcases p with ⟨bs, tail⟩
        cases b <;> simpa [bitOutcome, bitCode, parseBits, hp, boolSym, List.reverse_cons,
          List.append_assoc] using hr

lemma bitLoop_bad (count : ℕ) (input d : List BSym)
    (hs : input.head? ≠ some .sep) (ho : input.head? ≠ some .one)
    (hparse : parseBits (count + 1) input = none) : bitLoopSpec (count + 1) input d := by
  have hf : bitLoop.Exec (bitParserStore input (.one :: List.replicate count .one) d [.zero])
      (bitParserStore input (.one :: List.replicate count .one) d [.zero]) 1 := by
    apply StackProg.Exec.loopFalse
    simp [bitGuard, bitParserStore]
  have he := StackProg.Exec.loopTrue (test := bitGuard)
    (by simp [bitGuard, bitParserStore]) (bitBody_bad input _ d hs ho) hf
  refine ⟨bitParserStore input (.one :: List.replicate count .one) d [.zero], 6, ?_, by omega, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using he
  · simp [bitOutcome, hparse, bitParserStore]

lemma bitLoop_one_bad (count : ℕ) (input d : List BSym)
    (hs : input.head? ≠ some .sep)
    (hparse : parseBits (count + 1) (.one :: input) = none) :
    bitLoopSpec (count + 1) (.one :: input) d := by
  have hf : bitLoop.Exec (bitParserStore input (.one :: List.replicate count .one) d [.zero])
      (bitParserStore input (.one :: List.replicate count .one) d [.zero]) 1 := by
    apply StackProg.Exec.loopFalse
    simp [bitGuard, bitParserStore]
  have he := StackProg.Exec.loopTrue (test := bitGuard)
    (by simp [bitGuard, bitParserStore]) (bitBody_one_bad input _ d hs) hf
  refine ⟨bitParserStore input (.one :: List.replicate count .one) d [.zero], 9, ?_, by omega, ?_⟩
  · simpa [bitLoop, List.replicate_succ] using he
  · simp [bitOutcome, hparse, bitParserStore]

theorem bitLoop_spec (count : ℕ) (input d : List BSym) : bitLoopSpec count input d := by
  induction count generalizing input d with
  | zero =>
      refine ⟨bitParserStore input [] d [], 1, ?_, by simp, ?_⟩
      · apply StackProg.Exec.loopFalse
        simp [bitGuard, bitParserStore]
      · simp [bitOutcome, parseBits]
  | succ count ih =>
      cases input with
      | nil =>
          apply bitLoop_bad count [] d <;> simp [parseBits]
      | cons a input =>
          cases a with
          | zero => apply bitLoop_bad count (.zero :: input) d <;> simp [parseBits]
          | minus => apply bitLoop_bad count (.minus :: input) d <;> simp [parseBits]
          | sep =>
              simpa [bitCode, boolSym] using bitLoop_step count input d false (ih input (.zero :: d))
          | one =>
              cases input with
              | nil => apply bitLoop_one_bad count [] d <;> simp [parseBits]
              | cons a input =>
                  cases a with
                  | zero => apply bitLoop_one_bad count (.zero :: input) d <;> simp [parseBits]
                  | one => apply bitLoop_one_bad count (.one :: input) d <;> simp [parseBits]
                  | minus => apply bitLoop_one_bad count (.minus :: input) d <;> simp [parseBits]
                  | sep =>
                      simpa [bitCode, boolSym] using bitLoop_step count input d true (ih input (.one :: d))

theorem bit_parser_machine : ∃ p : StackProg (Fin 4) BSym,
    ∀ (count : ℕ) (input : List BSym), ∃ (s : Fin 4 → List BSym) (steps : ℕ),
      p.Exec (bitParserStore input (List.replicate count .one) [] []) s steps ∧
      steps ≤ 20 * (count + 1) ∧
      (∀ (bs : List Bool) (tail : List BSym), parseBits count input = some (bs, tail) →
        s = bitParserStore tail [] ((bs.map boolSym).reverse) [.one]) ∧
      (parseBits count input = none → s 3 = [.zero]) := by
  refine ⟨bitProgram, ?_⟩
  intro count input
  obtain ⟨s, n, he, hn, hr⟩ := bitLoop_spec count input []
  cases hp : parseBits count input with
  | none =>
      have hs : s 3 = [.zero] := by simpa [bitOutcome, hp] using hr
      have hk : (StackProg.act (fun _ _ => .keep)).Exec s s 1 := by
        simpa only [bitKeep_apply] using StackProg.Exec.act (fun _ _ => .keep) s
      have hb := StackProg.Exec.branchFalse (test := bitStatusEmpty)
        (p := .act (bitMark .one)) (by simp [bitStatusEmpty, hs]) hk
      have ht := StackProg.Exec.seq he hb
      refine ⟨s, n + 1 + (1 + 1), ?_, by omega, ?_, fun _ => hs⟩
      · exact ht
      · intro bs tail h
        simp at h
  | some p =>
      rcases p with ⟨bs, tail⟩
      have hs : s = bitParserStore tail [] ((bs.map boolSym).reverse) [] := by
        simpa [bitOutcome, hp] using hr
      subst s
      have ha : (StackProg.act (bitMark .one)).Exec
          (bitParserStore tail [] ((bs.map boolSym).reverse) [])
          (bitParserStore tail [] ((bs.map boolSym).reverse) [.one]) 1 := by
        simpa only [bitMark_apply] using StackProg.Exec.act (bitMark .one)
          (bitParserStore tail [] ((bs.map boolSym).reverse) [])
      have hb := StackProg.Exec.branchTrue (test := bitStatusEmpty)
        (q := .act (fun _ _ => .keep)) (by simp [bitStatusEmpty, bitParserStore]) ha
      have ht := StackProg.Exec.seq he hb
      refine ⟨bitParserStore tail [] ((bs.map boolSym).reverse) [.one], n + 1 + (1 + 1), ?_, by omega, ?_, ?_⟩
      · exact ht
      · intro bs' tail' h
        cases h
        rfl
      · intro h
        contradiction

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckModel -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem symmetryPrefix_true_iff (n : ℕ) (data : List BSym) (i count : ℕ) :
    symmetryPrefix n data i count = true ↔
    ∀ j : ℕ, j < count → data.getD (i*n+j) .zero = data.getD (j*n+i) .zero := by
  induction count with
  | zero => simp [symmetryPrefix]
  | succ count ih =>
      simp only [symmetryPrefix, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨he, hp⟩ j hj
        by_cases h : j = count
        · simpa [h] using he
        · exact hp j (by omega)
      · intro h
        exact ⟨h count (by omega), fun j hj => h j (by omega)⟩

theorem matrixCheckPrefix_true_iff (n : ℕ) (data : List BSym) (count : ℕ) :
    matrixCheckPrefix n data count = true ↔
    ∀ i : ℕ, i < count → data.getD (i*n+i) .zero = BSym.zero ∧
      ∀ j : ℕ, j < n → data.getD (i*n+j) .zero = data.getD (j*n+i) .zero := by
  induction count with
  | zero => simp [matrixCheckPrefix]
  | succ count ih =>
      simp only [matrixCheckPrefix, Bool.and_eq_true, decide_eq_true_eq,
        symmetryPrefix_true_iff, ih]
      constructor
      · rintro ⟨⟨hd, hs⟩, hp⟩ i hi
        by_cases h : i = count
        · subst i
          exact ⟨hd, hs⟩
        · exact hp i (by omega)
      · intro h
        refine ⟨⟨(h count (by omega)).1, (h count (by omega)).2⟩, ?_⟩
        intro i hi
        exact h i (by omega)

lemma boolSym_injective : Function.Injective boolSym := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolSym]

lemma getD_map_boolSym (bs : List Bool) (k : ℕ) :
    (bs.map boolSym).getD k .zero = boolSym (bs.getD k false) := by
  simpa [boolSym] using (List.getD_map (l := bs) (d := false) (n := k) boolSym)

theorem matrixCheckPrefix_valid (n : ℕ) (bs : List Bool) (hlen : bs.length = n*n) :
    matrixCheckPrefix n (bs.map boolSym) n = true ↔ ValidMatrix n bs := by
  rw [matrixCheckPrefix_true_iff]
  constructor
  · intro h
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      have hd := (h i.val i.isLt).1
      rw [getD_map_boolSym] at hd
      exact boolSym_injective (by simpa [boolSym] using hd)
    · intro i j
      have hs := (h i.val i.isLt).2 j.val j.isLt
      rw [getD_map_boolSym, getD_map_boolSym] at hs
      exact boolSym_injective hs
  · rintro ⟨_, hd, hs⟩ i hi
    let ii : Fin n := ⟨i, hi⟩
    constructor
    · rw [getD_map_boolSym]
      simpa [boolSym] using congrArg boolSym (hd ii)
    · intro j hj
      let jj : Fin n := ⟨j, hj⟩
      rw [getD_map_boolSym, getD_map_boolSym]
      exact congrArg boolSym (hs ii jj)

end TensorNP.Encoder
end


/- Inlined module: RawEntries -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

def naturalMonomial (row col a b : ℕ) : ℕ := if row = a ∧ col = b then 1 else 0

theorem naturalMonomial_cast (row col a b : ℕ) :
    ((naturalMonomial row col a b : ℕ) : ℤ) = monomialEntry row col a b := by
  simp [naturalMonomial, monomialEntry]

def neighborCount (v : ℕ) (data : List BSym) (vertex a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => neighborCount v data vertex a b j +
      if data.getD (vertex*v+j) .zero = .one then
        naturalMonomial vertex vertex a b + naturalMonomial vertex j a b + naturalMonomial j j a b
      else 0

theorem neighborCount_sum (v : ℕ) (data : List BSym) (vertex a b count : ℕ) :
    ((neighborCount v data vertex a b count : ℕ) : ℤ) =
      ∑ j ∈ Finset.range count, if data.getD (vertex*v+j) .zero = .one then
        monomialEntry vertex vertex a b + monomialEntry vertex j a b + monomialEntry j j a b else 0 := by
  induction count with
  | zero => simp [neighborCount]
  | succ count ih => simp [neighborCount, Finset.sum_range_succ, ih, naturalMonomial_cast]

def rawPositiveCount (v : ℕ) (data : List BSym) (family vertex a b : ℕ) : ℕ :=
  if family = 0 then naturalMonomial vertex (v+vertex) a b
  else if family = 1 then naturalMonomial (v+vertex) (2*v) a b
  else if family = 2 then naturalMonomial vertex (2*v) a b
  else if family = 3 then neighborCount v data vertex a b v else 0

def rawNegativeCount (v family vertex a b : ℕ) : ℕ :=
  if family = 0 then naturalMonomial (2*v) (2*v) a b
  else if family = 1 then naturalMonomial vertex vertex a b
  else if family = 2 then naturalMonomial (v+vertex) (v+vertex) a b else 0

def rawColorEntry (v : ℕ) (data : List BSym) (family vertex a b : ℕ) : ℤ :=
  (rawPositiveCount v data family vertex a b : ℤ) - (rawNegativeCount v family vertex a b : ℤ)

noncomputable def graphData {v : ℕ} (G : SimpleGraph (Fin v)) : List BSym :=
  (graphBits G).map boolSym

open Classical in
theorem graphData_getD {v : ℕ} (G : SimpleGraph (Fin v)) (i j : Fin v) :
    (graphData G).getD (i.val*v+j.val) .zero = if G.Adj i j then BSym.one else BSym.zero := by
  classical
  simp only [graphData, getD_map_boolSym, graphBits, flattenMatrix_getD, boolSym, decide_eq_true_eq]

theorem rawColorEntry_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin 4 × Fin v) (a b : Fin (2*v+1)) :
    rawColorEntry v (graphData G) p.1.val p.2.val a.val b.val = colorEntryInt G p a b := by
  classical
  rcases p with ⟨f, i⟩
  fin_cases f <;> simp [rawColorEntry, rawPositiveCount, rawNegativeCount,
    colorEntryInt, naturalMonomial_cast]
  rw [neighborCount_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [graphData_getD]
  by_cases hij : G.Adj i j <;> simp [hij]

end TensorNP.Encoder
end


/- Inlined module: RawTensor -/
section
set_option autoImplicit false
open TensorNP.Eigen Matrix

namespace TensorNP.Encoder

def rawRealSplit (m n : ℕ) (A : ℕ → ℕ → ℕ → ℤ) (q a b : ℕ) : ℤ :=
  if q < m then
    if a < n then (if b < n then A q a b else 0)
    else (if b < n then 0 else -A q (a-n) (b-n))
  else
    if a < n then (if b < n then 0 else A (q-m) a (b-n))
    else (if b < n then A (q-m) (a-n) b else 0)

theorem realSplit_raw {m n : ℕ} (A : ℕ → ℕ → ℕ → ℤ)
    (q : Fin (m+m)) (a b : Fin (n+n)) :
    realSplit (fun (q : Fin m) (a b : Fin n) => A q.val a.val b.val) q a b =
      rawRealSplit m n A q.val a.val b.val := by
  have hsum (l : ℕ) (i : Fin l) :
      finSumFinEquiv.symm (i.addNat l) = Sum.inr i := by
    have hi : i.addNat l = Fin.natAdd l i := by
      apply Fin.ext
      simp [Nat.add_comm]
    rw [hi, finSumFinEquiv_symm_apply_natAdd]
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective q
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  cases q <;> cases a <;> cases b <;>
    simp [realSplit, rawRealSplit, Matrix.reindex_apply, Matrix.fromBlocks, hsum]
  rfl


def rawPadSystem (m n : ℕ) (A : ℕ → ℕ → ℕ → ℤ) (r q a b : ℕ) : ℤ :=
  if q < m then (if a < n ∧ b < n then A q a b else 0)
  else if q+1 = r then (if n ≤ a ∧ a=b then 1 else 0) else 0

theorem padSystem_raw {m n : ℕ} (A : ℕ → ℕ → ℕ → ℤ) (r s : ℕ)
    (q : Fin r) (a b : Fin s) :
    padSystem (fun (q : Fin m) (a b : Fin n) => A q.val a.val b.val) r s q a b =
      rawPadSystem m n A r q.val a.val b.val := by
  simp [padSystem, rawPadSystem, Fin.ext_iff]

def rawColorMatrix (v : ℕ) (data : List ProjSchedTW.Complexity.BSym) (q a b : ℕ) : ℤ :=
  rawColorEntry v data (q/v) (q%v) a b

theorem rawColorMatrix_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (q : Fin (4*v)) (a b : Fin (2*v+1)) :
    rawColorMatrix v (graphData G) q.val a.val b.val = intColorEncodingFin G q a b := by
  unfold rawColorMatrix intColorEncodingFin
  simpa [finProdFinEquiv] using rawColorEntry_graphData G (finProdFinEquiv.symm q) a b

def rawTensorEntry (v : ℕ) (data : List ProjSchedTW.Complexity.BSym) (i j k : ℕ) : ℤ :=
  rawPadSystem (4*v+4*v) (2*v+1+(2*v+1))
    (rawRealSplit (4*v) (2*v+1) (rawColorMatrix v data)) (8*v+2) k i j

theorem rawTensorEntry_graphData {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    rawTensorEntry v (graphData G) i.val j.val k.val = intColorTensor G i j k := by
  have hA : (fun (q : Fin (4*v)) (a b : Fin (2*v+1)) =>
      rawColorMatrix v (graphData G) q.val a.val b.val) = intColorEncodingFin G := by
    funext q a b
    exact rawColorMatrix_graphData G q a b
  have hB : (fun (q : Fin (4*v+4*v)) (a b : Fin (2*v+1+(2*v+1))) =>
      rawRealSplit (4*v) (2*v+1) (rawColorMatrix v (graphData G)) q.val a.val b.val) =
      realSplit (intColorEncodingFin G) := by
    funext q a b
    rw [← realSplit_raw, hA]
  have hpad := padSystem_raw (m := 4*v+4*v) (n := 2*v+1+(2*v+1))
    (rawRealSplit (4*v) (2*v+1) (rawColorMatrix v (graphData G)))
    (colorSize v) (colorSize v) k i j
  rw [hB] at hpad
  exact hpad.symm

theorem rawTensorEntry_cast {v : ℕ} (G : SimpleGraph (Fin v))
    (i j k : Fin (colorSize v)) :
    (rawTensorEntry v (graphData G) i.val j.val k.val : ℚ) = colorTensor G i j k := by
  rw [rawTensorEntry_graphData, intColorTensor_cast]

end TensorNP.Encoder
end


/- Inlined module: RawCountBounds -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem naturalMonomial_le (row col a b : ℕ) : naturalMonomial row col a b ≤ 1 := by
  unfold naturalMonomial
  split <;> omega

theorem neighborCount_le (v : ℕ) (data : List BSym) (vertex a b count : ℕ) :
    neighborCount v data vertex a b count ≤ 3 * count := by
  induction count with
  | zero => simp [neighborCount]
  | succ count ih =>
      have h1 := naturalMonomial_le vertex vertex a b
      have h2 := naturalMonomial_le vertex count a b
      have h3 := naturalMonomial_le count count a b
      simp only [neighborCount]
      split <;> omega

theorem rawPositiveCount_le (v : ℕ) (data : List BSym) (family vertex a b : ℕ) :
    rawPositiveCount v data family vertex a b ≤ 3*v+1 := by
  have h0 := naturalMonomial_le vertex (v+vertex) a b
  have h1 := naturalMonomial_le (v+vertex) (2*v) a b
  have h2 := naturalMonomial_le vertex (2*v) a b
  have h3 := neighborCount_le v data vertex a b v
  unfold rawPositiveCount
  split_ifs <;> omega

theorem rawNegativeCount_le (v family vertex a b : ℕ) :
    rawNegativeCount v family vertex a b ≤ 1 := by
  have h0 := naturalMonomial_le (2*v) (2*v) a b
  have h1 := naturalMonomial_le vertex vertex a b
  have h2 := naturalMonomial_le (v+vertex) (v+vertex) a b
  unfold rawNegativeCount
  split_ifs <;> omega

theorem rawCounts_le (v : ℕ) (data : List BSym) (family vertex a b : ℕ) :
    rawPositiveCount v data family vertex a b + rawNegativeCount v family vertex a b ≤ 3*v+2 := by
  have hp := rawPositiveCount_le v data family vertex a b
  have hn := rawNegativeCount_le v family vertex a b
  omega

end TensorNP.Encoder
end


/- Inlined module: EntryCounts -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def countValue (p : ℕ × ℕ) : ℤ := (p.1 : ℤ)-(p.2 : ℤ)
def swapCounts (p : ℕ × ℕ) : ℕ × ℕ := (p.2,p.1)

def colorCounts (v : ℕ) (data : List BSym) (q a b : ℕ) : ℕ × ℕ :=
  (rawPositiveCount v data (q/v) (q%v) a b, rawNegativeCount v (q/v) (q%v) a b)

def splitCounts (m n : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ) (q a b : ℕ) : ℕ × ℕ :=
  if q < m then
    if a<n then (if b<n then A q a b else (0,0))
    else (if b<n then (0,0) else swapCounts (A q (a-n) (b-n)))
  else
    if a<n then (if b<n then (0,0) else A (q-m) a (b-n))
    else (if b<n then A (q-m) (a-n) b else (0,0))

def tensorCounts (v : ℕ) (data : List BSym) (i j k : ℕ) : ℕ × ℕ :=
  if k<8*v then
    if i<4*v+2 ∧ j<4*v+2 then splitCounts (4*v) (2*v+1) (colorCounts v data) k i j else (0,0)
  else if k+1=8*v+2 then (if 4*v+2 ≤ i ∧ i=j then (1,0) else (0,0)) else (0,0)

theorem splitCounts_value (m n : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ) (q a b : ℕ) :
    countValue (splitCounts m n A q a b) = rawRealSplit m n (fun q a b => countValue (A q a b)) q a b := by
  unfold splitCounts rawRealSplit
  split_ifs <;> simp [countValue, swapCounts]

theorem tensorCounts_value (v : ℕ) (data : List BSym) (i j k : ℕ) :
    countValue (tensorCounts v data i j k) = rawTensorEntry v data i j k := by
  have hA : (fun q a b => countValue (colorCounts v data q a b)) = rawColorMatrix v data := rfl
  unfold rawTensorEntry rawPadSystem
  have hm : 4*v+4*v=8*v := by omega
  have hn : 2*v+1+(2*v+1)=4*v+2 := by omega
  rw [hm, hn]
  unfold tensorCounts
  split_ifs
  · rw [splitCounts_value, hA]
  all_goals rfl

/-- Three bounded subtractions replace variable division in the executable evaluator. -/
def familyDecode (v q : ℕ) : ℕ × ℕ :=
  if q<v then (0,q) else if q-v<v then (1,q-v)
  else if q-v-v<v then (2,q-v-v) else (3,q-v-v-v)

theorem familyDecode_correct {v q : ℕ} (hq : q<4*v) : familyDecode v q = (q/v,q%v) := by
  unfold familyDecode
  split_ifs with h0 h1 h2
  · rw [Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0]
  · have hd : q/v=1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hd, Nat.mod_eq_sub_mul_div]
  · have hd : q/v=2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, Nat.mod_eq_sub_mul_div, hd]
    congr 1
    omega
  · have hd : q/v=3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, Nat.mod_eq_sub_mul_div, hd]
    congr 1
    omega

theorem familyDecode_vertex_lt {v q : ℕ} (hq : q<4*v) : (familyDecode v q).2 < v := by
  rw [familyDecode_correct hq]
  exact Nat.mod_lt _ (by omega)

end TensorNP.Encoder
end


/- Inlined module: EntryCounterSteps -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma reg_update_self (R : RegFile) (r : Fin 21) : Function.update R r (R r) = R := by
  funext k
  by_cases hk : k=r <;> simp [hk]

lemma regSize_update_le (R : RegFile) (r : Fin 21) (n : ℕ) :
    regSize (Function.update R r n) ≤ regSize R+n := by
  calc
    _ ≤ ∑ k : Fin 21, (R k + if k=r then n else 0) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k=r <;> simp [hk]
    _ = regSize R+n := by simp [regSize, Finset.sum_add_distrib]

def monoInc (target row col : Fin 21) : RegCmd :=
  .branch false row 1 (.branch false col 2 (.inc target) .skip) .skip

theorem monoInc_exec (data : List BSym) (R : RegFile) (target row col : Fin 21) :
    ∃ steps, RegExec data (monoInc target row col) R
      (Function.update R target (R target+naturalMonomial (R row) (R col) (R 1) (R 2))) steps ∧
      steps ≤ 3*regCharge R+2 := by
  by_cases hr : R row=R 1
  · by_cases hc : R col=R 2
    · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
        (less := false) (r := row) (s := 1)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (yes := .inc target) (no := .skip) (less := false) (r := col) (s := 2)
            (by simpa [regCompare, hc] using RegExec.inc (data := data) R target)))
      refine ⟨regCharge R+(regCharge R+regCharge R), ?_, by omega⟩
      simpa [monoInc, naturalMonomial, hr, hc] using he
    · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
        (less := false) (r := row) (s := 1)
        (by simpa [regCompare, hr] using
          (RegExec.branch (data := data) (R := R) (yes := .inc target) (no := .skip) (less := false) (r := col) (s := 2)
            (by simpa [regCompare, hc] using RegExec.skip (data := data) R)))
      refine ⟨regCharge R+(regCharge R+1), ?_, by omega⟩
      simpa [monoInc, naturalMonomial, hr, hc, reg_update_self] using he
  · have he := RegExec.branch (data := data) (R := R) (yes := .branch false col 2 (.inc target) .skip) (no := .skip)
      (less := false) (r := row) (s := 1)
      (by simpa [regCompare, hr] using RegExec.skip (data := data) R)
    refine ⟨regCharge R+1, ?_, by omega⟩
    simpa [monoInc, naturalMonomial, hr, reg_update_self] using he

end TensorNP.Encoder
end


/- Inlined module: ColorDispatch -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def qState (R : RegFile) (q : ℕ) : RegFile := Function.update R 3 q

def decodedFamily (v q : ℕ) : Fin 4 :=
  if q<v then 0 else if q-v<v then 1 else if q-v-v<v then 2 else 3

def colorDispatch (body : Fin 4 → RegCmd) : RegCmd :=
  .branch true 3 0 (body 0) (.seq (.sub 3 0 (by decide))
    (.branch true 3 0 (body 1) (.seq (.sub 3 0 (by decide))
      (.branch true 3 0 (body 2) (.seq (.sub 3 0 (by decide)) (body 3))))))

lemma qState_size_le (R : RegFile) (q : ℕ) (hq : q≤R 3) : regSize (qState R q)≤regSize R := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k=3 <;> simp [qState, hk, hq]

lemma qState_charge_le (R : RegFile) (q : ℕ) (hq : q≤R 3) : regCharge (qState R q)≤regCharge R :=
  Nat.mul_le_mul_left 100 (Nat.add_le_add_right (qState_size_le R q hq) 1)

lemma dispatchYes_exec (data : List BSym) (R : RegFile) (q : ℕ) (yes no : RegCmd)
    (T : RegFile) (n : ℕ) (hq : q<R 0) (he : RegExec data yes (qState R q) T n) :
    RegExec data (.branch true 3 0 yes no) (qState R q) T (regCharge (qState R q)+n) := by
  apply RegExec.branch
  simpa [regCompare, qState, hq] using he

lemma dispatchNo_exec (data : List BSym) (R : RegFile) (q : ℕ) (yes rest : RegCmd)
    (T : RegFile) (n : ℕ) (hq : ¬q<R 0)
    (he : RegExec data rest (qState R (q-R 0)) T n) :
    RegExec data (.branch true 3 0 yes (.seq (.sub 3 0 (by decide)) rest)) (qState R q) T
      (regCharge (qState R q)+(regCharge (qState R q)+1+n)) := by
  have hsub : RegExec data (.sub 3 0 (by decide)) (qState R q) (qState R (q-R 0))
      (regCharge (qState R q)) := by
    simpa [qState] using RegExec.sub (data := data) (qState R q) 3 0 (by decide)
  apply RegExec.branch
  simpa [regCompare, qState, hq] using RegExec.seq hsub he

lemma decodedFamily_val (v q : ℕ) : (decodedFamily v q).val = (familyDecode v q).1 := by
  unfold decodedFamily familyDecode
  split_ifs <;> rfl

theorem colorDispatch_exec (data : List BSym) (R : RegFile) (body : Fin 4 → RegCmd)
    (post : Fin 4 → ℕ → RegFile) (B : ℕ) (hq : R 3<4*R 0)
    (hbody : ∀ (f : Fin 4) (q : ℕ), q<R 0 → ∃ n,
      RegExec data (body f) (qState R q) (post f q) n ∧ n≤B) :
    ∃ n, RegExec data (colorDispatch body) R
      (post (decodedFamily (R 0) (R 3)) (familyDecode (R 0) (R 3)).2) n ∧
      n≤B+1000*(regSize R+1) := by
  let q := R 3
  let v := R 0
  let tail2 := RegCmd.branch true 3 0 (body 2) (.seq (.sub 3 0 (by decide)) (body 3))
  let tail1 := RegCmd.branch true 3 0 (body 1) (.seq (.sub 3 0 (by decide)) tail2)
  have hs0 : qState R q = R := reg_update_self R 3
  have hb0 : regCharge (qState R q)≤regCharge R := qState_charge_le R q le_rfl
  have hb1 : regCharge (qState R (q-v))≤regCharge R := qState_charge_le R (q-v) (Nat.sub_le _ _)
  have hb2 : regCharge (qState R (q-v-v))≤regCharge R :=
    qState_charge_le R (q-v-v) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  let c0 := regCharge R
  let c1 := regCharge (qState R (q-v))
  let c2 := regCharge (qState R (q-v-v))
  by_cases h0 : q<v
  · obtain ⟨n, he, hb⟩ := hbody 0 q h0
    have he' := dispatchYes_exec data R q (body 0) (.seq (.sub 3 0 (by decide)) tail1) _ n h0 he
    rw [hs0] at he'
    refine ⟨c0+n, ?_, ?_⟩
    · simpa [c0, c1, c2, colorDispatch, tail1, tail2, decodedFamily, familyDecode, q, v, h0] using he'
    · simp only [c0, regCharge] at hb0 ⊢
      omega
  · by_cases h1 : q-v<v
    · obtain ⟨n, he, hb⟩ := hbody 1 (q-v) h1
      have he1 := dispatchYes_exec data R (q-v) (body 1) (.seq (.sub 3 0 (by decide)) tail2) _ n h1 he
      have he0 := dispatchNo_exec data R q (body 0) tail1 _ _ h0 he1
      rw [hs0] at he0
      refine ⟨c0+(c0+1+(c1+n)), ?_, ?_⟩
      · simpa [c0, c1, c2, colorDispatch, tail1, tail2, decodedFamily, familyDecode, q, v, h0, h1] using he0
      · simp only [c0, c1, regCharge] at hb0 hb1 ⊢
        omega
    · by_cases h2 : q-v-v<v
      · obtain ⟨n, he, hb⟩ := hbody 2 (q-v-v) h2
        have he2 := dispatchYes_exec data R (q-v-v) (body 2) (.seq (.sub 3 0 (by decide)) (body 3)) _ n h2 he
        have he1 := dispatchNo_exec data R (q-v) (body 1) tail2 _ _ h1 he2
        have he0 := dispatchNo_exec data R q (body 0) tail1 _ _ h0 he1
        rw [hs0] at he0
        refine ⟨c0+(c0+1+(c1+(c1+1+(c2+n)))), ?_, ?_⟩
        · simpa [c0, c1, c2, colorDispatch, tail1, tail2, decodedFamily, familyDecode, q, v, h0, h1, h2] using he0
        · simp only [c0, c1, c2, regCharge] at hb0 hb1 hb2 ⊢
          omega
      · obtain ⟨n, he, hb⟩ := hbody 3 (q-v-v-v) (by dsimp [q,v] at *; omega)
        have he2 := dispatchNo_exec data R (q-v-v) (body 2) (body 3) _ n h2 he
        have he1 := dispatchNo_exec data R (q-v) (body 1) tail2 _ _ h1 he2
        have he0 := dispatchNo_exec data R q (body 0) tail1 _ _ h0 he1
        rw [hs0] at he0
        refine ⟨c0+(c0+1+(c1+(c1+1+(c2+(c2+1+n))))), ?_, ?_⟩
        · simpa [c0, c1, c2, colorDispatch, tail1, tail2, decodedFamily, familyDecode, q, v, h0, h1, h2] using he0
        · simp only [c0, c1, c2, regCharge] at hb0 hb1 hb2 ⊢
          omega

end TensorNP.Encoder
end


/- Inlined module: NeighborCounter -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def neighborTriple : RegCmd :=
  .seq (monoInc 14 3 3) (.seq (monoInc 14 3 8) (monoInc 14 8 8))

def neighborDelta (data : List BSym) (R : RegFile) : ℕ :=
  if data.getD (R 3*R 0+R 8) .zero = .one then
    naturalMonomial (R 3) (R 3) (R 1) (R 2) +
    naturalMonomial (R 3) (R 8) (R 1) (R 2) +
    naturalMonomial (R 8) (R 8) (R 1) (R 2) else 0

def neighborBody : RegCmd := .neighbor neighborTriple .skip

theorem neighborTriple_exec (data : List BSym) (R : RegFile) :
    ∃ steps, RegExec data neighborTriple R
      (Function.update R 14 (R 14 + naturalMonomial (R 3) (R 3) (R 1) (R 2) +
        naturalMonomial (R 3) (R 8) (R 1) (R 2) +
        naturalMonomial (R 8) (R 8) (R 1) (R 2))) steps ∧
      steps ≤ 2000*(regSize R+2) := by
  let a := naturalMonomial (R 3) (R 3) (R 1) (R 2)
  let b := naturalMonomial (R 3) (R 8) (R 1) (R 2)
  let c := naturalMonomial (R 8) (R 8) (R 1) (R 2)
  let S1 := Function.update R 14 (R 14+a)
  let S2 := Function.update R 14 (R 14+a+b)
  let S3 := Function.update R 14 (R 14+a+b+c)
  obtain ⟨m1, he1, hb1⟩ := monoInc_exec data R 14 3 3
  change RegExec data (monoInc 14 3 3) R S1 m1 at he1
  obtain ⟨m2, he2, hb2⟩ := monoInc_exec data S1 14 3 8
  have hu2 : Function.update S1 14
      (S1 14+naturalMonomial (S1 3) (S1 8) (S1 1) (S1 2)) = S2 := by
    funext k
    by_cases hk : k=14 <;> simp [S1, S2, b, hk]
  rw [hu2] at he2
  obtain ⟨m3, he3, hb3⟩ := monoInc_exec data S2 14 8 8
  have hu3 : Function.update S2 14
      (S2 14+naturalMonomial (S2 8) (S2 8) (S2 1) (S2 2)) = S3 := by
    funext k
    by_cases hk : k=14 <;> simp [S2, S3, c, hk]
  rw [hu3] at he3
  refine ⟨m1+1+(m2+1+m3), RegExec.seq he1 (RegExec.seq he2 he3), ?_⟩
  have ha : a≤1 := naturalMonomial_le _ _ _ _
  have hb : b≤1 := naturalMonomial_le _ _ _ _
  have hsize1 : regSize S1 ≤ regSize R+R 14+a := by
    simpa [S1, Nat.add_assoc] using regSize_update_le R 14 (R 14+a)
  have hsize2 : regSize S2 ≤ regSize R+R 14+a+b := by
    simpa [S2, Nat.add_assoc] using regSize_update_le R 14 (R 14+a+b)
  have hp := reg_le_size R 14
  unfold regCharge at hb1 hb2 hb3
  omega

theorem neighborDelta_le (data : List BSym) (R : RegFile) : neighborDelta data R≤3 := by
  have ha := naturalMonomial_le (R 3) (R 3) (R 1) (R 2)
  have hb := naturalMonomial_le (R 3) (R 8) (R 1) (R 2)
  have hc := naturalMonomial_le (R 8) (R 8) (R 1) (R 2)
  unfold neighborDelta
  split <;> omega

theorem neighborBody_exec (data : List BSym) (R : RegFile)
    (hr : R 3<R 0) (hc : R 8<R 0) (hlen : data.length=R 0*R 0) :
    ∃ steps, RegExec data neighborBody R (Function.update R 14 (R 14+neighborDelta data R)) steps ∧
      steps ≤ 100*(R 0+1)^2+2000*(regSize R+2) := by
  by_cases ha : data.getD (R 3*R 0+R 8) .zero = .one
  · obtain ⟨n, he, hb⟩ := neighborTriple_exec data R
    have he' : RegExec data (if regNeighbor data R then neighborTriple else .skip) R
        (Function.update R 14 (R 14+neighborDelta data R)) n := by
      simpa only [regNeighbor, decide_eq_true_eq, neighborDelta, if_pos ha, Nat.add_assoc] using he
    exact ⟨100*(R 0+1)^2+n, RegExec.neighbor hr hc hlen he', by omega⟩
  · have he' : RegExec data (if regNeighbor data R then neighborTriple else .skip) R
        (Function.update R 14 (R 14+neighborDelta data R)) 1 := by
      simpa only [regNeighbor, decide_eq_true_eq, neighborDelta, if_neg ha, Nat.add_zero, reg_update_self] using RegExec.skip (data := data) R
    exact ⟨100*(R 0+1)^2+1, RegExec.neighbor hr hc hlen he', by omega⟩

def neighborFrame (base : RegFile) (count total : ℕ) : RegFile :=
  Function.update (Function.update base 8 count) 14 total

lemma neighborFrame_size (base : RegFile) (count total : ℕ) :
    regSize (neighborFrame base count total) ≤ regSize base+count+total := by
  exact (regSize_update_le _ 14 total).trans (Nat.add_le_add_right (regSize_update_le base 8 count) total)

lemma neighborFrame_delta (data : List BSym) (base : RegFile) (count total : ℕ) :
    neighborDelta data (neighborFrame base count total) =
      if data.getD (base 3*base 0+count) .zero = .one then
        naturalMonomial (base 3) (base 3) (base 1) (base 2) +
        naturalMonomial (base 3) count (base 1) (base 2) +
        naturalMonomial count count (base 1) (base 2) else 0 := by
  simp [neighborDelta, neighborFrame]

theorem neighborLoop_exec (data : List BSym) (base : RegFile) (cap : ℕ)
    (hr : base 3<base 0) (hlen : data.length=base 0*base 0) :
    ∀ count : ℕ, count≤base 0 → ∀ total : ℕ, total+3*count≤cap → ∃ steps,
      RegExec data (.down 8 neighborBody) (neighborFrame base count total)
        (neighborFrame base 0 (total+neighborCount (base 0) data (base 3) (base 1) (base 2) count)) steps ∧
      steps ≤ count*(100*(base 0+1)^2+2000*(regSize base+base 0+cap+2)+5)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ total _
      refine ⟨1, ?_, by simp⟩
      simpa [neighborCount] using
        (RegExec.downFalse (data := data) (r := 8) (body := neighborBody)
          (R := neighborFrame base 0 total) (by simp [neighborFrame]))
  | succ count ih =>
      intro hc total hcap
      let R := neighborFrame base count total
      let delta := neighborDelta data R
      have hdelta : delta≤3 := neighborDelta_le data R
      obtain ⟨n, he, hb⟩ := neighborBody_exec data R
        (by simpa [R, neighborFrame] using hr)
        (by simpa [R, neighborFrame] using (show count<base 0 by omega))
        (by simpa [R, neighborFrame] using hlen)
      have hu : Function.update R 14 (R 14+neighborDelta data R) =
          neighborFrame base count (total+delta) := by
        funext k
        by_cases hk : k=14 <;> simp [R, neighborFrame, delta, hk]
      rw [hu] at he
      obtain ⟨m, hm, hmb⟩ := ih (by omega) (total+delta) (by omega)
      have hpop : Function.update (neighborFrame base (count+1) total) 8
          (neighborFrame base (count+1) total 8-1) = R := by
        funext k
        by_cases hk8 : k=8 <;> by_cases hk14 : k=14 <;> simp_all [R, neighborFrame]
      have he' := RegExec.downTrue (r := 8) (body := neighborBody)
        (R := neighborFrame base (count+1) total) (by simp [neighborFrame])
        (hpop ▸ he) hm
      have hout : total+delta+neighborCount (base 0) data (base 3) (base 1) (base 2) count =
          total+neighborCount (base 0) data (base 3) (base 1) (base 2) (count+1) := by
        rw [neighborCount]
        change total+neighborDelta data (neighborFrame base count total)+_ = _
        rw [neighborFrame_delta]
        omega
      rw [hout] at he'
      refine ⟨n+m+5, he', ?_⟩
      have hs := neighborFrame_size base count total
      have htotal : total≤cap := by omega
      have hR0 : R 0 = base 0 := by simp [R, neighborFrame]
      rw [hR0] at hb
      have hsR : regSize R ≤ regSize base+count+total := hs
      have hcount : count ≤ base 0 := (Nat.le_succ count).trans hc
      have hsizeCap : regSize R ≤ regSize base+base 0+cap :=
        hsR.trans (Nat.add_le_add (Nat.add_le_add_left hcount _) htotal)
      have hb' : n ≤ 100*(base 0+1)^2+2000*(regSize base+base 0+cap+2) :=
        hb.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left 2000 (Nat.add_le_add_right hsizeCap 2)) _)
      rw [Nat.add_mul]
      omega


def neighborFamily : RegCmd := .seq (.assign 8 0) (.down 8 neighborBody)

theorem neighborFamily_exec (data : List BSym) (R : RegFile)
    (hr : R 3<R 0) (hlen : data.length=R 0*R 0) (h8 : R 8=0) (h14 : R 14=0) :
    ∃ steps, RegExec data neighborFamily R
      (Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0))) steps ∧
      steps ≤ regCharge R+1+
        (R 0*(100*(R 0+1)^2+2000*(regSize R+4*R 0+2)+5)+1) := by
  obtain ⟨n, he, hb⟩ := neighborLoop_exec data R (3*R 0) hr hlen (R 0) le_rfl 0 (by omega)
  have hstart : neighborFrame R (R 0) 0 = Function.update R 8 (R 0) := by
    funext k
    by_cases hk : k=14 <;> simp [neighborFrame, hk, h14]
  have hend : neighborFrame R 0
      (0+neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) =
      Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) := by
    funext k
    by_cases hk8 : k=8 <;> by_cases hk14 : k=14 <;> simp_all [neighborFrame]
  rw [hstart, hend] at he
  refine ⟨regCharge R+1+n, RegExec.seq (RegExec.assign R 8 0) he, ?_⟩
  nlinarith

end TensorNP.Encoder
end


/- Inlined module: SmallFamilies -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def smallFamily (f : Fin 3) : RegCmd :=
  ![.seq (monoInc 14 3 9) (monoInc 15 4 4),
    .seq (monoInc 14 9 4) (monoInc 15 3 3),
    .seq (monoInc 14 3 4) (monoInc 15 9 9)] f

lemma monoPair_exec (data : List BSym) (R : RegFile) (pr pc nr nc : Fin 21)
    (hnr : nr ≠ 14) (hnc : nc ≠ 14) :
    ∃ steps, RegExec data (.seq (monoInc 14 pr pc) (monoInc 15 nr nc)) R
      (Function.update (Function.update R 14
        (R 14 + naturalMonomial (R pr) (R pc) (R 1) (R 2))) 15
        (R 15 + naturalMonomial (R nr) (R nc) (R 1) (R 2))) steps ∧
      steps ≤ 10000*(regSize R+2) := by
  let p := naturalMonomial (R pr) (R pc) (R 1) (R 2)
  let S := Function.update R 14 (R 14+p)
  obtain ⟨m, hm, hmB⟩ := monoInc_exec data R 14 pr pc
  obtain ⟨n, hn, hnB⟩ := monoInc_exec data S 15 nr nc
  have he := RegExec.seq hm hn
  have he' : RegExec data (.seq (monoInc 14 pr pc) (monoInc 15 nr nc)) R
      (Function.update S 15 (R 15 + naturalMonomial (R nr) (R nc) (R 1) (R 2))) (m+1+n) := by
    simpa [S, Function.update_of_ne hnr, Function.update_of_ne hnc] using he
  refine ⟨m+1+n, he', ?_⟩
  have hp : p ≤ 1 := naturalMonomial_le _ _ _ _
  have h14 := reg_le_size R 14
  have hS := regSize_update_le R 14 (R 14+p)
  dsimp [S] at hnB
  simp only [regCharge] at hmB hnB
  omega

theorem smallFamily_exec (data : List BSym) (R : RegFile) (f : Fin 3)
    (h4 : R 4 = 2*R 0) (h9 : R 9 = R 0+R 3) :
    ∃ steps, RegExec data (smallFamily f) R
      (Function.update (Function.update R 14
        (R 14 + rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (R 15 + rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 10000*(regSize R+2) := by
  fin_cases f
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 3 9 4 4 (by decide) (by decide)
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 9 4 3 3 (by decide) (by decide)
  · simpa [smallFamily, rawPositiveCount, rawNegativeCount, ← h4, ← h9] using
      monoPair_exec data R 3 4 9 9 (by decide) (by decide)

end TensorNP.Encoder
end


/- Inlined module: ColorFamily -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def colorFamilyBody (f : Fin 4) : RegCmd :=
  ![smallFamily 0, smallFamily 1, smallFamily 2, neighborFamily] f

def colorFamily (f : Fin 4) : RegCmd :=
  .seq (.assign 4 0) (.seq (.add 4 0 (by decide)) (.seq (.assign 9 0)
    (.seq (.add 9 3 (by decide)) (.seq (colorFamilyBody f) (.seq (.reset 4) (.reset 9))))))

lemma colorFamilyBody_exec (data : List BSym) (R : RegFile) (f : Fin 4)
    (hr : R 3 < R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 2*R 0) (h9 : R 9 = R 0+R 3) (h8 : R 8 = 0)
    (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ steps, RegExec data (colorFamilyBody f) R
      (Function.update (Function.update R 14
        (rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 5000*(regSize R+2)^3 := by
  have hs := reg_le_size R 0
  have hpow : regSize R+2 ≤ (regSize R+2)^3 := Nat.le_self_pow (by decide) _
  have hpow2 : 2*(regSize R+2) ≤ (regSize R+2)^3 := by nlinarith [Nat.zero_le ((regSize R)^3)]
  fin_cases f
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 0 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 1 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := smallFamily_exec data R 2 h4 h9
    refine ⟨m, ?_, ?_⟩
    · simpa [colorFamilyBody, h14, h15] using he
    · omega
  · obtain ⟨m, he, hb⟩ := neighborFamily_exec data R hr hlen h8 h14
    refine ⟨m, ?_, ?_⟩
    · have hu : Function.update (Function.update R 14
          (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0))) 15 0 =
          Function.update R 14 (neighborCount (R 0) data (R 3) (R 1) (R 2) (R 0)) := by
        funext r
        by_cases h15r : r = 15 <;> by_cases h14r : r = 14 <;> simp_all
      simpa [colorFamilyBody, rawPositiveCount, rawNegativeCount, hu] using he
    · simp only [regCharge] at hb
      have ha : R 0*(R 0+1)^2 ≤ regSize R*(regSize R+1)^2 :=
        Nat.mul_le_mul hs (Nat.pow_le_pow_left (by omega) 2)
      have hbmul : R 0*(regSize R+4*R 0+2) ≤ regSize R*(5*regSize R+2) :=
        Nat.mul_le_mul hs (by omega)
      nlinarith [Nat.zero_le ((regSize R)^3), Nat.zero_le ((regSize R)^2)]

theorem colorFamily_exec (data : List BSym) (R : RegFile) (f : Fin 4)
    (hr : R 3 < R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ steps, RegExec data (colorFamily f) R
      (Function.update (Function.update R 14
        (rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2))) 15
        (rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2))) steps ∧
      steps ≤ 1000000*(regSize R+2)^4 := by
  let A := Function.update R 4 (R 0)
  let B := Function.update A 4 (A 0 + A 4)
  let C := Function.update B 9 (B 0)
  let S := Function.update C 9 (C 3 + C 9)
  let P := rawPositiveCount (R 0) data f.val (R 3) (R 1) (R 2)
  let M := rawNegativeCount (R 0) f.val (R 3) (R 1) (R 2)
  let T := Function.update (Function.update S 14 P) 15 M
  let U := Function.update T 4 0
  have hS : S = Function.update (Function.update R 4 (2*R 0)) 9 (R 0+R 3) := by
    funext r
    fin_cases r <;> simp [S, C, B, A] <;> omega
  have hs4 : S 4 = 2*S 0 := by simp [hS]
  have hs9 : S 9 = S 0+S 3 := by simp [hS]
  have hs8 : S 8 = 0 := by simpa [hS] using h8
  have hs14 : S 14 = 0 := by simpa [hS] using h14
  have hs15 : S 15 = 0 := by simpa [hS] using h15
  have hsr : S 3 < S 0 := by simpa [hS] using hr
  have hslen : data.length = S 0*S 0 := by simpa [hS] using hlen
  obtain ⟨m, hm, hmB⟩ := colorFamilyBody_exec data S f hsr hslen hs4 hs9 hs8 hs14 hs15
  have hm' : RegExec data (colorFamilyBody f) S T m := by
    simpa [T, P, M, hS] using hm
  have hend : Function.update U 9 0 = Function.update (Function.update R 14 P) 15 M := by
    funext r
    fin_cases r <;> simp [U, T, hS, h4, h9]
  have he := RegExec.seq (RegExec.assign (data := data) R 4 0)
    (RegExec.seq (RegExec.add (data := data) A 4 0 (by decide))
      (RegExec.seq (RegExec.assign (data := data) B 9 0)
        (RegExec.seq (RegExec.add (data := data) C 9 3 (by decide))
          (RegExec.seq hm' (RegExec.seq (RegExec.reset (data := data) T 4)
            (RegExec.reset (data := data) U 9))))))
  rw [hend] at he
  refine ⟨_, he, ?_⟩
  have h0 := reg_le_size R 0
  have h3 := reg_le_size R 3
  have hA := regSize_update_le R 4 (R 0)
  have hB := regSize_update_le A 4 (A 0+A 4)
  have hC := regSize_update_le B 9 (B 0)
  have hTa := regSize_update_le S 14 P
  have hTb := regSize_update_le (Function.update S 14 P) 15 M
  have hU := regSize_update_le T 4 0
  have hPM : P+M ≤ 3*R 0+2 := rawCounts_le (R 0) data f.val (R 3) (R 1) (R 2)
  have hSizeA : regSize A ≤ 2*regSize R := by
    change regSize A ≤ _ at hA
    omega
  have hSizeB : regSize B ≤ 4*regSize R := by
    change regSize B ≤ regSize A+(A 0+A 4) at hB
    simp [A] at hB
    omega
  have hSizeC : regSize C ≤ 5*regSize R := by
    change regSize C ≤ regSize B+B 0 at hC
    have hB0 : B 0 = R 0 := by simp [B, A]
    rw [hB0] at hC
    omega
  have hSa := regSize_update_le R 4 (2*R 0)
  have hSb := regSize_update_le (Function.update R 4 (2*R 0)) 9 (R 0+R 3)
  have hSizeS : regSize S ≤ 5*regSize R := by
    rw [hS]
    omega
  have hSizeT : regSize T ≤ 8*regSize R+2 := by
    change regSize T ≤ regSize (Function.update S 14 P)+M at hTb
    omega
  have hSizeU : regSize U ≤ 8*regSize R+2 := by
    change regSize U ≤ regSize T+0 at hU
    omega
  have hpow : (regSize S+2)^3 ≤ (5*(regSize R+2))^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hpow' : (regSize S+2)^3 ≤ 125*(regSize R+2)^3 := by
    calc
      _ ≤ (5*(regSize R+2))^3 := hpow
      _ = _ := by ring
  have hquart : (regSize R+2)^3 ≤ (regSize R+2)^4 := pow_le_pow_right₀ (by omega) (by omega)
  have hlinear : regSize R+2 ≤ (regSize R+2)^4 := Nat.le_self_pow (by decide) _
  have hbody : m ≤ 625000*(regSize R+2)^4 := by
    have ht := Nat.mul_le_mul_left 5000 (hpow'.trans (Nat.mul_le_mul_left 125 hquart))
    omega
  simp only [regCharge]
  omega

end TensorNP.Encoder
end


/- Inlined module: ColorMatrix -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def colorMatrixProgram : RegCmd := colorDispatch colorFamily

theorem colorMatrix_exec (data : List BSym) (R : RegFile)
    (hq : R 3 < 4 * R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ n, RegExec data colorMatrixProgram R
      (Function.update (Function.update (qState R (R 3 % R 0)) 14
        (rawPositiveCount (R 0) data (R 3 / R 0) (R 3 % R 0) (R 1) (R 2))) 15
        (rawNegativeCount (R 0) (R 3 / R 0) (R 3 % R 0) (R 1) (R 2))) n ∧
      n ≤ 2000000 * (2 * regSize R + 2)^4 := by
  let post : Fin 4 → ℕ → RegFile := fun f q =>
    Function.update (Function.update (qState R q) 14
      (rawPositiveCount (R 0) data f.val q (R 1) (R 2))) 15
      (rawNegativeCount (R 0) f.val q (R 1) (R 2))
  let B := 1000000 * (2 * regSize R + 2)^4
  have hbody : ∀ (f : Fin 4) (q : ℕ), q < R 0 → ∃ n,
      RegExec data (colorFamily f) (qState R q) (post f q) n ∧ n ≤ B := by
    intro f q hq'
    have hr : (qState R q) 3 < (qState R q) 0 := by simpa [qState] using hq'
    have hl : data.length = (qState R q) 0 * (qState R q) 0 := by simpa [qState] using hlen
    have h4' : (qState R q) 4 = 0 := by simpa [qState] using h4
    have h9' : (qState R q) 9 = 0 := by simpa [qState] using h9
    have h8' : (qState R q) 8 = 0 := by simpa [qState] using h8
    have h14' : (qState R q) 14 = 0 := by simpa [qState] using h14
    have h15' : (qState R q) 15 = 0 := by simpa [qState] using h15
    obtain ⟨n, hn, hb⟩ := colorFamily_exec data (qState R q) f hr hl h4' h9' h8' h14' h15'
    have hsize : regSize (qState R q) ≤ regSize R + q := regSize_update_le R 3 q
    have hzero := reg_le_size R 0
    have hp : (regSize (qState R q) + 2)^4 ≤ (2 * regSize R + 2)^4 :=
      Nat.pow_le_pow_left (by omega) 4
    refine ⟨n, ?_, ?_⟩
    · simpa [post, qState] using hn
    · dsimp [B]
      have hm := Nat.mul_le_mul_left 1000000 hp
      omega
  obtain ⟨n, hn, hb⟩ := colorDispatch_exec data R colorFamily post B hq hbody
  have hf := decodedFamily_val (R 0) (R 3)
  have hd := familyDecode_correct hq
  have hf' : (decodedFamily (R 0) (R 3)).val = R 3 / R 0 := by
    rw [hf, hd]
  have hq' : (familyDecode (R 0) (R 3)).2 = R 3 % R 0 := by rw [hd]
  refine ⟨n, ?_, ?_⟩
  · simpa only [colorMatrixProgram, post, hf', hq'] using hn
  · have hp : 2 * regSize R + 2 ≤ (2 * regSize R + 2)^4 := Nat.le_self_pow (by decide) _
    dsimp [B] at hb
    omega

end TensorNP.Encoder
end


/- Inlined module: NativeWriter12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def nativeWriterPorts12 : Fin 5 ↪ Fin 12 :=
  ⟨fun k => ⟨k.val, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 12 => x.val) h)⟩

def nativeWriterDecode12 (l : Fin 12) : Option (Fin 5) :=
  if h : l.val < 5 then some ⟨l.val, h⟩ else none

lemma nativeWriterDecode12_spec (l : Fin 12) (k : Fin 5) :
    nativeWriterDecode12 l = some k ↔ nativeWriterPorts12 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def writerStore12 (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym) : Fin 12 → List BSym :=
  fun k => if k = 0 then List.replicate n .one else if k = 1 then tail
    else if h : 5 ≤ k.val then frame ⟨k.val - 5, by omega⟩ else []

lemma writerStore12_project (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym) :
    StackProgPortLift.project nativeWriterPorts12 (writerStore12 n tail frame) =
      fun k => if k = 0 then List.replicate n .one else if k = 1 then tail else [] := by
  funext k
  fin_cases k <;> rfl

private lemma native_write_at (t : Fin 5 → List BSym) (s : Fin 12 → List BSym) (k : Fin 5) :
    StackProgPortLift.write nativeWriterPorts12 t s (nativeWriterPorts12 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := nativeWriterPorts12.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma writerStore12_write (n : ℕ) (tail result : List BSym) (frame : Fin 7 → List BSym) :
    StackProgPortLift.write nativeWriterPorts12
      (fun k => if k = 0 then List.replicate n .one else if k = 1 then result else [])
      (writerStore12 n tail frame) = writerStore12 n result frame := by
  classical
  funext l
  by_cases hl : l.val < 5
  · let k : Fin 5 := ⟨l.val, hl⟩
    have hk : nativeWriterPorts12 k = l := Fin.ext rfl
    rw [← hk, native_write_at]
    exact (congrFun (writerStore12_project n result frame) k).symm
  · have hout : ¬ ∃ k, nativeWriterPorts12 k = l := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      have hklt := k.isLt
      change k.val = l.val at hv
      omega
    have h0 : l ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      omega
    have h1 : l ≠ 1 := by
      intro he
      have hv := congrArg Fin.val he
      omega
    simp [StackProgPortLift.write, hout, writerStore12, h0, h1]

theorem nativeWriter12 :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ),
      ∀ (n : ℕ) (tail : List BSym) (frame : Fin 7 → List BSym), ∃ steps,
        p.Exec (writerStore12 n tail frame) (writerStore12 n (encNat n ++ tail) frame) steps ∧
        steps ≤ C * (n + 1)^2 := by
  obtain ⟨p, C, hp⟩ := CookPvsNP.unary_to_encNat_stack
  refine ⟨StackProgPortLift.liftProgC nativeWriterPorts12 nativeWriterDecode12 p, C, ?_⟩
  intro n tail frame
  obtain ⟨steps, hs, hb⟩ := hp n tail
  refine ⟨steps, ?_, hb⟩
  have hlift := StackProgPortLift.liftProgC_exec nativeWriterPorts12 nativeWriterDecode12
    nativeWriterDecode12_spec hs (writerStore12 n tail frame)
    (writerStore12_project n tail frame)
  rw [writerStore12_write] at hlift
  exact hlift

end TensorNP.Encoder
end


/- Inlined module: Prefix12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def prefixPorts12 : Fin 3 ↪ Fin 12 := ⟨![1, 6, 8], by decide⟩

def prefixDecode12 (l : Fin 12) : Option (Fin 3) :=
  if l = 1 then some 0 else if l = 6 then some 1 else if l = 8 then some 2 else none

lemma prefixDecode12_spec (l : Fin 12) (k : Fin 3) :
    prefixDecode12 l = some k ↔ prefixPorts12 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def prefixFrameStore (pattern input status : List BSym) (frame : Fin 12 → List BSym) : Fin 12 → List BSym :=
  fun k => if k = 1 then pattern else if k = 6 then input else if k = 8 then status else frame k

def prefixProg12 : StackProg (Fin 12) BSym :=
  StackProgPortLift.liftProgC prefixPorts12 prefixDecode12 prefixProg

lemma prefixFrameStore_project (pattern input status : List BSym) (frame : Fin 12 → List BSym) :
    StackProgPortLift.project prefixPorts12 (prefixFrameStore pattern input status frame) =
      prefixStore pattern input status := by
  funext k
  fin_cases k <;> rfl

private lemma prefix_write_at (t : Fin 3 → List BSym) (s : Fin 12 → List BSym) (k : Fin 3) :
    StackProgPortLift.write prefixPorts12 t s (prefixPorts12 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := prefixPorts12.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma prefixFrameStore_write (pattern input status pattern' input' status' : List BSym)
    (frame : Fin 12 → List BSym) :
    StackProgPortLift.write prefixPorts12 (prefixStore pattern' input' status')
      (prefixFrameStore pattern input status frame) = prefixFrameStore pattern' input' status' frame := by
  classical
  funext l
  by_cases hl : ∃ k, prefixPorts12 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [prefix_write_at]
    exact (congrFun (prefixFrameStore_project pattern' input' status' frame) k).symm
  · have h1 : l ≠ 1 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h6 : l ≠ 6 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h8 : l ≠ 8 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    simp [StackProgPortLift.write, hl, prefixFrameStore, h1, h6, h8]

theorem prefixProg12_exec (pattern input status : List BSym) (frame : Fin 12 → List BSym) :
    prefixProg12.Exec (prefixFrameStore pattern input status frame)
      (prefixFrameStore (prefixResult pattern input).patternRest
        (prefixResult pattern input).inputRest
        ((if (prefixResult pattern input).patternRest = [] then BSym.one else .zero) :: status) frame)
      (3 * (prefixResult pattern input).matched + 3) := by
  have hlift := StackProgPortLift.liftProgC_exec prefixPorts12 prefixDecode12
    prefixDecode12_spec (prefixProg_exec pattern input status)
    (prefixFrameStore pattern input status frame)
    (prefixFrameStore_project pattern input status frame)
  rw [prefixFrameStore_write] at hlift
  exact hlift

end TensorNP.Encoder
end


/- Inlined module: HeaderBody -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

private lemma encNat_length_le (n : ℕ) : (encNat n).length ≤ n + 1 := by
  have hn : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  simp only [encNat, List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

private lemma prefixResult_rest_lengths (pattern input : List BSym) :
    (prefixResult pattern input).patternRest.length ≤ pattern.length ∧
    (prefixResult pattern input).inputRest.length ≤ input.length := by
  induction pattern generalizing input with
  | nil => simp [prefixResult]
  | cons a pattern ih =>
      cases input with
      | nil => simp [prefixResult]
      | cons b input =>
          by_cases hab : a = b
          · simp only [prefixResult, if_pos hab, List.length_cons]
            have h := ih input
            omega
          · simp [prefixResult, hab]

private def bodyStore (n fuel : ℕ) (input pattern work status : List BSym) : Fin 12 → List BSym :=
  prefixFrameStore pattern work status (headerStore n fuel input [] false)

private def writerFrame (input : List BSym) (fuel : ℕ) : Fin 7 → List BSym :=
  fun k => if k = 0 then input else if k = 2 then List.replicate fuel .one else []

private lemma writerFrame_store (n fuel : ℕ) (input pattern : List BSym) :
    writerStore12 n pattern (writerFrame input fuel) = bodyStore n fuel input pattern [] [] := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_initial (n fuel : ℕ) (input : List BSym) :
    bodyStore n fuel input [] [] [] = headerStore n fuel input [] false := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_copied (n fuel : ℕ) (input pattern : List BSym) :
    Function.update (bodyStore n fuel input pattern [] []) 6
      ((bodyStore n fuel input pattern [] []) 5 ++ (bodyStore n fuel input pattern [] []) 6) =
      bodyStore n fuel input pattern input [] := by
  funext k
  fin_cases k <;> simp [Function.update, bodyStore, prefixFrameStore, headerStore]

private lemma clear_exec (k : Fin 12) (s : Fin 12 → List BSym) :
    (clearProg k).Exec s (Function.update s k []) (3 * (s k).length + 1) := by
  have hf : transferStore k (fun _ => false) s = Function.update s k [] := by
    funext j
    by_cases hj : j = k <;> simp [transferStore, Function.update, hj]
  simpa only [clearProg, hf] using stack_transfer k (fun _ => false) s

private def bodyTest (h : Fin 12 → Option BSym) : Bool := h 8 == some .one

private def bodyIncrement (_ : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 0 then .push .one else if k = 7 then .pop else .keep

private def bodyKeep : StackProg (Fin 12) BSym := .act (fun _ _ => .keep)

private def bodyFail : StackProg (Fin 12) BSym :=
  .seq (clearProg 1) (.seq (clearProg 6) (.seq (clearProg 8) (.act bodyIncrement)))

private def bodyProgram (writer : StackProg (Fin 12) BSym) : StackProg (Fin 12) BSym :=
  .seq writer (.seq (copyProg 5 6 9) (.seq prefixProg12 (.branch bodyTest bodyKeep bodyFail)))

private lemma bodyStore_found (n fuel : ℕ) (input work : List BSym) :
    bodyStore n fuel input [] work [.one] = headerStore n fuel input work true := by
  funext k
  fin_cases k <;> rfl

private lemma bodyStore_failure (n fuel : ℕ) (input pattern work : List BSym) (hf : 0 < fuel) :
    StackProg.applyAct bodyIncrement
      (Function.update (Function.update (Function.update
        (bodyStore n fuel input pattern work [.zero]) 1 []) 6 []) 8 []) =
      headerStore (n + 1) (fuel - 1) input [] false := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      funext k
      fin_cases k <;> simp [StackProg.applyAct, bodyIncrement, StackAct.apply,
        Function.update, bodyStore, prefixFrameStore, headerStore, List.replicate_succ]

private lemma bodyFail_exec (n fuel : ℕ) (input pattern work : List BSym) (hf : 0 < fuel) :
    bodyFail.Exec (bodyStore n fuel input pattern work [.zero])
      (headerStore (n + 1) (fuel - 1) input [] false)
      (3 * pattern.length + 3 * work.length + 10) := by
  let s0 := bodyStore n fuel input pattern work [.zero]
  let s1 := Function.update s0 1 []
  let s2 := Function.update s1 6 []
  let s3 := Function.update s2 8 []
  have he1 : (clearProg 1).Exec s0 s1 (3 * pattern.length + 1) := by
    simpa [s0, s1, bodyStore, prefixFrameStore] using clear_exec 1 s0
  have he2 : (clearProg 6).Exec s1 s2 (3 * work.length + 1) := by
    simpa [s0, s1, s2, bodyStore, prefixFrameStore] using clear_exec 6 s1
  have he3 : (clearProg 8).Exec s2 s3 4 := by
    simpa [s0, s1, s2, s3, bodyStore, prefixFrameStore] using clear_exec 8 s2
  have he4 : (StackProg.act bodyIncrement).Exec s3
      (headerStore (n + 1) (fuel - 1) input [] false) 1 := by
    have he := StackProg.Exec.act bodyIncrement s3
    have heq : StackProg.applyAct bodyIncrement s3 =
        headerStore (n + 1) (fuel - 1) input [] false := by
      simpa only [s0, s1, s2, s3] using bodyStore_failure n fuel input pattern work hf
    rw [heq] at he
    exact he
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq he3 he4))
  convert he using 1 <;> first | rfl | omega

private lemma bodyBranch_exec (n fuel : ℕ) (input : List BSym) (hf : 0 < fuel) :
    ∃ steps, (StackProg.branch bodyTest bodyKeep bodyFail).Exec
      (bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest
        [if (prefixResult (encNat n) input).patternRest = [] then .one else .zero])
      (headerStepResult n fuel input) steps ∧
      steps ≤ 3 * (prefixResult (encNat n) input).patternRest.length +
        3 * (prefixResult (encNat n) input).inputRest.length + 11 := by
  by_cases hm : (prefixResult (encNat n) input).patternRest = []
  · let s := bodyStore n fuel input [] (prefixResult (encNat n) input).inputRest [.one]
    have ht : bodyTest (fun k => (s k).head?) = true := by
      simp [s, bodyTest, bodyStore, prefixFrameStore]
    have he : bodyKeep.Exec s s 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
        funext k
        rfl
      simpa only [bodyKeep, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) s)
    refine ⟨2, ?_, by omega⟩
    simpa [s, hm, headerStepResult, bodyStore_found] using
      (StackProg.Exec.branchTrue (q := bodyFail) ht he)
  · let s := bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest [.zero]
    have ht : bodyTest (fun k => (s k).head?) = false := by
      simp [s, bodyTest, bodyStore, prefixFrameStore]
    have he := bodyFail_exec n fuel input (prefixResult (encNat n) input).patternRest
      (prefixResult (encNat n) input).inputRest hf
    refine ⟨1 + (3 * (prefixResult (encNat n) input).patternRest.length +
      3 * (prefixResult (encNat n) input).inputRest.length + 10), ?_, by omega⟩
    simpa [s, hm, headerStepResult] using
      (StackProg.Exec.branchFalse (p := bodyKeep) ht he)

theorem header_body_exists :
    ∃ (body : StackProg (Fin 12) BSym) (C : ℕ),
      ∀ (input : List BSym) (n fuel : ℕ), 0 < fuel → n + fuel ≤ input.length + 1 →
        ∃ steps, body.Exec (headerStore n fuel input [] false)
          (headerStepResult n fuel input) steps ∧ steps ≤ C * (input.length + 2)^2 := by
  obtain ⟨writer, C, hw⟩ := nativeWriter12
  refine ⟨bodyProgram writer, C + 100, ?_⟩
  intro input n fuel hf hbudget
  obtain ⟨wt, heW, hwt⟩ := hw n [] (writerFrame input fuel)
  have heW' : writer.Exec (headerStore n fuel input [] false)
      (bodyStore n fuel input (encNat n) [] []) wt := by
    simpa only [writerFrame_store, bodyStore_initial, List.append_nil] using heW
  have heC : (copyProg 5 6 9).Exec (bodyStore n fuel input (encNat n) [] [])
      (bodyStore n fuel input (encNat n) input []) (6 * input.length + 3) := by
    have hc := stack_copy (5 : Fin 12) 6 9 (by decide) (by decide) (by decide)
      (bodyStore n fuel input (encNat n) [] []) (by rfl)
    rw [bodyStore_copied] at hc
    simpa [bodyStore, prefixFrameStore, headerStore] using hc
  have heP : prefixProg12.Exec (bodyStore n fuel input (encNat n) input [])
      (bodyStore n fuel input (prefixResult (encNat n) input).patternRest
        (prefixResult (encNat n) input).inputRest
        [if (prefixResult (encNat n) input).patternRest = [] then .one else .zero])
      (3 * (prefixResult (encNat n) input).matched + 3) :=
    prefixProg12_exec (encNat n) input [] (headerStore n fuel input [] false)
  obtain ⟨bt, heB, hbt⟩ := bodyBranch_exec n fuel input hf
  have he := StackProg.Exec.seq heW' (StackProg.Exec.seq heC (StackProg.Exec.seq heP heB))
  refine ⟨_, he, ?_⟩
  have hn : n ≤ input.length := by omega
  have hp : (prefixResult (encNat n) input).patternRest.length ≤ input.length + 1 := by
    have h := (prefixResult_rest_lengths (encNat n) input).1
    have henc := encNat_length_le n
    omega
  have hi := (prefixResult_rest_lengths (encNat n) input).2
  have hm := prefixResult_matched_le_input (encNat n) input
  have hL : input.length + 2 ≤ (input.length + 2)^2 := by nlinarith
  have hwt' : wt ≤ C * (input.length + 2)^2 :=
    hwt.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have hsum : wt + 1 + (6 * input.length + 3 + 1 +
      (3 * (prefixResult (encNat n) input).matched + 3 + 1 + bt)) ≤
      C * (input.length + 2)^2 + 100 * (input.length + 2)^2 := by omega
  calc
    _ ≤ C * (input.length + 2)^2 + 100 * (input.length + 2)^2 := hsum
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: HeaderInit -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def headerInputStore (input : List BSym) : Fin 12 → List BSym :=
  fun k => if k = 5 then input else []

private def initStore (input scratch fuel : List BSym) : Fin 12 → List BSym :=
  fun k => if k = 5 then input else if k = 9 then scratch else if k = 7 then fuel else []

private def initGuard (h : Fin 12 → Option BSym) : Bool := (h 5).isSome

private def initAct (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 5 then .pop else if k = 9 then
    match h 5 with | some a => .push a | none => .keep
  else if k = 7 then .push .one else .keep

private def initLoop : StackProg (Fin 12) BSym := .loop initGuard (.act initAct)

private def initRestore : StackProg (Fin 12) BSym :=
  transferProg 9 (fun k => decide (k = 5))

private def initProgram : StackProg (Fin 12) BSym :=
  .seq initLoop (.seq initRestore (pushProg 7 .one))

private lemma initAct_step (a : BSym) (input scratch fuel : List BSym) :
    StackProg.applyAct initAct (initStore (a :: input) scratch fuel) =
      initStore input (a :: scratch) (.one :: fuel) := by
  funext k
  fin_cases k <;> rfl

private lemma initLoop_exec (input scratch fuel : List BSym) :
    initLoop.Exec (initStore input scratch fuel)
      (initStore [] (input.reverse ++ scratch) (List.replicate input.length .one ++ fuel))
      (3 * input.length + 1) := by
  induction input generalizing scratch fuel with
  | nil =>
      exact StackProg.Exec.loopFalse (by rfl)
  | cons a input ih =>
      have hg : initGuard (fun k => (initStore (a :: input) scratch fuel k).head?) = true := by rfl
      have ha : (StackProg.act initAct).Exec (initStore (a :: input) scratch fuel)
          (initStore input (a :: scratch) (.one :: fuel)) 1 := by
        simpa only [initAct_step] using (StackProg.Exec.act initAct
          (initStore (a :: input) scratch fuel))
      have he := StackProg.Exec.loopTrue hg ha (ih (a :: scratch) (.one :: fuel))
      have hrep (m : ℕ) : List.replicate m BSym.one ++ .one :: fuel =
          .one :: (List.replicate m BSym.one ++ fuel) := by
        induction m with
        | zero => rfl
        | succ m ih => simp [List.replicate_succ, ih]
      simpa [initLoop, List.reverse_cons, List.append_assoc, List.replicate_succ, hrep,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem header_init_exists : ∃ p : StackProg (Fin 12) BSym, ∀ input : List BSym,
    p.Exec (headerInputStore input)
      (headerStore 0 (input.length + 1) input [] false) (6 * input.length + 5) := by
  refine ⟨initProgram, ?_⟩
  intro input
  have hstart : initStore input [] [] = headerInputStore input := by
    funext k
    fin_cases k <;> rfl
  have heLoop : initLoop.Exec (headerInputStore input)
      (initStore [] input.reverse (List.replicate input.length .one)) (3 * input.length + 1) := by
    simpa only [hstart, List.append_nil] using initLoop_exec input [] []
  have hrestore : transferStore (9 : Fin 12) (fun k => decide (k = 5))
      (initStore [] input.reverse (List.replicate input.length .one)) =
      initStore input [] (List.replicate input.length .one) := by
    funext k
    fin_cases k <;> simp [transferStore, initStore]
  have heRestore : initRestore.Exec (initStore [] input.reverse (List.replicate input.length .one))
      (initStore input [] (List.replicate input.length .one)) (3 * input.length + 1) := by
    have he := stack_transfer (9 : Fin 12) (fun k => decide (k = 5))
      (initStore [] input.reverse (List.replicate input.length .one))
    rw [hrestore] at he
    simpa [initRestore, initStore] using he
  have hePush : (pushProg 7 .one).Exec (initStore input [] (List.replicate input.length .one))
      (headerStore 0 (input.length + 1) input [] false) 1 := by
    have heq : StackProg.applyAct (fun _ k => if k = 7 then .push BSym.one else .keep)
        (initStore input [] (List.replicate input.length .one)) =
        headerStore 0 (input.length + 1) input [] false := by
      funext k
      fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, initStore, headerStore,
        List.replicate_succ]
    simpa only [pushProg, heq] using (StackProg.Exec.act
      (fun _ k => if k = 7 then .push BSym.one else .keep)
      (initStore input [] (List.replicate input.length .one)))
  convert StackProg.Exec.seq heLoop (StackProg.Exec.seq heRestore hePush) using 1 <;>
    first | rfl | omega

end TensorNP.Encoder
end


/- Inlined module: HeaderMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem nativeHeaderSearch :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ), ∀ input : List BSym, ∃ steps,
      p.Exec (headerStore 0 (input.length+1) input [] false)
        (headerResultStore (boundedHeader 0 (input.length+1) input) input) steps ∧
      steps ≤ C * (input.length+2)^3 := by
  obtain ⟨body, C, hbody⟩ := header_body_exists
  refine ⟨.loop headerGuard body, C+3, fun input => ?_⟩
  obtain ⟨steps, hs, hb⟩ := headerLoop_exec body (C*(input.length+2)^2) input
    (fun n fuel hf hbudget => hbody input n fuel hf hbudget)
    (input.length+1) 0 (by omega)
  refine ⟨steps, hs, hb.trans ?_⟩
  have hmul := Nat.mul_le_mul_right (C*(input.length+2)^2+2)
    (show input.length+1 ≤ input.length+2 by omega)
  have hcube : input.length+2 ≤ (input.length+2)^3 :=
    Nat.le_self_pow (by decide) _
  calc
    (input.length+1)*(C*(input.length+2)^2+2)+1 ≤
        (input.length+2)*(C*(input.length+2)^2+2)+1 := by omega
    _ = C*(input.length+2)^3 + 2*(input.length+2)+1 := by ring
    _ ≤ (C+3)*(input.length+2)^3 := by nlinarith

theorem header_parser_source :
    ∃ (p : StackProg (Fin 12) BSym) (C : ℕ), ∀ input : List BSym, ∃ steps,
      p.Exec (headerInputStore input)
        (headerResultStore (boundedHeader 0 (input.length+1) input) input) steps ∧
      steps ≤ C * (input.length+2)^3 := by
  obtain ⟨init, hi⟩ := header_init_exists
  obtain ⟨search, C, hs⟩ := nativeHeaderSearch
  refine ⟨.seq init search, C+8, fun input => ?_⟩
  obtain ⟨steps, hsteps, hbound⟩ := hs input
  refine ⟨(6*input.length+5)+1+steps, StackProg.Exec.seq (hi input) hsteps, ?_⟩
  have hcube : input.length+2 ≤ (input.length+2)^3 := Nat.le_self_pow (by decide) _
  calc
    (6*input.length+5)+1+steps ≤
        C*(input.length+2)^3 + 8*(input.length+2)^3 := by omega
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: MatrixLookup12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def checkerWorkStore (n row col : ℕ) (data output read : List BSym) (good : Bool) : Fin 12 → List BSym :=
  fun k => if k = 4 then output else if k = 11 then read else checkerStore n row col data good k

def lookupPorts12 : Bool → (Fin 8 ↪ Fin 12)
  | false => ⟨![0, 1, 2, 3, 4, 5, 6, 7], by decide⟩
  | true => ⟨![0, 1, 3, 2, 4, 5, 6, 7], by decide⟩

def lookupDecode12 (swapped : Bool) (l : Fin 12) : Option (Fin 8) :=
  if l = 0 then some 0 else if l = 1 then some 1
  else if l = 2 then some (if swapped then 3 else 2)
  else if l = 3 then some (if swapped then 2 else 3)
  else if l = 4 then some 4 else if l = 5 then some 5 else if l = 6 then some 6
  else if l = 7 then some 7 else none

lemma lookupDecode12_spec (swapped : Bool) (l : Fin 12) (k : Fin 8) :
    lookupDecode12 swapped l = some k ↔ lookupPorts12 swapped k = l := by
  cases swapped <;> fin_cases l <;> fin_cases k <;> decide

def lookupProg12 (swapped : Bool) : StackProg (Fin 12) BSym :=
  StackProgPortLift.liftProgC (lookupPorts12 swapped) (lookupDecode12 swapped)
    TensorAdjacencyLookup8.lookupProg

def checkerLookupStore (swapped : Bool) (n i j : ℕ) (data output : List BSym) : Fin 8 → List BSym :=
  TensorAdjacencyLookup8.store data (List.replicate n .one)
    (List.replicate (if swapped then j else i) .one)
    (List.replicate (if swapped then i else j) .one) output [] [] []

lemma checkerWorkStore_project (swapped : Bool) (n i j : ℕ) (data output read : List BSym)
    (good : Bool) : StackProgPortLift.project (lookupPorts12 swapped)
      (checkerWorkStore n i j data output read good) = checkerLookupStore swapped n i j data output := by
  funext k
  cases swapped <;> fin_cases k <;> rfl

private lemma lookup_write_at (swapped : Bool) (t : Fin 8 → List BSym)
    (s : Fin 12 → List BSym) (k : Fin 8) :
    StackProgPortLift.write (lookupPorts12 swapped) t s (lookupPorts12 swapped k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := (lookupPorts12 swapped).injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma checkerWorkStore_write (swapped : Bool) (n i j : ℕ) (data output output' read : List BSym)
    (good : Bool) : StackProgPortLift.write (lookupPorts12 swapped)
      (checkerLookupStore swapped n i j data output') (checkerWorkStore n i j data output read good) =
      checkerWorkStore n i j data output' read good := by
  classical
  funext l
  by_cases hl : ∃ k, lookupPorts12 swapped k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [lookup_write_at]
    exact (congrFun (checkerWorkStore_project swapped n i j data output' read good) k).symm
  · have hx : l.val < 8 → ∃ k, lookupPorts12 swapped k = l := by
      cases swapped <;> fin_cases l <;> decide
    have h4 : l ≠ 4 := by
      intro h
      subst l
      exact hl (hx (by decide))
    simp [StackProgPortLift.write, hl, checkerWorkStore, h4]

lemma checkerWorkStore_empty (n i j : ℕ) (data : List BSym) (good : Bool) :
    checkerWorkStore n i j data [] [] good = checkerStore n i j data good := by
  funext k
  fin_cases k <;> rfl

theorem lookupProg12_exec (swapped : Bool) (n i j : ℕ) (data output read : List BSym)
    (good : Bool) (hi : i < n) (hj : j < n) (hlen : data.length = n*n) :
    ∃ steps, steps ≤ 50*(n+1)^2 ∧
      (lookupProg12 swapped).Exec (checkerWorkStore n i j data output read good)
        (checkerWorkStore n i j data
          ((if swapped then data.getD (j*n+i) .zero else data.getD (i*n+j) .zero) :: output)
          read good) steps := by
  have hi' : (if swapped then j else i) < n := by cases swapped <;> simp_all
  have hj' : (if swapped then i else j) < n := by cases swapped <;> simp_all
  obtain ⟨steps, hbound, he⟩ := TensorAdjacencyLookup8.lookupProg_exec n
    (if swapped then j else i) (if swapped then i else j) data output hi' hj' hlen
  have hx : TensorAdjacencyLookup8.lookupProg.Exec
      (checkerLookupStore swapped n i j data output)
      (checkerLookupStore swapped n i j data
        (data.getD ((if swapped then j else i)*n+(if swapped then i else j)) .zero :: output)) steps := by
    exact he
  have hlift := StackProgPortLift.liftProgC_exec (lookupPorts12 swapped) (lookupDecode12 swapped)
    (lookupDecode12_spec swapped) hx (checkerWorkStore n i j data output read good)
    (checkerWorkStore_project swapped n i j data output read good)
  rw [checkerWorkStore_write] at hlift
  refine ⟨steps, hbound, ?_⟩
  cases swapped <;> simpa [lookupProg12] using hlift

end TensorNP.Encoder
end


/- Inlined module: MatrixCheckLoops -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def checkerColGuard (h : Fin 12 → Option BSym) : Bool := (h 3).isSome

def checkerRowGuard (h : Fin 12 → Option BSym) : Bool := (h 2).isSome

theorem symmetry_loop_exec (body : StackProg (Fin 12) BSym) (B n row : ℕ) (data : List BSym)
    (hstep : ∀ j : ℕ, j < n → ∀ good : Bool, ∃ steps,
      body.Exec (checkerStore n row (j+1) data good)
        (checkerStore n row j data
          (good && decide (data.getD (row*n+j) .zero = data.getD (j*n+row) .zero))) steps ∧ steps ≤ B) :
    ∀ count : ℕ, count ≤ n → ∀ good : Bool, ∃ steps,
      (StackProg.loop checkerColGuard body).Exec (checkerStore n row count data good)
        (checkerStore n row 0 data (good && symmetryPrefix n data row count)) steps ∧
      steps ≤ count*(B+2)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ good
      refine ⟨1, ?_, by simp⟩
      simpa [symmetryPrefix] using
        (StackProg.Exec.loopFalse (p := body) (test := checkerColGuard)
          (s := checkerStore n row 0 data good) (by simp [checkerColGuard, checkerStore]))
  | succ count ih =>
      intro hc good
      obtain ⟨m, hm, hmB⟩ := hstep count (by omega) good
      obtain ⟨r, hr, hrB⟩ := ih (by omega)
        (good && decide (data.getD (row*n+count) .zero = data.getD (count*n+row) .zero))
      refine ⟨1+m+1+r, ?_, ?_⟩
      · simpa [symmetryPrefix, Bool.and_assoc] using
          (StackProg.Exec.loopTrue (test := checkerColGuard)
            (by simp [checkerColGuard, checkerStore, List.replicate_succ]) hm hr)
      · nlinarith

theorem matrix_loop_exec (body : StackProg (Fin 12) BSym) (B n : ℕ) (data : List BSym)
    (hstep : ∀ i : ℕ, i < n → ∀ good : Bool, ∃ steps,
      body.Exec (checkerStore n (i+1) 0 data good)
        (checkerStore n i 0 data
          (good && decide (data.getD (i*n+i) .zero = BSym.zero) && symmetryPrefix n data i n)) steps ∧
      steps ≤ B) :
    ∀ count : ℕ, count ≤ n → ∀ good : Bool, ∃ steps,
      (StackProg.loop checkerRowGuard body).Exec (checkerStore n count 0 data good)
        (checkerStore n 0 0 data (good && matrixCheckPrefix n data count)) steps ∧
      steps ≤ count*(B+2)+1 := by
  intro count
  induction count with
  | zero =>
      intro _ good
      refine ⟨1, ?_, by simp⟩
      simpa [matrixCheckPrefix] using
        (StackProg.Exec.loopFalse (p := body) (test := checkerRowGuard)
          (s := checkerStore n 0 0 data good) (by simp [checkerRowGuard, checkerStore]))
  | succ count ih =>
      intro hc good
      obtain ⟨m, hm, hmB⟩ := hstep count (by omega) good
      obtain ⟨r, hr, hrB⟩ := ih (by omega)
        (good && decide (data.getD (count*n+count) .zero = BSym.zero) && symmetryPrefix n data count n)
      refine ⟨1+m+1+r, ?_, ?_⟩
      · simpa [matrixCheckPrefix, Bool.and_assoc] using
          (StackProg.Exec.loopTrue (test := checkerRowGuard)
            (by simp [checkerRowGuard, checkerStore, List.replicate_succ]) hm hr)
      · nlinarith

end TensorNP.Encoder
end


/- Inlined module: MatrixCoordinates -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def symmetrySave (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 then .pop else if k = 11 then
    match h 4 with | some a => .push a | none => .keep
  else .keep

def symmetryMark (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 ∨ k = 11 then .pop
  else if k = 8 ∧ h 8 = none ∧ h 4 ≠ h 11 then .push .zero else .keep

def symmetryBody : StackProg (Fin 12) BSym :=
  .seq (popProg 3) (.seq (lookupProg12 false) (.seq (.act symmetrySave)
    (.seq (lookupProg12 true) (.act symmetryMark))))

theorem symmetrySave_step (n row col : ℕ) (data : List BSym) (a : BSym) (good : Bool) :
    StackProg.applyAct symmetrySave (checkerWorkStore n row col data [a] [] good) =
      checkerWorkStore n row col data [] [a] good := by
  funext k
  fin_cases k <;> rfl

theorem symmetryMark_step (n row col : ℕ) (data : List BSym) (a b : BSym) (good : Bool) :
    StackProg.applyAct symmetryMark (checkerWorkStore n row col data [b] [a] good) =
      checkerStore n row col data (good && decide (a = b)) := by
  cases good <;> cases a <;> cases b <;> funext k <;> fin_cases k <;> rfl

theorem checkerPopCol_exec (n row col : ℕ) (data : List BSym) (good : Bool) :
    (popProg (3 : Fin 12)).Exec (checkerStore n row (col+1) data good)
      (checkerStore n row col data good) 1 := by
  have heq : Function.update (checkerStore n row (col+1) data good) 3
      ((checkerStore n row (col+1) data good) 3).tail = checkerStore n row col data good := by
    funext k
    fin_cases k <;> simp [checkerStore, Function.update, List.replicate_succ]
  simpa only [heq] using (stack_basic_macros (3 : Fin 12)
    (checkerStore n row (col+1) data good)).2.1

theorem symmetryBody_exec (n row col : ℕ) (data : List BSym) (good : Bool)
    (hrow : row < n) (hcol : col < n) (hlen : data.length = n*n) :
    ∃ steps, symmetryBody.Exec (checkerStore n row (col+1) data good)
      (checkerStore n row col data
        (good && decide (data.getD (row*n+col) .zero = data.getD (col*n+row) .zero))) steps ∧
      steps ≤ 107*(n+1)^2 := by
  let a := data.getD (row*n+col) BSym.zero
  let b := data.getD (col*n+row) BSym.zero
  obtain ⟨u, huB, hu⟩ := lookupProg12_exec false n row col data [] [] good hrow hcol hlen
  rw [checkerWorkStore_empty] at hu
  obtain ⟨v, hvB, hv⟩ := lookupProg12_exec true n row col data [] [a] good hrow hcol hlen
  have hsave : (StackProg.act symmetrySave).Exec
      (checkerWorkStore n row col data [a] [] good)
      (checkerWorkStore n row col data [] [a] good) 1 := by
    simpa only [symmetrySave_step] using StackProg.Exec.act symmetrySave
      (checkerWorkStore n row col data [a] [] good)
  have hmark : (StackProg.act symmetryMark).Exec
      (checkerWorkStore n row col data [b] [a] good)
      (checkerStore n row col data (good && decide (a=b))) 1 := by
    simpa only [symmetryMark_step] using StackProg.Exec.act symmetryMark
      (checkerWorkStore n row col data [b] [a] good)
  have hex := StackProg.Exec.seq (checkerPopCol_exec n row col data good)
    (StackProg.Exec.seq hu (StackProg.Exec.seq hsave (StackProg.Exec.seq hv hmark)))
  refine ⟨_, hex, ?_⟩
  have hsq : 1 ≤ (n+1)^2 := Nat.one_le_pow 2 (n+1) (by omega)
  omega

def symmetryProgram : StackProg (Fin 12) BSym := .loop checkerColGuard symmetryBody

theorem symmetryProgram_exec (n row count : ℕ) (data : List BSym) (good : Bool)
    (hrow : row < n) (hcount : count ≤ n) (hlen : data.length = n*n) :
    ∃ steps, symmetryProgram.Exec (checkerStore n row count data good)
      (checkerStore n row 0 data (good && symmetryPrefix n data row count)) steps ∧
      steps ≤ 110*(n+1)^3 := by
  obtain ⟨steps, hs, hb⟩ := symmetry_loop_exec symmetryBody (107*(n+1)^2) n row data
    (fun j hj good => symmetryBody_exec n row j data good hrow hj hlen) count hcount good
  refine ⟨steps, hs, hb.trans ?_⟩
  have hm := Nat.mul_le_mul_right (107*(n+1)^2+2) (show count ≤ n+1 by omega)
  have hcube : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by decide) _
  calc
    count*(107*(n+1)^2+2)+1 ≤ (n+1)*(107*(n+1)^2+2)+1 := by omega
    _ = 107*(n+1)^3+2*(n+1)+1 := by ring
    _ ≤ 110*(n+1)^3 := by omega

end TensorNP.Encoder
end


/- Inlined module: MatrixRow -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def diagonalMark (h : Fin 12 → Option BSym) (k : Fin 12) : StackAct BSym :=
  if k = 4 then .pop else if k = 8 ∧ h 8 = none ∧ h 4 ≠ some .zero then .push .zero else .keep

def matrixRowBody : StackProg (Fin 12) BSym :=
  .seq (popProg 2) (.seq (copyProg 2 3 7) (.seq (lookupProg12 false)
    (.seq (.act diagonalMark) (.seq (clearProg 3) (.seq (copyProg 1 3 7) symmetryProgram)))))

lemma diagonalMark_step (n row col : ℕ) (data : List BSym) (a : BSym) (good : Bool) :
    StackProg.applyAct diagonalMark (checkerWorkStore n row col data [a] [] good) =
      checkerStore n row col data (good && decide (a = .zero)) := by
  cases good <;> cases a <;> funext k <;> fin_cases k <;> rfl

lemma checkerPopRow_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (popProg (2 : Fin 12)).Exec (checkerStore n (row+1) 0 data good)
      (checkerStore n row 0 data good) 1 := by
  have hu : Function.update (checkerStore n (row+1) 0 data good) 2
      ((checkerStore n (row+1) 0 data good) 2).tail = checkerStore n row 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore, Function.update, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (2 : Fin 12)
    (checkerStore n (row+1) 0 data good)).2.1

lemma checkerCopyRow_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (2 : Fin 12) 3 7).Exec (checkerStore n row 0 data good)
      (checkerStore n row row data good) (6*row+3) := by
  have h := stack_copy (2 : Fin 12) 3 7 (by decide) (by decide) (by decide)
    (checkerStore n row 0 data good) (by simp [checkerStore])
  have hu : Function.update (checkerStore n row 0 data good) 3
      (checkerStore n row 0 data good 2 ++ checkerStore n row 0 data good 3) =
        checkerStore n row row data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [hu] at h
  simpa [checkerStore] using h

lemma checkerClearCol_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (clearProg (3 : Fin 12)).Exec (checkerStore n row row data good)
      (checkerStore n row 0 data good) (3*row+1) := by
  have hu : Function.update (checkerStore n row row data good) 3 [] =
      checkerStore n row 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  have he := (stack_basic_macros (3 : Fin 12) (checkerStore n row row data good)).2.2
  rw [hu] at he
  simpa [checkerStore] using he

lemma checkerCopyDimension_exec (n row : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (1 : Fin 12) 3 7).Exec (checkerStore n row 0 data good)
      (checkerStore n row n data good) (6*n+3) := by
  have h := stack_copy (1 : Fin 12) 3 7 (by decide) (by decide) (by decide)
    (checkerStore n row 0 data good) (by simp [checkerStore])
  have hu : Function.update (checkerStore n row 0 data good) 3
      (checkerStore n row 0 data good 1 ++ checkerStore n row 0 data good 3) =
        checkerStore n row n data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [hu] at h
  simpa [checkerStore] using h

theorem matrix_row_body_exists : ∃ body : StackProg (Fin 12) BSym,
    ∀ (n row : ℕ) (data : List BSym) (good : Bool), row < n → data.length = n*n → ∃ steps,
      body.Exec (checkerStore n (row+1) 0 data good)
        (checkerStore n row 0 data
          (good && decide (data.getD (row*n+row) .zero = BSym.zero) && symmetryPrefix n data row n)) steps ∧
      steps ≤ 500*(n+1)^3 := by
  refine ⟨matrixRowBody, ?_⟩
  intro n row data good hrow hlen
  let a := data.getD (row*n+row) BSym.zero
  let good' := good && decide (a = BSym.zero)
  obtain ⟨u, huB, hu⟩ := lookupProg12_exec false n row row data [] [] good hrow hrow hlen
  rw [checkerWorkStore_empty] at hu
  have hmark : (StackProg.act diagonalMark).Exec
      (checkerWorkStore n row row data [a] [] good) (checkerStore n row row data good') 1 := by
    simpa only [diagonalMark_step] using StackProg.Exec.act diagonalMark
      (checkerWorkStore n row row data [a] [] good)
  obtain ⟨v, hv, hvB⟩ := symmetryProgram_exec n row n data good' hrow (by rfl) hlen
  have he := StackProg.Exec.seq (checkerPopRow_exec n row data good)
    (StackProg.Exec.seq (checkerCopyRow_exec n row data good)
      (StackProg.Exec.seq hu (StackProg.Exec.seq hmark
        (StackProg.Exec.seq (checkerClearCol_exec n row data good')
          (StackProg.Exec.seq (checkerCopyDimension_exec n row data good') hv)))))
  refine ⟨_, he, ?_⟩
  have hs : (n+1)^2 ≤ (n+1)^3 := pow_le_pow_right₀ (by omega) (by omega)
  have hn : n+1 ≤ (n+1)^3 := Nat.le_self_pow (by decide) _
  omega

end TensorNP.Encoder
end


/- Inlined module: MatrixMachine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem checkerCopyRowCounter (n : ℕ) (data : List BSym) (good : Bool) :
    (copyProg (1 : Fin 12) 2 7).Exec (checkerStore n 0 0 data good)
      (checkerStore n n 0 data good) (6*n+3) := by
  have hc := stack_copy (1 : Fin 12) 2 7 (by decide) (by decide) (by decide)
    (checkerStore n 0 0 data good) (by simp [checkerStore])
  have heq : Function.update (checkerStore n 0 0 data good) 2
      (checkerStore n 0 0 data good 1 ++ checkerStore n 0 0 data good 2) =
      checkerStore n n 0 data good := by
    funext k
    fin_cases k <;> simp [checkerStore]
  rw [heq] at hc
  simpa [checkerStore] using hc

theorem matrix_checker_source : ∃ p : StackProg (Fin 12) BSym,
    ∀ (n : ℕ) (data : List BSym) (good : Bool), data.length = n*n → ∃ steps,
      p.Exec (checkerStore n 0 0 data good)
        (checkerStore n 0 0 data (good && matrixCheckPrefix n data n)) steps ∧
      steps ≤ 1000*(n+1)^4 := by
  obtain ⟨body, hbody⟩ := matrix_row_body_exists
  refine ⟨.seq (copyProg 1 2 7) (.loop checkerRowGuard body), ?_⟩
  intro n data good hlen
  obtain ⟨steps, hs, hb⟩ := matrix_loop_exec body (500*(n+1)^3) n data
    (fun i hi good => hbody n i data good hi hlen) n le_rfl good
  refine ⟨(6*n+3)+1+steps, StackProg.Exec.seq (checkerCopyRowCounter n data good) hs, ?_⟩
  have hm := Nat.mul_le_mul_right (500*(n+1)^3+2) (show n ≤ n+1 by omega)
  have hquart : n+1 ≤ (n+1)^4 := Nat.le_self_pow (by decide) _
  calc
    (6*n+3)+1+steps ≤ (6*n+4)+((n+1)*(500*(n+1)^3+2)+1) := by omega
    _ = 500*(n+1)^4+8*n+7 := by ring
    _ ≤ 1000*(n+1)^4 := by omega

end TensorNP.Encoder
end


/- Inlined module: FrontendSpec -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- Global frontend layout: original0, dimension1, suffix2, reversedbits3,
status4, reserved output5, unaryfuel6, row-major matrix7; remaining ports are scratch. -/
def frontendStore (input : List BSym) (dimension : ℕ)
    (suffix bitsRev status fuel data : List BSym) : Fin 32 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then List.replicate dimension .one
    else if k = 2 then suffix else if k = 3 then bitsRev else if k = 4 then status
    else if k = 6 then fuel else if k = 7 then data else []

def frontendInputStore (input : List BSym) : Fin 32 → List BSym :=
  fun k => if k = 0 then input else []

def frontendHeaderStore (input : List BSym) (r : HeaderResult) : Fin 32 → List BSym :=
  frontendStore input r.dimension r.suffix [] (if r.found then [.one] else [])
    (List.replicate r.fuel .one) []

def frontendGraphStore (input : List BSym) (dimension : ℕ) (data : List BSym) : Fin 32 → List BSym :=
  frontendStore input dimension [] [] [.one] [] data

end TensorNP.Encoder
end


/- Inlined module: EmitterSpec -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

/-- Backend dimension14, descending coordinates15/16/17, output5;
working18--31 start empty, and the validated frontend fields are preserved. -/
def emitterStore (input data : List BSym) (v N i j k : ℕ) (output : List BSym) : Fin 32 → List BSym :=
  fun l => if l = 5 then output else if l = 14 then List.replicate N .one
    else if l = 15 then List.replicate i .one else if l = 16 then List.replicate j .one
    else if l = 17 then List.replicate k .one else frontendGraphStore input v data l

end TensorNP.Encoder
end


/- Inlined module: Compare32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def comparePorts32 : Fin 6 ↪ Fin 32 := ⟨![23, 24, 18, 25, 26, 19], by decide⟩

def compareDecode32 (l : Fin 32) : Option (Fin 6) :=
  if l = 23 then some 0 else if l = 24 then some 1 else if l = 18 then some 2
  else if l = 25 then some 3 else if l = 26 then some 4 else if l = 19 then some 5 else none

lemma compareDecode32_spec (l : Fin 32) (k : Fin 6) :
    compareDecode32 l = some k ↔ comparePorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def compareFrameStore32 (x y left right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 23 then List.replicate x .one else if k = 24 then List.replicate y .one
    else if k = 18 then List.replicate left .one else if k = 25 then List.replicate right .one
    else if k = 26 then [] else if k = 19 then flags else frame k

lemma compareFrameStore32_project (x y left right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.project comparePorts32 (compareFrameStore32 x y left right flags frame) =
      compareStore x y left right flags := by
  funext k
  fin_cases k <;> rfl

private lemma compare_write_at (t : Fin 6 → List BSym) (s : Fin 32 → List BSym) (k : Fin 6) :
    StackProgPortLift.write comparePorts32 t s (comparePorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := comparePorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma compareFrameStore32_write (x y left right left' right' : ℕ) (flags flags' : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.write comparePorts32 (compareStore x y left' right' flags')
      (compareFrameStore32 x y left right flags frame) =
      compareFrameStore32 x y left' right' flags' frame := by
  classical
  funext l
  by_cases hl : ∃ k, comparePorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [compare_write_at]
    exact (congrFun (compareFrameStore32_project x y left' right' flags' frame) k).symm
  · have h23 : l ≠ 23 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h24 : l ≠ 24 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h18 : l ≠ 18 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    have h25 : l ≠ 25 := by
      intro he
      apply hl
      exact ⟨3, he.symm⟩
    have h26 : l ≠ 26 := by
      intro he
      apply hl
      exact ⟨4, he.symm⟩
    have h19 : l ≠ 19 := by
      intro he
      apply hl
      exact ⟨5, he.symm⟩
    simp [StackProgPortLift.write, hl, compareFrameStore32, h23, h24, h18, h25, h26, h19]

theorem unary_compare32 : ∃ p : StackProg (Fin 32) BSym,
    ∀ (x y : ℕ) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (compareFrameStore32 x y 0 0 [] frame)
        (compareFrameStore32 x y (x-y) (y-x)
          [if x=y then BSym.one else .zero, if x<y then BSym.one else .zero] frame) steps ∧
      steps ≤ 10 * (x + y + 2) := by
  obtain ⟨p, hp⟩ := unary_compare_machine
  refine ⟨StackProgPortLift.liftProgC comparePorts32 compareDecode32 p, ?_⟩
  intro x y frame
  obtain ⟨steps, he, hb⟩ := hp x y
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec comparePorts32 compareDecode32
    compareDecode32_spec he (compareFrameStore32 x y 0 0 [] frame)
    (compareFrameStore32_project x y 0 0 [] frame)
  rw [compareFrameStore32_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: Magnitude32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def magnitude (x y : ℕ) : ℕ := if x < y then y - x else x - y

theorem magnitude_le (x y : ℕ) : magnitude x y ≤ x + y := by
  unfold magnitude
  split_ifs <;> omega

theorem magnitude_value (x y : ℕ) :
    (if x < y then -(magnitude x y : ℚ) else (magnitude x y : ℚ)) = (x : ℚ) - (y : ℚ) := by
  by_cases h : x < y
  · simp only [magnitude, h, if_true]
    rw [Nat.cast_sub (by omega : x ≤ y)]
    ring
  · simp only [magnitude, h, if_false]
    rw [Nat.cast_sub (by omega : y ≤ x)]

private def magnitudeTest (h : Fin 32 → Option BSym) : Bool := h 19 == some .one
private def magnitudeTransfer : StackProg (Fin 32) BSym :=
  transferProg 25 (fun k => decide (k = 18))
private def magnitudeKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
private def magnitudeProgram (compare : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq compare (.seq (popProg 19) (.branch magnitudeTest magnitudeTransfer magnitudeKeep))

private lemma popFlag_exec (x y left right : ℕ) (eqFlag ltFlag : BSym)
    (frame : Fin 32 → List BSym) :
    (popProg 19).Exec (compareFrameStore32 x y left right [eqFlag, ltFlag] frame)
      (compareFrameStore32 x y left right [ltFlag] frame) 1 := by
  have heq : StackProg.applyAct (fun _ k => if k = 19 then .pop else .keep)
      (compareFrameStore32 x y left right [eqFlag, ltFlag] frame) =
      compareFrameStore32 x y left right [ltFlag] frame := by
    funext k
    fin_cases k <;> rfl
  simpa only [popProg, heq] using (StackProg.Exec.act
    (fun _ k => if k = 19 then .pop else .keep)
    (compareFrameStore32 x y left right [eqFlag, ltFlag] frame))

private lemma transferMagnitude_exec (x y right : ℕ) (flags : List BSym)
    (frame : Fin 32 → List BSym) :
    magnitudeTransfer.Exec (compareFrameStore32 x y 0 right flags frame)
      (compareFrameStore32 x y right 0 flags frame) (3 * right + 1) := by
  have he := stack_transfer (25 : Fin 32) (fun k => decide (k = 18))
    (compareFrameStore32 x y 0 right flags frame)
  have heq : transferStore (25 : Fin 32) (fun k => decide (k = 18))
      (compareFrameStore32 x y 0 right flags frame) = compareFrameStore32 x y right 0 flags frame := by
    funext k
    fin_cases k <;> simp [transferStore, compareFrameStore32]
  rw [heq] at he
  simpa [magnitudeTransfer, compareFrameStore32] using he

private lemma magnitudeBranch_exec (x y : ℕ) (frame : Fin 32 → List BSym) :
    ∃ steps, (StackProg.branch magnitudeTest magnitudeTransfer magnitudeKeep).Exec
      (compareFrameStore32 x y (x-y) (y-x) [if x < y then BSym.one else .zero] frame)
      (compareFrameStore32 x y (magnitude x y) 0 [if x < y then BSym.one else .zero] frame) steps ∧
      steps ≤ 3 * (x + y) + 2 := by
  by_cases h : x < y
  · have hx : x - y = 0 := by omega
    have ht : magnitudeTest (fun k => (compareFrameStore32 x y 0 (y-x) [.one] frame k).head?) = true := by
      rfl
    have he := StackProg.Exec.branchTrue (q := magnitudeKeep) ht
      (transferMagnitude_exec x y (y-x) [.one] frame)
    refine ⟨1 + (3 * (y-x) + 1), ?_, by omega⟩
    simpa [h, hx, magnitude] using he
  · have hy : y - x = 0 := by omega
    let s := compareFrameStore32 x y (x-y) 0 [.zero] frame
    have ht : magnitudeTest (fun k => (s k).head?) = false := by rfl
    have hk : magnitudeKeep.Exec s s 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
        funext k
        rfl
      simpa only [magnitudeKeep, hid] using (StackProg.Exec.act (fun _ _ => StackAct.keep) s)
    have he := StackProg.Exec.branchFalse (p := magnitudeTransfer) ht hk
    refine ⟨2, ?_, by omega⟩
    simpa [s, h, hy, magnitude] using he

theorem magnitude32 : ∃ p : StackProg (Fin 32) BSym,
    ∀ (x y : ℕ) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (compareFrameStore32 x y 0 0 [] frame)
        (compareFrameStore32 x y (magnitude x y) 0
          [if x < y then BSym.one else .zero] frame) steps ∧
      steps ≤ 20 * (x + y + 2) := by
  obtain ⟨compare, hc⟩ := unary_compare32
  refine ⟨magnitudeProgram compare, ?_⟩
  intro x y frame
  obtain ⟨ct, heC, hct⟩ := hc x y frame
  have heP := popFlag_exec x y (x-y) (y-x)
    (if x = y then BSym.one else .zero) (if x < y then BSym.one else .zero) frame
  obtain ⟨bt, heB, hbt⟩ := magnitudeBranch_exec x y frame
  have he := StackProg.Exec.seq heC (StackProg.Exec.seq heP heB)
  refine ⟨ct + 1 + (1 + 1 + bt), he, ?_⟩
  omega

end TensorNP.Encoder
end


/- Inlined module: IntegerWriter12 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def integerFrame12 (negative : Bool) (frame : Fin 7 → List BSym) : Fin 7 → List BSym :=
  fun k => if k = 5 then [if negative then BSym.one else .zero] else frame k

def integerStore12 (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) : Fin 12 → List BSym :=
  writerStore12 n tail (integerFrame12 negative frame)

private lemma integer_encoding (n : ℕ) (negative : Bool) :
    TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) =
      (if negative && decide (0 < n) then [BSym.minus] else []) ++ encNat n ++ encNat 1 := by
  cases negative with
  | false =>
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, TensorNP.Eigen.encRat,
        Rat.num_natCast, Rat.den_natCast, encInt, Int.natAbs_natCast]
      simp
  | true =>
      simp only [Bool.true_and, ↓reduceIte, TensorNP.Eigen.encRat,
        Rat.num_neg_eq_neg_num, Rat.num_natCast, Rat.den_neg_eq_den, Rat.den_natCast,
        encInt, Int.natAbs_neg, Int.natAbs_natCast]
      simp

private def integerSignTest (h : Fin 12 → Option BSym) : Bool :=
  (h 10 == some .one) && (h 0).isSome

private def integerKeep : StackProg (Fin 12) BSym := .act (fun _ _ => .keep)

private def integerProgram (writer : StackProg (Fin 12) BSym) : StackProg (Fin 12) BSym :=
  .seq (pushProg 1 .sep) (.seq (pushProg 1 .one)
    (.seq writer (.branch integerSignTest (pushProg 1 .minus) integerKeep)))

private lemma integerStore_push (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) (a : BSym) :
    StackProg.applyAct (fun _ k => if k = 1 then .push a else .keep)
      (integerStore12 n negative tail frame) = integerStore12 n negative (a :: tail) frame := by
  funext k
  fin_cases k <;> rfl

private lemma integerPush_exec (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) (a : BSym) :
    (pushProg 1 a).Exec (integerStore12 n negative tail frame)
      (integerStore12 n negative (a :: tail) frame) 1 := by
  simpa only [pushProg, integerStore_push] using
    (StackProg.Exec.act (fun _ k => if k = 1 then .push a else .keep)
      (integerStore12 n negative tail frame))

private lemma integerSignTest_store (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) :
    integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) =
      (negative && decide (0 < n)) := by
  cases negative <;> cases n <;> rfl

private lemma integerSign_exec (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 7 → List BSym) :
    (StackProg.branch integerSignTest (pushProg 1 .minus) integerKeep).Exec
      (integerStore12 n negative tail frame)
      (integerStore12 n negative
        ((if negative && decide (0 < n) then [BSym.minus] else []) ++ tail) frame) 2 := by
  by_cases h : (negative && decide (0 < n)) = true
  · have ht : integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) = true := by
      rw [integerSignTest_store, h]
    have he := StackProg.Exec.branchTrue (q := integerKeep) ht
      (integerPush_exec n negative tail frame .minus)
    simpa [h] using he
  · have hf : (negative && decide (0 < n)) = false := Bool.eq_false_of_not_eq_true h
    have ht : integerSignTest (fun k => (integerStore12 n negative tail frame k).head?) = false := by
      rw [integerSignTest_store, hf]
    have hk : integerKeep.Exec (integerStore12 n negative tail frame)
        (integerStore12 n negative tail frame) 1 := by
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep)
          (integerStore12 n negative tail frame) = integerStore12 n negative tail frame := by
        funext k
        rfl
      simpa only [integerKeep, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) (integerStore12 n negative tail frame))
    have he := StackProg.Exec.branchFalse (p := pushProg 1 .minus) ht hk
    simpa [hf] using he

theorem integer_writer12 : ∃ (p : StackProg (Fin 12) BSym) (C : ℕ),
    ∀ (n : ℕ) (negative : Bool) (tail : List BSym) (frame : Fin 7 → List BSym), ∃ steps,
      p.Exec (integerStore12 n negative tail frame)
        (integerStore12 n negative
          (TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (n + 1)^2 := by
  obtain ⟨writer, C, hw⟩ := nativeWriter12
  refine ⟨integerProgram writer, C + 7, ?_⟩
  intro n negative tail frame
  obtain ⟨wt, heW, hwt⟩ := hw n (.one :: .sep :: tail) (integerFrame12 negative frame)
  have heW' : writer.Exec (integerStore12 n negative (.one :: .sep :: tail) frame)
      (integerStore12 n negative (encNat n ++ .one :: .sep :: tail) frame) wt := heW
  have he1 := integerPush_exec n negative tail frame .sep
  have he2 := integerPush_exec n negative (.sep :: tail) frame .one
  have he3 := integerSign_exec n negative (encNat n ++ .one :: .sep :: tail) frame
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq heW' he3))
  have hone : encNat 1 = [BSym.one, BSym.sep] := by decide
  refine ⟨1 + 1 + (1 + 1 + (wt + 1 + 2)), ?_, ?_⟩
  · simpa only [integerProgram, integer_encoding, hone, List.append_assoc, List.cons_append, List.nil_append] using he
  · have hq : 1 ≤ (n + 1)^2 := Nat.one_le_pow 2 (n + 1) (by omega)
    nlinarith

end TensorNP.Encoder
end


/- Inlined module: IntegerWriter32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def integerPorts32 : Fin 12 ↪ Fin 32 := ⟨![18, 5, 20, 21, 22, 1, 7, 14, 15, 16, 19, 17], by decide⟩

def integerDecode32 (l : Fin 32) : Option (Fin 12) :=
  if l = 18 then some 0 else if l = 5 then some 1 else if l = 20 then some 2
  else if l = 21 then some 3 else if l = 22 then some 4 else if l = 1 then some 5
  else if l = 7 then some 6 else if l = 14 then some 7 else if l = 15 then some 8
  else if l = 16 then some 9 else if l = 19 then some 10 else if l = 17 then some 11 else none

lemma integerDecode32_spec (l : Fin 32) (k : Fin 12) :
    integerDecode32 l = some k ↔ integerPorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

def integerFrameStore32 (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 18 then List.replicate n .one else if k = 5 then tail
    else if k = 19 then [if negative then .one else .zero]
    else if k = 20 ∨ k = 21 ∨ k = 22 then [] else frame k

def integerNativeFrame32 (frame : Fin 32 → List BSym) : Fin 7 → List BSym :=
  fun k => frame (integerPorts32 ⟨k.val + 5, by omega⟩)

lemma integerFrameStore32_project (n : ℕ) (negative : Bool) (tail : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.project integerPorts32 (integerFrameStore32 n negative tail frame) =
      integerStore12 n negative tail (integerNativeFrame32 frame) := by
  funext k
  fin_cases k <;> rfl

private lemma integer_write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write integerPorts32 t s (integerPorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := integerPorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma integerFrameStore32_write (n : ℕ) (negative : Bool) (tail tail' : List BSym)
    (frame : Fin 32 → List BSym) :
    StackProgPortLift.write integerPorts32 (integerStore12 n negative tail' (integerNativeFrame32 frame))
      (integerFrameStore32 n negative tail frame) = integerFrameStore32 n negative tail' frame := by
  classical
  funext l
  by_cases hl : ∃ k, integerPorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [integer_write_at]
    exact (congrFun (integerFrameStore32_project n negative tail' frame) k).symm
  · have h18 : l ≠ 18 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h5 : l ≠ 5 := by
      intro he
      apply hl
      exact ⟨1, he.symm⟩
    have h19 : l ≠ 19 := by
      intro he
      apply hl
      exact ⟨10, he.symm⟩
    have h20 : l ≠ 20 := by
      intro he
      apply hl
      exact ⟨2, he.symm⟩
    have h21 : l ≠ 21 := by
      intro he
      apply hl
      exact ⟨3, he.symm⟩
    have h22 : l ≠ 22 := by
      intro he
      apply hl
      exact ⟨4, he.symm⟩
    simp [StackProgPortLift.write, hl, integerFrameStore32, h18, h5, h19, h20, h21, h22]

theorem integer_writer32 : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (n : ℕ) (negative : Bool) (tail : List BSym) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (integerFrameStore32 n negative tail frame)
        (integerFrameStore32 n negative
          (TensorNP.Eigen.encRat (if negative then -(n : ℚ) else (n : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (n + 1)^2 := by
  obtain ⟨p, C, hp⟩ := integer_writer12
  refine ⟨StackProgPortLift.liftProgC integerPorts32 integerDecode32 p, C, ?_⟩
  intro n negative tail frame
  obtain ⟨steps, he, hb⟩ := hp n negative tail (integerNativeFrame32 frame)
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec integerPorts32 integerDecode32
    integerDecode32_spec he (integerFrameStore32 n negative tail frame)
    (integerFrameStore32_project n negative tail frame)
  rw [integerFrameStore32_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: SignedWriter32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def countWriterStore32 (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) : Fin 32 → List BSym :=
  fun k => if k = 23 then List.replicate x .one else if k = 24 then List.replicate y .one
    else if k = 5 then tail else if k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨
      k = 25 ∨ k = 26 then [] else frame k

private lemma compare_start (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) :
    compareFrameStore32 x y 0 0 [] (countWriterStore32 x y tail frame) = countWriterStore32 x y tail frame := by
  funext k
  fin_cases k <;> rfl

private lemma compare_to_integer (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym) :
    compareFrameStore32 x y (magnitude x y) 0 [if x < y then .one else .zero]
        (countWriterStore32 x y tail frame) =
      integerFrameStore32 (magnitude x y) (decide (x < y)) tail (countWriterStore32 x y tail frame) := by
  funext k
  fin_cases k <;> simp [compareFrameStore32, integerFrameStore32, countWriterStore32]

private def signedCleanup : StackProg (Fin 32) BSym :=
  .seq (clearProg 18) (.seq (clearProg 19) (.seq (clearProg 23) (clearProg 24)))

private lemma signedCleanup_exec (x y n : ℕ) (negative : Bool) (tail oldTail : List BSym)
    (frame : Fin 32 → List BSym) :
    signedCleanup.Exec (integerFrameStore32 n negative tail (countWriterStore32 x y oldTail frame))
      (countWriterStore32 0 0 tail frame) (3 * n + 3 * x + 3 * y + 10) := by
  let s0 := integerFrameStore32 n negative tail (countWriterStore32 x y oldTail frame)
  let s1 := Function.update s0 18 []
  let s2 := Function.update s1 19 []
  let s3 := Function.update s2 23 []
  let s4 := Function.update s3 24 []
  have he1 : (clearProg 18).Exec s0 s1 (3 * n + 1) := by
    simpa [s0, s1, integerFrameStore32] using (stack_basic_macros (18 : Fin 32) s0).2.2
  have he2 : (clearProg 19).Exec s1 s2 4 := by
    simpa [s0, s1, s2, integerFrameStore32] using (stack_basic_macros (19 : Fin 32) s1).2.2
  have he3 : (clearProg 23).Exec s2 s3 (3 * x + 1) := by
    simpa [s0, s1, s2, s3, integerFrameStore32, countWriterStore32] using
      (stack_basic_macros (23 : Fin 32) s2).2.2
  have he4 : (clearProg 24).Exec s3 s4 (3 * y + 1) := by
    simpa [s0, s1, s2, s3, s4, integerFrameStore32, countWriterStore32] using
      (stack_basic_macros (24 : Fin 32) s3).2.2
  have hend : s4 = countWriterStore32 0 0 tail frame := by
    funext k
    fin_cases k <;> simp [s0, s1, s2, s3, s4, integerFrameStore32, countWriterStore32, Function.update]
  rw [hend] at he4
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 (StackProg.Exec.seq he3 he4))
  convert he using 1 <;> first | rfl | omega

theorem signed_count_writer32 : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (x y : ℕ) (tail : List BSym) (frame : Fin 32 → List BSym), ∃ steps,
      p.Exec (countWriterStore32 x y tail frame)
        (countWriterStore32 0 0 (TensorNP.Eigen.encRat ((x : ℚ) - (y : ℚ)) ++ tail) frame) steps ∧
      steps ≤ C * (x + y + 2)^2 := by
  obtain ⟨mag, hm⟩ := magnitude32
  obtain ⟨writer, C, hw⟩ := integer_writer32
  refine ⟨.seq mag (.seq writer signedCleanup), C + 100, ?_⟩
  intro x y tail frame
  let base := countWriterStore32 x y tail frame
  obtain ⟨mt, heM, hmt⟩ := hm x y base
  have heM' : mag.Exec (countWriterStore32 x y tail frame)
      (integerFrameStore32 (magnitude x y) (decide (x < y)) tail base) mt := by
    simpa only [base, compare_start, compare_to_integer] using heM
  obtain ⟨wt, heW, hwt⟩ := hw (magnitude x y) (decide (x < y)) tail base
  have hvalue : (if decide (x < y) then -(magnitude x y : ℚ) else (magnitude x y : ℚ)) =
      (x : ℚ) - (y : ℚ) := by
    simpa using magnitude_value x y
  rw [hvalue] at heW
  have heClean := signedCleanup_exec x y (magnitude x y) (decide (x < y))
    (TensorNP.Eigen.encRat ((x : ℚ) - (y : ℚ)) ++ tail) tail frame
  have he := StackProg.Exec.seq heM' (StackProg.Exec.seq heW heClean)
  refine ⟨_, he, ?_⟩
  have hmag := magnitude_le x y
  have hsquare : x + y + 2 ≤ (x + y + 2)^2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _
  have hwt' : wt ≤ C * (x + y + 2)^2 :=
    hwt.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have hsum : mt + 1 + (wt + 1 + (3 * magnitude x y + 3 * x + 3 * y + 10)) ≤
      C * (x + y + 2)^2 + 100 * (x + y + 2)^2 := by omega
  calc
    _ ≤ C * (x + y + 2)^2 + 100 * (x + y + 2)^2 := hsum
    _ = _ := by ring

end TensorNP.Encoder
end


/- Inlined module: EntryFrame -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def entryRegs (v N i j k x y : ℕ) : Fin 21 → ℕ :=
  fun r => if r = 0 then v else if r = 10 then N else if r = 11 then i
    else if r = 12 then j else if r = 13 then k else if r = 14 then x
    else if r = 15 then y else 0

theorem entryRegs_count_store (input data : List BSym) (v N i j k x y : ℕ) (tail : List BSym) :
    regStore (emitterStore input data v N i j k tail) (entryRegs v N i j k x y) =
      countWriterStore32 x y tail (emitterStore input data v N i j k tail) := by
  classical
  funext l
  by_cases hl : ∃ r, regPorts r = l
  · obtain ⟨r, rfl⟩ := hl
    rw [regStore_at]
    fin_cases r <;> simp [entryRegs, regPorts, countWriterStore32, emitterStore,
      frontendGraphStore, frontendStore]
  · have hout : ∀ r, regPorts r ≠ l := by intro r h; exact hl ⟨r, h⟩
    rw [regStore, port_write_outside _ _ _ _ hout]
    have h23 : l ≠ 23 := by intro h; apply hl; exact ⟨14, h.symm⟩
    have h24 : l ≠ 24 := by intro h; apply hl; exact ⟨15, h.symm⟩
    by_cases h5 : l = 5
    · subst l
      rfl
    · simp only [countWriterStore32, regBase, regScratch, if_neg h23, if_neg h24, if_neg h5]
      split <;> simp_all

lemma entryCountWriter_zero_store (input data : List BSym) (v N i j k : ℕ)
    (tail output : List BSym) :
    countWriterStore32 0 0 output (emitterStore input data v N i j k tail) =
      emitterStore input data v N i j k output := by
  funext l
  fin_cases l <;> rfl

theorem entryRegs_zero_store (input data : List BSym) (v N i j k : ℕ) (tail : List BSym) :
    regStore (emitterStore input data v N i j k tail) (entryRegs v N i j k 0 0) =
      emitterStore input data v N i j k tail := by
  rw [entryRegs_count_store, entryCountWriter_zero_store]

theorem entry_count_emit_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (input data : List BSym) (v N i j k x y : ℕ) (tail : List BSym), ∃ steps,
      p.Exec (regStore (emitterStore input data v N i j k tail) (entryRegs v N i j k x y))
        (emitterStore input data v N i j k (TensorNP.Eigen.encRat ((x : ℚ) - (y : ℚ)) ++ tail)) steps ∧
      steps ≤ C*(x+y+2)^2 := by
  obtain ⟨p, C, hp⟩ := signed_count_writer32
  refine ⟨p, C, ?_⟩
  intro input data v N i j k x y tail
  obtain ⟨steps, hs, hb⟩ := hp x y tail (emitterStore input data v N i j k tail)
  rw [entryCountWriter_zero_store] at hs
  rw [entryRegs_count_store]
  exact ⟨steps, hs, hb⟩

end TensorNP.Encoder
end


/- Inlined module: CountCleanup -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

private def clearList : List (Fin 21) → RegCmd
  | [] => .skip
  | r :: rs => .seq (.reset r) (clearList rs)

private def cleared (R : RegFile) (rs : List (Fin 21)) : RegFile :=
  fun r => if r ∈ rs then 0 else R r

private theorem clearList_exec (data : List BSym) (R : RegFile) (rs : List (Fin 21)) :
    ∃ n, RegExec data (clearList rs) R (cleared R rs) n ∧
      n ≤ (rs.length + 1) * (regCharge R + 1) := by
  induction rs generalizing R with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · have hz : cleared R [] = R := by
          funext k
          simp [cleared]
        simpa [clearList, hz] using RegExec.skip (data := data) R
      · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
  | cons r rs ih =>
      let S := Function.update R r 0
      obtain ⟨n, hn, hbound⟩ := ih S
      have hsize : regSize S ≤ regSize R := by
        simpa [S] using regSize_update_le R r 0
      have hcharge : regCharge S ≤ regCharge R := by
        simp only [regCharge]
        omega
      have hend : cleared S rs = cleared R (r :: rs) := by
        funext k
        by_cases hk : k ∈ rs <;> by_cases hr : k = r <;> simp [cleared, S, hk, hr]
      rw [hend] at hn
      refine ⟨regCharge R + 1 + n, ?_, ?_⟩
      · exact RegExec.seq (RegExec.reset R r) hn
      · have hm : (rs.length + 1) * (regCharge S + 1) ≤
            (rs.length + 1) * (regCharge R + 1) := Nat.mul_le_mul_left _ (by omega)
        simp only [Nat.add_mul, Nat.one_mul] at hm hbound
        simp only [List.length_cons, Nat.add_assoc, Nat.add_mul, Nat.one_mul]
        omega

def swapEntryCounts : RegCmd :=
  .seq (.assign 4 14) (.seq (.assign 14 15) (.seq (.assign 15 4) (.reset 4)))

theorem swapEntryCounts_exec (data : List BSym) (R : RegFile) (h4 : R 4 = 0) :
    ∃ n, RegExec data swapEntryCounts R
      (Function.update (Function.update R 14 (R 15)) 15 (R 14)) n ∧
      n ≤ 10000 * (regSize R + 2) := by
  let S := Function.update R 4 (R 14)
  let T := Function.update S 14 (S 15)
  let U := Function.update T 15 (T 4)
  have he1 : RegExec data (.assign 4 14) R S (regCharge R) := RegExec.assign R 4 14
  have he2 : RegExec data (.assign 14 15) S T (regCharge S) := RegExec.assign S 14 15
  have he3 : RegExec data (.assign 15 4) T U (regCharge T) := RegExec.assign T 15 4
  have he4 := RegExec.reset (data := data) U 4
  have hend : Function.update U 4 0 =
      Function.update (Function.update R 14 (R 15)) 15 (R 14) := by
    funext k
    fin_cases k <;> simp [S, T, U, Function.update, h4]
  rw [hend] at he4
  have he := RegExec.seq he1 (RegExec.seq he2 (RegExec.seq he3 he4))
  have hsize1 : regSize S ≤ regSize R + R 14 := regSize_update_le R 4 (R 14)
  have hsize2 : regSize T ≤ regSize S + S 15 := regSize_update_le S 14 (S 15)
  have hsize3 : regSize U ≤ regSize T + T 4 := regSize_update_le T 15 (T 4)
  have hs15 : S 15 = R 15 := by simp [S]
  have ht4 : T 4 = R 14 := by simp [S, T]
  have hr14 := reg_le_size R 14
  have hr15 := reg_le_size R 15
  refine ⟨_, he, ?_⟩
  simp only [regCharge]
  omega

def clearEntryWork : RegCmd := clearList [1,2,3,4,5,6,7,8,9,16,17,18,19,20]

theorem clearEntryWork_exec (data : List BSym) (R : RegFile) :
    ∃ n, RegExec data clearEntryWork R (entryRegs (R 0) (R 10) (R 11) (R 12) (R 13) (R 14) (R 15)) n ∧
      n ≤ 5000 * (regSize R + 1) := by
  obtain ⟨n, hn, hbound⟩ := clearList_exec data R [1,2,3,4,5,6,7,8,9,16,17,18,19,20]
  have heq : cleared R [1,2,3,4,5,6,7,8,9,16,17,18,19,20] =
      entryRegs (R 0) (R 10) (R 11) (R 12) (R 13) (R 14) (R 15) := by
    funext r
    fin_cases r <;> simp [cleared, entryRegs]
  rw [heq] at hn
  refine ⟨n, hn, ?_⟩
  simp only [List.length_cons, List.length_nil, regCharge] at hbound
  omega

end TensorNP.Encoder
end


/- Inlined module: NegativeBlock -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma regSize_update_le_of_le (R : RegFile) (r : Fin 21) (n : ℕ) (hn : n≤R r) :
    regSize (Function.update R r n)≤regSize R := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k=r <;> simp [hk, hn]

def baseResult (R : RegFile) (data : List BSym) : RegFile :=
  Function.update (Function.update (qState R (R 3%R 0)) 14
    (rawPositiveCount (R 0) data (R 3/R 0) (R 3%R 0) (R 1) (R 2))) 15
    (rawNegativeCount (R 0) (R 3/R 0) (R 3%R 0) (R 1) (R 2))

def shiftBoth (R : RegFile) : RegFile :=
  Function.update (Function.update R 1 (R 1-R 6)) 2 (R 2-R 6)

def negativeResult (R : RegFile) (data : List BSym) : RegFile :=
  let T := baseResult (shiftBoth R) data
  Function.update (Function.update T 14 (T 15)) 15 (T 14)

def negativeBlock : RegCmd :=
  .seq (.sub 1 6 (by decide)) (.seq (.sub 2 6 (by decide))
    (.seq colorMatrixProgram swapEntryCounts))

theorem negativeBlock_exec (data : List BSym) (R : RegFile)
    (hq : R 3<4*R 0) (hlen : data.length=R 0*R 0)
    (h4 : R 4=0) (h9 : R 9=0) (h8 : R 8=0) (h14 : R 14=0) (h15 : R 15=0) :
    ∃ n, RegExec data negativeBlock R (negativeResult R data) n ∧
      n≤3000000*(2*regSize R+2)^4 := by
  let S1 := Function.update R 1 (R 1-R 6)
  let S2 := shiftBoth R
  let T := baseResult S2 data
  have he1 := RegExec.sub (data := data) R 1 6 (by decide)
  have he2 : RegExec data (.sub 2 6 (by decide)) S1 S2 (regCharge S1) := by
    simpa [S1, S2, shiftBoth] using RegExec.sub (data := data) S1 2 6 (by decide)
  obtain ⟨m, heM, hbM⟩ := colorMatrix_exec data S2
    (by simpa [S2, shiftBoth] using hq) (by simpa [S2, shiftBoth] using hlen)
    (by simpa [S2, shiftBoth] using h4) (by simpa [S2, shiftBoth] using h9)
    (by simpa [S2, shiftBoth] using h8) (by simpa [S2, shiftBoth] using h14)
    (by simpa [S2, shiftBoth] using h15)
  change RegExec data colorMatrixProgram S2 T m at heM
  have ht4 : T 4=0 := by simpa [T, baseResult, S2, shiftBoth, qState] using h4
  obtain ⟨s, heS, hbS⟩ := swapEntryCounts_exec data T ht4
  have he := RegExec.seq he1 (RegExec.seq he2 (RegExec.seq heM heS))
  refine ⟨_, he, ?_⟩
  have hs1 : regSize S1≤regSize R := regSize_update_le_of_le R 1 _ (Nat.sub_le _ _)
  have hs2' : regSize S2≤regSize S1 := by
    have h := regSize_update_le_of_le S1 2 (S1 2-S1 6) (Nat.sub_le _ _)
    simpa [S1, S2, shiftBoth] using h
  have hs2 : regSize S2≤regSize R := hs2'.trans hs1
  have hqsize : regSize (qState S2 (S2 3%S2 0))≤regSize S2 :=
    qState_size_le S2 _ (Nat.mod_le _ _)
  have hP := regSize_update_le (qState S2 (S2 3%S2 0)) 14
    (rawPositiveCount (S2 0) data (S2 3/S2 0) (S2 3%S2 0) (S2 1) (S2 2))
  have hM := regSize_update_le (Function.update (qState S2 (S2 3%S2 0)) 14
    (rawPositiveCount (S2 0) data (S2 3/S2 0) (S2 3%S2 0) (S2 1) (S2 2))) 15
    (rawNegativeCount (S2 0) (S2 3/S2 0) (S2 3%S2 0) (S2 1) (S2 2))
  have hcounts := rawCounts_le (S2 0) data (S2 3/S2 0) (S2 3%S2 0) (S2 1) (S2 2)
  have hzero := reg_le_size R 0
  have hS0 : S2 0=R 0 := by simp [S2, shiftBoth]
  have hT : regSize T≤4*regSize R+2 := by
    change regSize T≤_ at hM
    omega
  have hp : (2*regSize S2+2)^4≤(2*regSize R+2)^4 := Nat.pow_le_pow_left (by omega) 4
  have hlinear : 2*regSize R+2≤(2*regSize R+2)^4 := Nat.le_self_pow (by decide) _
  have htime : m≤2000000*(2*regSize R+2)^4 :=
    hbM.trans (Nat.mul_le_mul_left 2000000 hp)
  simp only [regCharge]
  omega

theorem negativeResult_counts (data : List BSym) (R : RegFile) :
    negativeResult R data 14=(colorCounts (R 0) data (R 3) (R 1-R 6) (R 2-R 6)).2 ∧
    negativeResult R data 15=(colorCounts (R 0) data (R 3) (R 1-R 6) (R 2-R 6)).1 := by
  simp [negativeResult, baseResult, shiftBoth, qState, colorCounts]

end TensorNP.Encoder
end


/- Inlined module: PrepareEntry -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def preparedRegs (v N i j k : ℕ) : RegFile :=
  fun r => if r = 0 then v else if r = 1 then i else if r = 2 then j else if r = 3 then k
    else if r = 5 then 4*v+2 else if r = 6 then 2*v+1 else if r = 7 then 4*v
    else if r = 10 then N else if r = 11 then i else if r = 12 then j
    else if r = 13 then k else if r = 16 then 8*v else 0

def prepareEntry : RegCmd :=
  .seq (.assign 1 11) (.seq (.assign 2 12) (.seq (.assign 3 13)
    (.seq (.assign 6 0) (.seq (.add 6 0 (by decide)) (.seq (.inc 6)
    (.seq (.assign 7 0) (.seq (.add 7 0 (by decide)) (.seq (.add 7 0 (by decide))
    (.seq (.add 7 0 (by decide)) (.seq (.assign 5 6) (.seq (.add 5 6 (by decide))
    (.seq (.assign 16 7) (.add 16 7 (by decide))))))))))))))

theorem prepareEntry_exec (data : List BSym) (v N i j k : ℕ) :
    ∃ steps, RegExec data prepareEntry (entryRegs v N i j k 0 0) (preparedRegs v N i j k) steps ∧
      steps ≤ 100000*(v+N+i+j+k+2) := by
  let R0 := entryRegs v N i j k 0 0
  let R1 := Function.update R0 1 (i)
  let R2 := Function.update R1 2 (j)
  let R3 := Function.update R2 3 (k)
  let R4 := Function.update R3 6 (v)
  let R5 := Function.update R4 6 (2*v)
  let R6 := Function.update R5 6 (2*v+1)
  let R7 := Function.update R6 7 (v)
  let R8 := Function.update R7 7 (2*v)
  let R9 := Function.update R8 7 (3*v)
  let R10 := Function.update R9 7 (4*v)
  let R11 := Function.update R10 5 (2*v+1)
  let R12 := Function.update R11 5 (4*v+2)
  let R13 := Function.update R12 16 (4*v)
  let R14 := Function.update R13 16 (8*v)
  have hv2 : v+v = 2*v := by omega
  have hv3 : v+2*v = 3*v := by omega
  have hv4 : v+3*v = 4*v := by omega
  have hv42 : (2*v+1)+(2*v+1) = 4*v+2 := by omega
  have hv8 : 4*v+4*v = 8*v := by omega
  have he1 : RegExec data (.assign 1 11) R0 R1 (regCharge R0) := by
    simpa [R1, R0, entryRegs] using RegExec.assign (data := data) R0 1 11
  have he2 : RegExec data (.assign 2 12) R1 R2 (regCharge R1) := by
    simpa [R2, R1, R0, entryRegs] using RegExec.assign (data := data) R1 2 12
  have he3 : RegExec data (.assign 3 13) R2 R3 (regCharge R2) := by
    simpa [R3, R2, R1, R0, entryRegs] using RegExec.assign (data := data) R2 3 13
  have he4 : RegExec data (.assign 6 0) R3 R4 (regCharge R3) := by
    simpa [R4, R3, R2, R1, R0, entryRegs] using RegExec.assign (data := data) R3 6 0
  have he5 : RegExec data (.add 6 0 (by decide)) R4 R5 (regCharge R4) := by
    simpa [R5, R4, R3, R2, R1, R0, entryRegs, hv2] using RegExec.add (data := data) R4 6 0 (by decide)
  have he6 : RegExec data (.inc 6) R5 R6 (regCharge R5) := by
    simpa [R6, R5, R4, R3, R2, R1, R0, entryRegs] using RegExec.inc (data := data) R5 6
  have he7 : RegExec data (.assign 7 0) R6 R7 (regCharge R6) := by
    simpa [R7, R6, R5, R4, R3, R2, R1, R0, entryRegs] using RegExec.assign (data := data) R6 7 0
  have he8 : RegExec data (.add 7 0 (by decide)) R7 R8 (regCharge R7) := by
    simpa [R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs, hv2] using RegExec.add (data := data) R7 7 0 (by decide)
  have he9 : RegExec data (.add 7 0 (by decide)) R8 R9 (regCharge R8) := by
    simpa [R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs, hv3] using RegExec.add (data := data) R8 7 0 (by decide)
  have he10 : RegExec data (.add 7 0 (by decide)) R9 R10 (regCharge R9) := by
    simpa [R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs, hv4] using RegExec.add (data := data) R9 7 0 (by decide)
  have he11 : RegExec data (.assign 5 6) R10 R11 (regCharge R10) := by
    simpa [R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs] using RegExec.assign (data := data) R10 5 6
  have he12 : RegExec data (.add 5 6 (by decide)) R11 R12 (regCharge R11) := by
    simpa [R12, R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs, hv42] using RegExec.add (data := data) R11 5 6 (by decide)
  have he13 : RegExec data (.assign 16 7) R12 R13 (regCharge R12) := by
    simpa [R13, R12, R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs] using RegExec.assign (data := data) R12 16 7
  have he14 : RegExec data (.add 16 7 (by decide)) R13 R14 (regCharge R13) := by
    simpa [R14, R13, R12, R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs, hv8] using RegExec.add (data := data) R13 16 7 (by decide)
  have hfinal : R14 = preparedRegs v N i j k := by
    funext r
    fin_cases r <;> simp [preparedRegs, R14, R13, R12, R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, entryRegs]
  have he := (RegExec.seq he1 (RegExec.seq he2 (RegExec.seq he3 (RegExec.seq he4 (RegExec.seq he5 (RegExec.seq he6 (RegExec.seq he7 (RegExec.seq he8 (RegExec.seq he9 (RegExec.seq he10 (RegExec.seq he11 (RegExec.seq he12 (RegExec.seq he13 he14)))))))))))))
  rw [hfinal] at he
  refine ⟨_, he, ?_⟩
  have hsize0 : regSize R0 = v+N+i+j+k := by
    simp [R0, regSize, entryRegs, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm]
  have hs1 : regSize R1 ≤ regSize R0+(i) := regSize_update_le R0 1 (i)
  have hs2 : regSize R2 ≤ regSize R1+(j) := regSize_update_le R1 2 (j)
  have hs3 : regSize R3 ≤ regSize R2+(k) := regSize_update_le R2 3 (k)
  have hs4 : regSize R4 ≤ regSize R3+(v) := regSize_update_le R3 6 (v)
  have hs5 : regSize R5 ≤ regSize R4+(2*v) := regSize_update_le R4 6 (2*v)
  have hs6 : regSize R6 ≤ regSize R5+(2*v+1) := regSize_update_le R5 6 (2*v+1)
  have hs7 : regSize R7 ≤ regSize R6+(v) := regSize_update_le R6 7 (v)
  have hs8 : regSize R8 ≤ regSize R7+(2*v) := regSize_update_le R7 7 (2*v)
  have hs9 : regSize R9 ≤ regSize R8+(3*v) := regSize_update_le R8 7 (3*v)
  have hs10 : regSize R10 ≤ regSize R9+(4*v) := regSize_update_le R9 7 (4*v)
  have hs11 : regSize R11 ≤ regSize R10+(2*v+1) := regSize_update_le R10 5 (2*v+1)
  have hs12 : regSize R12 ≤ regSize R11+(4*v+2) := regSize_update_le R11 5 (4*v+2)
  have hs13 : regSize R13 ≤ regSize R12+(4*v) := regSize_update_le R12 16 (4*v)
  have hs14 : regSize R14 ≤ regSize R13+(8*v) := regSize_update_le R13 16 (8*v)
  simp only [regCharge]
  omega

theorem prepareEntry_exec_bounded (data : List BSym) (v i j k : ℕ)
    (hi : i < TensorNP.Eigen.colorSize v) (hj : j < TensorNP.Eigen.colorSize v)
    (hk : k < TensorNP.Eigen.colorSize v) :
    ∃ steps, RegExec data prepareEntry (entryRegs v (TensorNP.Eigen.colorSize v) i j k 0 0)
      (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) steps ∧
      steps ≤ 10000000*(v+1) := by
  obtain ⟨steps, he, hb⟩ := prepareEntry_exec data v (TensorNP.Eigen.colorSize v) i j k
  refine ⟨steps, he, ?_⟩
  simp [TensorNP.Eigen.colorSize] at hi hj hk hb
  omega

end TensorNP.Encoder
end


/- Inlined module: TensorEntryPlan -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

/-- All eight real-split blocks use the original equation number before taking its remainder. -/
def splitBlock : RegCmd :=
  .branch true 3 7
    (.branch true 1 6
      (.branch true 2 6 colorMatrixProgram .skip)
      (.branch true 2 6 .skip negativeBlock))
    (.seq (.sub 3 7 (by decide))
      (.branch true 1 6
        (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
        (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip)))

/-- The last padded equation is the identity on the additional variables. -/
def paddingBlock : RegCmd :=
  .seq (.assign 17 3) (.seq (.inc 17)
    (.branch false 17 10
      (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip))

def selectTensorEntry : RegCmd :=
  .branch true 3 16
    (.branch true 1 5 (.branch true 2 5 splitBlock .skip) .skip)
    paddingBlock

def tensorCountProgram : RegCmd := .seq prepareEntry (.seq selectTensorEntry clearEntryWork)

/-- The fields surviving the final register cleanup. -/
def EntryKeeps (R T : RegFile) : Prop :=
  T 0=R 0 ∧ T 10=R 10 ∧ T 11=R 11 ∧ T 12=R 12 ∧ T 13=R 13

end TensorNP.Encoder
end


/- Inlined module: PaddingBlock -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

private lemma padBranchTrue (data : List BSym) (less : Bool) (r s : Fin 21)
    (yes no : RegCmd) (R T : RegFile) (n : ℕ) (hg : regCompare less r s R = true)
    (he : RegExec data yes R T n) :
    RegExec data (.branch less r s yes no) R T (regCharge R+n) := by
  apply RegExec.branch (T := T) (n := n)
  rw [hg]
  exact he

private lemma padBranchFalse (data : List BSym) (less : Bool) (r s : Fin 21)
    (yes no : RegCmd) (R T : RegFile) (n : ℕ) (hg : regCompare less r s R = false)
    (he : RegExec data no R T n) :
    RegExec data (.branch less r s yes no) R T (regCharge R+n) := by
  apply RegExec.branch (T := T) (n := n)
  rw [hg]
  exact he

lemma paddingCompare_exec (data : List BSym) (R : RegFile) (h14 : R 14 = 0) :
    let S := Function.update R 17 (R 3+1)
    let P := R 3+1 = R 10 ∧ R 5 ≤ R 1 ∧ R 1 = R 2
    ∃ n, RegExec data
      (.branch false 17 10 (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
      S (if P then Function.update S 14 1 else S) n ∧ n ≤ 4*regCharge S+1 := by
  let S := Function.update R 17 (R 3+1)
  change ∃ n, RegExec data
    (.branch false 17 10 (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
    S (if R 3+1 = R 10 ∧ R 5 ≤ R 1 ∧ R 1 = R 2 then Function.update S 14 1 else S) n ∧
      n ≤ 4*regCharge S+1
  by_cases hA : R 3+1 = R 10
  · have ga : regCompare false 17 10 S = true := by simp [regCompare, S, hA]
    by_cases hB : R 1 < R 5
    · have gb : regCompare true 1 5 S = true := by simp [regCompare, S, hB]
      have hb : RegExec data (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip))
          S S (regCharge S+1) :=
        padBranchTrue data true 1 5 .skip (.branch false 1 2 (.inc 14) .skip) S S 1 gb (RegExec.skip S)
      have ha : RegExec data (.branch false 17 10
          (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
          S S (regCharge S+(regCharge S+1)) :=
        padBranchTrue data false 17 10 _ _ S S _ ga hb
      have hn : ¬R 5 ≤ R 1 := by omega
      refine ⟨regCharge S+(regCharge S+1), ?_, by omega⟩
      rw [if_neg (by exact fun hp => hn hp.2.1)]
      exact ha
    · have gb : regCompare true 1 5 S = false := by simp [regCompare, S, hB]
      have hle : R 5 ≤ R 1 := by omega
      by_cases hC : R 1 = R 2
      · have gc : regCompare false 1 2 S = true := by simp [regCompare, S, hC]
        have hinc : RegExec data (.inc 14) S (Function.update S 14 1) (regCharge S) := by
          simpa [S, h14] using RegExec.inc (data := data) S 14
        have hc : RegExec data (.branch false 1 2 (.inc 14) .skip) S
            (Function.update S 14 1) (regCharge S+regCharge S) :=
          padBranchTrue data false 1 2 _ _ S _ _ gc hinc
        have hb : RegExec data (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip))
            S (Function.update S 14 1) (regCharge S+(regCharge S+regCharge S)) :=
          padBranchFalse data true 1 5 _ _ S _ _ gb hc
        have ha : RegExec data (.branch false 17 10
            (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
            S (Function.update S 14 1) (regCharge S+(regCharge S+(regCharge S+regCharge S))) :=
          padBranchTrue data false 17 10 _ _ S _ _ ga hb
        refine ⟨regCharge S+(regCharge S+(regCharge S+regCharge S)), ?_, by omega⟩
        rw [if_pos ⟨hA, hle, hC⟩]
        exact ha
      · have gc : regCompare false 1 2 S = false := by simp [regCompare, S, hC]
        have hc : RegExec data (.branch false 1 2 (.inc 14) .skip) S S (regCharge S+1) :=
          padBranchFalse data false 1 2 _ _ S S 1 gc (RegExec.skip S)
        have hb : RegExec data (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip))
            S S (regCharge S+(regCharge S+1)) :=
          padBranchFalse data true 1 5 _ _ S S _ gb hc
        have ha : RegExec data (.branch false 17 10
            (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
            S S (regCharge S+(regCharge S+(regCharge S+1))) :=
          padBranchTrue data false 17 10 _ _ S S _ ga hb
        refine ⟨regCharge S+(regCharge S+(regCharge S+1)), ?_, by omega⟩
        rw [if_neg (by exact fun hp => hC hp.2.2)]
        exact ha
  · have ga : regCompare false 17 10 S = false := by simp [regCompare, S, hA]
    have ha : RegExec data (.branch false 17 10
        (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip)
        S S (regCharge S+1) :=
      padBranchFalse data false 17 10 _ _ S S 1 ga (RegExec.skip S)
    refine ⟨regCharge S+1, ?_, by omega⟩
    rw [if_neg (by exact fun hp => hA hp.1)]
    exact ha

theorem paddingBlock_exec (data : List BSym) (R : RegFile) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ T n, RegExec data paddingBlock R T n ∧ EntryKeeps R T ∧
      T 14 = (if R 3+1 = R 10 ∧ R 5 ≤ R 1 ∧ R 1 = R 2 then 1 else 0) ∧
      T 15 = 0 ∧ regSize T ≤ 10*(regSize R+2) ∧ n ≤ 10000*(regSize R+2) := by
  let A := Function.update R 17 (R 3)
  let S := Function.update R 17 (R 3+1)
  let P := R 3+1 = R 10 ∧ R 5 ≤ R 1 ∧ R 1 = R 2
  let T := if P then Function.update S 14 1 else S
  have he1 : RegExec data (.assign 17 3) R A (regCharge R) := RegExec.assign R 17 3
  have hu : Function.update A 17 (A 17+1) = S := by
    funext r
    by_cases hr : r = 17 <;> simp [A, S, hr]
  have he2 : RegExec data (.inc 17) A S (regCharge A) := by
    rw [← hu]
    exact RegExec.inc A 17
  obtain ⟨m, hm, hmB⟩ := paddingCompare_exec data R h14
  change RegExec data (.branch false 17 10
    (.branch true 1 5 .skip (.branch false 1 2 (.inc 14) .skip)) .skip) S T m at hm
  change m ≤ 4*regCharge S+1 at hmB
  have he := RegExec.seq he1 (RegExec.seq he2 hm)
  refine ⟨T, regCharge R+1+(regCharge A+1+m), he, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [EntryKeeps, T, P, S]
    split <;> simp
  · dsimp [T, P]
    split <;> simp [S, h14]
  · dsimp [T, P]
    split <;> simp [S, h15]
  · have hS := regSize_update_le R 17 (R 3+1)
    have hr := reg_le_size R 3
    have hT : regSize T ≤ regSize S+1 := by
      by_cases hp : P
      · simpa [T, hp] using regSize_update_le S 14 1
      · simp [T, hp]
    change regSize S ≤ regSize R+(R 3+1) at hS
    omega
  · have hA := regSize_update_le R 17 (R 3)
    have hS := regSize_update_le R 17 (R 3+1)
    have hr := reg_le_size R 3
    change regSize A ≤ regSize R+R 3 at hA
    change regSize S ≤ regSize R+(R 3+1) at hS
    simp only [regCharge] at hmB ⊢
    omega

end TensorNP.Encoder
end


/- Inlined module: PaddingValue -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity
namespace TensorNP.Encoder

theorem tensorCounts_padding_first (data : List BSym) (v i j k : ℕ) (hk : ¬k<8*v) :
    (tensorCounts v data i j k).1 =
      (if k+1=8*v+2 ∧ 4*v+2 ≤ i ∧ i=j then 1 else 0) := by
  unfold tensorCounts
  rw [if_neg hk]
  by_cases heq : k+1=8*v+2
  · rw [if_pos heq]
    by_cases hpad : 4*v+2 ≤ i ∧ i=j
    · rw [if_pos hpad, if_pos (show k+1=8*v+2 ∧ 4*v+2 ≤ i ∧ i=j from ⟨heq,hpad⟩)]
    · rw [if_neg hpad, if_neg (show ¬(k+1=8*v+2 ∧ 4*v+2 ≤ i ∧ i=j) from fun h => hpad h.2)]
  · rw [if_neg heq, if_neg (show ¬(k+1=8*v+2 ∧ 4*v+2 ≤ i ∧ i=j) from fun h => heq h.1)]

theorem tensorCounts_padding_second (data : List BSym) (v i j k : ℕ) (hk : ¬k<8*v) :
    (tensorCounts v data i j k).2=0 := by
  unfold tensorCounts
  rw [if_neg hk]
  split_ifs <;> rfl

end TensorNP.Encoder
end


/- Inlined module: SelectEntry -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

private lemma selectorBranchTrue (data : List BSym) (less : Bool) (r s : Fin 21)
    (yes no : RegCmd) (R T : RegFile) (n : ℕ) (hg : regCompare less r s R = true)
    (he : RegExec data yes R T n) :
    RegExec data (.branch less r s yes no) R T (regCharge R+n) := by
  apply RegExec.branch (T := T) (n := n)
  rw [hg]
  exact he

private lemma selectorBranchFalse (data : List BSym) (less : Bool) (r s : Fin 21)
    (yes no : RegCmd) (R T : RegFile) (n : ℕ) (hg : regCompare less r s R = false)
    (he : RegExec data no R T n) :
    RegExec data (.branch less r s yes no) R T (regCharge R+n) := by
  apply RegExec.branch (T := T) (n := n)
  rw [hg]
  exact he

theorem selectTensorEntry_exec_of_split (data : List BSym) (v i j k : ℕ)
    (hsplit : let R := preparedRegs v (colorSize v) i j k
      k < 8*v → i < 4*v+2 → j < 4*v+2 → ∃ T n,
        RegExec data splitBlock R T n ∧ EntryKeeps R T ∧
        T 14 = (splitCounts (4*v) (2*v+1) (colorCounts v data) k i j).1 ∧
        T 15 = (splitCounts (4*v) (2*v+1) (colorCounts v data) k i j).2 ∧
        regSize T ≤ 10*(regSize R+2) ∧ n ≤ 100000000*(2*regSize R+2)^4) :
    let R := preparedRegs v (colorSize v) i j k
    ∃ T n, RegExec data selectTensorEntry R T n ∧ EntryKeeps R T ∧
      T 14 = (tensorCounts v data i j k).1 ∧ T 15 = (tensorCounts v data i j k).2 ∧
      regSize T ≤ 10*(regSize R+2) ∧ n ≤ 200000000*(2*regSize R+2)^4 := by
  let R := preparedRegs v (colorSize v) i j k
  change k < 8*v → i < 4*v+2 → j < 4*v+2 → ∃ T n,
    RegExec data splitBlock R T n ∧ EntryKeeps R T ∧
    T 14 = (splitCounts (4*v) (2*v+1) (colorCounts v data) k i j).1 ∧
    T 15 = (splitCounts (4*v) (2*v+1) (colorCounts v data) k i j).2 ∧
    regSize T ≤ 10*(regSize R+2) ∧ n ≤ 100000000*(2*regSize R+2)^4 at hsplit
  change ∃ T n, RegExec data selectTensorEntry R T n ∧ EntryKeeps R T ∧
    T 14 = (tensorCounts v data i j k).1 ∧ T 15 = (tensorCounts v data i j k).2 ∧
    regSize T ≤ 10*(regSize R+2) ∧ n ≤ 200000000*(2*regSize R+2)^4
  have hp : regSize R+2 ≤ (2*regSize R+2)^4 := by
    have hle : regSize R+2 ≤ 2*regSize R+2 := by omega
    exact hle.trans (Nat.le_self_pow (by decide) _)
  by_cases hk : k < 8*v
  · have ga : regCompare true 3 16 R = true := by simp [regCompare, R, preparedRegs, hk]
    by_cases hi : i < 4*v+2
    · have gb : regCompare true 1 5 R = true := by simp [regCompare, R, preparedRegs, hi]
      by_cases hj : j < 4*v+2
      · have gc : regCompare true 2 5 R = true := by simp [regCompare, R, preparedRegs, hj]
        obtain ⟨T, n, he, hkeep, h14, h15, hsize, htime⟩ := hsplit hk hi hj
        have hc : RegExec data (.branch true 2 5 splitBlock .skip) R T (regCharge R+n) :=
          selectorBranchTrue data true 2 5 _ _ R T n gc he
        have hb : RegExec data (.branch true 1 5 (.branch true 2 5 splitBlock .skip) .skip)
            R T (regCharge R+(regCharge R+n)) :=
          selectorBranchTrue data true 1 5 _ _ R T _ gb hc
        have ha : RegExec data selectTensorEntry R T (regCharge R+(regCharge R+(regCharge R+n))) :=
          selectorBranchTrue data true 3 16 _ _ R T _ ga hb
        refine ⟨T, _, ha, hkeep, ?_, ?_, hsize, ?_⟩
        · simpa [tensorCounts, hk, hi, hj] using h14
        · simpa [tensorCounts, hk, hi, hj] using h15
        · simp only [regCharge]
          omega
      · have gc : regCompare true 2 5 R = false := by simp [regCompare, R, preparedRegs, hj]
        have hc : RegExec data (.branch true 2 5 splitBlock .skip) R R (regCharge R+1) :=
          selectorBranchFalse data true 2 5 _ _ R R 1 gc (RegExec.skip R)
        have hb : RegExec data (.branch true 1 5 (.branch true 2 5 splitBlock .skip) .skip)
            R R (regCharge R+(regCharge R+1)) :=
          selectorBranchTrue data true 1 5 _ _ R R _ gb hc
        have ha : RegExec data selectTensorEntry R R (regCharge R+(regCharge R+(regCharge R+1))) :=
          selectorBranchTrue data true 3 16 _ _ R R _ ga hb
        refine ⟨R, _, ha, by simp [EntryKeeps], ?_, ?_, by omega, ?_⟩
        · simp [tensorCounts, hk, hj, R, preparedRegs]
        · simp [tensorCounts, hk, hj, R, preparedRegs]
        · simp only [regCharge]
          omega
    · have gb : regCompare true 1 5 R = false := by simp [regCompare, R, preparedRegs, hi]
      have hb : RegExec data (.branch true 1 5 (.branch true 2 5 splitBlock .skip) .skip)
          R R (regCharge R+1) :=
        selectorBranchFalse data true 1 5 _ _ R R 1 gb (RegExec.skip R)
      have ha : RegExec data selectTensorEntry R R (regCharge R+(regCharge R+1)) :=
        selectorBranchTrue data true 3 16 _ _ R R _ ga hb
      refine ⟨R, _, ha, by simp [EntryKeeps], ?_, ?_, by omega, ?_⟩
      · simp [tensorCounts, hk, hi, R, preparedRegs]
      · simp [tensorCounts, hk, hi, R, preparedRegs]
      · simp only [regCharge]
        omega
  · have ga : regCompare true 3 16 R = false := by simp [regCompare, R, preparedRegs, hk]
    have h14R : R 14 = 0 := by simp [R, preparedRegs]
    have h15R : R 15 = 0 := by simp [R, preparedRegs]
    obtain ⟨T, n, he, hkeep, h14, h15, hsize, htime⟩ := paddingBlock_exec data R h14R h15R
    have ha : RegExec data selectTensorEntry R T (regCharge R+n) :=
      selectorBranchFalse data true 3 16 _ _ R T n ga he
    refine ⟨T, _, ha, hkeep, ?_, ?_, hsize, ?_⟩
    · have h14' : T 14 = (if k+1 = 8*v+2 ∧ 4*v+2 ≤ i ∧ i = j then 1 else 0) := by
        change T 14 = (if k+1 = 8*v+2 ∧ 4*v+2 ≤ i ∧ i = j then 1 else 0) at h14
        exact h14
      exact h14'.trans (tensorCounts_padding_first data v i j k hk).symm
    · exact h15.trans (tensorCounts_padding_second data v i j k hk).symm
    · simp only [regCharge]
      omega

end TensorNP.Encoder
end


/- Inlined module: BlockFacts -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma baseResult_keeps (data : List BSym) (R : RegFile) : EntryKeeps R (baseResult R data) := by
  simp [EntryKeeps, baseResult, qState]

lemma negativeResult_keeps (data : List BSym) (R : RegFile) : EntryKeeps R (negativeResult R data) := by
  simp [EntryKeeps, negativeResult, baseResult, shiftBoth, qState]

lemma baseResult_counts (data : List BSym) (R : RegFile) :
    baseResult R data 14=(colorCounts (R 0) data (R 3) (R 1) (R 2)).1 ∧
    baseResult R data 15=(colorCounts (R 0) data (R 3) (R 1) (R 2)).2 := by
  simp [baseResult, colorCounts]

lemma baseResult_size (data : List BSym) (R : RegFile) : regSize (baseResult R data)≤4*regSize R+2 := by
  have hq := qState_size_le R (R 3%R 0) (Nat.mod_le _ _)
  have hp := regSize_update_le (qState R (R 3%R 0)) 14
    (rawPositiveCount (R 0) data (R 3/R 0) (R 3%R 0) (R 1) (R 2))
  have hn := regSize_update_le (Function.update (qState R (R 3%R 0)) 14
    (rawPositiveCount (R 0) data (R 3/R 0) (R 3%R 0) (R 1) (R 2))) 15
    (rawNegativeCount (R 0) (R 3/R 0) (R 3%R 0) (R 1) (R 2))
  have hc := rawCounts_le (R 0) data (R 3/R 0) (R 3%R 0) (R 1) (R 2)
  have hv := reg_le_size R 0
  change regSize (baseResult R data)≤_ at hn
  omega

lemma shiftBoth_size (R : RegFile) : regSize (shiftBoth R)≤regSize R := by
  let S := Function.update R 1 (R 1-R 6)
  have ha := regSize_update_le_of_le R 1 (R 1-R 6) (Nat.sub_le _ _)
  have hb := regSize_update_le_of_le S 2 (S 2-S 6) (Nat.sub_le _ _)
  have he : Function.update S 2 (S 2-S 6)=shiftBoth R := by simp [S, shiftBoth]
  rw [he] at hb
  exact hb.trans ha

lemma negativeResult_size (data : List BSym) (R : RegFile) : regSize (negativeResult R data)≤7*regSize R+4 := by
  let T := baseResult (shiftBoth R) data
  have ht := baseResult_size data (shiftBoth R)
  change regSize T≤_ at ht
  have hs := shiftBoth_size R
  have hp := regSize_update_le T 14 (T 15)
  have hn := regSize_update_le (Function.update T 14 (T 15)) 15 (T 14)
  have hc : T 14+T 15≤3*R 0+2 := by
    simpa [T, baseResult, shiftBoth] using rawCounts_le (R 0) data (R 3/R 0) (R 3%R 0)
      (R 1-R 6) (R 2-R 6)
  have hv := reg_le_size R 0
  change regSize (negativeResult R data)≤_ at hn
  omega

end TensorNP.Encoder
end


/- Inlined module: SplitBlock -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

private def shifted (R : RegFile) (r : Fin 21) : RegFile :=
  Function.update R r (R r - R 6)

private theorem offsetMatrix_exec (data : List BSym) (R : RegFile) (r : Fin 21)
    (hr : r = 1 ∨ r = 2) (hq : R 3 < 4 * R 0) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ n, RegExec data (.seq (.sub r 6 (by rcases hr with rfl | rfl <;> decide)) colorMatrixProgram)
      R (baseResult (shifted R r) data) n ∧
      n ≤ 3000000 * (2 * regSize R + 2)^4 := by
  let S := shifted R r
  have hs0 : S 0 = R 0 := by rcases hr with rfl | rfl <;> simp [S, shifted]
  have hs3 : S 3 = R 3 := by rcases hr with rfl | rfl <;> simp [S, shifted]
  have hs4 : S 4 = 0 := by rcases hr with rfl | rfl <;> simpa [S, shifted] using h4
  have hs9 : S 9 = 0 := by rcases hr with rfl | rfl <;> simpa [S, shifted] using h9
  have hs8 : S 8 = 0 := by rcases hr with rfl | rfl <;> simpa [S, shifted] using h8
  have hs14 : S 14 = 0 := by rcases hr with rfl | rfl <;> simpa [S, shifted] using h14
  have hs15 : S 15 = 0 := by rcases hr with rfl | rfl <;> simpa [S, shifted] using h15
  obtain ⟨n, hn, hb⟩ := colorMatrix_exec data S (by simpa [hs0, hs3] using hq)
    (by simpa [hs0] using hlen) hs4 hs9 hs8 hs14 hs15
  change RegExec data colorMatrixProgram S (baseResult S data) n at hn
  have hsub : RegExec data (.sub r 6 (by rcases hr with rfl | rfl <;> decide)) R S (regCharge R) :=
    RegExec.sub R r 6 (by rcases hr with rfl | rfl <;> decide)
  have he := RegExec.seq hsub hn
  refine ⟨_, he, ?_⟩
  have hsize : regSize S ≤ regSize R := regSize_update_le_of_le R r _ (Nat.sub_le _ _)
  have hp : (2 * regSize S + 2)^4 ≤ (2 * regSize R + 2)^4 :=
    Nat.pow_le_pow_left (by omega) 4
  have hm := Nat.mul_le_mul_left 2000000 hp
  have hlin : 2 * regSize R + 2 ≤ (2 * regSize R + 2)^4 := Nat.le_self_pow (by decide) _
  simp only [regCharge]
  omega


private theorem branchLess_yes (data : List BSym) (R T : RegFile) (r s : Fin 21)
    (yes no : RegCmd) (n : ℕ) (h : R r < R s) (he : RegExec data yes R T n) :
    RegExec data (.branch true r s yes no) R T (regCharge R + n) := by
  apply RegExec.branch
  simpa [regCompare, h] using he

private theorem branchLess_no (data : List BSym) (R T : RegFile) (r s : Fin 21)
    (yes no : RegCmd) (n : ℕ) (h : ¬ R r < R s) (he : RegExec data no R T n) :
    RegExec data (.branch true r s yes no) R T (regCharge R + n) := by
  apply RegExec.branch
  simpa [regCompare, h] using he

private def lowerSplit : RegCmd :=
  .branch true 1 6 (.branch true 2 6 colorMatrixProgram .skip)
    (.branch true 2 6 .skip negativeBlock)

private theorem lowerSplit_exec (data : List BSym) (R : RegFile)
    (hq : R 3 < 4 * R 0) (hn : R 6 = 2 * R 0 + 1)
    (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ T n, RegExec data lowerSplit R T n ∧ EntryKeeps R T ∧
      T 14 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3) (R 1) (R 2)).1 ∧
      T 15 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3) (R 1) (R 2)).2 ∧
      regSize T ≤ 10 * (regSize R + 2) ∧ n ≤ 10000000 * (2 * regSize R + 2)^4 := by
  have hp : 2 * regSize R + 2 ≤ (2 * regSize R + 2)^4 := Nat.le_self_pow (by decide) _
  by_cases ha : R 1 < R 6 <;> by_cases hb : R 2 < R 6
  · obtain ⟨n, he, ht⟩ := colorMatrix_exec data R hq hlen h4 h9 h8 h14 h15
    change RegExec data colorMatrixProgram R (baseResult R data) n at he
    have he' := branchLess_yes data R _ 1 6 (.branch true 2 6 colorMatrixProgram .skip)
      (.branch true 2 6 .skip negativeBlock) _ ha
      (branchLess_yes data R _ 2 6 colorMatrixProgram .skip _ hb he)
    refine ⟨baseResult R data, _, he', baseResult_keeps data R, ?_, ?_, ?_, ?_⟩
    · simpa [splitCounts, hq, ← hn, ha, hb] using (baseResult_counts data R).1
    · simpa [splitCounts, hq, ← hn, ha, hb] using (baseResult_counts data R).2
    · have h := baseResult_size data R
      omega
    · simp only [regCharge]
      omega
  · have he' := branchLess_yes data R _ 1 6 (.branch true 2 6 colorMatrixProgram .skip)
      (.branch true 2 6 .skip negativeBlock) _ ha
      (branchLess_no data R R 2 6 colorMatrixProgram .skip _ hb (RegExec.skip R))
    refine ⟨R, _, he', ?_, ?_, ?_, by omega, ?_⟩
    · simp [EntryKeeps]
    · simpa [splitCounts, hq, ← hn, ha, hb] using h14
    · simpa [splitCounts, hq, ← hn, ha, hb] using h15
    · simp only [regCharge]
      omega
  · have he' := branchLess_no data R _ 1 6 (.branch true 2 6 colorMatrixProgram .skip)
      (.branch true 2 6 .skip negativeBlock) _ ha
      (branchLess_yes data R R 2 6 .skip negativeBlock _ hb (RegExec.skip R))
    refine ⟨R, _, he', ?_, ?_, ?_, by omega, ?_⟩
    · simp [EntryKeeps]
    · simpa [splitCounts, hq, ← hn, ha, hb] using h14
    · simpa [splitCounts, hq, ← hn, ha, hb] using h15
    · simp only [regCharge]
      omega
  · obtain ⟨n, he, ht⟩ := negativeBlock_exec data R hq hlen h4 h9 h8 h14 h15
    have he' := branchLess_no data R _ 1 6 (.branch true 2 6 colorMatrixProgram .skip)
      (.branch true 2 6 .skip negativeBlock) _ ha
      (branchLess_no data R _ 2 6 .skip negativeBlock _ hb he)
    refine ⟨negativeResult R data, _, he', negativeResult_keeps data R, ?_, ?_, ?_, ?_⟩
    · simpa [splitCounts, hq, ← hn, ha, hb, swapCounts] using (negativeResult_counts data R).1
    · simpa [splitCounts, hq, ← hn, ha, hb, swapCounts] using (negativeResult_counts data R).2
    · have h := negativeResult_size data R
      omega
    · simp only [regCharge]
      omega


private def upperSplit : RegCmd :=
  .branch true 1 6
    (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
    (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip)

private theorem upperSplit_exec (data : List BSym) (R : RegFile)
    (hq : R 3 < 4 * R 0) (hn : R 6 = 2 * R 0 + 1)
    (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ T n, RegExec data upperSplit R T n ∧ EntryKeeps R T ∧
      T 14 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3 + 4 * R 0) (R 1) (R 2)).1 ∧
      T 15 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3 + 4 * R 0) (R 1) (R 2)).2 ∧
      regSize T ≤ 10 * (regSize R + 2) ∧ n ≤ 10000000 * (2 * regSize R + 2)^4 := by
  have hp : 2 * regSize R + 2 ≤ (2 * regSize R + 2)^4 := Nat.le_self_pow (by decide) _
  have hq' : ¬ R 3 + 4 * R 0 < 4 * R 0 := by omega
  by_cases ha : R 1 < R 6 <;> by_cases hb : R 2 < R 6
  · have he' := branchLess_yes data R _ 1 6
      (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
      (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip) _ ha
      (branchLess_yes data R R 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram)
        _ hb (RegExec.skip R))
    refine ⟨R, _, he', ?_, ?_, ?_, by omega, ?_⟩
    · simp [EntryKeeps]
    · simpa [splitCounts, hq', ← hn, ha, hb] using h14
    · simpa [splitCounts, hq', ← hn, ha, hb] using h15
    · simp only [regCharge]
      omega
  · obtain ⟨n, he, ht⟩ := offsetMatrix_exec data R 2 (Or.inr rfl) hq hlen h4 h9 h8 h14 h15
    have he' := branchLess_yes data R _ 1 6
      (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
      (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip) _ ha
      (branchLess_no data R _ 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram) _ hb he)
    refine ⟨baseResult (shifted R 2) data, _, he', ?_, ?_, ?_, ?_, ?_⟩
    · simp [EntryKeeps, baseResult, shifted, qState]
    · simpa [splitCounts, hq', ← hn, ha, hb, shifted] using (baseResult_counts data (shifted R 2)).1
    · simpa [splitCounts, hq', ← hn, ha, hb, shifted] using (baseResult_counts data (shifted R 2)).2
    · have hs := regSize_update_le_of_le R 2 (R 2 - R 6) (Nat.sub_le _ _)
      have ht' := baseResult_size data (shifted R 2)
      change regSize (shifted R 2) ≤ regSize R at hs
      omega
    · simp only [regCharge]
      omega
  · obtain ⟨n, he, ht⟩ := offsetMatrix_exec data R 1 (Or.inl rfl) hq hlen h4 h9 h8 h14 h15
    have he' := branchLess_no data R _ 1 6
      (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
      (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip) _ ha
      (branchLess_yes data R _ 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip _ hb he)
    refine ⟨baseResult (shifted R 1) data, _, he', ?_, ?_, ?_, ?_, ?_⟩
    · simp [EntryKeeps, baseResult, shifted, qState]
    · simpa [splitCounts, hq', ← hn, ha, hb, shifted] using (baseResult_counts data (shifted R 1)).1
    · simpa [splitCounts, hq', ← hn, ha, hb, shifted] using (baseResult_counts data (shifted R 1)).2
    · have hs := regSize_update_le_of_le R 1 (R 1 - R 6) (Nat.sub_le _ _)
      have ht' := baseResult_size data (shifted R 1)
      change regSize (shifted R 1) ≤ regSize R at hs
      omega
    · simp only [regCharge]
      omega
  · have he' := branchLess_no data R _ 1 6
      (.branch true 2 6 .skip (.seq (.sub 2 6 (by decide)) colorMatrixProgram))
      (.branch true 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip) _ ha
      (branchLess_no data R R 2 6 (.seq (.sub 1 6 (by decide)) colorMatrixProgram) .skip
        _ hb (RegExec.skip R))
    refine ⟨R, _, he', ?_, ?_, ?_, by omega, ?_⟩
    · simp [EntryKeeps]
    · simpa [splitCounts, hq', ← hn, ha, hb] using h14
    · simpa [splitCounts, hq', ← hn, ha, hb] using h15
    · simp only [regCharge]
      omega


theorem splitBlock_exec (data : List BSym) (R : RegFile)
    (hq : R 3 < 8 * R 0) (hn : R 6 = 2 * R 0 + 1) (hm : R 7 = 4 * R 0)
    (_ha : R 1 < 2 * R 6) (_hb : R 2 < 2 * R 6) (hlen : data.length = R 0 * R 0)
    (h4 : R 4 = 0) (h9 : R 9 = 0) (h8 : R 8 = 0) (h14 : R 14 = 0) (h15 : R 15 = 0) :
    ∃ T n, RegExec data splitBlock R T n ∧ EntryKeeps R T ∧
      T 14 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3) (R 1) (R 2)).1 ∧
      T 15 = (splitCounts (4 * R 0) (2 * R 0 + 1) (colorCounts (R 0) data) (R 3) (R 1) (R 2)).2 ∧
      regSize T ≤ 10 * (regSize R + 2) ∧ n ≤ 100000000 * (2 * regSize R + 2)^4 := by
  have hp : 2 * regSize R + 2 ≤ (2 * regSize R + 2)^4 := Nat.le_self_pow (by decide) _
  by_cases hq7 : R 3 < R 7
  · obtain ⟨T, n, he, hk, hc14, hc15, hs, ht⟩ := lowerSplit_exec data R
      (by omega) hn hlen h4 h9 h8 h14 h15
    have he' := branchLess_yes data R T 3 7 lowerSplit
      (.seq (.sub 3 7 (by decide)) upperSplit) n hq7 he
    refine ⟨T, _, he', hk, hc14, hc15, hs, ?_⟩
    simp only [regCharge]
    omega
  · let S := qState R (R 3 - R 7)
    have hs0 : S 0 = R 0 := by simp [S, qState]
    have hs1 : S 1 = R 1 := by simp [S, qState]
    have hs2 : S 2 = R 2 := by simp [S, qState]
    have hs3 : S 3 = R 3 - R 7 := by simp [S, qState]
    have hs6 : S 6 = R 6 := by simp [S, qState]
    have hsq : S 3 < 4 * S 0 := by rw [hs3, hs0]; omega
    have hslen : data.length = S 0 * S 0 := by simpa [hs0] using hlen
    have hs4 : S 4 = 0 := by simpa [S, qState] using h4
    have hs9 : S 9 = 0 := by simpa [S, qState] using h9
    have hs8 : S 8 = 0 := by simpa [S, qState] using h8
    have hs14 : S 14 = 0 := by simpa [S, qState] using h14
    have hs15 : S 15 = 0 := by simpa [S, qState] using h15
    obtain ⟨T, n, he, hk, hc14, hc15, hs, ht⟩ := upperSplit_exec data S hsq
      (by simpa [hs0, hs6] using hn) hslen hs4 hs9 hs8 hs14 hs15
    have hsub : RegExec data (.sub 3 7 (by decide)) R S (regCharge R) := by
      simpa [S, qState] using RegExec.sub (data := data) R 3 7 (by decide)
    have he' := branchLess_no data R T 3 7 lowerSplit
      (.seq (.sub 3 7 (by decide)) upperSplit) _ hq7 (RegExec.seq hsub he)
    have hsSize : regSize S ≤ regSize R := qState_size_le R _ (Nat.sub_le _ _)
    have hp' : (2 * regSize S + 2)^4 ≤ (2 * regSize R + 2)^4 :=
      Nat.pow_le_pow_left (by omega) 4
    have hbudget := Nat.mul_le_mul_left 10000000 hp'
    have hqeq : S 3 + 4 * R 0 = R 3 := by rw [hs3]; omega
    refine ⟨T, _, he', ?_, ?_, ?_, ?_, ?_⟩
    · simpa [EntryKeeps, S, qState] using hk
    · simpa only [hs0, hs1, hs2, hqeq] using hc14
    · simpa only [hs0, hs1, hs2, hqeq] using hc15
    · omega
    · simp only [regCharge]
      omega

end TensorNP.Encoder
end


/- Inlined module: EntryCounterAssembly -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

lemma preparedRegs_size_le (v i j k : ℕ)
    (hi : i < TensorNP.Eigen.colorSize v) (hj : j < TensorNP.Eigen.colorSize v)
    (hk : k < TensorNP.Eigen.colorSize v) :
    regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) ≤ 100 * (v + 1) := by
  have heq : regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) =
      19*v + 3 + TensorNP.Eigen.colorSize v + 2*(i+j+k) := by
    simp [regSize, preparedRegs, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm]
    omega
  rw [heq]
  simp only [TensorNP.Eigen.colorSize] at hi hj hk ⊢
  omega

theorem tensorCountProgram_exec_of_select (data : List BSym) (v i j k : ℕ)
    (hi : i < TensorNP.Eigen.colorSize v) (hj : j < TensorNP.Eigen.colorSize v)
    (hk : k < TensorNP.Eigen.colorSize v)
    (hselect : ∃ T n, RegExec data selectTensorEntry
        (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) T n ∧
      EntryKeeps (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) T ∧
      T 14 = (tensorCounts v data i j k).1 ∧ T 15 = (tensorCounts v data i j k).2 ∧
      regSize T ≤ 10 * (regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) + 2) ∧
      n ≤ 200000000 * (2 * regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) + 2)^4) :
    ∃ steps, RegExec data tensorCountProgram (entryRegs v (TensorNP.Eigen.colorSize v) i j k 0 0)
      (entryRegs v (TensorNP.Eigen.colorSize v) i j k
        (tensorCounts v data i j k).1 (tensorCounts v data i j k).2) steps ∧
      steps ≤ 1000000000000000000 * (v + 1)^4 := by
  obtain ⟨a, ha, haB⟩ := prepareEntry_exec_bounded data v i j k hi hj hk
  obtain ⟨T, n, he, hk', hp, hm, hs, ht⟩ := hselect
  obtain ⟨c, hc, hcB⟩ := clearEntryWork_exec data T
  have hresult : entryRegs (T 0) (T 10) (T 11) (T 12) (T 13) (T 14) (T 15) =
      entryRegs v (TensorNP.Eigen.colorSize v) i j k
        (tensorCounts v data i j k).1 (tensorCounts v data i j k).2 := by
    rcases hk' with ⟨h0, h10, h11, h12, h13⟩
    simp [preparedRegs] at h0 h10 h11 h12 h13
    rw [h0, h10, h11, h12, h13, hp, hm]
  rw [hresult] at hc
  have hexec := RegExec.seq ha (RegExec.seq he hc)
  refine ⟨_, hexec, ?_⟩
  have hR := preparedRegs_size_le v i j k hi hj hk
  have hb : 2 * regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) + 2 ≤ 202 * (v+1) := by omega
  have hp4 := Nat.pow_le_pow_left hb 4
  have hp4' : (2 * regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) + 2)^4 ≤
      202^4 * (v+1)^4 := by
    calc
      _ ≤ (202*(v+1))^4 := hp4
      _ = _ := by ring
  have hselector : n ≤ 400000000000000000 * (v+1)^4 := by
    calc
      n ≤ 200000000 * (2 * regSize (preparedRegs v (TensorNP.Eigen.colorSize v) i j k) + 2)^4 := ht
      _ ≤ 200000000 * (202^4 * (v+1)^4) := Nat.mul_le_mul_left _ hp4'
      _ = (200000000 * 202^4) * (v+1)^4 := by rw [Nat.mul_assoc]
      _ ≤ 400000000000000000 * (v+1)^4 := Nat.mul_le_mul_right _ (by norm_num)
  have hlinear : v + 1 ≤ (v+1)^4 := Nat.le_self_pow (by decide) _
  have hcost : a + c + 2 ≤ 16000000 * (v+1) := by omega
  calc
    a + 1 + (n + 1 + c) = n + (a+c+2) := by omega
    _ ≤ 400000000000000000 * (v+1)^4 + 16000000 * (v+1) :=
      Nat.add_le_add hselector hcost
    _ ≤ 400000000000000000 * (v+1)^4 + 16000000 * (v+1)^4 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hlinear) _
    _ = (400000000000000000 + 16000000) * (v+1)^4 := by rw [Nat.add_mul]
    _ ≤ 1000000000000000000 * (v+1)^4 := Nat.mul_le_mul_right _ (by decide)

end TensorNP.Encoder
end


/- Inlined module: ActualCounts -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

theorem tensorCountProgram_exec (data : List BSym) (v i j k : ℕ)
    (hlen : data.length=v*v) (hi : i<colorSize v) (hj : j<colorSize v) (hk : k<colorSize v) :
    ∃ steps, RegExec data tensorCountProgram (entryRegs v (colorSize v) i j k 0 0)
      (entryRegs v (colorSize v) i j k (tensorCounts v data i j k).1 (tensorCounts v data i j k).2) steps ∧
      steps≤1000000000000000000*(v+1)^4 := by
  apply tensorCountProgram_exec_of_select data v i j k hi hj hk
  apply selectTensorEntry_exec_of_split data v i j k
  dsimp only
  intro hk8 hi4 hj4
  let R := preparedRegs v (colorSize v) i j k
  have h0 : R 0=v := by simp [R, preparedRegs]
  have h1 : R 1=i := by simp [R, preparedRegs]
  have h2 : R 2=j := by simp [R, preparedRegs]
  have h3 : R 3=k := by simp [R, preparedRegs]
  have h6 : R 6=2*v+1 := by simp [R, preparedRegs]
  have he := splitBlock_exec data R
    (by simpa only [h0, h3] using hk8)
    (by simp [R, preparedRegs]) (by simp [R, preparedRegs])
    (by rw [h1,h6]; omega) (by rw [h2,h6]; omega)
    (by simpa only [h0] using hlen)
    (by simp [R, preparedRegs]) (by simp [R, preparedRegs]) (by simp [R, preparedRegs])
    (by simp [R, preparedRegs]) (by simp [R, preparedRegs])
  simpa only [h0, h1, h2, h3] using he

end TensorNP.Encoder
end


/- Inlined module: RegisterMacros -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def regKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
def regReset (r : Fin 21) : StackProg (Fin 32) BSym := clearProg (regPorts r)
def regInc (r : Fin 21) : StackProg (Fin 32) BSym := pushProg (regPorts r) .one
def regPop (r : Fin 21) : StackProg (Fin 32) BSym := popProg (regPorts r)
def regAdd (dst src : Fin 21) : StackProg (Fin 32) BSym := copyProg (regPorts src) (regPorts dst) 20
def regAssign (dst src : Fin 21) : StackProg (Fin 32) BSym :=
  if dst = src then regKeep else .seq (regReset dst) (regAdd dst src)

theorem regKeep_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    regKeep.Exec (regStore frame R) (regStore frame R) 1 := by
  have he : StackProg.applyAct (fun _ _ => StackAct.keep) (regStore frame R) = regStore frame R := by
    funext k
    rfl
  simpa only [regKeep, he] using StackProg.Exec.act (fun _ _ => StackAct.keep) (regStore frame R)

theorem regReset_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regReset r).Exec (regStore frame R) (regStore frame (Function.update R r 0)) (3*(R r)+1) := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).2.2
  rw [regStore_update]
  simpa [regReset] using he

theorem regInc_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regInc r).Exec (regStore frame R) (regStore frame (Function.update R r (R r+1))) 1 := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).1 BSym.one
  rw [regStore_update]
  simpa [regInc, List.replicate_succ] using he

theorem regPop_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) :
    (regPop r).Exec (regStore frame R) (regStore frame (Function.update R r (R r-1))) 1 := by
  have he := (stack_basic_macros (regPorts r) (regStore frame R)).2.1
  rw [regStore_update]
  simpa [regPop] using he

theorem regAdd_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (dst src : Fin 21)
    (h : dst ≠ src) :
    (regAdd dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R src + R dst))) (6*(R src)+3) := by
  have hsd : regPorts src ≠ regPorts dst := fun he => h (regPorts.injective he).symm
  have hst : regPorts src ≠ 20 := regScratch_outside 20 (by decide) src
  have hdt : regPorts dst ≠ 20 := regScratch_outside 20 (by decide) dst
  have he := stack_copy (regPorts src) (regPorts dst) 20 hsd hst hdt (regStore frame R)
    (regStore_scratch frame R 20 (by decide))
  have hu : Function.update (regStore frame R) (regPorts dst)
      (regStore frame R (regPorts src) ++ regStore frame R (regPorts dst)) =
      regStore frame (Function.update R dst (R src + R dst)) := by
    rw [regStore_update]
    simp
  rw [hu] at he
  simpa [regAdd] using he

theorem regAssign_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (dst src : Fin 21) :
    ∃ steps, (regAssign dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R src))) steps ∧ steps ≤ 10*(regSize R+1) := by
  by_cases h : dst = src
  · subst src
    have hu : Function.update R dst (R dst) = R := by
      funext r
      by_cases hr : r = dst <;> simp [hr]
    refine ⟨1, ?_, ?_⟩
    · simpa [regAssign, hu] using regKeep_exec frame R
    · omega
  · let S := Function.update R dst 0
    have hs : S src = R src := by simp [S, Ne.symm h]
    have hu : Function.update S dst (S src + S dst) = Function.update R dst (R src) := by
      funext r
      by_cases hr : r = dst <;> simp [S, hr, Ne.symm h]
    have he := StackProg.Exec.seq (regReset_exec frame R dst) (regAdd_exec frame S dst src h)
    rw [hu] at he
    refine ⟨(3*(R dst)+1)+1+(6*(S src)+3), ?_, ?_⟩
    · simpa [regAssign, h, S] using he
    · have hdst := reg_le_size R dst
      have hsrc := reg_le_size R src
      omega

def regIncs (r : Fin 21) : ℕ → StackProg (Fin 32) BSym
  | 0 => regKeep
  | n+1 => .seq (regInc r) (regIncs r n)

def regSetConst (r : Fin 21) (n : ℕ) : StackProg (Fin 32) BSym :=
  .seq (regReset r) (regIncs r n)

theorem regIncs_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    (regIncs r n).Exec (regStore frame R) (regStore frame (Function.update R r (R r+n))) (2*n+1) := by
  induction n generalizing R with
  | zero =>
      have hu : Function.update R r (R r + 0) = R := by
        funext q
        by_cases hq : q = r <;> simp [hq]
      simpa [regIncs, hu] using regKeep_exec frame R
  | succ n ih =>
      have he := StackProg.Exec.seq (regInc_exec frame R r) (ih (Function.update R r (R r+1)))
      have hu : Function.update (Function.update R r (R r+1)) r
          ((Function.update R r (R r+1)) r+n) = Function.update R r (R r+(n+1)) := by
        funext q
        by_cases hq : q = r <;> simp [hq, Nat.add_comm, Nat.add_left_comm]
      rw [hu] at he
      convert he using 1 <;> first | rfl | omega

theorem regSetConst_exec (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (r : Fin 21) (n : ℕ) :
    ∃ steps, (regSetConst r n).Exec (regStore frame R)
      (regStore frame (Function.update R r n)) steps ∧ steps ≤ 3*(R r)+2*n+5 := by
  have he := StackProg.Exec.seq (regReset_exec frame R r) (regIncs_exec frame (Function.update R r 0) r n)
  have hu : Function.update (Function.update R r 0) r ((Function.update R r 0) r+n) =
      Function.update R r n := by
    funext q
    by_cases hq : q = r <;> simp [hq]
  rw [hu] at he
  exact ⟨_, he, by omega⟩

end TensorNP.Encoder
end


/- Inlined module: RegisterBranch -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

noncomputable def branchEmbedding (r s : Fin 21) (hne : r ≠ s) : Fin 6 ↪ Fin 32 :=
  ⟨![regPorts r, regPorts s, 18, 25, 26, 19], by
    intro i j h
    have hrs : regPorts r ≠ regPorts s := fun he => hne (regPorts.injective he)
    have hr := regPorts_not_scratch r
    have hs := regPorts_not_scratch s
    simp only [regScratch, not_or] at hr hs
    fin_cases i <;> fin_cases j <;> simp_all⟩

private lemma register_write_update {M : ℕ} {A : Type} (r : Fin 6 ↪ Fin M)
    (t : Fin 6 → List A) (frame : Fin M → List A) (q : Fin 6) (v : List A) :
    Function.update (StackProgPortLift.write r t frame) (r q) v =
      StackProgPortLift.write r (Function.update t q v) frame := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    by_cases hk : k = q
    · subst k
      simp [register_write_at]
    · have hneq : r k ≠ r q := fun h => hk (r.injective h)
      simp [register_write_at, hk, hneq]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    have hl : l ≠ r q := fun he => hex ⟨q, he.symm⟩
    rw [Function.update_of_ne hl, register_write_outside r t frame l hout,
      register_write_outside r (Function.update t q v) frame l hout]

private lemma register_compare_start (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    StackProgPortLift.write (branchEmbedding r s hne) (compareStore (R r) (R s) 0 0 [])
      (regStore frame R) = regStore frame R := by
  funext l
  by_cases hex : ∃ k, branchEmbedding r s hne k = l
  · obtain ⟨k, rfl⟩ := hex
    rw [register_write_at]
    have h18 := regStore_scratch frame R 18 (by decide)
    have h19 := regStore_scratch frame R 19 (by decide)
    have h25 := regStore_scratch frame R 25 (by decide)
    have h26 := regStore_scratch frame R 26 (by decide)
    fin_cases k
    · exact (regStore_at frame R r).symm
    · exact (regStore_at frame R s).symm
    · exact h18.symm
    · exact h25.symm
    · exact h26.symm
    · exact h19.symm
  · have hout : ∀ k, branchEmbedding r s hne k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    exact register_write_outside _ _ _ _ hout

private noncomputable def comparisonState (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) : Fin 32 → List BSym :=
  StackProgPortLift.write (branchEmbedding r s hne) (compareStore (R r) (R s) left right flags)
    (regStore frame R)

private lemma comparisonState_clear18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 18 [] =
      comparisonState r s hne frame R 0 right flags := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 2) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_clear25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 25 [] =
      comparisonState r s hne frame R left 0 flags := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 3) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_clear19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    Function.update (comparisonState r s hne frame R left right flags) 19 [] =
      comparisonState r s hne frame R left right [] := by
  change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
    (compareStore (R r) (R s) left right flags) (regStore frame R)) (branchEmbedding r s hne 5) [] = _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma comparisonState_at18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 18 = List.replicate left .one := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 2) = _
  rw [register_write_at]
  rfl

private lemma comparisonState_at25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 25 = List.replicate right .one := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 3) = _
  rw [register_write_at]
  rfl

private lemma comparisonState_at19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    comparisonState r s hne frame R left right flags 19 = flags := by
  change StackProgPortLift.write (branchEmbedding r s hne) _ _ (branchEmbedding r s hne 5) = _
  rw [register_write_at]
  rfl

private def branchCleanup : StackProg (Fin 32) BSym :=
  .seq (clearProg 18) (.seq (clearProg 25) (clearProg 19))

private lemma branchCleanup_exec (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    branchCleanup.Exec (comparisonState r s hne frame R left right flags) (regStore frame R)
      (3 * left + 3 * right + 3 * flags.length + 5) := by
  have he1 := (stack_basic_macros (18 : Fin 32) (comparisonState r s hne frame R left right flags)).2.2
  rw [comparisonState_clear18, comparisonState_at18, List.length_replicate] at he1
  have he2 := (stack_basic_macros (25 : Fin 32) (comparisonState r s hne frame R 0 right flags)).2.2
  rw [comparisonState_clear25, comparisonState_at25, List.length_replicate] at he2
  have he3 := (stack_basic_macros (19 : Fin 32) (comparisonState r s hne frame R 0 0 flags)).2.2
  rw [comparisonState_clear19, comparisonState_at19] at he3
  have hend : comparisonState r s hne frame R 0 0 [] = regStore frame R :=
    register_compare_start r s hne frame R
  rw [hend] at he3
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq he2 he3)
  convert he using 1 <;> first | rfl | omega

private lemma comparisonState_pop19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (a b : BSym) :
    (popProg 19).Exec (comparisonState r s hne frame R left right [a,b])
      (comparisonState r s hne frame R left right [b]) 1 := by
  have he := (stack_basic_macros (19 : Fin 32)
    (comparisonState r s hne frame R left right [a,b])).2.1
  rw [comparisonState_at19] at he
  simp only [List.tail_cons] at he
  have heq : Function.update (comparisonState r s hne frame R left right [a,b]) 19 [b] =
      comparisonState r s hne frame R left right [b] := by
    change Function.update (StackProgPortLift.write (branchEmbedding r s hne)
      (compareStore (R r) (R s) left right [a,b]) (regStore frame R)) (branchEmbedding r s hne 5) [b] = _
    rw [register_write_update]
    apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
    funext k
    fin_cases k <;> simp [Function.update, compareStore]
  rw [heq] at he
  exact he

private def branchSkip : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)
private def branchFlagTest (h : Fin 32 → Option BSym) : Bool := h 19 == some .one
private def branchPrep (less : Bool) : StackProg (Fin 32) BSym :=
  if less then popProg 19 else branchSkip

noncomputable def regBranch (less : Bool) (r s : Fin 21)
    (yes no : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym := by
  classical
  exact if heq : r = s then (if less then no else yes) else
    .seq (Classical.choose (unary_compare_framed 32 (branchEmbedding r s heq)))
      (.seq (branchPrep less) (.branch branchFlagTest (.seq branchCleanup yes) (.seq branchCleanup no)))

private def eqBit (x y : ℕ) : BSym := if x = y then .one else .zero
private def ltBit (x y : ℕ) : BSym := if x < y then .one else .zero
private def testedFlags (less : Bool) (x y : ℕ) : List BSym :=
  if less then [ltBit x y] else [eqBit x y, ltBit x y]

private lemma branchPrep_exec (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) :
    (branchPrep less).Exec
      (comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)])
      (comparisonState r s hne frame R left right (testedFlags less (R r) (R s))) 1 := by
  cases less with
  | false =>
      let store := comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)]
      have hid : StackProg.applyAct (fun _ _ => StackAct.keep) store = store := by
        funext k
        rfl
      simpa only [branchPrep, testedFlags, Bool.false_eq_true, ↓reduceIte, branchSkip, hid] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) store)
  | true =>
      exact comparisonState_pop19 r s hne frame R left right (eqBit (R r) (R s)) (ltBit (R r) (R s))

private lemma branchFlagTest_correct (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) :
    branchFlagTest (fun k => (comparisonState r s hne frame R left right
      (testedFlags less (R r) (R s)) k).head?) =
      decide (if less then R r < R s else R r = R s) := by
  unfold branchFlagTest
  dsimp only
  rw [comparisonState_at19]
  cases less with
  | false => by_cases h : R r = R s <;> simp [testedFlags, eqBit, h]
  | true => by_cases h : R r < R s <;> simp [testedFlags, ltBit, h]

private lemma branchAfter_exec (less : Bool) (r s : Fin 21) (hne : r ≠ s)
    (yes no : StackProg (Fin 32) BSym) (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ)
    (T : Fin 32 → List BSym) (n left right : ℕ)
    (ha : (if (if less then R r < R s else R r = R s) then yes else no).Exec (regStore frame R) T n) :
    ∃ m, (StackProg.seq (branchPrep less)
      (.branch branchFlagTest (.seq branchCleanup yes) (.seq branchCleanup no))).Exec
      (comparisonState r s hne frame R left right [eqBit (R r) (R s), ltBit (R r) (R s)]) T m ∧
      m ≤ 3 * left + 3 * right + 15 + n := by
  let flags := testedFlags less (R r) (R s)
  have hf : flags.length ≤ 2 := by cases less <;> simp [flags, testedFlags]
  have heP := branchPrep_exec less r s hne frame R left right
  have heC := branchCleanup_exec r s hne frame R left right flags
  have ht := branchFlagTest_correct less r s hne frame R left right
  by_cases h : (if less then R r < R s else R r = R s)
  · have htest : branchFlagTest (fun k => (comparisonState r s hne frame R left right flags k).head?) = true := by
      simpa [flags, h] using ht
    have hy : yes.Exec (regStore frame R) T n := by simpa [h] using ha
    have heArm := StackProg.Exec.seq heC hy
    have heB := StackProg.Exec.branchTrue (q := .seq branchCleanup no) htest heArm
    have he := StackProg.Exec.seq heP heB
    refine ⟨_, he, ?_⟩
    omega
  · have htest : branchFlagTest (fun k => (comparisonState r s hne frame R left right flags k).head?) = false := by
      simpa [flags, h] using ht
    have hn : no.Exec (regStore frame R) T n := by simpa [h] using ha
    have heArm := StackProg.Exec.seq heC hn
    have heB := StackProg.Exec.branchFalse (p := .seq branchCleanup yes) htest heArm
    have he := StackProg.Exec.seq heP heB
    refine ⟨_, he, ?_⟩
    omega

theorem regBranch_exec (less : Bool) (r s : Fin 21) (yes no : StackProg (Fin 32) BSym)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (T : Fin 32 → List BSym) (n : ℕ)
    (ha : (if (if less then R r < R s else R r = R s) then yes else no).Exec (regStore frame R) T n) :
    ∃ m, (regBranch less r s yes no).Exec (regStore frame R) T m ∧
      m ≤ 100 * (regSize R + 1) + n := by
  classical
  by_cases heq : r = s
  · subst s
    cases less with
    | false =>
        refine ⟨n, ?_, by omega⟩
        simpa [regBranch] using ha
    | true =>
        refine ⟨n, ?_, by omega⟩
        simpa [regBranch] using ha
  · have hc := Classical.choose_spec (unary_compare_framed 32 (branchEmbedding r s heq))
    obtain ⟨ct, heC, hct⟩ := hc (R r) (R s) (regStore frame R)
    have heC' : (Classical.choose (unary_compare_framed 32 (branchEmbedding r s heq))).Exec
        (regStore frame R)
        (comparisonState r s heq frame R (R r - R s) (R s - R r)
          [eqBit (R r) (R s), ltBit (R r) (R s)]) ct := by
      simpa only [register_compare_start, comparisonState, eqBit, ltBit] using heC
    obtain ⟨bt, heB, hbt⟩ := branchAfter_exec less r s heq yes no frame R T n
      (R r - R s) (R s - R r) ha
    have he := StackProg.Exec.seq heC' heB
    refine ⟨ct + 1 + bt, ?_, ?_⟩
    · simpa only [regBranch, dif_neg heq] using he
    · have hr := reg_le_size R r
      have hs := reg_le_size R s
      omega

private lemma transfer_to_update (src dst : Fin 32) (hne : dst ≠ src) (store : Fin 32 → List BSym) :
    transferStore src (fun k => decide (k = dst)) store =
      Function.update (Function.update store src []) dst ((store src).reverse ++ store dst) := by
  classical
  funext k
  by_cases hsrc : k = src <;> by_cases hdst : k = dst <;>
    simp [transferStore, Function.update, hsrc, hdst, hne, Ne.symm hne] at *

noncomputable def regSub (dst src : Fin 21) : StackProg (Fin 32) BSym := by
  classical
  exact if heq : dst = src then clearProg (regPorts dst) else
    .seq (Classical.choose (unary_compare_framed 32 (branchEmbedding dst src heq)))
      (.seq (clearProg (regPorts dst))
        (.seq (transferProg 18 (fun k => decide (k = regPorts dst)))
          (.seq (clearProg 25) (clearProg 19))))


private noncomputable def changedState (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ)
    (flags : List BSym) : Fin 32 → List BSym :=
  StackProgPortLift.write (branchEmbedding r s hne) (compareStore x (R s) left right flags)
    (regStore frame R)

private lemma changedState_set (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym)
    (q : Fin 6) (v : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) (branchEmbedding r s hne q) v =
      StackProgPortLift.write (branchEmbedding r s hne)
        (Function.update (compareStore x (R s) left right flags) q v) (regStore frame R) := by
  exact register_write_update _ _ _ _ _

private lemma changedState_setdst (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x y left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) (regPorts r)
      (List.replicate y .one) = changedState r s hne frame R y left right flags := by
  change Function.update _ (branchEmbedding r s hne 0) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear18 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 18 [] =
      changedState r s hne frame R x 0 right flags := by
  change Function.update _ (branchEmbedding r s hne 2) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear25 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 25 [] =
      changedState r s hne frame R x left 0 flags := by
  change Function.update _ (branchEmbedding r s hne 3) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_clear19 (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym) :
    Function.update (changedState r s hne frame R x left right flags) 19 [] =
      changedState r s hne frame R x left right [] := by
  change Function.update _ (branchEmbedding r s hne 5) _ = _
  rw [changedState_set]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]

private lemma changedState_end (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x : ℕ) :
    changedState r s hne frame R x 0 0 [] = regStore frame (Function.update R r x) := by
  rw [regStore_update]
  rw [← register_compare_start r s hne frame R]
  change _ = Function.update _ (branchEmbedding r s hne 0) _
  rw [register_write_update]
  apply congrArg (fun t => StackProgPortLift.write (branchEmbedding r s hne) t (regStore frame R))
  funext k
  fin_cases k <;> simp [Function.update, compareStore]


private lemma changedState_at (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (x left right : ℕ) (flags : List BSym)
    (q : Fin 6) :
    changedState r s hne frame R x left right flags (branchEmbedding r s hne q) =
      compareStore x (R s) left right flags q := by
  exact register_write_at _ _ _ _

private lemma subAfter_exec (r s : Fin 21) (hne : r ≠ s)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (left right : ℕ) (flags : List BSym) :
    (StackProg.seq (clearProg (regPorts r))
      (.seq (transferProg 18 (fun k => decide (k = regPorts r)))
        (.seq (clearProg 25) (clearProg 19)))).Exec
      (changedState r s hne frame R (R r) left right flags)
      (regStore frame (Function.update R r left))
      (3 * R r + 3 * left + 3 * right + 3 * flags.length + 7) := by
  have he1 := (stack_basic_macros (regPorts r) (changedState r s hne frame R (R r) left right flags)).2.2
  have hv1 : changedState r s hne frame R (R r) left right flags (regPorts r) = List.replicate (R r) .one := by
    change changedState r s hne frame R (R r) left right flags (branchEmbedding r s hne 0) = _
    rw [changedState_at]
    rfl
  rw [show ([] : List BSym) = List.replicate 0 .one from rfl, changedState_setdst, hv1, List.length_replicate] at he1
  have ht := stack_transfer (18 : Fin 32) (fun k => decide (k = regPorts r))
    (changedState r s hne frame R 0 left right flags)
  have hp18 : changedState r s hne frame R 0 left right flags 18 = List.replicate left .one := by
    change changedState r s hne frame R 0 left right flags (branchEmbedding r s hne 2) = _
    rw [changedState_at]
    rfl
  have hpdst : changedState r s hne frame R 0 left right flags (regPorts r) = [] := by
    change changedState r s hne frame R 0 left right flags (branchEmbedding r s hne 0) = _
    rw [changedState_at]
    rfl
  have hne18 : regPorts r ≠ (18 : Fin 32) := by
    intro h
    apply regPorts_not_scratch r
    rw [h]
    decide
  rw [transfer_to_update 18 (regPorts r) hne18, hp18, hpdst, List.reverse_replicate,
    List.append_nil, changedState_clear18, changedState_setdst, List.length_replicate] at ht
  have he2 := (stack_basic_macros (25 : Fin 32) (changedState r s hne frame R left 0 right flags)).2.2
  have hp25 : changedState r s hne frame R left 0 right flags 25 = List.replicate right .one := by
    change changedState r s hne frame R left 0 right flags (branchEmbedding r s hne 3) = _
    rw [changedState_at]
    rfl
  rw [changedState_clear25, hp25, List.length_replicate] at he2
  have he3 := (stack_basic_macros (19 : Fin 32) (changedState r s hne frame R left 0 0 flags)).2.2
  have hp19 : changedState r s hne frame R left 0 0 flags 19 = flags := by
    change changedState r s hne frame R left 0 0 flags (branchEmbedding r s hne 5) = _
    rw [changedState_at]
    rfl
  rw [changedState_clear19, changedState_end, hp19] at he3
  have he := StackProg.Exec.seq he1 (StackProg.Exec.seq ht (StackProg.Exec.seq he2 he3))
  convert he using 1; first | rfl | omega

theorem regSub_exec (dst src : Fin 21) (hne : dst ≠ src)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    ∃ m, (regSub dst src).Exec (regStore frame R)
      (regStore frame (Function.update R dst (R dst - R src))) m ∧
      m ≤ 100 * (regSize R + 1) := by
  classical
  have hc := Classical.choose_spec (unary_compare_framed 32 (branchEmbedding dst src hne))
  obtain ⟨ct, heC, hct⟩ := hc (R dst) (R src) (regStore frame R)
  have heC' : (Classical.choose (unary_compare_framed 32 (branchEmbedding dst src hne))).Exec
      (regStore frame R)
      (changedState dst src hne frame R (R dst) (R dst - R src) (R src - R dst)
        [eqBit (R dst) (R src), ltBit (R dst) (R src)]) ct := by
    simpa only [register_compare_start, changedState, eqBit, ltBit] using heC
  have heA := subAfter_exec dst src hne frame R (R dst - R src) (R src - R dst)
    [eqBit (R dst) (R src), ltBit (R dst) (R src)]
  have he := StackProg.Exec.seq heC' heA
  refine ⟨ct + 1 + (3 * R dst + 3 * (R dst - R src) + 3 * (R src - R dst) + 3 * 2 + 7), ?_, ?_⟩
  · simpa only [regSub, dif_neg hne, List.length_cons, List.length_nil] using he
  · have hr := reg_le_size R dst
    have hs := reg_le_size R src
    simp only [List.length_cons, List.length_nil] at *
    omega

end TensorNP.Encoder
end


/- Inlined module: RegisterNeighbor -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def regNeighborPorts : Fin 8 ↪ Fin 32 := ⟨![7,1,6,12,18,20,21,22], by decide⟩
def regNeighborDecode (l : Fin 32) : Option (Fin 8) :=
  if l = 7 then some 0 else if l = 1 then some 1 else if l = 6 then some 2
  else if l = 12 then some 3 else if l = 18 then some 4 else if l = 20 then some 5
  else if l = 21 then some 6 else if l = 22 then some 7 else none

lemma regNeighborDecode_spec (l : Fin 32) (k : Fin 8) :
    regNeighborDecode l = some k ↔ regNeighborPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

noncomputable def regNeighborWork (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (out : List BSym) : Fin 32 → List BSym :=
  Function.update (regStore frame R) 18 out

def regNeighborGuard (h : Fin 32 → Option BSym) : Bool := h 18 == some .one

def regNeighborBranch (yes no : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq (StackProgPortLift.liftProgC regNeighborPorts regNeighborDecode TensorAdjacencyLookup8.lookupProg)
    (.branch regNeighborGuard (.seq (popProg 18) yes) (.seq (popProg 18) no))

lemma regStore_data (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) : regStore frame R 7 = frame 7 := by
  rw [regStore, port_write_outside]
  · rfl
  · intro r
    fin_cases r <;> decide

lemma regNeighbor_project (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (out : List BSym) :
    StackProgPortLift.project regNeighborPorts (regNeighborWork frame R out) =
      TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) out [] [] [] := by
  have h1 : regStore frame R 1 = List.replicate (R 0) .one := regStore_at frame R 0
  have h6 : regStore frame R 6 = List.replicate (R 3) .one := regStore_at frame R 3
  have h12 : regStore frame R 12 = List.replicate (R 8) .one := regStore_at frame R 8
  have h20 := regStore_scratch frame R 20 (by decide)
  have h21 := regStore_scratch frame R 21 (by decide)
  have h22 := regStore_scratch frame R 22 (by decide)
  funext k
  fin_cases k <;> simp [StackProgPortLift.project, regNeighborPorts, regNeighborWork,
    TensorAdjacencyLookup8.store, regStore_data, h1, h6, h12, h20, h21, h22]

lemma regNeighborWork_empty (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) :
    regNeighborWork frame R [] = regStore frame R := by
  have h18 := regStore_scratch frame R 18 (by decide)
  funext l
  by_cases hl : l = 18 <;> simp [regNeighborWork, hl, h18]

lemma regNeighbor_write (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (a : BSym) :
    StackProgPortLift.write regNeighborPorts
      (TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) [a] [] [] [])
      (regStore frame R) = regNeighborWork frame R [a] := by
  classical
  funext l
  by_cases hl : ∃ k, regNeighborPorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [port_write_at]
    exact (congrFun (regNeighbor_project frame R [a]) k).symm
  · have h18 : l ≠ 18 := by intro h; apply hl; exact ⟨4, h.symm⟩
    simp [StackProgPortLift.write, hl, regNeighborWork, h18]

lemma regNeighborPop (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (a : BSym) :
    (popProg (18 : Fin 32)).Exec (regNeighborWork frame R [a]) (regStore frame R) 1 := by
  have h18 := regStore_scratch frame R 18 (by decide)
  have hu : Function.update (regNeighborWork frame R [a]) 18
      ((regNeighborWork frame R [a]) 18).tail = regStore frame R := by
    funext l
    by_cases hl : l = 18 <;> simp [regNeighborWork, hl, h18]
  simpa only [hu] using (stack_basic_macros (18 : Fin 32) (regNeighborWork frame R [a])).2.1

theorem regNeighborBranch_exec (yes no : StackProg (Fin 32) BSym)
    (frame : Fin 32 → List BSym) (R : Fin 21 → ℕ) (T : Fin 32 → List BSym) (n : ℕ)
    (hrow : R 3 < R 0) (hcol : R 8 < R 0) (hlen : (frame 7).length = R 0 * R 0)
    (harm : (if (frame 7).getD (R 3 * R 0 + R 8) .zero = .one then yes else no).Exec
      (regStore frame R) T n) :
    ∃ m, (regNeighborBranch yes no).Exec (regStore frame R) T m ∧
      m ≤ 100*(R 0+1)^2+n := by
  let a := (frame 7).getD (R 3 * R 0 + R 8) BSym.zero
  change (if a = .one then yes else no).Exec (regStore frame R) T n at harm
  obtain ⟨steps, hbound, he⟩ := TensorAdjacencyLookup8.lookupProg_exec (R 0) (R 3) (R 8)
    (frame 7) [] hrow hcol hlen
  have hproject : StackProgPortLift.project regNeighborPorts (regStore frame R) =
      TensorAdjacencyLookup8.store (frame 7) (List.replicate (R 0) .one)
        (List.replicate (R 3) .one) (List.replicate (R 8) .one) [] [] [] [] := by
    simpa only [regNeighborWork_empty] using regNeighbor_project frame R []
  have hlift := StackProgPortLift.liftProgC_exec regNeighborPorts regNeighborDecode
    regNeighborDecode_spec he (regStore frame R) hproject
  rw [regNeighbor_write] at hlift
  have hsq : 1 ≤ (R 0+1)^2 := Nat.one_le_pow 2 (R 0+1) (by omega)
  by_cases ha : a = .one
  · have hy : yes.Exec (regStore frame R) T n := by simpa [ha] using harm
    have hg : regNeighborGuard (fun k => (regNeighborWork frame R [a] k).head?) = true := by
      simp [regNeighborGuard, regNeighborWork, ha]
    have hb := StackProg.Exec.branchTrue (test := regNeighborGuard) (q := .seq (popProg 18) no)
      hg (StackProg.Exec.seq (regNeighborPop frame R a) hy)
    have ht := StackProg.Exec.seq hlift hb
    refine ⟨steps+1+(1+(1+1+n)), ht, ?_⟩
    omega
  · have hn : no.Exec (regStore frame R) T n := by simpa [ha] using harm
    have hg : regNeighborGuard (fun k => (regNeighborWork frame R [a] k).head?) = false := by
      simp [regNeighborGuard, regNeighborWork, ha]
    have hb := StackProg.Exec.branchFalse (test := regNeighborGuard) (p := .seq (popProg 18) yes)
      hg (StackProg.Exec.seq (regNeighborPop frame R a) hn)
    have ht := StackProg.Exec.seq hlift hb
    refine ⟨steps+1+(1+(1+1+n)), ht, ?_⟩
    omega

end TensorNP.Encoder
end


/- Inlined module: ActualCounterBackend -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

noncomputable def actualRegBackend : RegBackend where
  keep := regKeep
  reset := regReset
  inc := regInc
  assign := regAssign
  add := fun dst src _ => regAdd dst src
  sub := fun dst src _ => regSub dst src
  branch := regBranch
  neighbor := regNeighborBranch
  keep_ok := regKeep_exec
  reset_ok := by
    intro frame R r
    refine ⟨3 * R r + 1, regReset_exec frame R r, ?_⟩
    have hr := reg_le_size R r
    simp only [regCharge]
    omega
  inc_ok := by
    intro frame R r
    refine ⟨1, regInc_exec frame R r, ?_⟩
    simp only [regCharge]
    omega
  assign_ok := by
    intro frame R dst src
    obtain ⟨n, hn, hbound⟩ := regAssign_exec frame R dst src
    refine ⟨n, hn, ?_⟩
    simp only [regCharge]
    omega
  add_ok := by
    intro frame R dst src h
    refine ⟨6 * R src + 3, regAdd_exec frame R dst src h, ?_⟩
    have hs := reg_le_size R src
    simp only [regCharge]
    omega
  sub_ok := by
    intro frame R dst src h
    exact regSub_exec dst src h frame R
  pop_ok := regPop_exec
  branch_ok := by
    intro less r s yes no frame R T n harm
    apply regBranch_exec less r s yes no frame R T n
    cases less <;> simpa only [regCompare, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq] using harm
  neighbor_ok := by
    intro yes no frame R T n hr hc hlen harm
    apply regNeighborBranch_exec yes no frame R T n hr hc hlen
    simpa only [regNeighbor, decide_eq_true_eq] using harm

theorem actual_compileReg_sound {data : List BSym} {p : RegCmd} {R T : RegFile} {n : ℕ}
    (h : RegExec data p R T n) (frame : Fin 32 → List BSym) (hdata : frame 7 = data) :
    ∃ m, (compileReg actualRegBackend p).Exec (regStore frame R) (regStore frame T) m ∧ m ≤ n := by
  exact compileReg_sound actualRegBackend h frame hdata

end TensorNP.Encoder
end


/- Inlined module: EmitterLoops -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def chunkK (E : ℕ → ℕ → ℕ → List BSym) (i j count : ℕ) : List BSym :=
  (List.range count).flatMap (E i j)
def chunkJ (E : ℕ → ℕ → ℕ → List BSym) (N i count : ℕ) : List BSym :=
  (List.range count).flatMap (fun j => chunkK E i j N)
def chunkI (E : ℕ → ℕ → ℕ → List BSym) (N count : ℕ) : List BSym :=
  (List.range count).flatMap (fun i => chunkJ E N i N)

def emitKGuard (h : Fin 32 → Option BSym) : Bool := (h 17).isSome
def emitJGuard (h : Fin 32 → Option BSym) : Bool := (h 16).isSome
def emitIGuard (h : Fin 32 → Option BSym) : Bool := (h 15).isSome

def emitKLoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitKGuard (.seq (popProg 17) entry)
def emitJLoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitJGuard (.seq (popProg 16) (.seq (copyProg 14 17 20) (emitKLoop entry)))
def emitILoop (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .loop emitIGuard (.seq (popProg 15) (.seq (copyProg 14 16 20) (emitJLoop entry)))
def denseEmitter (entry : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq (copyProg 14 15 20) (emitILoop entry)

lemma emitPopK (input data : List BSym) (v N i j k : ℕ) (tail : List BSym) :
    (popProg (17 : Fin 32)).Exec (emitterStore input data v N i j (k+1) tail)
      (emitterStore input data v N i j k tail) 1 := by
  have hu : Function.update (emitterStore input data v N i j (k+1) tail) 17
      ((emitterStore input data v N i j (k+1) tail) 17).tail = emitterStore input data v N i j k tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (17 : Fin 32)
    (emitterStore input data v N i j (k+1) tail)).2.1

lemma emitPopJ (input data : List BSym) (v N i j : ℕ) (tail : List BSym) :
    (popProg (16 : Fin 32)).Exec (emitterStore input data v N i (j+1) 0 tail)
      (emitterStore input data v N i j 0 tail) 1 := by
  have hu : Function.update (emitterStore input data v N i (j+1) 0 tail) 16
      ((emitterStore input data v N i (j+1) 0 tail) 16).tail = emitterStore input data v N i j 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (16 : Fin 32)
    (emitterStore input data v N i (j+1) 0 tail)).2.1

lemma emitPopI (input data : List BSym) (v N i : ℕ) (tail : List BSym) :
    (popProg (15 : Fin 32)).Exec (emitterStore input data v N (i+1) 0 0 tail)
      (emitterStore input data v N i 0 0 tail) 1 := by
  have hu : Function.update (emitterStore input data v N (i+1) 0 0 tail) 15
      ((emitterStore input data v N (i+1) 0 0 tail) 15).tail = emitterStore input data v N i 0 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore, List.replicate_succ]
  simpa only [hu] using (stack_basic_macros (15 : Fin 32)
    (emitterStore input data v N (i+1) 0 0 tail)).2.1

lemma emitCopyK (input data : List BSym) (v N i j : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 17 20).Exec (emitterStore input data v N i j 0 tail)
      (emitterStore input data v N i j N tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 17 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N i j 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N i j 0 tail) 17
      (emitterStore input data v N i j 0 tail 14 ++ emitterStore input data v N i j 0 tail 17) =
      emitterStore input data v N i j N tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

lemma emitCopyJ (input data : List BSym) (v N i : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 16 20).Exec (emitterStore input data v N i 0 0 tail)
      (emitterStore input data v N i N 0 tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 16 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N i 0 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N i 0 0 tail) 16
      (emitterStore input data v N i 0 0 tail 14 ++ emitterStore input data v N i 0 0 tail 16) =
      emitterStore input data v N i N 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

lemma emitCopyI (input data : List BSym) (v N : ℕ) (tail : List BSym) :
    (copyProg (14 : Fin 32) 15 20).Exec (emitterStore input data v N 0 0 0 tail)
      (emitterStore input data v N N 0 0 tail) (6*N+3) := by
  have h := stack_copy (14 : Fin 32) 15 20 (by decide) (by decide) (by decide)
    (emitterStore input data v N 0 0 0 tail) (by rfl)
  have hu : Function.update (emitterStore input data v N 0 0 0 tail) 15
      (emitterStore input data v N 0 0 0 tail 14 ++ emitterStore input data v N 0 0 0 tail 15) =
      emitterStore input data v N N 0 0 tail := by
    funext l
    fin_cases l <;> simp [emitterStore, frontendGraphStore, frontendStore]
  rw [hu] at h
  simpa [emitterStore] using h

def denseEntrySpec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) : Prop :=
  ∀ (i j k : ℕ) (tail : List BSym), i < N → j < N → k < N →
    ∃ steps, entry.Exec (emitterStore input data v N i j k tail)
      (emitterStore input data v N i j k (E i j k ++ tail)) steps ∧ steps ≤ B

theorem emitKLoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (i j count : ℕ)
    (hi : i < N) (hj : j < N) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitKLoop entry).Exec (emitterStore input data v N i j count tail)
      (emitterStore input data v N i j 0 (chunkK E i j count ++ tail)) steps ∧
      steps ≤ count*(B+5)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitKLoop, chunkK] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 17) entry) (test := emitKGuard)
        (s := emitterStore input data v N i j 0 tail) (by simp [emitKGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := hentry i j count tail hi hj (by omega)
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (E i j count ++ tail)
      have hguard : emitKGuard (fun k => (emitterStore input data v N i j (count+1) tail k).head?) = true := by
        simp [emitKGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopK input data v N i j count tail) hm) hr
      refine ⟨1 + (1 + 1 + m) + 1 + r, ?_, ?_⟩
      · simpa [emitKLoop, chunkK, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem emitJLoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (i count : ℕ)
    (hi : i < N) (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitJLoop entry).Exec (emitterStore input data v N i count 0 tail)
      (emitterStore input data v N i 0 0 (chunkJ E N i count ++ tail)) steps ∧
      steps ≤ count*(N*(B+5)+6*N+10)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitJLoop, chunkJ] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 16) (.seq (copyProg 14 17 20) (emitKLoop entry))) (test := emitJGuard)
        (s := emitterStore input data v N i 0 0 tail) (by simp [emitJGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := emitKLoop_exec entry E B input data v N hentry i count N hi (by omega) le_rfl tail
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (chunkK E i count N ++ tail)
      have hguard : emitJGuard (fun k => (emitterStore input data v N i (count+1) 0 tail k).head?) = true := by
        simp [emitJGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopJ input data v N i count tail)
          (StackProg.Exec.seq (emitCopyK input data v N i count tail) hm)) hr
      refine ⟨1 + (1 + 1 + ((6*N+3) + 1 + m)) + 1 + r, ?_, ?_⟩
      · simpa [emitJLoop, chunkJ, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem emitILoop_exec (entry : StackProg (Fin 32) BSym) (E : ℕ → ℕ → ℕ → List BSym)
    (B : ℕ) (input data : List BSym) (v N : ℕ) (hentry : denseEntrySpec entry E B input data v N) (count : ℕ)
    (hc : count ≤ N) (tail : List BSym) :
    ∃ steps, (emitILoop entry).Exec (emitterStore input data v N count 0 0 tail)
      (emitterStore input data v N 0 0 0 (chunkI E N count ++ tail)) steps ∧
      steps ≤ count*(N*(N*(B+5)+6*N+10)+6*N+10)+1 := by
  induction count generalizing tail with
  | zero =>
      refine ⟨1, ?_, by simp⟩
      simpa [emitILoop, chunkI] using (StackProg.Exec.loopFalse
        (p := .seq (popProg 15) (.seq (copyProg 14 16 20) (emitJLoop entry))) (test := emitIGuard)
        (s := emitterStore input data v N 0 0 0 tail) (by simp [emitIGuard, emitterStore]))
  | succ count ih =>
      obtain ⟨m, hm, hmB⟩ := emitJLoop_exec entry E B input data v N hentry count N (by omega) le_rfl tail
      obtain ⟨r, hr, hrB⟩ := ih (by omega) (chunkJ E N count N ++ tail)
      have hguard : emitIGuard (fun k => (emitterStore input data v N (count+1) 0 0 tail k).head?) = true := by
        simp [emitIGuard, emitterStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hguard
        (StackProg.Exec.seq (emitPopI input data v N count tail)
          (StackProg.Exec.seq (emitCopyJ input data v N count tail) hm)) hr
      refine ⟨1 + (1 + 1 + ((6*N+3) + 1 + m)) + 1 + r, ?_, ?_⟩
      · simpa [emitILoop, chunkI, List.range_succ, List.flatMap_append, List.append_assoc] using he
      · rw [Nat.add_mul]
        omega

theorem dense_emitter_source (entry : StackProg (Fin 32) BSym) :
    ∃ p : StackProg (Fin 32) BSym,
      ∀ (E : ℕ → ℕ → ℕ → List BSym) (B : ℕ) (input data : List BSym) (v N : ℕ),
      denseEntrySpec entry E B input data v N → ∀ (tail : List BSym), ∃ steps,
        p.Exec (emitterStore input data v N 0 0 0 tail)
          (emitterStore input data v N 0 0 0 (chunkI E N N ++ tail)) steps ∧
        steps ≤ (B+100)*(N+1)^4 := by
  refine ⟨denseEmitter entry, ?_⟩
  intro E B input data v N hentry tail
  obtain ⟨m, hm, hmB⟩ := emitILoop_exec entry E B input data v N hentry N le_rfl tail
  have he := StackProg.Exec.seq (emitCopyI input data v N tail) hm
  refine ⟨(6*N+3)+1+m, he, ?_⟩
  nlinarith [Nat.zero_le (B*N^4), Nat.zero_le (B*N^3), Nat.zero_le (B*N^2),
    Nat.zero_le (B*N), Nat.zero_le (N^4), Nat.zero_le (N^3), Nat.zero_le (N^2)]

end TensorNP.Encoder
end


/- Inlined module: TensorWord -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

lemma rangeFlatMap_ofFn {α : Type} (N : ℕ) (f : ℕ → List α) (g : Fin N → List α)
    (h : ∀ i : Fin N, f i.val = g i) :
    (List.range N).flatMap f = (List.ofFn g).flatten := by
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.ofFn_eq_map]
  congr 1
  funext i
  exact h i

theorem dense_tensor_code {N : ℕ} (A : Fin N → Fin N → Fin N → ℚ)
    (E : ℕ → ℕ → ℕ → List BSym)
    (h : ∀ i j k : Fin N, E i.val j.val k.val = encRat (A i j k)) :
    encNat N ++ chunkI E N N = tensorCode A := by
  unfold tensorCode chunkI
  congr 1
  apply rangeFlatMap_ofFn
  intro i
  unfold chunkJ
  apply rangeFlatMap_ofFn
  intro j
  unfold chunkK
  apply rangeFlatMap_ofFn
  intro k
  exact h i j k

lemma splitCounts_le (m n bound : ℕ) (A : ℕ → ℕ → ℕ → ℕ × ℕ)
    (hA : ∀ q a b, (A q a b).1 + (A q a b).2 ≤ bound) (q a b : ℕ) :
    (splitCounts m n A q a b).1 + (splitCounts m n A q a b).2 ≤ bound := by
  unfold splitCounts
  split_ifs
  all_goals try dsimp only [swapCounts]
  all_goals first | exact hA _ _ _ | (rw [Nat.add_comm]; exact hA _ _ _) | omega

theorem tensorCounts_le (v : ℕ) (data : List BSym) (i j k : ℕ) :
    (tensorCounts v data i j k).1 + (tensorCounts v data i j k).2 ≤ 3*v+2 := by
  have hA : ∀ q a b, (colorCounts v data q a b).1 + (colorCounts v data q a b).2 ≤ 3*v+2 := by
    intro q a b
    exact rawCounts_le v data (q/v) (q%v) a b
  have hs := splitCounts_le (4*v) (2*v+1) (3*v+2) (colorCounts v data) hA k i j
  unfold tensorCounts
  split_ifs <;> simp_all

theorem raw_tensor_code {v : ℕ} (G : SimpleGraph (Fin v)) :
    encNat (colorSize v) ++
      chunkI (fun i j k => encRat ((rawTensorEntry v (graphData G) i j k : ℤ) : ℚ))
        (colorSize v) (colorSize v) = tensorCode (colorTensor G) := by
  apply dense_tensor_code
  intro i j k
  rw [rawTensorEntry_cast]

end TensorNP.Encoder
end


/- Inlined module: EntrySource -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

theorem tensor_entry_source : ∃ (entry : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (input data : List BSym) (v i j k : ℕ) (tail : List BSym),
      data.length = v*v → i < colorSize v → j < colorSize v → k < colorSize v →
      ∃ steps, entry.Exec (emitterStore input data v (colorSize v) i j k tail)
        (emitterStore input data v (colorSize v) i j k
          (encRat ((rawTensorEntry v data i j k : ℤ) : ℚ) ++ tail)) steps ∧
        steps ≤ C * (v+1)^4 := by
  obtain ⟨writer, Cw, hwriter⟩ := entry_count_emit_source
  refine ⟨.seq (compileReg actualRegBackend tensorCountProgram) writer,
    1000000000000000000 + 16*Cw + 1, ?_⟩
  intro input data v i j k tail hlen hi hj hk
  let P := (tensorCounts v data i j k).1
  let M := (tensorCounts v data i j k).2
  let frame := emitterStore input data v (colorSize v) i j k tail
  obtain ⟨n, hn, hnB⟩ := tensorCountProgram_exec data v i j k hlen hi hj hk
  have hframe : frame 7 = data := by rfl
  obtain ⟨m, he, hmB⟩ := actual_compileReg_sound hn frame hframe
  have he' : (compileReg actualRegBackend tensorCountProgram).Exec frame
      (regStore frame (entryRegs v (colorSize v) i j k P M)) m := by
    simpa only [frame, entryRegs_zero_store, P, M] using he
  obtain ⟨w, hw, hwB⟩ := hwriter input data v (colorSize v) i j k P M tail
  have hvalue : (P : ℚ) - (M : ℚ) = ((rawTensorEntry v data i j k : ℤ) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (tensorCounts_value v data i j k)
    simpa [countValue, P, M] using h
  rw [hvalue] at hw
  have hexe := StackProg.Exec.seq he' hw
  refine ⟨m + 1 + w, hexe, ?_⟩
  have hcounts : P + M ≤ 3*v + 2 := tensorCounts_le v data i j k
  have hbase : P + M + 2 ≤ 4 * (v+1) := by omega
  have hpow : (P + M + 2)^2 ≤ (4*(v+1))^2 := Nat.pow_le_pow_left hbase 2
  have hquart : (v+1)^2 ≤ (v+1)^4 := pow_le_pow_right₀ (by omega) (by omega)
  have hpow' : (P+M+2)^2 ≤ 16*(v+1)^4 := by
    calc
      _ ≤ (4*(v+1))^2 := hpow
      _ = 16*(v+1)^2 := by ring
      _ ≤ 16*(v+1)^4 := Nat.mul_le_mul_left _ hquart
  have hW : w ≤ (16*Cw)*(v+1)^4 := by
    calc
      w ≤ Cw*(P+M+2)^2 := hwB
      _ ≤ Cw*(16*(v+1)^4) := Nat.mul_le_mul_left _ hpow'
      _ = (16*Cw)*(v+1)^4 := by ring
  have hC : m ≤ 1000000000000000000*(v+1)^4 := hmB.trans hnB
  have hP : 1 ≤ (v+1)^4 := Nat.one_le_pow 4 (v+1) (by omega)
  calc
    m + 1 + w ≤ 1000000000000000000*(v+1)^4 + (16*Cw)*(v+1)^4 + 1 := by omega
    _ ≤ 1000000000000000000*(v+1)^4 + (16*Cw)*(v+1)^4 + (v+1)^4 := by omega
    _ = (1000000000000000000 + 16*Cw + 1)*(v+1)^4 := by ring

end TensorNP.Encoder
end


/- Inlined module: GraphInputValid -/
section
set_option autoImplicit false
open ProjSchedTW.Complexity

namespace TensorNP.Encoder

instance validMatrixDecidable (n : ℕ) (bs : List Bool) : Decidable (ValidMatrix n bs) := by
  unfold ValidMatrix
  infer_instance

def graphInputValid (input : List BSym) : Bool :=
  let r := boundedHeader 0 (input.length + 1) input
  if r.found then
    match parseBits (r.dimension * r.dimension) r.suffix with
    | none => false
    | some (bs, tail) => decide (tail = [] ∧ ValidMatrix r.dimension bs)
  else false

theorem graphInputValid_iff (input : List BSym) : graphInputValid input = true ↔
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G := by
  rw [canonicalGraph_iff]
  by_cases hf : (boundedHeader 0 (input.length + 1) input).found = true
  · cases hp : parseBits ((boundedHeader 0 (input.length + 1) input).dimension *
        (boundedHeader 0 (input.length + 1) input).dimension)
        (boundedHeader 0 (input.length + 1) input).suffix with
    | none => simp [graphInputValid, hf, hp]
    | some p =>
        rcases p with ⟨bs, tail⟩
        simp [graphInputValid, hf, hp]
  · simp [graphInputValid, hf]

theorem graphInputValid_graphCode {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphInputValid (TensorNP.Eigen.graphCode G) = true := by
  exact (graphInputValid_iff _).2 ⟨n, G, rfl⟩

theorem graphInputValid_invalid (input : List BSym)
    (h : ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin n)), input = TensorNP.Eigen.graphCode G) :
    graphInputValid input = false := by
  cases hv : graphInputValid input with
  | false => rfl
  | true => exact False.elim (h ((graphInputValid_iff input).1 hv))

end TensorNP.Encoder
end


/- Inlined module: FrontLemmas -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

theorem boundedHeader_fuel_le (n fuel : ℕ) (input : List BSym) :
    (boundedHeader n fuel input).fuel ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [boundedHeader]
  | succ fuel ih =>
      by_cases hmatch : (prefixResult (encNat n) input).patternRest = []
      · simp [boundedHeader, hmatch]
      · simp only [boundedHeader, if_neg hmatch]
        exact Nat.le_trans (ih (n+1)) (Nat.le_succ fuel)

theorem boundedHeader_dimension_le (input : List BSym)
    (hf : (boundedHeader 0 (input.length+1) input).found = true) :
    (boundedHeader 0 (input.length+1) input).dimension ≤ input.length := by
  have h := (boundedHeader_sound 0 (input.length+1) input hf).2.1
  omega

theorem canonical_front_packet {v : ℕ} (G : SimpleGraph (Fin v)) (input : List BSym)
    (hinput : input = TensorNP.Eigen.graphCode G) :
    let r := boundedHeader 0 (input.length+1) input
    r.found = true ∧ r.dimension = v ∧
      parseBits (r.dimension*r.dimension) r.suffix = some (graphBits G, []) ∧
      ValidMatrix r.dimension (graphBits G) := by
  subst input
  obtain ⟨hdim, hsuffix, hfound⟩ := boundedHeader_graphCode G
  refine ⟨hfound, hdim, ?_, ?_⟩
  · rw [hdim, hsuffix, graphTail_eq_bitsCode, ← (graphBits_valid G).1]
    simpa only [List.append_nil] using parseBits_complete (graphBits G) []
  · rw [hdim]
    exact graphBits_valid G

theorem canonical_packet_accept (input : List BSym) (bs : List Bool)
    (hf : (boundedHeader 0 (input.length+1) input).found = true)
    (hp : parseBits ((boundedHeader 0 (input.length+1) input).dimension *
        (boundedHeader 0 (input.length+1) input).dimension)
      (boundedHeader 0 (input.length+1) input).suffix = some (bs, []))
    (hv : ValidMatrix (boundedHeader 0 (input.length+1) input).dimension bs) :
    ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G := by
  exact (canonicalGraph_iff input).2 ⟨hf, bs, hp, hv⟩

end TensorNP.Encoder
end


/- Inlined module: EncoderValue -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def denseWord (v : ℕ) (data : List BSym) : List BSym :=
  encNat (colorSize v) ++ chunkI
    (fun i j k => encRat ((rawTensorEntry v data i j k : ℤ) : ℚ)) (colorSize v) (colorSize v)

/-- Total value function: the same bounded parser used by the executable frontend. -/
def eigenEncoderValue (input : List BSym) : List BSym :=
  let r := boundedHeader 0 (input.length+1) input
  if graphInputValid input then
    match parseBits (r.dimension*r.dimension) r.suffix with
    | none => []
    | some (bs, _) => denseWord r.dimension (bs.map boolSym)
  else []

theorem eigenEncoderValue_graphCode {v : ℕ} (G : SimpleGraph (Fin v)) :
    eigenEncoderValue (graphCode G) = tensorCode (colorTensor G) := by
  have hc := canonical_front_packet G (graphCode G) rfl
  simp only [eigenEncoderValue, graphInputValid_graphCode, ↓reduceIte]
  rw [hc.2.2.1, hc.2.1]
  exact raw_tensor_code G

theorem eigenEncoderValue_invalid (input : List BSym)
    (h : ¬∃ (v : ℕ) (G : SimpleGraph (Fin v)), input=graphCode G) :
    eigenEncoderValue input=[] := by
  simp [eigenEncoderValue, graphInputValid_invalid input h]

end TensorNP.Encoder
end


/- Inlined module: Header32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def headerPorts32 : Fin 12 ↪ Fin 32 := ⟨![1, 7, 8, 9, 10, 0, 2, 6, 4, 11, 12, 13], by decide⟩

def headerDecode32 (l : Fin 32) : Option (Fin 12) :=
  if l = 1 then some 0 else if l = 7 then some 1 else if l = 8 then some 2
  else if l = 9 then some 3 else if l = 10 then some 4 else if l = 0 then some 5
  else if l = 2 then some 6 else if l = 6 then some 7 else if l = 4 then some 8
  else if l = 11 then some 9 else if l = 12 then some 10 else if l = 13 then some 11 else none

lemma headerDecode32_spec (l : Fin 32) (k : Fin 12) :
    headerDecode32 l = some k ↔ headerPorts32 k = l := by
  fin_cases l <;> fin_cases k <;> decide

lemma headerFrontend_project (input : List BSym) :
    StackProgPortLift.project headerPorts32 (frontendInputStore input) = headerInputStore input := by
  funext k
  fin_cases k <;> rfl

private lemma header_write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write headerPorts32 t s (headerPorts32 k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := headerPorts32.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma headerFrontend_write (input : List BSym) (r : HeaderResult) :
    StackProgPortLift.write headerPorts32 (headerResultStore r input) (frontendInputStore input) =
      frontendHeaderStore input r := by
  classical
  funext l
  by_cases hl : ∃ k, headerPorts32 k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [header_write_at]
    fin_cases k <;> rfl
  · have h0 : l ≠ 0 := by
      intro he
      apply hl
      exact ⟨5, he.symm⟩
    have h1 : l ≠ 1 := by
      intro he
      apply hl
      exact ⟨0, he.symm⟩
    have h2 : l ≠ 2 := by
      intro he
      apply hl
      exact ⟨6, he.symm⟩
    have h4 : l ≠ 4 := by
      intro he
      apply hl
      exact ⟨8, he.symm⟩
    have h6 : l ≠ 6 := by
      intro he
      apply hl
      exact ⟨7, he.symm⟩
    simp [StackProgPortLift.write, hl, frontendInputStore, frontendHeaderStore, frontendStore,
      h0, h1, h2, h4, h6]

theorem frontend_header_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ input : List BSym, ∃ steps,
      p.Exec (frontendInputStore input)
        (frontendHeaderStore input (boundedHeader 0 (input.length + 1) input)) steps ∧
      steps ≤ C * (input.length + 2)^3 := by
  obtain ⟨p, C, hp⟩ := header_parser_source
  refine ⟨StackProgPortLift.liftProgC headerPorts32 headerDecode32 p, C, ?_⟩
  intro input
  obtain ⟨steps, he, hb⟩ := hp input
  refine ⟨steps, ?_, hb⟩
  have he' := StackProgPortLift.liftProgC_exec headerPorts32 headerDecode32
    headerDecode32_spec he (frontendInputStore input) (headerFrontend_project input)
  rw [headerFrontend_write] at he'
  exact he'

end TensorNP.Encoder
end


/- Inlined module: UnarySquare -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def squareStore (n out count : ℕ) : Fin 4 → List BSym :=
  fun k => if k = 0 then List.replicate n .one
    else if k = 1 then List.replicate out .one
    else if k = 2 then List.replicate count .one else []

def squareBody : StackProg (Fin 4) BSym := .seq (popProg 2) (copyProg 0 1 3)
def squareLoop : StackProg (Fin 4) BSym := .loop (fun h => (h 2).isSome) squareBody
def squareProg : StackProg (Fin 4) BSym := .seq (copyProg 0 2 3) squareLoop

lemma squarePop (n out count : ℕ) :
    (popProg (2 : Fin 4)).Exec (squareStore n out (count + 1)) (squareStore n out count) 1 := by
  have he : StackProg.applyAct (fun (_ : Fin 4 → Option BSym) (k : Fin 4) => if k = 2 then .pop else .keep)
      (squareStore n out (count + 1)) = squareStore n out count := by
    funext k
    fin_cases k <;> simp [StackProg.applyAct, squareStore, StackAct.apply, List.replicate_succ]
  simpa only [popProg, he] using StackProg.Exec.act
    (fun (_ : Fin 4 → Option BSym) (k : Fin 4) => if k = 2 then .pop else .keep) (squareStore n out (count + 1))

lemma squareCopyOutput (n out count : ℕ) :
    (copyProg (0 : Fin 4) 1 3).Exec (squareStore n out count)
      (squareStore n (n + out) count) (6 * n + 3) := by
  have h := stack_copy (0 : Fin 4) 1 3 (by decide) (by decide) (by decide)
    (squareStore n out count) (by simp [squareStore])
  have hu : Function.update (squareStore n out count) 1
      (squareStore n out count 0 ++ squareStore n out count 1) =
      squareStore n (n + out) count := by
    funext k
    fin_cases k <;> simp [squareStore]
  rw [hu] at h
  simpa [squareStore] using h

lemma squareCopyCounter (n : ℕ) :
    (copyProg (0 : Fin 4) 2 3).Exec (squareStore n 0 0) (squareStore n 0 n) (6 * n + 3) := by
  have h := stack_copy (0 : Fin 4) 2 3 (by decide) (by decide) (by decide)
    (squareStore n 0 0) (by simp [squareStore])
  have hu : Function.update (squareStore n 0 0) 2
      (squareStore n 0 0 0 ++ squareStore n 0 0 2) = squareStore n 0 n := by
    funext k
    fin_cases k <;> simp [squareStore]
  rw [hu] at h
  simpa [squareStore] using h

lemma squareLoop_exec (n count out : ℕ) :
    squareLoop.Exec (squareStore n out count) (squareStore n (out + count * n) 0)
      ((6 * n + 7) * count + 1) := by
  induction count generalizing out with
  | zero =>
      simpa [squareLoop] using (StackProg.Exec.loopFalse
        (test := fun h : Fin 4 → Option BSym => (h 2).isSome)
        (p := squareBody) (s := squareStore n out 0) (by simp [squareStore]))
  | succ count ih =>
      have hb : squareBody.Exec (squareStore n out (count + 1))
          (squareStore n (n + out) count) (6 * n + 5) := by
        have he := StackProg.Exec.seq (squarePop n out count) (squareCopyOutput n out count)
        convert he using 1 <;> first | rfl | omega
      have hg : (fun h : Fin 4 → Option BSym => (h 2).isSome)
          (fun k => (squareStore n out (count + 1) k).head?) = true := by
        simp [squareStore, List.replicate_succ]
      have he := StackProg.Exec.loopTrue hg hb (ih (n + out))
      have hout : n + out + count * n = out + (count + 1) * n := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hsteps : 1 + (6 * n + 5) + 1 + ((6 * n + 7) * count + 1) =
          (6 * n + 7) * (count + 1) + 1 := by
        rw [Nat.mul_add]
        omega
      simpa only [squareLoop, ← hout, ← hsteps] using he

theorem unary_square_machine : ∃ p : StackProg (Fin 4) BSym, ∀ n : ℕ,
    p.Exec (squareStore n 0 0) (squareStore n (n * n) 0) (6 * n * n + 13 * n + 5) := by
  refine ⟨squareProg, ?_⟩
  intro n
  have he := StackProg.Exec.seq (squareCopyCounter n) (squareLoop_exec n n 0)
  convert he using 1 <;> simp [squareProg, Nat.add_mul]
  all_goals omega

end TensorNP.Encoder
end


/- Inlined module: Packet32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def packetSquarePorts : Fin 4 ↪ Fin 32 := ⟨![1, 6, 7, 8], by decide⟩
def packetBitPorts : Fin 4 ↪ Fin 32 := ⟨![2, 6, 3, 4], by decide⟩

def packetSquareDecode (l : Fin 32) : Option (Fin 4) :=
  if l = 1 then some 0 else if l = 6 then some 1 else if l = 7 then some 2
    else if l = 8 then some 3 else none

def packetBitDecode (l : Fin 32) : Option (Fin 4) :=
  if l = 2 then some 0 else if l = 6 then some 1 else if l = 3 then some 2
    else if l = 4 then some 3 else none

lemma packetSquareDecode_spec (l : Fin 32) (k : Fin 4) :
    packetSquareDecode l = some k ↔ packetSquarePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

lemma packetBitDecode_spec (l : Fin 32) (k : Fin 4) :
    packetBitDecode l = some k ↔ packetBitPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private lemma packetWrite_at (r : Fin 4 ↪ Fin 32) (t : Fin 4 → List BSym)
    (s : Fin 32 → List BSym) (k : Fin 4) :
    StackProgPortLift.write r t s (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma packetSquare_project (input suffix : List BSym) (n out : ℕ) :
    StackProgPortLift.project packetSquarePorts
      (frontendStore input n suffix [] [.one] (List.replicate out .one) []) = squareStore n out 0 := by
  funext k
  fin_cases k <;> rfl

lemma packetSquare_write (input suffix : List BSym) (n : ℕ) :
    StackProgPortLift.write packetSquarePorts (squareStore n (n*n) 0)
      (frontendStore input n suffix [] [.one] [] []) =
      frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [] := by
  classical
  funext l
  by_cases hl : ∃ k, packetSquarePorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [packetWrite_at]
    exact (congrFun (packetSquare_project input suffix n (n*n)) k).symm
  · have h6 : l ≠ 6 := by
      intro h
      apply hl
      exact ⟨1, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h6]

lemma packetBit_project (input suffix fuel : List BSym) (n : ℕ) :
    StackProgPortLift.project packetBitPorts (frontendStore input n suffix [] [] fuel []) =
      bitParserStore suffix fuel [] [] := by
  funext k
  fin_cases k <;> rfl

lemma packetBit_write (input suffix tail bits : List BSym) (n : ℕ) :
    StackProgPortLift.write packetBitPorts (bitParserStore tail [] bits [.one])
      (frontendStore input n suffix [] [] (List.replicate (n*n) .one) []) =
      frontendStore input n tail bits [.one] [] [] := by
  classical
  funext l
  by_cases hl : ∃ k, packetBitPorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [packetWrite_at]
    fin_cases k <;> rfl
  · have h2 : l ≠ 2 := by intro h; apply hl; exact ⟨0, h.symm⟩
    have h6 : l ≠ 6 := by intro h; apply hl; exact ⟨1, h.symm⟩
    have h3 : l ≠ 3 := by intro h; apply hl; exact ⟨2, h.symm⟩
    have h4 : l ≠ 4 := by intro h; apply hl; exact ⟨3, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h2, h6, h3, h4]

lemma packetBit_write_status (s : Fin 4 → List BSym) (base : Fin 32 → List BSym) :
    StackProgPortLift.write packetBitPorts s base 4 = s 3 := by
  exact packetWrite_at packetBitPorts s base 3

lemma packetBit_write_output (s : Fin 4 → List BSym) (base : Fin 32 → List BSym) :
    StackProgPortLift.write packetBitPorts s base 5 = base 5 := by
  classical
  have hn : ¬ ∃ k, packetBitPorts k = 5 := by decide
  simp [StackProgPortLift.write, hn]

lemma packetPopStatus_exec (input suffix : List BSym) (n : ℕ) :
    (popProg (4 : Fin 32)).Exec
      (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [])
      (frontendStore input n suffix [] [] (List.replicate (n*n) .one) []) 1 := by
  have hu : Function.update (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) []) 4
      ((frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) []) 4).tail =
      frontendStore input n suffix [] [] (List.replicate (n*n) .one) [] := by
    funext k
    fin_cases k <;> simp [frontendStore]
  simpa only [hu] using (stack_basic_macros (4 : Fin 32)
    (frontendStore input n suffix [] [.one] (List.replicate (n*n) .one) [])).2.1

theorem frontend_packet_source : ∃ p : StackProg (Fin 32) BSym,
    ∀ (input : List BSym) (n : ℕ) (suffix : List BSym), ∃ (s : Fin 32 → List BSym) (steps : ℕ),
      p.Exec (frontendStore input n suffix [] [.one] [] []) s steps ∧
      steps ≤ 100*(n+1)^2 ∧
      (∀ (bs : List Bool) (tail : List BSym), parseBits (n*n) suffix = some (bs, tail) →
        s = frontendStore input n tail ((bs.map boolSym).reverse) [.one] [] []) ∧
      (parseBits (n*n) suffix = none → s 4 = [.zero] ∧ s 5 = []) := by
  obtain ⟨ps, hs⟩ := unary_square_machine
  obtain ⟨pb, hb⟩ := bit_parser_machine
  refine ⟨.seq (StackProgPortLift.liftProgC packetSquarePorts packetSquareDecode ps)
    (.seq (popProg 4) (StackProgPortLift.liftProgC packetBitPorts packetBitDecode pb)), ?_⟩
  intro input n suffix
  have hsq := StackProgPortLift.liftProgC_exec packetSquarePorts packetSquareDecode
    packetSquareDecode_spec (hs n) (frontendStore input n suffix [] [.one] [] [])
    (by simpa using packetSquare_project input suffix n 0)
  rw [packetSquare_write] at hsq
  obtain ⟨t, m, hbit, hm, hsuccess, hfailure⟩ := hb (n*n) suffix
  have hbp := StackProgPortLift.liftProgC_exec packetBitPorts packetBitDecode
    packetBitDecode_spec hbit
    (frontendStore input n suffix [] [] (List.replicate (n*n) .one) [])
    (packetBit_project input suffix (List.replicate (n*n) .one) n)
  have hex := StackProg.Exec.seq hsq (StackProg.Exec.seq (packetPopStatus_exec input suffix n) hbp)
  refine ⟨_, _, hex, ?_, ?_, ?_⟩
  · nlinarith
  · intro bs tail h
    rw [hsuccess bs tail h]
    exact packetBit_write input suffix tail ((bs.map boolSym).reverse) n
  · intro h
    constructor
    · rw [packetBit_write_status, hfailure h]
    · rw [packetBit_write_output]
      rfl

end TensorNP.Encoder
end


/- Inlined module: Matrix32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def matrix32Ports : Fin 12 ↪ Fin 32 := ⟨![7,1,6,8,9,10,11,12,4,13,14,15], by decide⟩

def matrix32Decode (l : Fin 32) : Option (Fin 12) :=
  if l = 7 then some 0 else if l = 1 then some 1 else if l = 6 then some 2
  else if l = 8 then some 3 else if l = 9 then some 4 else if l = 10 then some 5
  else if l = 11 then some 6 else if l = 12 then some 7 else if l = 4 then some 8
  else if l = 13 then some 9 else if l = 14 then some 10 else if l = 15 then some 11 else none

lemma matrix32Decode_spec (l : Fin 32) (k : Fin 12) :
    matrix32Decode l = some k ↔ matrix32Ports k = l := by
  fin_cases l <;> fin_cases k <;> decide

private lemma matrix32Write_at (t : Fin 12 → List BSym) (s : Fin 32 → List BSym) (k : Fin 12) :
    StackProgPortLift.write matrix32Ports t s (matrix32Ports k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := matrix32Ports.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma matrix32_project (input data : List BSym) (n : ℕ) (good : Bool) :
    StackProgPortLift.project matrix32Ports
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data) =
      checkerStore n 0 0 data good := by
  funext k
  fin_cases k <;> rfl

lemma matrix32_write (input data : List BSym) (n : ℕ) (good : Bool) :
    StackProgPortLift.write matrix32Ports (checkerStore n 0 0 data good)
      (frontendStore input n [] [] [] [] data) =
      frontendStore input n [] [] (if good then [] else [.zero]) [] data := by
  classical
  funext l
  by_cases hl : ∃ k, matrix32Ports k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [matrix32Write_at]
    exact (congrFun (matrix32_project input data n good) k).symm
  · have h4 : l ≠ 4 := by intro h; apply hl; exact ⟨8, h.symm⟩
    simp [StackProgPortLift.write, hl, frontendStore, h4]

def matrix32Targets (k : Fin 32) : Bool := decide (k = 7)

def matrix32Normalize (h : Fin 32 → Option BSym) (k : Fin 32) : StackAct BSym :=
  if k = 4 ∧ h 4 = none then .push .one else .keep

lemma matrix32Transfer_exec (input data : List BSym) (n : ℕ) :
    (transferProg (3 : Fin 32) matrix32Targets).Exec
      (frontendStore input n [] data.reverse [.one] [] [])
      (frontendStore input n [] [] [.one] [] data) (3*data.length+1) := by
  have h := stack_transfer (3 : Fin 32) matrix32Targets
    (frontendStore input n [] data.reverse [.one] [] [])
  have hu : transferStore (3 : Fin 32) matrix32Targets
      (frontendStore input n [] data.reverse [.one] [] []) =
      frontendStore input n [] [] [.one] [] data := by
    funext k
    fin_cases k <;> simp [transferStore, matrix32Targets, frontendStore]
  rw [hu] at h
  simpa [frontendStore] using h

lemma matrix32Pop_exec (input data : List BSym) (n : ℕ) :
    (popProg (4 : Fin 32)).Exec (frontendStore input n [] [] [.one] [] data)
      (frontendStore input n [] [] [] [] data) 1 := by
  have hu : Function.update (frontendStore input n [] [] [.one] [] data) 4
      ((frontendStore input n [] [] [.one] [] data) 4).tail =
      frontendStore input n [] [] [] [] data := by
    funext k
    fin_cases k <;> simp [frontendStore]
  simpa only [hu] using (stack_basic_macros (4 : Fin 32)
    (frontendStore input n [] [] [.one] [] data)).2.1

lemma matrix32Normalize_exec (input data : List BSym) (n : ℕ) (good : Bool) :
    (StackProg.act matrix32Normalize).Exec
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data)
      (frontendStore input n [] [] [if good then .one else .zero] [] data) 1 := by
  have hu : StackProg.applyAct matrix32Normalize
      (frontendStore input n [] [] (if good then [] else [.zero]) [] data) =
      frontendStore input n [] [] [if good then .one else .zero] [] data := by
    cases good <;> funext k <;> fin_cases k <;> rfl
  simpa only [hu] using StackProg.Exec.act matrix32Normalize
    (frontendStore input n [] [] (if good then [] else [.zero]) [] data)

theorem frontend_matrix_source : ∃ p : StackProg (Fin 32) BSym,
    ∀ (input : List BSym) (n : ℕ) (bs : List Bool), bs.length = n*n → ∃ steps,
      p.Exec (frontendStore input n [] ((bs.map boolSym).reverse) [.one] [] [])
        (frontendStore input n [] [] [if decide (ValidMatrix n bs) then BSym.one else .zero]
          [] (bs.map boolSym)) steps ∧
      steps ≤ 1100*(n+1)^4 := by
  obtain ⟨pc, hc⟩ := matrix_checker_source
  refine ⟨.seq (transferProg 3 matrix32Targets)
    (.seq (popProg 4) (.seq (StackProgPortLift.liftProgC matrix32Ports matrix32Decode pc)
      (.act matrix32Normalize))), ?_⟩
  intro input n bs hlen
  have hlen' : (bs.map boolSym).length = n*n := by simpa using hlen
  obtain ⟨m, hm, hmB⟩ := hc n (bs.map boolSym) true hlen'
  have hlift := StackProgPortLift.liftProgC_exec matrix32Ports matrix32Decode matrix32Decode_spec
    hm (frontendStore input n [] [] [] [] (bs.map boolSym))
    (by simpa using matrix32_project input (bs.map boolSym) n true)
  rw [matrix32_write] at hlift
  have he := StackProg.Exec.seq (matrix32Transfer_exec input (bs.map boolSym) n)
    (StackProg.Exec.seq (matrix32Pop_exec input (bs.map boolSym) n)
      (StackProg.Exec.seq hlift (matrix32Normalize_exec input (bs.map boolSym) n
        (true && matrixCheckPrefix n (bs.map boolSym) n))))
  have hflag : matrixCheckPrefix n (bs.map boolSym) n = decide (ValidMatrix n bs) := by
    have hiff := matrixCheckPrefix_valid n bs hlen
    cases h : matrixCheckPrefix n (bs.map boolSym) n <;> simp_all
  rw [Bool.true_and, hflag] at he
  refine ⟨_, he, ?_⟩
  have hpow : (n+1)^2 ≤ (n+1)^4 := pow_le_pow_right₀ (by omega) (by omega)
  have hsquare : n*n ≤ (n+1)^2 := by nlinarith
  have hquart : n*n ≤ (n+1)^4 := le_trans hsquare hpow
  have hone : 1 ≤ (n+1)^4 := Nat.one_le_pow 4 (n+1) (by omega)
  simp only [List.length_map, hlen]
  omega

end TensorNP.Encoder
end


/- Inlined module: Frontend -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def frontendHeaderGuard (h : Fin 32 → Option BSym) : Bool := h 4 == some .one

def frontendPacketGuard (h : Fin 32 → Option BSym) : Bool :=
  (h 4 == some .one) && (h 2).isNone

def frontendReject : StackProg (Fin 32) BSym := .seq (popProg 4) (pushProg 4 .zero)

def frontendProgram (header packet matrix : StackProg (Fin 32) BSym) : StackProg (Fin 32) BSym :=
  .seq header (.branch frontendHeaderGuard
    (.seq (clearProg 6) (.seq packet (.branch frontendPacketGuard matrix frontendReject))) frontendReject)

def FrontCorrect (input : List BSym) (s : Fin 32 → List BSym) : Prop :=
  (∀ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G →
    s = frontendGraphStore input v ((graphBits G).map boolSym)) ∧
  ((¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input = TensorNP.Eigen.graphCode G) →
    s 4 = [.zero] ∧ s 5 = [])

theorem frontendReject_exec (s : Fin 32 → List BSym) (hstatus : (s 4).tail = []) :
    frontendReject.Exec s (Function.update s 4 [.zero]) 3 := by
  have hp := (stack_basic_macros (4 : Fin 32) s).2.1
  have hq := (stack_basic_macros (4 : Fin 32) (Function.update s 4 (s 4).tail)).1 BSym.zero
  have he := StackProg.Exec.seq hp hq
  have heq : Function.update (Function.update s 4 (s 4).tail) 4
      (.zero :: (Function.update s 4 (s 4).tail) 4) = Function.update s 4 [.zero] := by
    simp [hstatus]
  simpa only [frontendReject, heq] using he

theorem frontendClearFuel_exec (input : List BSym) (n : ℕ)
    (suffix bits status fuel data : List BSym) :
    (clearProg (6 : Fin 32)).Exec (frontendStore input n suffix bits status fuel data)
      (frontendStore input n suffix bits status [] data) (3*fuel.length+1) := by
  have heq : Function.update (frontendStore input n suffix bits status fuel data) 6 [] =
      frontendStore input n suffix bits status [] data := by
    funext k
    fin_cases k <;> simp [frontendStore]
  have hc := (stack_basic_macros (6 : Fin 32) (frontendStore input n suffix bits status fuel data)).2.2
  rw [heq] at hc
  simpa [frontendStore] using hc

theorem frontendHeaderGuard_store (input : List BSym) (r : HeaderResult) :
    frontendHeaderGuard (fun k => (frontendHeaderStore input r k).head?) = r.found := by
  cases hf : r.found <;> simp [frontendHeaderGuard, frontendHeaderStore, frontendStore, hf]

theorem frontend_budget (C L head clear packet matrix : ℕ)
    (hh : head ≤ C*(L+2)^3) (hc : clear ≤ 3*(L+1)+1)
    (hp : packet ≤ 100*(L+1)^2) (hm : matrix ≤ 1100*(L+1)^4) :
    head+clear+packet+matrix+20 ≤ (C+5000)*(L+2)^5 := by
  have h1 : L+2 ≤ (L+2)^5 := Nat.le_self_pow (by decide) _
  have h3 : (L+2)^3 ≤ (L+2)^5 := pow_le_pow_right₀ (by omega) (by decide)
  have h2 : (L+1)^2 ≤ (L+2)^5 :=
    (Nat.pow_le_pow_left (by omega : L+1 ≤ L+2) 2).trans
      (pow_le_pow_right₀ (by omega) (by decide))
  have h4 : (L+1)^4 ≤ (L+2)^5 :=
    (Nat.pow_le_pow_left (by omega : L+1 ≤ L+2) 4).trans
      (pow_le_pow_right₀ (by omega) (by decide))
  have hh' := hh.trans (Nat.mul_le_mul_left C h3)
  have hp' := hp.trans (Nat.mul_le_mul_left 100 h2)
  have hm' := hm.trans (Nat.mul_le_mul_left 1100 h4)
  rw [Nat.add_mul]
  omega

theorem graph_frontend_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ input : List BSym, ∃ (s : Fin 32 → List BSym) (steps : ℕ),
      p.Exec (frontendInputStore input) s steps ∧ steps ≤ C*(input.length+2)^5 ∧ FrontCorrect input s := by
  obtain ⟨ph, Ch, hph⟩ := frontend_header_source
  obtain ⟨pp, hpp⟩ := frontend_packet_source
  obtain ⟨pm, hpm⟩ := frontend_matrix_source
  refine ⟨frontendProgram ph pp pm, Ch+5000, fun input => ?_⟩
  let r := boundedHeader 0 (input.length+1) input
  obtain ⟨h, hhead, hh⟩ := hph input
  by_cases hf : r.found = true
  · have hclear : (clearProg (6 : Fin 32)).Exec (frontendHeaderStore input r)
        (frontendStore input r.dimension r.suffix [] [.one] [] []) (3*r.fuel+1) := by
      simpa [frontendHeaderStore, hf] using
        frontendClearFuel_exec input r.dimension r.suffix [] [.one] (List.replicate r.fuel .one) []
    obtain ⟨s, u, hpacket, hu, hps, hpf⟩ := hpp input r.dimension r.suffix
    have hn : r.dimension ≤ input.length := boundedHeader_dimension_le input hf
    have hrf : r.fuel ≤ input.length+1 := boundedHeader_fuel_le 0 (input.length+1) input
    have hu' : u ≤ 100*(input.length+1)^2 :=
      hu.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))
    cases hp0 : parseBits (r.dimension*r.dimension) r.suffix with
    | none =>
        have hfail := hpf hp0
        have hreject := frontendReject_exec s (by simp [hfail.1])
        have hinner := StackProg.Exec.branchFalse (test := frontendPacketGuard)
          (p := pm) (by simp [frontendPacketGuard, hfail.1]) hreject
        have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
          (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
          (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
        have hex := StackProg.Exec.seq hhead houter
        refine ⟨_, _, hex, ?_, ?_, ?_⟩
        · have hbudget := frontend_budget Ch input.length h (3*r.fuel+1) u 0 hh
            (by omega) hu' (by omega)
          omega
        · intro vertex G hinput
          have hc := canonical_front_packet G input hinput
          have hp := hc.2.2.1
          rw [hp0] at hp
          contradiction
        · intro _
          simp [hfail.2]
    | some pair =>
        rcases pair with ⟨bs, tail⟩
        rw [hps bs tail hp0] at hpacket
        by_cases ht : tail = []
        · subst tail
          have hlen : bs.length = r.dimension*r.dimension := (parseBits_sound _ _ _ _ hp0).1
          obtain ⟨v, hmatrix, hv⟩ := hpm input r.dimension bs hlen
          have hinner := StackProg.Exec.branchTrue (test := frontendPacketGuard)
            (q := frontendReject) (by simp [frontendPacketGuard, frontendStore]) hmatrix
          have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
            (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
            (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
          have hex := StackProg.Exec.seq hhead houter
          refine ⟨_, _, hex, ?_, ?_, ?_⟩
          · have hv' : v ≤ 1100*(input.length+1)^4 :=
              hv.trans (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left (by omega) 4))
            have hb := frontend_budget Ch input.length h (3*r.fuel+1) u v hh (by omega) hu' hv'
            omega
          · intro vertex G hinput
            have hc := canonical_front_packet G input hinput
            have hpEq : (bs, []) = (graphBits G, []) := Option.some.inj (hp0.symm.trans hc.2.2.1)
            have hbs : bs = graphBits G := congrArg Prod.fst hpEq
            have hvalid : ValidMatrix r.dimension bs := by simpa [hbs] using hc.2.2.2
            have htag : (if decide (ValidMatrix r.dimension bs) then BSym.one else .zero) = BSym.one := by
              simp [hvalid]
            rw [htag, hc.2.1, hbs]
            rfl
          · intro hnon
            have hbad : ¬ ValidMatrix r.dimension bs := by
              intro hvalid
              exact hnon (canonical_packet_accept input bs hf hp0 hvalid)
            simp [frontendStore, hbad]
        · have hguard : frontendPacketGuard (fun k =>
              (frontendStore input r.dimension tail ((bs.map boolSym).reverse) [.one] [] [] k).head?) = false := by
              cases tail with
              | nil => exact (ht rfl).elim
              | cons a tail => rfl
          have hreject := frontendReject_exec
            (frontendStore input r.dimension tail ((bs.map boolSym).reverse) [.one] [] [])
            (by simp [frontendStore])
          have hinner := StackProg.Exec.branchFalse (test := frontendPacketGuard) (p := pm)
            hguard hreject
          have houter := StackProg.Exec.branchTrue (test := frontendHeaderGuard)
            (q := frontendReject) (by rw [frontendHeaderGuard_store, hf])
            (StackProg.Exec.seq hclear (StackProg.Exec.seq hpacket hinner))
          have hex := StackProg.Exec.seq hhead houter
          refine ⟨_, _, hex, ?_, ?_, ?_⟩
          · have hbudget := frontend_budget Ch input.length h (3*r.fuel+1) u 0 hh
              (by omega) hu' (by omega)
            omega
          · intro vertex G hinput
            have hc := canonical_front_packet G input hinput
            have hpEq : (bs, tail) = (graphBits G, []) := Option.some.inj (hp0.symm.trans hc.2.2.1)
            exact (ht (congrArg Prod.snd hpEq)).elim
          · intro _
            simp [frontendStore]
  · have hf' : r.found = false := Bool.eq_false_of_not_eq_true hf
    have hreject := frontendReject_exec (frontendHeaderStore input r) (by
      simp [frontendHeaderStore, frontendStore, hf'])
    have houter := StackProg.Exec.branchFalse (test := frontendHeaderGuard)
      (p := .seq (clearProg 6) (.seq pp (.branch frontendPacketGuard pm frontendReject)))
      (by rw [frontendHeaderGuard_store, hf']) hreject
    have hex := StackProg.Exec.seq hhead houter
    refine ⟨_, _, hex, ?_, ?_, ?_⟩
    · have hbudget := frontend_budget Ch input.length h 0 0 0 hh (by omega) (by omega) (by omega)
      omega
    · intro vertex G hinput
      have hc := canonical_front_packet G input hinput
      exact (hf hc.1).elim
    · intro _
      simp [frontendHeaderStore, frontendStore]

end TensorNP.Encoder
end


/- Inlined module: EncoderSource -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

def encoderKeep : StackProg (Fin 32) BSym := .act (fun _ _ => .keep)

lemma encoderKeep_exec (s : Fin 32 → List BSym) : encoderKeep.Exec s s 1 := by
  have he : StackProg.applyAct (fun _ _ => StackAct.keep) s=s := by funext k; rfl
  simpa only [encoderKeep, he] using StackProg.Exec.act (fun _ _ => StackAct.keep) s

lemma encoderSource_budget (Cf Cb d L front back : ℕ)
    (hf : front≤Cf*(L+2)^5) (hb : back≤Cb*(L+2)^d) :
    front+back+3≤(Cf+Cb+3)*(L+2)^(d+5) := by
  have hp5 : (L+2)^5≤(L+2)^(d+5) := pow_le_pow_right₀ (by omega) (by omega)
  have hpd : (L+2)^d≤(L+2)^(d+5) := pow_le_pow_right₀ (by omega) (by omega)
  have hp0 : 1≤(L+2)^(d+5) := Nat.one_le_pow _ _ (by omega)
  have hf' := hf.trans (Nat.mul_le_mul_left Cf hp5)
  have hb' := hb.trans (Nat.mul_le_mul_left Cb hpd)
  rw [Nat.add_mul, Nat.add_mul]
  omega

/-- The frontend rejects every malformed input and exposes the unique canonical matrix otherwise. -/
theorem encoder_source_of_backend (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps≤Cb*(v+1)^d ∧ s 5=tensorCode (colorTensor G)) :
    ∃ (p : StackProg (Fin 32) BSym) (C : ℕ), ∀ input : List BSym,
      ∃ (s : Fin 32 → List BSym) (steps : ℕ), p.Exec (frontendInputStore input) s steps ∧
        steps≤C*(input.length+2)^(d+5) ∧ s 5=eigenEncoderValue input := by
  obtain ⟨front, Cf, hfront⟩ := graph_frontend_source
  refine ⟨.seq front (.branch frontendHeaderGuard backend encoderKeep), Cf+Cb+3, ?_⟩
  intro input
  obtain ⟨s, n, he, hn, hcorrect⟩ := hfront input
  classical
  by_cases hcan : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), input=graphCode G
  · obtain ⟨v, G, hinput⟩ := hcan
    have hs : s=frontendGraphStore input v (graphData G) := by
      simpa only [graphData] using hcorrect.1 v G hinput
    rw [hs] at he
    obtain ⟨out, m, hb, hm, hout⟩ := hbackend input v G
    have hg : frontendHeaderGuard (fun k => (frontendGraphStore input v (graphData G) k).head?)=true := by
      simp [frontendHeaderGuard, frontendGraphStore, frontendStore]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchTrue (test := frontendHeaderGuard) (q := encoderKeep) hg hb)
    refine ⟨out, n+1+(1+m), hex, ?_, ?_⟩
    · have hv : v ≤ input.length := by simpa only [hinput] using graphCode_dimension_le G
      have hm' := hm.trans (Nat.mul_le_mul_left Cb
        (Nat.pow_le_pow_left (by omega : v+1 ≤ input.length+2) d))
      have hbudget := encoderSource_budget Cf Cb d input.length n m hn hm'
      omega
    · rw [hout, hinput, eigenEncoderValue_graphCode]
  · have hc := hcorrect.2 hcan
    have hg : frontendHeaderGuard (fun k => (s k).head?)=false := by
      simp [frontendHeaderGuard, hc.1]
    have hex := StackProg.Exec.seq he
      (StackProg.Exec.branchFalse (test := frontendHeaderGuard) (p := backend) hg (encoderKeep_exec s))
    refine ⟨s, n+1+(1+1), hex, ?_, ?_⟩
    · simpa using encoderSource_budget Cf Cb d input.length n 0 hn (by omega)
    · rw [hc.2, eigenEncoderValue_invalid input hcan]

end TensorNP.Encoder
end


/- Inlined module: NativeBridge -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen
namespace TensorNP.Encoder

/-- Every explicit source polynomial fits the exact Cook budget, including inputs of length zero. -/
theorem source_budget (A d : ℕ) : ∃ k, ∀ n : ℕ, A*(n+2)^d≤n^k+k := by
  let k := A+2*d+A*3^d+1
  refine ⟨k, ?_⟩
  intro n
  have hk : k≠0 := by dsimp [k]; omega
  by_cases hz : n=0
  · subst n
    have hb : A*2^d≤A*3^d := Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by decide) d)
    simp only [Nat.zero_add, zero_pow hk]
    dsimp [k]
    omega
  by_cases ho : n=1
  · subst n
    simp only [one_pow]
    dsimp [k]
    omega
  have hn : 2≤n := by omega
  have hc : A≤n^A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left hn A)
  have hb : n+2≤n^2 := by nlinarith
  calc
    A*(n+2)^d ≤ n^A*(n^2)^d := Nat.mul_le_mul hc (Nat.pow_le_pow_left hb d)
    _ = n^(A+2*d) := by rw [pow_add, pow_mul]
    _ ≤ n^k+k := by
      have hp : n^(A+2*d)≤n^k := Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)
      omega

theorem encoder_polytime_of_backend (backend : StackProg (Fin 32) BSym) (Cb d : ℕ)
    (hbackend : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps≤Cb*(v+1)^d ∧ s 5=tensorCode (colorTensor G)) :
    CookPvsNP.PolyTimeComputable eigenEncoderValue := by
  obtain ⟨p, C, hp⟩ := encoder_source_of_backend backend Cb d hbackend
  obtain ⟨k, hk⟩ := source_budget C (d+5)
  apply CookPvsNP.stack_program_polytime p (0 : Fin 32) 5 eigenEncoderValue k
  intro input
  obtain ⟨s, n, he, hn, hout⟩ := hp input
  exact ⟨s, n, hn.trans (hk input.length), he, hout⟩

end TensorNP.Encoder
end


/- Inlined module: UnaryAffine -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace TensorNP.Encoder

def affineStore (n out : ℕ) : Fin 3 → List BSym :=
  fun k => if k = 0 then List.replicate n .one else if k = 1 then List.replicate out .one else []

private def affineKeep : StackProg (Fin 3) BSym := .act (fun _ _ => .keep)

private def affineCopies : ℕ → StackProg (Fin 3) BSym
  | 0 => affineKeep
  | a + 1 => .seq (copyProg 0 1 2) (affineCopies a)

private def affinePushes : ℕ → StackProg (Fin 3) BSym
  | 0 => affineKeep
  | b + 1 => .seq (pushProg 1 .one) (affinePushes b)

private lemma affineKeep_exec (n out : ℕ) :
    affineKeep.Exec (affineStore n out) (affineStore n out) 1 := by
  have hid : StackProg.applyAct (fun _ _ => StackAct.keep) (affineStore n out) = affineStore n out := by
    funext k
    rfl
  simpa only [affineKeep, hid] using (StackProg.Exec.act (fun _ _ => StackAct.keep) (affineStore n out))

private lemma affineCopy_exec (n out : ℕ) :
    (copyProg 0 1 2).Exec (affineStore n out) (affineStore n (n + out)) (6 * n + 3) := by
  have he := stack_copy (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    (affineStore n out) (by rfl)
  have heq : Function.update (affineStore n out) 1
      ((affineStore n out) 0 ++ (affineStore n out) 1) = affineStore n (n + out) := by
    funext k
    fin_cases k <;> simp [affineStore, Function.update]
  rw [heq] at he
  simpa [affineStore] using he

private lemma affineCopies_exec (a n out : ℕ) :
    (affineCopies a).Exec (affineStore n out) (affineStore n (out + a * n))
      (a * (6 * n + 4) + 1) := by
  induction a generalizing out with
  | zero => simpa [affineCopies] using affineKeep_exec n out
  | succ a ih =>
      have he := StackProg.Exec.seq (affineCopy_exec n out) (ih (n + out))
      have hout : (n + out) + a * n = out + (a + 1) * n := by ring
      have hcost : 6 * n + 3 + 1 + (a * (6 * n + 4) + 1) =
          (a + 1) * (6 * n + 4) + 1 := by ring
      rw [hout, hcost] at he
      exact he

private lemma affinePush_exec (n out : ℕ) :
    (pushProg 1 .one).Exec (affineStore n out) (affineStore n (out + 1)) 1 := by
  have heq : StackProg.applyAct (fun _ k => if k = 1 then .push BSym.one else .keep)
      (affineStore n out) = affineStore n (out + 1) := by
    funext k
    fin_cases k <;> rfl
  simpa only [pushProg, heq] using (StackProg.Exec.act
    (fun _ k => if k = 1 then .push BSym.one else .keep) (affineStore n out))

private lemma affinePushes_exec (b n out : ℕ) :
    (affinePushes b).Exec (affineStore n out) (affineStore n (out + b)) (2 * b + 1) := by
  induction b generalizing out with
  | zero => simpa [affinePushes] using affineKeep_exec n out
  | succ b ih =>
      have he := StackProg.Exec.seq (affinePush_exec n out) (ih (out + 1))
      have hout : (out + 1) + b = out + (b + 1) := by omega
      have hcost : 1 + 1 + (2 * b + 1) = 2 * (b + 1) + 1 := by omega
      rw [hout, hcost] at he
      exact he

theorem unary_affine_machine (a b : ℕ) : ∃ p : StackProg (Fin 3) BSym, ∀ n : ℕ, ∃ steps,
    p.Exec (affineStore n 0) (affineStore n (a*n+b)) steps ∧
      steps ≤ (8*a+2*b+10)*(n+1) := by
  refine ⟨.seq (affineCopies a) (affinePushes b), ?_⟩
  intro n
  have hc := affineCopies_exec a n 0
  simp only [Nat.zero_add] at hc
  have hp := affinePushes_exec b n (a * n)
  have he := StackProg.Exec.seq hc hp
  refine ⟨a * (6 * n + 4) + 1 + 1 + (2 * b + 1), he, ?_⟩
  nlinarith

end TensorNP.Encoder
end


/- Inlined module: EmitterFrames32 -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Encoder

def emitterAffinePorts : Fin 3 ↪ Fin 32 := ⟨![1,14,20], by decide⟩
def emitterAffineDecode (l : Fin 32) : Option (Fin 3) :=
  if l = 1 then some 0 else if l = 14 then some 1 else if l = 20 then some 2 else none

lemma emitterAffineDecode_spec (l : Fin 32) (k : Fin 3) :
    emitterAffineDecode l = some k ↔ emitterAffinePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

def emitterWriterPorts : Fin 12 ↪ Fin 32 := ⟨![14,5,20,21,22,1,7,15,16,17,19,23], by decide⟩
def emitterWriterDecode (l : Fin 32) : Option (Fin 12) :=
  if l = 14 then some 0 else if l = 5 then some 1 else if l = 20 then some 2
  else if l = 21 then some 3 else if l = 22 then some 4 else if l = 1 then some 5
  else if l = 7 then some 6 else if l = 15 then some 7 else if l = 16 then some 8
  else if l = 17 then some 9 else if l = 19 then some 10 else if l = 23 then some 11 else none

lemma emitterWriterDecode_spec (l : Fin 32) (k : Fin 12) :
    emitterWriterDecode l = some k ↔ emitterWriterPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private lemma emitterWrite_at {K : Type} (r : K ↪ Fin 32) (t : K → List BSym)
    (s : Fin 32 → List BSym) (k : K) :
    StackProgPortLift.write r t s (r k) = t k := by
  classical
  unfold StackProgPortLift.write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

lemma emitter_zero (input data : List BSym) (v : ℕ) :
    frontendGraphStore input v data = emitterStore input data v 0 0 0 0 [] := by
  funext l
  fin_cases l <;> rfl

lemma emitterAffine_project (input data : List BSym) (v out : ℕ) :
    StackProgPortLift.project emitterAffinePorts (emitterStore input data v out 0 0 0 []) =
      affineStore v out := by
  funext k
  fin_cases k <;> rfl

lemma emitterAffine_write (input data : List BSym) (v out : ℕ) :
    StackProgPortLift.write emitterAffinePorts (affineStore v out)
      (emitterStore input data v 0 0 0 0 []) = emitterStore input data v out 0 0 0 [] := by
  classical
  funext l
  by_cases hl : ∃ k, emitterAffinePorts k = l
  · obtain ⟨k, rfl⟩ := hl
    rw [emitterWrite_at]
    exact (congrFun (emitterAffine_project input data v out) k).symm
  · have h14 : l ≠ 14 := by intro h; apply hl; exact ⟨1, h.symm⟩
    simp [StackProgPortLift.write, hl, emitterStore, h14]

def emitterWriterFrame (data : List BSym) (v i j k : ℕ) : Fin 7 → List BSym :=
  fun l => if l = 0 then List.replicate v .one else if l = 1 then data
    else if l = 2 then List.replicate i .one else if l = 3 then List.replicate j .one
    else if l = 4 then List.replicate k .one else []

lemma emitterWriter_project (input data : List BSym) (v N i j k : ℕ) (tail : List BSym) :
    StackProgPortLift.project emitterWriterPorts (emitterStore input data v N i j k tail) =
      writerStore12 N tail (emitterWriterFrame data v i j k) := by
  funext l
  fin_cases l <;> rfl

lemma emitterWriter_write (input data : List BSym) (v N i j k : ℕ) (tail output : List BSym) :
    StackProgPortLift.write emitterWriterPorts (writerStore12 N output (emitterWriterFrame data v i j k))
      (emitterStore input data v N i j k tail) = emitterStore input data v N i j k output := by
  classical
  funext l
  by_cases hl : ∃ k, emitterWriterPorts k = l
  · obtain ⟨a, rfl⟩ := hl
    rw [emitterWrite_at]
    exact (congrFun (emitterWriter_project input data v N i j k output) a).symm
  · have h5 : l ≠ 5 := by intro h; apply hl; exact ⟨1, h.symm⟩
    simp [StackProgPortLift.write, hl, emitterStore, h5]

theorem emitter_init_source : ∃ p : StackProg (Fin 32) BSym,
    ∀ (input data : List BSym) (v : ℕ), ∃ steps,
      p.Exec (frontendGraphStore input v data) (emitterStore input data v (8*v+2) 0 0 0 []) steps ∧
      steps ≤ 100*(v+1) := by
  obtain ⟨p, hp⟩ := unary_affine_machine 8 2
  refine ⟨StackProgPortLift.liftProgC emitterAffinePorts emitterAffineDecode p, ?_⟩
  intro input data v
  obtain ⟨steps, hs, hb⟩ := hp v
  have hlift := StackProgPortLift.liftProgC_exec emitterAffinePorts emitterAffineDecode
    emitterAffineDecode_spec hs (emitterStore input data v 0 0 0 0 [])
    (emitterAffine_project input data v 0)
  rw [emitterAffine_write] at hlift
  refine ⟨steps, ?_, ?_⟩
  · rw [emitter_zero]
    exact hlift
  · omega

theorem emitter_header_source : ∃ (p : StackProg (Fin 32) BSym) (C : ℕ),
    ∀ (input data : List BSym) (v N i j k : ℕ) (tail : List BSym), ∃ steps,
      p.Exec (emitterStore input data v N i j k tail)
        (emitterStore input data v N i j k (encNat N ++ tail)) steps ∧
      steps ≤ C*(N+1)^2 := by
  obtain ⟨p, C, hp⟩ := nativeWriter12
  refine ⟨StackProgPortLift.liftProgC emitterWriterPorts emitterWriterDecode p, C, ?_⟩
  intro input data v N i j k tail
  obtain ⟨steps, hs, hb⟩ := hp N tail (emitterWriterFrame data v i j k)
  have hlift := StackProgPortLift.liftProgC_exec emitterWriterPorts emitterWriterDecode
    emitterWriterDecode_spec hs (emitterStore input data v N i j k tail)
    (emitterWriter_project input data v N i j k tail)
  rw [emitterWriter_write] at hlift
  exact ⟨steps, hlift, hb⟩

end TensorNP.Encoder
end


/- Inlined module: DenseBackend -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen

namespace TensorNP.Encoder

lemma denseBackend_budget (C d Ch v init dense header : ℕ)
    (hi : init ≤ 100*(v+1))
    (hd : dense ≤ (C*(v+1)^d+100)*(colorSize v+1)^4)
    (hh : header ≤ Ch*(colorSize v+1)^2) :
    init+1+(dense+1+header) ≤ (100+14641*(C+100)+121*Ch+3)*(v+1)^(d+4) := by
  have hn : colorSize v+1 ≤ 11*(v+1) := by simp [colorSize]; omega
  have h4 : (colorSize v+1)^4 ≤ 14641*(v+1)^4 := by
    calc
      _ ≤ (11*(v+1))^4 := Nat.pow_le_pow_left hn 4
      _ = _ := by ring
  have h2 : (colorSize v+1)^2 ≤ 121*(v+1)^2 := by
    calc
      _ ≤ (11*(v+1))^2 := Nat.pow_le_pow_left hn 2
      _ = _ := by ring
  have hone : 1 ≤ (v+1)^d := Nat.one_le_pow d (v+1) (by omega)
  have hp1 : v+1 ≤ (v+1)^(d+4) := by
    simpa using (pow_le_pow_right₀ (a := v+1) (by omega) (show 1 ≤ d+4 by omega))
  have hp2 : (v+1)^2 ≤ (v+1)^(d+4) :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hp4 : (v+1)^4 ≤ (v+1)^(d+4) :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hp0 : 1 ≤ (v+1)^(d+4) := Nat.one_le_pow _ _ (by omega)
  have hcoeff : C*(v+1)^d+100 ≤ (C+100)*(v+1)^d := by nlinarith
  have hdb : dense ≤ 14641*(C+100)*(v+1)^(d+4) := by
    calc
      dense ≤ (C*(v+1)^d+100)*(colorSize v+1)^4 := hd
      _ ≤ ((C+100)*(v+1)^d)*(14641*(v+1)^4) := Nat.mul_le_mul hcoeff h4
      _ = 14641*(C+100)*(v+1)^(d+4) := by rw [pow_add]; ring
  have hib := hi.trans (Nat.mul_le_mul_left 100 hp1)
  have hhb : header ≤ (121*Ch)*(v+1)^(d+4) := by
    calc
      header ≤ Ch*(colorSize v+1)^2 := hh
      _ ≤ Ch*(121*(v+1)^2) := Nat.mul_le_mul_left Ch h2
      _ ≤ (121*Ch)*(v+1)^(d+4) := by nlinarith
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem dense_backend_of_entry (entry : StackProg (Fin 32) BSym) (C d : ℕ)
    (hentry : ∀ (input data : List BSym) (v i j k : ℕ) (tail : List BSym),
      data.length = v*v → i < colorSize v → j < colorSize v → k < colorSize v → ∃ steps,
        entry.Exec (emitterStore input data v (colorSize v) i j k tail)
          (emitterStore input data v (colorSize v) i j k
            (encRat ((rawTensorEntry v data i j k : ℤ) : ℚ) ++ tail)) steps ∧
        steps ≤ C*(v+1)^d) :
    ∃ (p : StackProg (Fin 32) BSym) (C' : ℕ), ∀ (input data : List BSym) (v : ℕ),
      data.length = v*v → ∃ steps,
        p.Exec (frontendGraphStore input v data)
          (emitterStore input data v (colorSize v) 0 0 0
            (encNat (colorSize v) ++ chunkI
              (fun i j k => encRat ((rawTensorEntry v data i j k : ℤ) : ℚ))
              (colorSize v) (colorSize v))) steps ∧
        steps ≤ C'*(v+1)^(d+4) := by
  obtain ⟨pi, hi⟩ := emitter_init_source
  obtain ⟨pd, hd⟩ := dense_emitter_source entry
  obtain ⟨ph, Ch, hh⟩ := emitter_header_source
  refine ⟨.seq pi (.seq pd ph), 100+14641*(C+100)+121*Ch+3, ?_⟩
  intro input data v hlen
  let E := fun i j k => encRat ((rawTensorEntry v data i j k : ℤ) : ℚ)
  have hspec : denseEntrySpec entry E (C*(v+1)^d) input data v (colorSize v) := by
    intro i j k tail hi hj hk
    exact hentry input data v i j k tail hlen hi hj hk
  obtain ⟨a, ha, haB⟩ := hi input data v
  have ha' : pi.Exec (frontendGraphStore input v data)
      (emitterStore input data v (colorSize v) 0 0 0 []) a := by
    simpa [colorSize] using ha
  obtain ⟨b, hb, hbB⟩ := hd E (C*(v+1)^d) input data v (colorSize v) hspec []
  simp only [List.append_nil] at hb
  obtain ⟨c, hc, hcB⟩ := hh input data v (colorSize v) 0 0 0 (chunkI E (colorSize v) (colorSize v))
  have he := StackProg.Exec.seq ha' (StackProg.Exec.seq hb hc)
  refine ⟨a+1+(b+1+c), he, ?_⟩
  exact denseBackend_budget C d Ch v a b c haB hbB hcB

theorem dense_backend_graph_of_entry (entry : StackProg (Fin 32) BSym) (C d : ℕ)
    (hentry : ∀ (input data : List BSym) (v i j k : ℕ) (tail : List BSym),
      data.length = v*v → i < colorSize v → j < colorSize v → k < colorSize v → ∃ steps,
        entry.Exec (emitterStore input data v (colorSize v) i j k tail)
          (emitterStore input data v (colorSize v) i j k
            (encRat ((rawTensorEntry v data i j k : ℤ) : ℚ) ++ tail)) steps ∧
        steps ≤ C*(v+1)^d) :
    ∃ (p : StackProg (Fin 32) BSym) (C' : ℕ), ∀ (input : List BSym) (v : ℕ)
      (G : SimpleGraph (Fin v)), ∃ steps,
        p.Exec (frontendGraphStore input v (graphData G))
          (emitterStore input (graphData G) v (colorSize v) 0 0 0 (tensorCode (colorTensor G))) steps ∧
        steps ≤ C'*(v+1)^(d+4) := by
  obtain ⟨p, C', hp⟩ := dense_backend_of_entry entry C d hentry
  refine ⟨p, C', ?_⟩
  intro input v G
  have hlen : (graphData G).length = v*v := by simpa [graphData] using (graphBits_valid G).1
  obtain ⟨steps, he, hb⟩ := hp input (graphData G) v hlen
  rw [raw_tensor_code G] at he
  exact ⟨steps, he, hb⟩

end TensorNP.Encoder
end


/- Inlined module: FinalAssembled -/
section
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity TensorNP.Eigen TensorNP.Encoder

theorem solution :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)), f (graphCode G)=tensorCode (colorTensor G)) ∧
      (∀ w, (¬∃ (v : ℕ) (G : SimpleGraph (Fin v)), w=graphCode G) → f w=[]) := by
  obtain ⟨entry, C, hentry⟩ := tensor_entry_source
  obtain ⟨backend, Cb, hbackend⟩ := dense_backend_graph_of_entry entry C 4 hentry
  have hbackend' : ∀ (input : List BSym) (v : ℕ) (G : SimpleGraph (Fin v)),
      ∃ (s : Fin 32 → List BSym) (steps : ℕ),
        backend.Exec (frontendGraphStore input v (graphData G)) s steps ∧
        steps≤Cb*(v+1)^8 ∧ s 5=tensorCode (colorTensor G) := by
    intro input v G
    obtain ⟨steps, he, hb⟩ := hbackend input v G
    exact ⟨_, steps, he, hb, rfl⟩
  refine ⟨eigenEncoderValue, encoder_polytime_of_backend backend Cb 8 hbackend', ?_, ?_⟩
  · intro v G
    exact eigenEncoderValue_graphCode G
  · intro input h
    exact eigenEncoderValue_invalid input h
end


#print axioms solution
#check solution
