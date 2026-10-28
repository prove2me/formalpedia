-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.minusExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:33:04.624969+00:00
-- url     : https://prove2.me/submissions/8ea79c59-8244-43ca-9b79-65eac565ce58

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
















@[simp] theorem maximum_cons (x : ℕ) (xs : List ℕ) :
    maximum (x::xs) = max x (maximum xs) := rfl

theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤  maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)



theorem Expr.eval_maximum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.maximum es).eval v = ThreeBoundNumeric.maximum (es.map (fun e => e.eval v)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.maximum, List.foldr_cons, Expr.eval,
      List.map_cons, maximum_cons] using congrArg (Nat.max (e.eval v)) ih







theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤  k ∧ k <  b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Semantic interpretation of interval maxima in the transfer formula. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

theorem bool_boundary (f : ℕ → Bool) (j k : ℕ) (hjk : j <  k)
    (hj : f j = true) (hk : f k = false) :
    ∃ m, j ≤  m ∧ m <  k ∧ f m = true ∧ f (m+1) = false := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases hm : f k with
      | true => exact ⟨k,by omega,by omega,hm,hk⟩
      | false =>
          have hjk' : j <  k := by
            by_contra h
            have : j = k := by omega
            subst j
            simp [hm] at hj
          obtain ⟨m,hmj,hmk,hmt,hmf⟩ := ih hjk' hm
          exact ⟨m,hmj,by omega,hmt,hmf⟩

theorem fin_bool_boundary {n : ℕ} (f : Fin n → Bool) (j k : Fin n)
    (hjk : j <  k) (hj : f j = true) (hk : f k = false) :
    ∃ m : Fin n, j ≤  m ∧ m <  k ∧ f m = true ∧ f (next m) = false := by
  let ff : ℕ → Bool := fun a => if h : a <  n then f ⟨a,h⟩ else false
  have hj' : ff j.val = true := by simpa [ff] using hj
  have hk' : ff k.val = false := by simpa [ff] using hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := bool_boundary ff j.val k.val hjk hj' hk'
  have hmn : m <  n := hmk.trans k.isLt
  have hmn' : m+1 <  n := lt_of_le_of_lt hmk k.isLt
  refine ⟨⟨m,hmn⟩,hmj,hmk,?_,?_⟩
  · simpa [ff,hmn] using hmt
  · simpa [ff,hmn',next] using hmf

variable {n : ℕ} {I : Type} [Fintype I]





theorem minusExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k : Fin n) (hij : i ≤  j) (hjk : j <  k) :
    MBound F i j k ((minusExpr n i.val j.val k.val).eval v) := by
  intro x hj hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) j k hjk hj hk
  have hmn : m.val+1 <  n := lt_of_le_of_lt hmk k.isLt
  have hm := hv (.m i m) (hij.trans hmj) hmn x hmt hmf
  apply hm.trans
  simp only [minusExpr, if_pos (show i.val ≤  j.val ∧ j.val <  k.val from ⟨hij,hjk⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmj,hmk⟩,?_⟩
  simp only [Function.comp_apply,mExpr,dif_pos i.isLt,dif_pos m.isLt,Expr.eval]





end ThreeBoundNumeric





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v) (i j k : Fin n)
  (hij : @LE.le.{0} (Fin n) (@instLEFin n) i j) (hjk : @LT.lt.{0} (Fin n) (@instLTFin n) j k),
  @Sensitivity213981Formal.ThreeBoundProfiles.MBound (Fin n) I inst F i j k
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.minusExpr n (@Fin.val n i) (@Fin.val n j) (@Fin.val n k))) := @Sensitivity213981Formal.ThreeBoundNumeric.minusExpr_bound
