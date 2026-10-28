-- Prove2me | solution 1 for ThreeBoundNumeric.unionExpr_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:55.598844+00:00
-- url     : https://prove2.me/submissions/13981857-4be6-4c51-90fa-55083239a6f2

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures

namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles
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
    x ≤ maximum xs := by
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







theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤ k ∧ k < b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











end ThreeBoundNumeric



end

section
/- Semantic interpretation of interval maxima in the transfer formula. -/


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

theorem bool_boundary (f : ℕ → Bool) (j k : ℕ) (hjk : j < k)
    (hj : f j = true) (hk : f k = false) :
    ∃ m, j ≤ m ∧ m < k ∧ f m = true ∧ f (m+1) = false := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases hm : f k with
      | true => exact ⟨k,by omega,by omega,hm,hk⟩
      | false =>
          have hjk' : j < k := by
            by_contra h
            have : j = k := by omega
            subst j
            simp [hm] at hj
          obtain ⟨m,hmj,hmk,hmt,hmf⟩ := ih hjk' hm
          exact ⟨m,hmj,by omega,hmt,hmf⟩

theorem fin_bool_boundary {n : ℕ} (f : Fin n → Bool) (j k : Fin n)
    (hjk : j < k) (hj : f j = true) (hk : f k = false) :
    ∃ m : Fin n, j ≤ m ∧ m < k ∧ f m = true ∧ f (next m) = false := by
  let ff : ℕ → Bool := fun a => if h : a < n then f ⟨a,h⟩ else false
  have hj' : ff j.val = true := by simpa [ff] using hj
  have hk' : ff k.val = false := by simpa [ff] using hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := bool_boundary ff j.val k.val hjk hj' hk'
  have hmn : m < n := hmk.trans k.isLt
  have hmn' : m+1 < n := lt_of_le_of_lt hmk k.isLt
  refine ⟨⟨m,hmn⟩,hmj,hmk,?_,?_⟩
  · simpa [ff,hmn] using hmt
  · simpa [ff,hmn',next] using hmf

variable {n : ℕ} {I : Type} [Fintype I]











end ThreeBoundNumeric





end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile
variable {n : ℕ} {I : Type} [Fintype I]

theorem solution (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k l : Fin n)
    (hij : i ≤ j) (hjk : j < k) (hkl : k ≤ l) :
    DBound F i j k l ((unionExpr n i.val j.val k.val l.val).eval v) := by
  intro x hj hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) j k hjk hj hk
  have hm := hv (.d i m l) (hij.trans hmj) (hmk.trans_le hkl) x hmt hmf
  apply hm.trans
  simp only [unionExpr, if_pos
    (show i.val ≤ j.val ∧ j.val < k.val ∧ k.val ≤ l.val from ⟨hij,hjk,hkl⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmj,hmk⟩,?_⟩
  simp only [Function.comp_apply,dExpr,dif_pos i.isLt,dif_pos m.isLt,dif_pos l.isLt,Expr.eval]
end
