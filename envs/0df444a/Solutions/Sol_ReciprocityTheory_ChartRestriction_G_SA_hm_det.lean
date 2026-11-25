-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:55.026233+00:00
-- url     : https://prove2.me/submissions/dbbd9f9d-b354-4475-a109-e6cacacf4867

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) K) : (hm σ J e f M).det = M.det := by
  have hfd : ∀ x y : ι → K, ∑ i, (J *ᵥ (σ ∘ y)) i * x i = hf σ J x y := by
    intro x y
    simp only [hf, Matrix.mulVec, dotProduct, Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hfe : hf σ J f e = 1 := hf_fe hσ hJ he hff hef
  set U : Matrix ι (Fin 2) K := Matrix.of fun i a => ![e i, f i] a with hU
  set V : Matrix (Fin 2) ι K := Matrix.of ![J *ᵥ (σ ∘ f), J *ᵥ (σ ∘ e)] with hV
  have hVU : V * U = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hV, hU, Matrix.mul_apply, hfd, he, hff, hef, hfe]
  have hform : hm σ J e f M = 1 + U * (M - 1) * V := by
    ext i j
    simp [hm, hU, hV, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply, Matrix.sub_apply,
      Matrix.one_apply]
    ring
  rw [hform, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hVU, Matrix.one_mul,
    add_sub_cancel]
end ReciprocityTheory.ChartRestriction.G.SA
