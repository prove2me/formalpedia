-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.tmap_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:19.502819+00:00
-- url     : https://prove2.me/submissions/066f4305-1523-4854-b24f-7cf5601d0710

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
import Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tmap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}
namespace PositivityTheory.Rg.Cz.CGlue
theorem _root_.solution (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) (lam : M →ₗ[ℂ] ℂ)
    (h : Jh *ᵥ (fun I => lam (f I)) ≠ 0) : tmap Jh f ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg (fun x => TensorProduct.lid ℂ (Fin d → ℂ) (lam.rTensor _ x)) h0
  simp only [tmap_apply, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h1
  funext m
  have h2 := congrFun h1 m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _
end PositivityTheory.Rg.Cz.CGlue
