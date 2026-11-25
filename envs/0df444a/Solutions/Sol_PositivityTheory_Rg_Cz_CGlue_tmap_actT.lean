-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CGlue.tmap_actT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:14.782722+00:00
-- url     : https://prove2.me/submissions/f56fad47-350e-45ba-895f-4c8d2160ae3f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
import Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tmap_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_actT_apply

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
theorem _root_.solution {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (Jh : Matrix (Fin d) (P → Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ)
    (h : Jh * Matrix.of (fun I J : P → Fin n => ∏ p, κ (lab p) γ (I p) (J p)) = B * Jh) (f : TV n M P) :
    tmap Jh (actT lab κ ρ γ f) = TensorProduct.map (ρ γ) (Matrix.toLin' B) (tmap Jh f) := by
  rw [tmap_apply, tmap_apply, map_sum]
  simp only [actT_apply, TensorProduct.sum_tmul, TensorProduct.smul_tmul, TensorProduct.map_tmul, Matrix.toLin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← TensorProduct.tmul_sum]
  congr 1
  funext m
  have := congrFun (congrFun h m) J
  simp only [Matrix.mul_apply, Matrix.of_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ← this]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _
end PositivityTheory.Rg.Cz.CGlue
