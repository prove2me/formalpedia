-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.dl_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:58.314859+00:00
-- url     : https://prove2.me/submissions/5cb56c07-b5db-417d-818f-efe0a48db140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_sub_mul_tri
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_tri_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_dl_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_pm_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (g * y)‖₊ = cl τ l * ‖Dl k r l (g * κ)‖₊ := by
  rw [dl_eq, dl_eq, pm_right τ hY, sub_mul_tri _ _ _ hτ, Matrix.det_mul,
    Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul, nnnorm_prod, mul_comm]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
