-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.dl_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:42.505807+00:00
-- url     : https://prove2.me/submissions/c1761eac-09d5-4e4a-b799-0aec875fc96f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_sub_tri_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_tri_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_dl_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_pm_left

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
theorem _root_.solution {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (x⁻¹ * g)‖₊ = cl τ l * ‖Dl k r l (κ⁻¹ * g)‖₊ := by
  rw [dl_eq, dl_eq, pm_left hx hκ τ hY, sub_tri_mul _ _ _ hτ, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul,
    nnnorm_star, nnnorm_prod]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
