-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.pm_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:55.127208+00:00
-- url     : https://prove2.me/submissions/7f2e6c0d-a417-45d3-a3f5-f851f1023c4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_sum_r
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_inv

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
    (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (x⁻¹ * g) = τᴴ * Pm k r (κ⁻¹ * g) := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [herm_inv hx, hY a, herm_sum_r]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [herm_inv hκ]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
