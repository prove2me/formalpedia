-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.ofReal_fsR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:06.620379+00:00
-- url     : https://prove2.me/submissions/daa530ed-fdba-4df3-80c6-928204cc2ee1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_iic_eq

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
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
