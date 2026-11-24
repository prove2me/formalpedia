-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:45.966243+00:00
-- url     : https://prove2.me/submissions/cb47083b-76bd-4ad3-826e-34809a2338f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec

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
theorem _root_.solution (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by
  unfold FsE
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [h l, ENNReal.coe_mul, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
