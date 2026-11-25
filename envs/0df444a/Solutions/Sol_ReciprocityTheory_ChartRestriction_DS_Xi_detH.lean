-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.detH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:10:14.070911+00:00
-- url     : https://prove2.me/submissions/a4344161-fd83-4ed9-bd62-6f4c1533f44b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_fac_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 DetB
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) : DET := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -⟩ := hB2
  intro k r s A _ hs hA
  refine ⟨∏ l, Real.toNNReal (cl k r l ^ s l), fun h hh => ?_⟩
  have hM : 1 ≤ gN h := hGN k r h hh
  have hM0 : 0 < gN h := by linarith
  calc ENNReal.ofReal (gN h ^ (-A))
        ≤ ENNReal.ofReal (gN h ^ (-∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hM (neg_le_neg hA))
    _ = ∏ l : Fin (r + 1), ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s l))) := by
        rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hM0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg hM0.le _)]
    _ ≤ ∏ l : Fin (r + 1), (ENNReal.ofReal (cl k r l ^ s l) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s l)) :=
        Finset.prod_le_prod' fun l _ => fac_le k r l (s l) (hs l) h hM
    _ = _ := by
        rw [Finset.prod_mul_distrib, FsE, ENNReal.ofNNReal_finsetProd]; rfl
end ReciprocityTheory.ChartRestriction.DS.Xi
