-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.measurable_PsiF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:43.405211+00:00
-- url     : https://prove2.me/submissions/109d5049-e964-40a4-99ff-8407bc777148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_continuous_tW

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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) (s : ℝ) :
    Measurable (PsiF p q s) := by
  have h1 : Measurable fun x : ι → ℂ => (1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ) := by
    first
    | exact measurable_const.sub (((continuous_star.comp (continuous_apply p)).measurable).div
        (Complex.continuous_ofReal.comp (continuous_tW q)).measurable)
    | fun_prop
  show Measurable fun x : ι → ℂ => (‖(1 : ℂ) - star (x p) / ((tW q x : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ (-s)
  exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp h1)).pow_const _
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
