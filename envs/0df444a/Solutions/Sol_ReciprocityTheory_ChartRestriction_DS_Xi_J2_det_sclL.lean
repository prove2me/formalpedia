-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.det_sclL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:19.679837+00:00
-- url     : https://prove2.me/submissions/45db9a5f-89e1-4650-9f04-9caef7cb51af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) (t : ℝ) : LinearMap.det (sclL p m t) = t ^ (4 * p + 2 * m + 2) := by
  unfold sclL
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_prodMap]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
