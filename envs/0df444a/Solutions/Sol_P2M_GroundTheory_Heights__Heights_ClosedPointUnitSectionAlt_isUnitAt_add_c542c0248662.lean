-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:24.685363+00:00
-- url     : https://prove2.me/submissions/531df87f-becf-4549-91e8-17e726c4f1ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_iff_3571b1996383

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {g h : K'} (hg : IsUnitAt y P d g) (hh : ¬IsUnitAt y P d h) : IsUnitAt y P d (g + h) := by
  obtain ⟨t, -, ht⟩ := exists_max y hy P
  rw [isUnitAt_iff y ht] at hg hh ⊢
  rw [not_le] at hh
  rwa [Valuation.map_add_eq_of_lt_left _ (hh.trans_le hg)]
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
