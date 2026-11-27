-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_proof_83b10cf83e4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:19.884358+00:00
-- url     : https://prove2.me/submissions/a662e25e-983d-4a48-bacb-df3948900f8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceBundleRadicalAway
theorem _root_.solution : SliceBundleRadicalAway.Statement := by
  intro n d J q hJ k f hf
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  obtain ⟨m, hm⟩ := hf
  have h0 : SliceBundleRadicalAway.solveMap J d q k f = 0 := by
    apply IsNilpotent.eq_zero
    exact ⟨m, by rw [← map_pow]; exact SliceBundleRadicalAway.le_ker_solveMap J d q k hm⟩
  have h1 : SliceBundleRadicalAway.toTot J d q k f = 0 := by
    rw [← SliceBundleRadicalAway.backMap_comp_solveMap J d q k, RingHom.comp_apply, h0, map_zero]
  rw [SliceBundleRadicalAway.toTot_apply] at h1
  obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (SliceBundleRadicalAway.uQuo J d q k)) (SliceBundleRadicalAway.Tot J d q k) _).1 h1
  refine ⟨e, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
  exact he
end SliceBundleRadicalAway
end GroundTheory.Heights₂.Heights
