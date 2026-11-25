-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:12.104691+00:00
-- url     : https://prove2.me/submissions/8a14896a-7536-4924-a96a-6b304e70f60b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialPieceRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
  refine ⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [map_residue_weightedHomogeneousComponent]
    exact weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)
end GroundTheory.Heights₂.Heights.NumbersDVR
