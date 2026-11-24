-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealSurj_proof_5a2bf0b15861
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:22.72994+00:00
-- url     : https://prove2.me/submissions/72eb7070-8f32-4d41-be35-3a57833ce9ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealSurj

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpecialIdealSurj
theorem _root_.solution : SpecialIdealSurj.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ V hV
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hπ : Function.Surjective π :=
    MvPolynomial.map_surjective _ (IsLocalRing.residue_surjective)
  refine ⟨V.comap π, Ideal.comap_isPrime π V, ?_, ?_⟩
  · have h0 : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).2
        ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
    rw [Ideal.mem_comap]
    have : π (C ϖ) = 0 := by
      simp only [π, MvPolynomial.map_C, h0, map_zero]
    rw [this]
    exact V.zero_mem
  · exact Ideal.map_comap_of_surjective π hπ V
end SpecialIdealSurj
end GroundTheory.Heights₂.Heights.NumbersDVR
