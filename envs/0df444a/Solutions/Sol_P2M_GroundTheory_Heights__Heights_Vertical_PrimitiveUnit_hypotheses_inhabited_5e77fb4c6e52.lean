-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_PrimitiveUnit_hypotheses_inhabited_5e77fb4c6e52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:40.637588+00:00
-- url     : https://prove2.me/submissions/93fdd64b-1fa5-4ea4-a6bd-9ec3f17027df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace PrimitiveUnit
theorem _root_.solution :
    (∃ m, IsUnit ((1 : MvPolynomial (Fin 1) ℤ_[2]).coeff m)) ∧
      (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) =
        C (1 : ℚ_[2]) * (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) :=
  ⟨⟨0, by simp⟩, by simp⟩
end PrimitiveUnit
end GroundTheory.Heights₂.Heights.Vertical
