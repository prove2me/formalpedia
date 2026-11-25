-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_mem_of_dvd_mem_67dc305db825
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:45.270822+00:00
-- url     : https://prove2.me/submissions/f401adba-3a7c-4bb4-843f-638881c9c455

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPrimeOpensCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry TopologicalSpace
open GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
namespace GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
theorem _root_.solution {P : Ideal ℤ} {a b : ℤ} (h : a ∣ b) (ha : a ∈ P) : b ∈ P := by
  obtain ⟨c, rfl⟩ := h
  exact P.mul_mem_right c ha
end GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
