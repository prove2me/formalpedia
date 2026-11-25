-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_not_mem_of_isCoprime_27a59e8a7789
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:58.930768+00:00
-- url     : https://prove2.me/submissions/31f78928-dd08-444c-b781-625b533201ef

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
theorem _root_.solution {P : Ideal ℤ} (hP : P ≠ ⊤) {a b : ℤ} (h : IsCoprime a b)
    (ha : a ∈ P) : b ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ := h
  exact hP ((Ideal.eq_top_iff_one P).mpr (huv ▸ P.add_mem (P.mul_mem_left u ha) (P.mul_mem_left v hb)))
end GroundTheory.Heights₂.Heights.Model.PrimeOpensCover
