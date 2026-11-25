-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplBoxVolume_set_eq_preimage_c34e58dd3381
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:46.590672+00:00
-- url     : https://prove2.me/submissions/133aa714-64fe-4684-b461-699325c6baa0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplBoxVolume

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplBoxVolume
namespace GroundTheory.Heights₂.Heights.PSymplBoxVolume
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]
end GroundTheory.Heights₂.Heights.PSymplBoxVolume
