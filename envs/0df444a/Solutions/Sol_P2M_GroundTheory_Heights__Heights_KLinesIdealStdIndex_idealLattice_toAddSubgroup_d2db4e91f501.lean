-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:53.883657+00:00
-- url     : https://prove2.me/submissions/6cfa14b3-e7a7-4cd2-8a97-bcdf0b2c238a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealStdIndex

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
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealStdIndex
namespace GroundTheory.Heights₂.Heights.KLinesIdealStdIndex
theorem _root_.solution {K : Type} [Field K] {k : ℕ}
    (a : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).toAddSubgroup =
      AddSubgroup.pi Set.univ fun j => (a j : Submodule (𝓞 K) K).toAddSubgroup := by
  ext x
  simp [idealLattice, Submodule.mem_pi, AddSubgroup.mem_pi]
end GroundTheory.Heights₂.Heights.KLinesIdealStdIndex
