-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_le_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:33:18.250196+00:00
-- url     : https://prove2.me/submissions/1fd0dfbe-eccd-4934-8ce9-35eed5bd843e

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) :
    twoThirdsSeparationProfile G scale ≤ scale := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.mp hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hcard := (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices
  exact (minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card G vertices).trans hcard.2
end QEC.Locality
