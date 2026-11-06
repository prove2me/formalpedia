-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_lt_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:11:35.38596+00:00
-- url     : https://prove2.me/submissions/3965e026-0470-4113-b54f-0811aa429777

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {scale : Nat} (hscale : 2 ≤ scale) :
    twoThirdsSeparationProfile G scale < scale := by
  classical
  unfold twoThirdsSeparationProfile
  rw [Finset.max'_lt_iff]
  intro size hsize
  rcases Finset.mem_image.mp hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hcard := (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices
  by_cases hfull : vertices.card = scale
  · rw [← hfull]
    exact minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
      G vertices (by omega)
  · have hminimumLe :=
      minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card G vertices
    omega
end QEC.Locality
