-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.finite_support_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:00.509+00:00
-- url     : https://prove2.me/submissions/2881b289-57f8-45fc-b9d1-816f28f5fecf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_TraceMulOfFinrankOne
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open scoped Pointwise
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution (K : Subgroup G) (hK : IsOpen (K : Set G)) {M : Type} [Zero M] [TopologicalSpace M]
    (f : G → M) (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover (fun x : tsupport f => (x : G) • (K : Set G))
    (fun x => hK.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K.one_mem, mul_one x⟩⟩)
  refine (s.finite_toSet.image (fun i : tsupport f => ((i : G) : G ⧸ K))).subset ?_
  intro q hq
  have hx : q.out ∈ tsupport f := subset_tsupport _ hq
  have h2 := hs hx
  simp only [Set.mem_iUnion] at h2
  obtain ⟨i, hi, k, hk, hik⟩ := h2
  refine ⟨i, hi, ?_⟩
  show ((i : G) : G ⧸ K) = q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [← hik]
  exact (QuotientGroup.mk_mul_of_mem (i : G) hk).symm
end PositivityTheory.Rg.BcB.F.EigA
