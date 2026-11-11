-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.corners_membership
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:48:07.927609+00:00
-- url     : https://prove2.me/submissions/623c5eef-a9df-4ca6-8a3e-c306e5052929

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace N
export BDL26NativePresentationGenerator (Code FaceRow Frame)
end N
open N
noncomputable section
open scoped Classical
private theorem index_eq_decode (S : OddScale) (n : ℕ) (a : Index S n)
    (v : Vertex (P S n)) :
    a=BDL26NativePresentationGenerator.generatedVertexIndex S n v ↔
      BDL26NativeStateRows.decode S n a=v := by
  constructor
  · intro h; rw [h]; exact Equiv.symm_apply_apply _ _
  · intro h
    exact (Equiv.apply_symm_apply (BDL26NativePresentationGenerator.generatedVertexIndex S n) a).symm.trans
      (congrArg (BDL26NativePresentationGenerator.generatedVertexIndex S n) h)
end
end QEC.Coding.BDL26NativeSupportMetadata
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeSupportMetadata
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (a : Index S n) :
    a∈tripleList (corners S n t) ↔
      BDL26NativeStateRows.decode S n a∈triangleSupport (P S n) t := by
  change a∈[(BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 0),
      (BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 1),
      (BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 2)] ↔
    BDL26NativeStateRows.decode S n a∈Finset.univ.image (triangleVertex (P S n) t)
  constructor
  · intro ha
    rcases List.mem_cons.mp ha with h0|ha
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,((index_eq_decode S n a _).mp h0).symm⟩
    rcases List.mem_cons.mp ha with h1|ha
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,((index_eq_decode S n a _).mp h1).symm⟩
    rcases List.mem_cons.mp ha with h2|ha
    · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,((index_eq_decode S n a _).mp h2).symm⟩
    · cases ha
  · intro ha
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    have he := (index_eq_decode S n a (triangleVertex (P S n) t i)).mpr hi.symm
    fin_cases i
    · exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))))
end QEC.Coding.BDL26NativeSupportMetadata
