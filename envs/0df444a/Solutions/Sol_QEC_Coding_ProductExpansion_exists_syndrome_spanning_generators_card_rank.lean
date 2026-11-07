-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_syndrome_spanning_generators_card_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:34:05.9601+00:00
-- url     : https://prove2.me/submissions/45b00aa9-046f-4146-b5af-973bec6c9153

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) := by
  classical
  let M : Matrix R' W F := h' * x
  let V : Submodule F (R' → F) := LinearMap.range M.mulVecLin
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let preimage (i : Fin (Module.finrank F V)) : Word F W :=
    Classical.choose (b i).2
  have hPreimage (i : Fin (Module.finrank F V)) :
      M.mulVec (preimage i) = (b i).1 := by
    exact Classical.choose_spec (b i).2
  let representative (i : Fin (Module.finrank F V)) : Word F W :=
    x.mulVec (preimage i)
  have hRepresentative (i : Fin (Module.finrank F V)) :
      h'.mulVec (representative i) = (b i).1 := by
    simpa [M, representative, Matrix.mulVec_mulVec] using hPreimage i
  have hRepresentativeInjective : Function.Injective representative := by
    intro i j hij
    apply b.injective
    apply Subtype.ext
    calc
      (b i).1 = h'.mulVec (representative i) := (hRepresentative i).symm
      _ = h'.mulVec (representative j) := by rw [hij]
      _ = (b j).1 := hRepresentative j
  let C : Finset (Word F W) := Finset.univ.image representative
  have hCard : C.card = M.rank := by
    simp [C, Finset.card_image_of_injective _ hRepresentativeInjective,
      M, Matrix.rank, V]
  have hBasisInSpan (i : Fin (Module.finrank F V)) :
      ((b i).1 : R' → F) ∈ syndromeSpan h' C := by
    apply Submodule.subset_span
    refine ⟨representative i, ?_, hRepresentative i⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hBasisSpan : Submodule.span F (Set.range b) ≤
      (syndromeSpan h' C).comap V.subtype := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    exact hBasisInSpan i
  refine ⟨C, ?_, ?_⟩
  · simpa [M] using hCard
  · intro j
    have hColumnRange : h'.mulVec (column x j) ∈ V := by
      change h'.mulVec (column x j) ∈ LinearMap.range M.mulVecLin
      refine ⟨Pi.single j (1 : F), ?_⟩
      change M.mulVec (Pi.single j (1 : F)) = h'.mulVec (column x j)
      rw [Matrix.mulVec_single_one]
      ext i
      simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct, column]
    let v : V := ⟨h'.mulVec (column x j), hColumnRange⟩
    exact hBasisSpan (b.mem_span v)
end QEC.Coding.ProductExpansion
