-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_min_weight_syndrome_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:36:18.017413+00:00
-- url     : https://prove2.me/submissions/0e9dbccf-0b8e-4195-a019-b4e8679bcd44

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_syndrome_spanning_generators_card_rank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  classical
  let candidates : Finset (Finset (Word F W)) :=
    Finset.univ.filter (fun C =>
      C.card = (h' * x).rank ∧
      ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
  have hNonempty : candidates.Nonempty := by
    obtain ⟨C, hCard, hSpanning⟩ :=
      exists_syndrome_spanning_generators_card_rank h' x
    exact ⟨C, Finset.mem_filter.mpr
      ⟨Finset.mem_univ C, ⟨hCard, hSpanning⟩⟩⟩
  obtain ⟨C, hC, hMinimal⟩ :=
    Finset.exists_min_image candidates (generatorRestrictedWeight A) hNonempty
  have hCProperties := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCProperties.1, hCProperties.2, ?_⟩
  intro D hCard hSpanning
  exact hMinimal D (Finset.mem_filter.mpr
    ⟨Finset.mem_univ D, ⟨hCard, hSpanning⟩⟩)
end QEC.Coding.ProductExpansion
