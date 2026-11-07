-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.codeword_eq_zero_of_vanish_on_large_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:29:05.788443+00:00
-- url     : https://prove2.me/submissions/b4457f5b-eb7b-40ed-a98c-d9e95bb34b1b

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hVanish : ∀ i ∈ A, c i = 0) : c = 0 := by
  classical
  by_contra hnonzero
  have hSupport : hammingSupport c ⊆ Finset.univ \ A := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hiA
    have hci : c i ≠ 0 := by simpa [hammingSupport] using hi
    exact hci (hVanish i hiA)
  have hCard := Finset.card_le_card hSupport
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  rw [hComplement] at hCard
  have hd := hDistance c hc hnonzero
  unfold HammingWeight at hd
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  omega
end QEC.Coding.ProductExpansion
