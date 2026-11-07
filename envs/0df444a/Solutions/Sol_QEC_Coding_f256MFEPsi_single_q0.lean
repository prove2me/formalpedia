-- Prove2me | solution 1 for QEC.Coding.f256MFEPsi_single_q0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:11.060936+00:00
-- url     : https://prove2.me/submissions/87f3e9e1-fe1e-4311-90af-0db7c889400a

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256MFEPsi_apply
import Theorems.Thm_QEC_Coding_f256PolynomialBasis_apply

section
namespace QEC.Coding
private theorem f256SelectorQ0_eq_index_iff (i j k : Fin 8) :
    f256SelectorQ0 = f256MFEIndex i j k ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h
    have hindex : (0, (0, 0)) = (i, (j, k)) := f256MFEIndexEquiv.injective (by
      simpa [f256SelectorQ0, f256MFEIndex] using h)
    have hi : (0 : Fin 8) = i := congrArg Prod.fst hindex
    have hjk : (0, 0) = (j, k) := congrArg Prod.snd hindex
    have hj : (0 : Fin 8) = j := congrArg Prod.fst hjk
    have hk : (0 : Fin 8) = k := congrArg Prod.snd hjk
    exact ⟨hi.symm, hj.symm, hk.symm⟩
  · rintro ⟨hi, hj, hk⟩
    subst i
    subst j
    subst k
    rfl
private theorem f256MFEIndex_eq_selectorQ0_iff (i j k : Fin 8) :
    f256MFEIndex i j k = f256SelectorQ0 ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h
    exact (f256SelectorQ0_eq_index_iff i j k).mp h.symm
  · intro h
    exact ((f256SelectorQ0_eq_index_iff i j k).mpr h).symm
end QEC.Coding
end

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f256MFEPsi (Pi.single f256SelectorQ0 1) = 1 := by
  rw [f256MFEPsi_apply]
  classical
  simp [Pi.single_apply, f256MFEIndex_eq_selectorQ0_iff, f256PolynomialBasis_apply]
  rw [Fintype.sum_eq_single (0 : Fin 8)]
  · rw [Fintype.sum_eq_single (0 : Fin 8)]
    · rw [Fintype.sum_eq_single (0 : Fin 8)]
      · simp
      · intro k hk
        simp [hk]
    · intro j hj
      simp [hj]
  · intro i hi
    simp [hi]
end QEC.Coding
