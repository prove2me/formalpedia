-- Prove2me | solution 2 for QEC.Coding.f256MFEPsi_single_q0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:49:27.161082+00:00
-- url     : https://prove2.me/submissions/055026b1-7235-47cd-8f57-77bac21e8e98

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
set_option autoImplicit false
open QEC QEC.Coding

private theorem f256MFEPsi_apply (v : Fin 512 → ZMod 2) :
    f256MFEPsi v =
      ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        v (f256MFEIndex i j k) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k) := rfl

private theorem f256PolynomialBasis_apply (i : Fin 8) :
    f256PolynomialBasis i = f256Alpha ^ (i : ℕ) := by
  rw [f256PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f256Modulus_monic).basis_eq_pow]
  rfl

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

theorem solution :
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
