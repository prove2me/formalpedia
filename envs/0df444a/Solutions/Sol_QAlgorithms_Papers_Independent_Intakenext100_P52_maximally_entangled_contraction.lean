-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.maximally_entangled_contraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:38:05.021101+00:00
-- url     : https://prove2.me/submissions/da260964-2f0a-4a0e-92e9-6a5aad89c5a7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 in
theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (alpha : Vec I) (halpha : IsState alpha) :
    teleportContraction alpha (finiteMaxEntangled I) (finiteMaxEntangled I) =
      ((Fintype.card I : ℂ)⁻¹) • alpha := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ((Real.sqrt (Fintype.card I))⁻¹ : ℂ) := ⟨_, rfl⟩
  have key : conj s * s = ((Fintype.card I : ℂ)⁻¹) := by
    rw [hs]
    simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  have hφ : ∀ i j : I, (finiteMaxEntangled I) (i, j) = if i = j then s else 0 := by
    intro i j; rw [hs]; rfl
  ext k
  simp only [teleportContraction, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, hφ,
    apply_ite (starRingEnd ℂ), map_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← key]
  ring

end
