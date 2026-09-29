-- Prove2me | solution 1 for ResidualGaloisRep.det_complexConjugation_eq_neg_one_of_detIsCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4669a5de-3342-5356-8f66-a2cff72d0a9a

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic

set_option autoImplicit false

open Polynomial

noncomputable section

namespace P2mCCDet

abbrev Qb := AlgebraicClosure ℚ

lemma complexConjugation_apply_eq_inv_of_pow_eq_one {μ : Qb} {N : ℕ} (hN : N ≠ 0)
    (hμ : μ ^ N = 1) : complexConjugation μ = μ⁻¹ := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hμ
    exact zero_ne_one hμ
  apply (complexEmbedding : Qb →ₐ[ℚ] ℂ).toRingHom.injective
  change complexEmbedding (complexConjugation μ) = complexEmbedding μ⁻¹
  rw [complexEmbedding_complexConjugation, map_inv₀]
  set z : ℂ := complexEmbedding μ with hz
  have hzN : z ^ N = 1 := by rw [hz, ← map_pow, hμ, map_one]
  have habs : ‖z‖ = 1 := by
    have h := congrArg (‖·‖) hzN
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hN).mp h
  exact (Complex.inv_eq_conj habs).symm

theorem det_complexConjugation_eq_neg_one {k : Type} [Field k] (p : ℕ) [Fact p.Prime]
    (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) :
    LinearMap.det (ρbar.ρ complexConjugation) = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hpk, hcyc⟩ := hdet

  have hp0 : (p : k) = 0 := by
    rw [IsLocalRing.maximalIdeal_eq_bot] at hpk
    simpa using hpk

  have hact : ∀ μ : Qb, μ ^ p ^ 1 = 1 → complexConjugation μ = μ ^ (p - 1) := by
    intro μ hμ
    rw [pow_one] at hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hμ
      exact zero_ne_one hμ
    rw [complexConjugation_apply_eq_inv_of_pow_eq_one hp.ne_zero hμ]
    have : μ ^ (p - 1) * μ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hμ]
    exact (eq_inv_of_mul_eq_one_left this).symm
  have h := hcyc 1 complexConjugation (p - 1) hact
  rw [pow_one, hp0, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at h
  change LinearMap.det (ρbar.ρ complexConjugation) = ((p - 1 : ℕ) : k) at h
  rw [h, Nat.cast_sub hp.one_le, hp0, Nat.cast_one, zero_sub]

end P2mCCDet

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p) :
    LinearMap.det (ρbar.ρ complexConjugation) = -1 :=
  P2mCCDet.det_complexConjugation_eq_neg_one p ρbar hdet

end

end S_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic
end P2MW
export P2MW.S_ResidualGaloisRep_det_complexConjugation_eq_neg_one_of_detIsCyclotomic (solution)
