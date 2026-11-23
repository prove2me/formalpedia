-- Prove2me | solution 1 for PI.FinOrdValD.WA.exists_nat_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:43.712804+00:00
-- url     : https://prove2.me/submissions/29220b33-9165-4fa5-bc27-9a3baafaf368

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
import Theorems.Thm_PI_FinOrdValD_WA_exists_pow_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
namespace PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
private lemma pow_le_exp_neg_of_lt_one (x : ℤᵐ⁰) (hx : x < 1) (n : ℕ) : x ^ n ≤ exp (-(n : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | h0
  · rcases n with _ | n
    · simp
    · simp [zero_pow (Nat.succ_ne_zero n)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, exp k = x := ⟨log x, exp_log h0⟩
    have hk : k ≤ -1 := by
      have : k < 0 := by rwa [← exp_zero, exp_lt_exp] at hx
      omega
    rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]
    nlinarith [(Int.natCast_nonneg n : (0 : ℤ) ≤ n)]
end PI.FinOrdValD.WA
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 L))) (δ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰)
    (hδ : ∀ v ∈ T, δ v ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ T, v.valuation L (N : L) < δ v := by
  classical
  have hpos : ∀ w : HeightOneSpectrum (𝓞 L), 0 < Ideal.absNorm w.asIdeal := fun w =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
  set M : ℕ := ∏ w ∈ T, Ideal.absNorm w.asIdeal with hM
  have hM0 : 0 < M := Finset.prod_pos fun w _ => hpos w
  have hMv : ∀ w ∈ T, w.valuation L (M : L) < 1 := by
    intro w hw
    have hmem : ((M : ℕ) : 𝓞 L) ∈ w.asIdeal := by
      obtain ⟨c, hc⟩ : Ideal.absNorm w.asIdeal ∣ M := Finset.dvd_prod_of_mem _ hw
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have := (w.valuation_lt_one_iff_mem (K := L) _).mpr hmem
    simpa using this
  let n : HeightOneSpectrum (𝓞 L) → ℕ := fun w =>
    if h : δ w ≠ 0 then Classical.choose (exists_pow_lt h) else 0
  refine ⟨M ^ (∑ w ∈ T, n w), pow_pos hM0 _, fun w hw => ?_⟩
  have hn : exp (-((n w : ℕ) : ℤ)) < δ w := by
    simp only [n, dif_pos (hδ w hw)]
    exact Classical.choose_spec (exists_pow_lt (hδ w hw))
  have hle : n w ≤ ∑ u ∈ T, n u := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
  calc w.valuation L ((M ^ (∑ u ∈ T, n u) : ℕ) : L)
        = (w.valuation L (M : L)) ^ (∑ u ∈ T, n u) := by rw [Nat.cast_pow, map_pow]
    _ ≤ exp (-((∑ u ∈ T, n u : ℕ) : ℤ)) := pow_le_exp_neg_of_lt_one _ (hMv w hw) _
    _ ≤ exp (-((n w : ℕ) : ℤ)) := by rw [exp_le_exp]; omega
    _ < δ w := hn
end PI.FinOrdValD.WA
