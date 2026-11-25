-- Prove2me | solution 1 for PI.FinOrdValD.WA.weakApprox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:50.396896+00:00
-- url     : https://prove2.me/submissions/7ff32d15-f89d-42bf-9da3-d5926d7872af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
import Theorems.Thm_PI_FinOrdValD_WA_val_alg
import Theorems.Thm_PI_FinOrdValD_WA_exists_pow_lt
import Theorems.Thm_PI_FinOrdValD_WA_val_nat_le_one
import Theorems.Thm_PI_FinOrdValD_WA_exists_nat_small
import Theorems.Thm_PI_FinOrdValD_WA_exists_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : (v : HeightOneSpectrum (𝓞 L)) → v.adicCompletion L)
    (γ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰) (hγ : ∀ v ∈ T, γ v ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ (∀ v ∈ T, Valued.v (algebraMap L (v.adicCompletion L) a - x v) < γ v) ∧
      ∀ σ : L →+* ℝ, 0 < σ a := by
  classical
  have hnear : ∀ w : T, ∃ b : L, Valued.v (algebraMap L (w.1.adicCompletion L) b - x w.1) < γ w.1 :=
    fun w => exists_near w.1 (x w.1) (hγ w.1 w.2)
  choose b hb using hnear
  obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 L))
    (S := L) (s := (Finset.univ : Finset T)) (f := b)
  have hr : ∀ w : T, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * b w := by
    intro w
    obtain ⟨r, hr⟩ := hdint w (Finset.mem_univ _)
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose r hr using hr
  set dL : L := algebraMap (𝓞 L) L d with hdL
  have hdL0 : dL ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hvd : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L dL ≠ 0 := fun w =>
    (Valuation.ne_zero_iff _).mpr hdL0
  let e : HeightOneSpectrum (𝓞 L) → ℕ := fun w =>
    if h : w ∈ T then Classical.choose (exists_pow_lt (mul_ne_zero (hγ w h) (hvd w))) else 0
  have he : ∀ w (h : w ∈ T), exp (-((e w : ℕ) : ℤ)) < γ w * w.valuation L dL := by
    intro w h
    simp only [e, dif_pos h]
    exact Classical.choose_spec (exists_pow_lt (mul_ne_zero (hγ w h) (hvd w)))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) e
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime)
    (fun w _ u _ hne h => hne (HeightOneSpectrum.ext h)) r
  set a0 : L := algebraMap (𝓞 L) L y / dL with ha0
  have hclose : ∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) a0 - x w) < γ w := by
    intro w hw
    have hmem := hy w hw
    have hval : w.valuation L (algebraMap (𝓞 L) L (y - r ⟨w, hw⟩)) ≤ exp (-((e w : ℕ) : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      first
      | exact (w.intValuation_le_pow_iff_mem _ _).mpr hmem
      | exact (w.intValuation_le_pow_iff_dvd _ _).mpr (Ideal.dvd_span_singleton.mpr hmem)
    have hnum : algebraMap (𝓞 L) L (y - r ⟨w, hw⟩) = (a0 - b ⟨w, hw⟩) * dL := by
      rw [map_sub, hr, ha0, sub_mul, div_mul_cancel₀ _ hdL0, mul_comm dL]
    rw [hnum, Valuation.map_mul] at hval
    have h1 : w.valuation L (a0 - b ⟨w, hw⟩) < γ w := by
      by_contra hle
      push_neg at hle
      exact absurd (lt_of_le_of_lt hval (he w hw)) (not_lt.mpr (mul_le_mul_of_nonneg_right hle zero_le'))
    have hsplit : algebraMap L (w.adicCompletion L) a0 - x w =
        algebraMap L (w.adicCompletion L) (a0 - b ⟨w, hw⟩) +
          (algebraMap L (w.adicCompletion L) (b ⟨w, hw⟩) - x w) := by
      rw [map_sub]; ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (by rw [val_alg]; exact h1) (hb ⟨w, hw⟩)
  obtain ⟨N, hN, hNs⟩ := exists_nat_small T γ hγ
  haveI : Finite (L →+* ℝ) := Finite.of_injective (fun σ : L →+* ℝ => Complex.ofRealHom.comp σ)
    (fun σ τ h => RingHom.ext fun z => Complex.ofReal_injective (RingHom.congr_fun h z))
  obtain ⟨B, hB⟩ := (Set.finite_range (fun σ : L →+* ℝ => |σ a0|)).bddAbove
  obtain ⟨t, ht⟩ := exists_nat_gt B
  have good : ∀ s : ℕ, B < s → (∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L)
      (a0 + (N : L) * (s : L)) - x w) < γ w) ∧ ∀ σ : L →+* ℝ, 0 < σ (a0 + (N : L) * (s : L)) := by
    intro s hs
    refine ⟨fun w hw => ?_, fun σ => ?_⟩
    · have hsplit : algebraMap L (w.adicCompletion L) (a0 + (N : L) * (s : L)) - x w =
          (algebraMap L (w.adicCompletion L) a0 - x w) +
            algebraMap L (w.adicCompletion L) ((N : L) * (s : L)) := by
        rw [map_add]; ring
      rw [hsplit]
      refine Valuation.map_add_lt _ (hclose w hw) ?_
      rw [val_alg, Valuation.map_mul]
      calc w.valuation L (N : L) * w.valuation L (s : L) ≤ w.valuation L (N : L) * 1 :=
            mul_le_mul_of_nonneg_left (val_nat_le_one w s) zero_le'
        _ = w.valuation L (N : L) := mul_one _
        _ < γ w := hNs w hw
    · have h1 : |σ a0| ≤ B := hB ⟨σ, rfl⟩
      have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      rw [map_add, map_mul, map_natCast, map_natCast]
      nlinarith [neg_abs_le (σ a0), mul_nonneg (sub_nonneg.mpr hN1) hs0]
  by_cases h0 : a0 + (N : L) * (t : L) = 0
  · have ht1 : B < ((t + 1 : ℕ) : ℝ) := by push_cast; linarith
    refine ⟨a0 + (N : L) * ((t + 1 : ℕ) : L), ?_, (good (t + 1) ht1).1, (good (t + 1) ht1).2⟩
    intro h1
    have hN0 : (N : L) = 0 := by push_cast at h1; linear_combination h1 - h0
    exact hN.ne' (by exact_mod_cast hN0)
  · exact ⟨a0 + (N : L) * (t : L), h0, (good t ht).1, (good t ht).2⟩
end PI.FinOrdValD.WA
