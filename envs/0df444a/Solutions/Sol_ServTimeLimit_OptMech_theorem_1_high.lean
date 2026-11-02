-- Prove2me | solution 1 for ServTimeLimit.OptMech.theorem_1_high
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:10:39.436191+00:00
-- url     : https://prove2.me/submissions/316ea562-e11e-403a-9818-1f604eac2e5e

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace STLHigh
open MeasureTheory ServTimeLimit.OptMech

lemma intOn_of_alloc (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) (hA : IsAllocation P Φ t)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ θ ∈ Φ, |f θ| ≤ M) : IntegrableOn f Φ := by
  obtain ⟨hΦ, hsub, -, -, -⟩ := hA
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top)
  · rw [ae_restrict_iff' hΦ]
    exact Filter.Eventually.of_forall (fun θ h => by simpa [Real.norm_eq_abs] using hM θ h)

/-- The key inequality `x − c x²/(2u) ≤ (c+2)(1−s)²/2` (with `u = 1 − x`, `s² = c/(c+2)`). -/
lemma alg (Λ θ c L m M s : ℝ) (hΛ : 0 < Λ) (hθ : 0 < θ) (hc : 0 < c) (hL : 0 ≤ L)
    (hm : 0 ≤ m) (hCS : L ^ 2 ≤ m * M) (hstab : Λ * L < θ) (hs : 0 < s)
    (hs2 : s ^ 2 = c / (c + 2)) :
    Λ / θ * (L - m * (c * (Λ * M / (2 * (θ - Λ * L))))) ≤ (c + 2) * (1 - s) ^ 2 / 2 := by
  have hD : 0 < θ - Λ * L := by linarith
  have hK : 0 < c + 2 := by linarith
  have hKs : (c + 2) * s ^ 2 = c := by rw [hs2]; field_simp
  have step1 : c * Λ * L ^ 2 / (2 * (θ - Λ * L)) ≤ m * (c * (Λ * M / (2 * (θ - Λ * L)))) := by
    rw [show m * (c * (Λ * M / (2 * (θ - Λ * L)))) = c * Λ * (m * M) / (2 * (θ - Λ * L)) by
      ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hCS (by positivity)
  have step2 : Λ / θ * (L - c * Λ * L ^ 2 / (2 * (θ - Λ * L))) ≤ (c + 2) * (1 - s) ^ 2 / 2 := by
    set u := (θ - Λ * L) / θ with hu
    have hu0 : 0 < u := div_pos hD hθ
    have hx : Λ * L / θ = 1 - u := by rw [hu]; field_simp; ring
    have e : Λ / θ * (L - c * Λ * L ^ 2 / (2 * (θ - Λ * L)))
        = (1 - u) - c * (1 - u) ^ 2 / (2 * u) := by
      rw [← hx, hu]; field_simp
    rw [e, show (1 - u) - c * (1 - u) ^ 2 / (2 * u) = (2 * u * (1 - u) - c * (1 - u) ^ 2) / (2 * u)
      by field_simp, div_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) = (c + 2) * (1 - s ^ 2) := by nlinarith
    have : 0 ≤ (c + 2) * (u - s) ^ 2 := by positivity
    have e3 : c * (1 - u) ^ 2 = (c + 2) * s ^ 2 * (1 - u) ^ 2 := by rw [hKs]
    have : 2 * u * (1 - u) = (c + 2) * (1 - s ^ 2) * u * (1 - u) := by rw [← h2]
    nlinarith
  have hk : 0 ≤ Λ / θ := by positivity
  calc Λ / θ * (L - m * (c * (Λ * M / (2 * (θ - Λ * L)))))
      ≤ Λ / θ * (L - c * Λ * L ^ 2 / (2 * (θ - Λ * L))) := by
        apply mul_le_mul_of_nonneg_left _ hk; linarith
    _ ≤ _ := step2

/-- Every feasible allocation has welfare at most `fbValue`. -/
lemma welfare_le (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t : ℝ → ℝ)
    (hA : IsAllocation P Φ t) : welfare P Φ t ≤ fbValue P := by
  obtain ⟨hΛ, hc, hθ⟩ := hP
  have hA' := hA
  obtain ⟨hΦ, hsub, ht, hbd, hstab⟩ := hA
  have tb : ∀ θ ∈ Φ, |t θ| ≤ P.θbar := fun θ h => by
    rw [abs_le]; have := hbd θ h; have := (hsub h).2; constructor <;> linarith
  have t2b : ∀ θ ∈ Φ, |t θ ^ 2| ≤ P.θbar ^ 2 := fun θ h => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (tb θ h) 2
  have hIt : IntegrableOn t Φ := intOn_of_alloc P Φ t hA' t ht _ tb
  have hIt2 : IntegrableOn (fun θ => t θ ^ 2) Φ :=
    intOn_of_alloc P Φ t hA' _ (ht.pow_const 2) _ t2b
  have hIc : ∀ x : ℝ, IntegrableOn (fun _ : ℝ => x) Φ := fun x =>
    intOn_of_alloc P Φ t hA' _ measurable_const |x| (fun _ _ => le_rfl)
  set m := volume.real Φ with hm
  set L := load Φ t with hL
  set M := moment2 Φ t with hM
  have hL0 : 0 ≤ L := setIntegral_nonneg hΦ (fun θ h => (hbd θ h).1)
  have hM0 : 0 ≤ M := setIntegral_nonneg hΦ (fun θ _ => sq_nonneg _)
  have hm0 : 0 ≤ m := measureReal_nonneg
  -- quadratic in r
  have quad : ∀ r : ℝ, 0 ≤ M - 2 * r * L + r ^ 2 * m := by
    intro r
    have h0 : 0 ≤ ∫ θ in Φ, (t θ - r) ^ 2 := setIntegral_nonneg hΦ (fun θ _ => sq_nonneg _)
    have : ∫ θ in Φ, (t θ - r) ^ 2 = M - 2 * r * L + r ^ 2 * m := by
      have e : (fun θ => (t θ - r) ^ 2) = fun θ => (t θ ^ 2 - (2 * r) * t θ) + r ^ 2 := by
        funext θ; ring
      have i1 : IntegrableOn (fun θ => t θ ^ 2 - (2 * r) * t θ) Φ :=
        hIt2.sub (hIt.const_mul (2 * r))
      rw [e, integral_add i1 (hIc _),
        integral_sub hIt2 (hIt.const_mul (2 * r)), integral_const_mul, setIntegral_const]
      simp [hM, hL, hm, moment2, load, smul_eq_mul]; ring
    linarith
  have hCS : L ^ 2 ≤ m * M := by
    rcases eq_or_lt_of_le hm0 with h | h
    · have hL' : L = 0 := by
        by_contra hne
        have := quad ((M + 1) / (2 * L))
        rw [← h] at this
        have : 2 * ((M + 1) / (2 * L)) * L = M + 1 := by field_simp
        nlinarith
      rw [hL', ← h]; simp
    · have := quad (L / m)
      have e : M - 2 * (L / m) * L + (L / m) ^ 2 * m = (m * M - L ^ 2) / m := by
        field_simp; ring
      rw [e] at this
      have := (div_nonneg_iff.mp this)
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · linarith
      · linarith
  have hW : welfare P Φ t = P.Lam / P.θbar * (L - m * (P.c * (P.Lam * M / (2 * (P.θbar - P.Lam * L))))) := by
    unfold welfare
    rw [integral_sub hIt (hIc _), setIntegral_const]
    simp [waitTime, hL, hM, hm, smul_eq_mul, load, moment2]
  rw [hW]
  have hs : 0 < Real.sqrt (P.c / (P.c + 2)) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : Real.sqrt (P.c / (P.c + 2)) ^ 2 = P.c / (P.c + 2) := Real.sq_sqrt (by positivity)
  exact alg _ _ _ _ _ _ _ hΛ hθ hc hL0 hm0 hCS hstab hs hs2

end STLHigh

open MeasureTheory ServTimeLimit.OptMech in
theorem solution (P : Params) (hP : P.Standing) (hΛ : lam2 P ≤ P.Lam) :
    2 * Ttilde P ≤ P.θbar ∧
    IsFirstBest P (Set.Icc (Ttilde P) (2 * Ttilde P)) (fun _ => Ttilde P) ∧
    welfare P (Set.Icc (Ttilde P) (2 * Ttilde P)) (fun _ => Ttilde P) = fbValue P := by
  have hP' := hP
  obtain ⟨hL, hc, hθ⟩ := hP
  set s := Real.sqrt (P.c / (P.c + 2)) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = P.c / (P.c + 2) := Real.sq_sqrt (by positivity)
  have hs1 : s < 1 := by
    have : P.c / (P.c + 2) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  set T := Ttilde P with hTdef
  have hT0 : 0 < T := Real.sqrt_pos.mpr (by
    have : 0 < 1 - s := by linarith
    positivity)
  have hT2 : P.Lam * T ^ 2 = P.θbar * (1 - s) := by
    have h1s : 0 < 1 - s := by linarith
    rw [hTdef, Ttilde, ← hsdef, Real.sq_sqrt (by positivity)]
    field_simp
  have h2T : 2 * T ≤ P.θbar := by
    have hl : 4 * (1 - s) / P.θbar ≤ P.Lam := hΛ
    rw [div_le_iff₀ hθ] at hl
    -- (2T)^2 ≤ θ̄^2
    have : (2 * T) ^ 2 ≤ P.θbar ^ 2 := by
      have : P.Lam * (2 * T) ^ 2 ≤ P.Lam * P.θbar ^ 2 := by nlinarith
      exact le_of_mul_le_mul_left this hL
    nlinarith
  -- integrals over [T, 2T]
  have hvol : volume.real (Set.Icc T (2 * T)) = T := by
    rw [Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring
  have hload : load (Set.Icc T (2 * T)) (fun _ => T) = T * T := by
    unfold load; rw [setIntegral_const, hvol, smul_eq_mul]
  have hmom : moment2 (Set.Icc T (2 * T)) (fun _ => T) = T * T ^ 2 := by
    unfold moment2; rw [setIntegral_const, hvol, smul_eq_mul]
  have hstab : P.Lam * load (Set.Icc T (2 * T)) (fun _ => T) < P.θbar := by
    rw [hload, ← sq, hT2]; nlinarith
  have hA : IsAllocation P (Set.Icc T (2 * T)) (fun _ => T) :=
    ⟨measurableSet_Icc, fun θ h => ⟨by linarith [h.1], by linarith [h.2]⟩, measurable_const,
      fun θ h => ⟨hT0.le, h.1⟩, hstab⟩
  have hval : welfare P (Set.Icc T (2 * T)) (fun _ => T) = fbValue P := by
    unfold welfare waitTime fbValue
    rw [setIntegral_const, hvol, smul_eq_mul, hload, hmom, ← hsdef]
    have hKs : (P.c + 2) * s ^ 2 = P.c := by rw [hs2]; field_simp
    have hD : P.θbar - P.Lam * (T * T) = P.θbar * s := by
      rw [← sq, hT2]; ring
    rw [hD]
    have e1 : P.Lam / P.θbar * (T * (T - P.c * (P.Lam * (T * T ^ 2) / (2 * (P.θbar * s)))))
        = (P.Lam * T ^ 2 / P.θbar) - P.c * (P.Lam * T ^ 2 / P.θbar) ^ 2 / (2 * s) := by
      field_simp
    rw [e1, hT2]
    have e2 : P.θbar * (1 - s) / P.θbar = 1 - s := by field_simp
    rw [e2, ← hKs]
    field_simp
    have h2 : (2 : ℝ) = (P.c + 2) * (1 - s ^ 2) := by nlinarith
    nlinarith [h2]
  refine ⟨h2T, ⟨hA, fun Φ' t' hA' => ?_⟩, hval⟩
  rw [hval]
  exact STLHigh.welfare_le P hP' Φ' t' hA'
