-- Prove2me | solution 1 for ServTimeLimit.OptMech.theorem_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:06:48.054219+00:00
-- url     : https://prove2.me/submissions/d774f517-8ca0-4f60-9759-0349e23e3448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model
import Theorems.Thm_ServTimeLimit_OptMech_theorem_1_low
import Theorems.Thm_ServTimeLimit_OptMech_theorem_1_mid
import Theorems.Thm_ServTimeLimit_OptMech_theorem_1_high
import Theorems.Thm_ServTimeLimit_OptMech_full_extraction
import Theorems.Thm_ServTimeLimit_OptMech_revenue_le_first_best

namespace STLFBPrice
open MeasureTheory ServTimeLimit.OptMech

lemma intOn_of_alloc (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) (hA : IsAllocation P Φ t)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ θ ∈ Φ, |f θ| ≤ M) : IntegrableOn f Φ := by
  obtain ⟨hΦ, hsub, -, -, -⟩ := hA
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top)
  · rw [ae_restrict_iff' hΦ]
    exact Filter.Eventually.of_forall (fun θ h => by simpa [Real.norm_eq_abs] using hM θ h)

/-- In a first-best allocation, almost no admitted type has `t(θ) < c W`. -/
lemma fb_null (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t : ℝ → ℝ)
    (hFB : IsFirstBest P Φ t) :
    volume (Φ \ {θ | P.c * waitTime P Φ t ≤ t θ}) = 0 := by
  obtain ⟨hA, hopt⟩ := hFB
  obtain ⟨hΛ, hc, hθ⟩ := hP
  have hA' := hA
  obtain ⟨hΦ, hsub, ht, hbd, hstab⟩ := hA
  set w := waitTime P Φ t with hw
  set S : Set ℝ := {θ | P.c * w ≤ t θ} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const ht
  by_contra hne
  have hpos : 0 < volume (Φ \ S) := pos_iff_ne_zero.mpr hne
  -- bounds
  have tb : ∀ θ ∈ Φ, |t θ| ≤ P.θbar := fun θ h => by
    rw [abs_le]; have := hbd θ h; have := (hsub h).2; constructor <;> linarith
  have t2b : ∀ θ ∈ Φ, |t θ ^ 2| ≤ P.θbar ^ 2 := fun θ h => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (tb θ h) 2
  have hIt : IntegrableOn t Φ := intOn_of_alloc P Φ t hA' t ht _ tb
  have hIt2 : IntegrableOn (fun θ => t θ ^ 2) Φ :=
    intOn_of_alloc P Φ t hA' _ (ht.pow_const 2) _ t2b
  have hIc : ∀ x : ℝ, IntegrableOn (fun _ : ℝ => x) Φ := fun x =>
    intOn_of_alloc P Φ t hA' _ measurable_const |x| (fun _ _ => le_rfl)
  set Φ' := Φ ∩ S with hΦ'
  have hsub' : Φ' ⊆ Φ := Set.inter_subset_left
  -- Φ' is an allocation
  have hload : load Φ' t ≤ load Φ t := by
    unfold load
    refine setIntegral_mono_set hIt ?_ (Filter.Eventually.of_forall hsub')
    rw [Filter.EventuallyLE, ae_restrict_iff' hΦ]
    exact Filter.Eventually.of_forall (fun θ h => (hbd θ h).1)
  have hmom : moment2 Φ' t ≤ moment2 Φ t := by
    unfold moment2
    refine setIntegral_mono_set hIt2 ?_ (Filter.Eventually.of_forall hsub')
    exact Filter.Eventually.of_forall (fun θ => sq_nonneg (t θ))
  have hmom0 : 0 ≤ moment2 Φ' t := setIntegral_nonneg (hΦ.inter hSm) (fun θ _ => sq_nonneg _)
  have hA2 : IsAllocation P Φ' t :=
    ⟨hΦ.inter hSm, hsub'.trans hsub, ht, fun θ h => hbd θ h.1,
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hload hΛ.le) hstab⟩
  -- waiting time decreases
  have hw' : waitTime P Φ' t ≤ w := by
    rw [hw]; unfold waitTime
    have d1 : 0 < 2 * (P.θbar - P.Lam * load Φ t) := by linarith
    have d2 : 2 * (P.θbar - P.Lam * load Φ t) ≤ 2 * (P.θbar - P.Lam * load Φ' t) := by
      nlinarith
    calc P.Lam * moment2 Φ' t / (2 * (P.θbar - P.Lam * load Φ' t))
        ≤ P.Lam * moment2 Φ' t / (2 * (P.θbar - P.Lam * load Φ t)) :=
          div_le_div_of_nonneg_left (mul_nonneg hΛ.le hmom0) d1 d2
      _ ≤ P.Lam * moment2 Φ t / (2 * (P.θbar - P.Lam * load Φ t)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmom hΛ.le) d1.le
  -- integrals
  have hIf : IntegrableOn (fun θ => t θ - P.c * w) Φ := hIt.sub (hIc _)
  have hsplit := integral_inter_add_sdiff (μ := volume) hSm hIf
  have hneg : ∫ θ in Φ \ S, (t θ - P.c * w) < 0 := by
    have hpos' : 0 < ∫ θ in Φ \ S, (P.c * w - t θ) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · refine lt_of_lt_of_le hpos (measure_mono ?_)
        intro θ hθ
        refine ⟨?_, hθ⟩
        simp only [Function.mem_support]
        have : ¬ (P.c * w ≤ t θ) := hθ.2
        intro h0; apply this; linarith
      · rw [Filter.EventuallyLE, ae_restrict_iff' (hΦ.diff hSm)]
        refine Filter.Eventually.of_forall (fun θ h => ?_)
        have : ¬ (P.c * w ≤ t θ) := h.2
        simp only [Pi.zero_apply]; linarith
      · exact ((hIc _).sub hIt).mono_set Set.sdiff_subset
    have : ∫ θ in Φ \ S, (P.c * w - t θ) = - ∫ θ in Φ \ S, (t θ - P.c * w) := by
      rw [← integral_neg]; congr 1; funext θ; ring
    linarith
  have hmono : ∫ θ in Φ', (t θ - P.c * w) ≤ ∫ θ in Φ', (t θ - P.c * waitTime P Φ' t) := by
    refine setIntegral_mono_on (hIf.mono_set hsub') ((hIt.sub (hIc _)).mono_set hsub')
      (hΦ.inter hSm) (fun θ _ => ?_)
    have := mul_le_mul_of_nonneg_left hw' hc.le
    linarith
  have key := hopt Φ' t hA2
  unfold welfare at key
  have hk : 0 < P.Lam / P.θbar := div_pos hΛ hθ
  have : ∫ θ in Φ, (t θ - P.c * w) < ∫ θ in Φ', (t θ - P.c * waitTime P Φ' t) := by
    linarith
  have := mul_lt_mul_of_pos_left this hk
  linarith

/-- Pointwise version on an interval `[a, b]` where `a ≤ t(θ) ≤ θ`. -/
lemma fb_price_nonneg (P : Params) (hP : P.Standing) (a b : ℝ) (t : ℝ → ℝ)
    (hFB : IsFirstBest P (Set.Icc a b) t) (hlow : ∀ θ ∈ Set.Icc a b, a ≤ t θ) :
    ∀ θ ∈ Set.Icc a b, P.c * waitTime P (Set.Icc a b) t ≤ t θ := by
  intro θ hθ
  have hab : a ≤ b := hθ.1.trans hθ.2
  rcases eq_or_lt_of_le hab with hab | hab
  · -- singleton: waiting time is zero
    subst hab
    have hw : waitTime P (Set.Icc a a) t = 0 := by
      unfold waitTime moment2
      simp
    rw [hw, mul_zero]
    exact le_trans (by have := hFB.1.2.2.2.1 θ hθ; exact this.1) le_rfl
  · by_contra hlt
    push Not at hlt
    set w := P.c * waitTime P (Set.Icc a b) t
    have haw : a < w := lt_of_le_of_lt (hlow θ hθ) hlt
    have hnull := fb_null P hP _ t hFB
    have hsub : Set.Ioo a (min w b) ⊆ Set.Icc a b \ {θ | w ≤ t θ} := by
      intro x hx
      refine ⟨⟨hx.1.le, hx.2.le.trans (min_le_right _ _)⟩, ?_⟩
      simp only [Set.mem_ofPred_eq, not_le]
      have h1 := (hFB.1.2.2.2.1 x ⟨hx.1.le, hx.2.le.trans (min_le_right _ _)⟩).2
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hx.2 (min_le_left _ _))
    have := measure_mono_null hsub hnull
    rw [Real.volume_Ioo] at this
    have h2 : a < min w b := lt_min haw hab
    simp only [ENNReal.ofReal_eq_zero, tsub_nonpos] at this
    linarith

/-- One regime of Theorem 8, for a first-best allocation on an interval. -/
lemma regime (P : Params) (hP : P.Standing) (a b : ℝ) (t : ℝ → ℝ) (htc : Continuous t)
    (hFB : IsFirstBest P (Set.Icc a b) t) (hlow : ∀ θ ∈ Set.Icc a b, a ≤ t θ) :
    ∀ (Φ : Set ℝ) (p : ℝ → ℝ), Φ = Set.Icc a b →
      (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
      IsFirstBest P Φ t ∧
      (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
      (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
        min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
      (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
        IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
      revenue P Φ p = welfare P Φ t := by
  intro Φ p hΦ hp
  subst hΦ
  have hFE := full_extraction P hP _ t hFB.1 p hp
  obtain ⟨hIC, hzero, hnon, hrev⟩ := hFE
  have hpf : p = fun θ => min θ (t θ) - P.c * waitTime P (Set.Icc a b) t := funext hp
  have hpc : Continuous p := by rw [hpf]; fun_prop
  have hnn := fb_price_nonneg P hP a b t hFB hlow
  refine ⟨hFB, ⟨⟨hFB.1, hpc.measurable, hpc.integrableOn_Icc, fun θ hθ => ?_⟩, hIC,
    fun θ hθ => (hzero θ hθ).symm.le⟩, hnon, fun Φ' t' p' hM _ hIR => ?_, hrev⟩
  · rw [hp, min_eq_right (hFB.1.2.2.2.1 θ hθ).2]
    linarith [hnn θ hθ]
  · rw [hrev]
    exact (revenue_le_first_best P hP Φ' t' p' hM hIR).2 _ t hFB

end STLFBPrice

open MeasureTheory ServTimeLimit.OptMech in
theorem solution (P : ServTimeLimit.OptMech.Params) (hP : P.Standing) :
    -- case Λ ≤ Λ₁: admit [θ_l, θ̄], t(θ) = θ
    (P.Lam ≤ lam1 P →
      ∃ θl : ℝ, 0 ≤ θl ∧ θl ≤ P.θbar ∧
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc θl P.θbar → t = (fun θ => θ) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) ∧
    -- case Λ₁ ≤ Λ ≤ Λ₂: admit [θ_l, θ̄], time limit t(θ) = min{θ, T}
    (lam1 P ≤ P.Lam → P.Lam ≤ lam2 P →
      ∃ θl T : ℝ, 0 ≤ θl ∧ θl ≤ T ∧ T ≤ P.θbar ∧
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc θl P.θbar → t = (fun θ => min θ T) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) ∧
    -- case Λ ≥ Λ₂: admit [T̃, 2T̃], t(θ) = T̃
    (lam2 P ≤ P.Lam →
        ∀ (Φ : Set ℝ) (t p : ℝ → ℝ), Φ = Set.Icc (Ttilde P) (2 * Ttilde P) →
          t = (fun _ => Ttilde P) →
          (∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) →
          IsFirstBest P Φ t ∧
          (IsMechanism P Φ t p ∧ IsIC Φ t p ∧ IsIR P Φ t p) ∧
          (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ'' ∈ Φ,
            min (t θ'') θ - p θ'' - P.c * waitTime P Φ t ≤ 0) ∧
          (∀ (Φ' : Set ℝ) (t' p' : ℝ → ℝ), IsMechanism P Φ' t' p' → IsIC Φ' t' p' →
            IsIR P Φ' t' p' → revenue P Φ' p' ≤ revenue P Φ p) ∧
          revenue P Φ p = welfare P Φ t) := by
  refine ⟨fun hΛ => ?_, fun hΛ1 hΛ2 => ?_, fun hΛ => ?_⟩
  · obtain ⟨θl, ⟨⟨h0, h1⟩, hFB⟩, -⟩ := theorem_1_low P hP hΛ
    refine ⟨θl, h0, h1, fun Φ t p hΦ ht hp => ?_⟩
    subst ht
    exact STLFBPrice.regime P hP θl P.θbar (fun θ => θ) continuous_id hFB
      (fun θ hθ => hθ.1) Φ p hΦ hp
  · obtain ⟨⟨θl, T⟩, ⟨⟨h0, h1, h2⟩, hFB⟩, -⟩ := theorem_1_mid P hP hΛ1 hΛ2
    refine ⟨θl, T, h0, h1, h2, fun Φ t p hΦ ht hp => ?_⟩
    subst ht
    exact STLFBPrice.regime P hP θl P.θbar (fun θ => min θ T) (by fun_prop) hFB
      (fun θ hθ => le_min hθ.1 h1) Φ p hΦ hp
  · intro Φ t p hΦ ht hp
    obtain ⟨-, hFB, -⟩ := theorem_1_high P hP hΛ
    subst ht
    exact STLFBPrice.regime P hP (Ttilde P) (2 * Ttilde P) (fun _ => Ttilde P)
      continuous_const hFB (fun θ _ => le_rfl) Φ p hΦ hp
