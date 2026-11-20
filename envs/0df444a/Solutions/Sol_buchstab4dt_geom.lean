-- Prove2me | solution 1 for buchstab4dt_geom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:31:16.277319+00:00
-- url     : https://prove2.me/submissions/2cd4c6d7-746d-4b95-9660-0a3cee973da4

import Mathlib
import Definitions.Def_Buchstab4DT_Core

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

namespace Sol_Buchstab4DT_Geom

private lemma buchstab_integral_eq {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * ω b - a * ω a = ∫ s in (a - 1)..(b - 1), ω s := by
  rcases hω with ⟨hcont, _, hderiv, _⟩
  have hsub : Icc a b ⊆ Ici (1 : ℝ) := fun x hx => le_trans (by linarith) hx.1
  have hcont_mul : ContinuousOn (fun v => v * ω v) (Icc a b) :=
    continuousOn_id.mul (hcont.mono hsub)
  have hderiv_open : ∀ x ∈ Ioo a b, HasDerivAt (fun v => v * ω v) (ω (x - 1)) x :=
    fun x hx => hderiv x (by linarith [hx.1])
  have hcont_shift : ContinuousOn (fun t => ω (t - 1)) (Icc a b) := by
    refine hcont.comp (continuousOn_id.sub continuousOn_const) ?_
    intro x hx; change 1 ≤ x - 1; linarith [hx.1]
  have hint : IntervalIntegrable (fun t => ω (t - 1)) volume a b :=
    hcont_shift.intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont_mul hderiv_open hint
  rw [← hftc, intervalIntegral.integral_comp_sub_right]

private lemma buchstab_nonneg_on_Icc {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) :
    ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → 0 ≤ ω u := by
  intro n
  induction n with
  | zero =>
    intro u hu1 hu2
    push_cast at hu2
    rw [hω.2.1 u hu1 (by linarith)]
    positivity
  | succ n ih =>
    intro u hu1 hu2
    by_cases hle : u ≤ (n : ℝ) + 2
    · exact ih u hu1 hle
    · push Not at hle
      set b : ℝ := (n : ℝ) + 2
      have hb2 : 2 ≤ b := by dsimp only [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := le_of_lt hle
      have heq := buchstab_integral_eq hω hb2 hbu
      have hwb : 0 ≤ ω b := ih b (by linarith) (le_refl b)
      have hint_nn : 0 ≤ ∫ s in (b - 1)..(u - 1), ω s := by
        apply intervalIntegral.integral_nonneg (by linarith)
        intro s hs
        exact ih s (by linarith [hs.1]) (by push_cast at hu2; linarith [hs.2])
      have hu_pos : 0 < u := by linarith
      have hmul : 0 ≤ u * ω u := by nlinarith
      exact nonneg_of_mul_nonneg_right hmul hu_pos

lemma buchstab_nonneg {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    (u : ℝ) : 0 ≤ ω u := by
  by_cases h1 : u < 1
  · rw [hω.2.2.2 u h1]
  · push Not at h1
    exact buchstab_nonneg_on_Icc hω (Nat.ceil u) u h1 (by linarith [Nat.le_ceil u])

private lemma buchstab_max_propagate {ω : ℝ → ℝ} (hω : IsBuchstabCore ω) {a M : ℝ}
    (ha : 2 ≤ a) (hM : ∀ u ∈ Icc a (a + 1), ω u ≤ M) :
    ∀ n : ℕ, ∀ u ∈ Icc a (a + 1 + (n : ℝ)), ω u ≤ M := by
  intro n
  induction n with
  | zero =>
    intro u hu; simp only [Nat.cast_zero, add_zero] at hu; exact hM u hu
  | succ n ih =>
    intro u hu
    by_cases hle : u ≤ a + 1 + (n : ℝ)
    · exact ih u ⟨hu.1, hle⟩
    · push Not at hle
      set b : ℝ := a + 1 + (n : ℝ)
      have hb2 : 2 ≤ b := by dsimp only [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := le_of_lt hle
      have heq := buchstab_integral_eq hω hb2 hbu
      have hwb : ω b ≤ M := ih b ⟨by dsimp only [b]; linarith [Nat.cast_nonneg (α := ℝ) n], le_refl b⟩
      have hcont_sub : ContinuousOn ω (Icc (b - 1) (u - 1)) :=
        hω.1.mono (fun s hs => by dsimp only [b] at hs; change 1 ≤ s; linarith [hs.1, Nat.cast_nonneg (α := ℝ) n])
      have hint_le : ∫ s in (b - 1)..(u - 1), ω s ≤ ∫ _ in (b - 1)..(u - 1), M := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hcont_sub.intervalIntegrable_of_Icc (by linarith))
          intervalIntegrable_const
        intro s hs
        exact ih s ⟨by dsimp only [b] at hs; linarith [hs.1, Nat.cast_nonneg (α := ℝ) n],
          by push_cast at hu; dsimp only [b] at hs ⊢; linarith [hs.2, hu.2]⟩
      rw [intervalIntegral.integral_const, smul_eq_mul] at hint_le
      have hu_pos : 0 < u := by linarith
      have hmul : u * ω u ≤ u * M := by nlinarith
      exact le_of_mul_le_mul_left hmul hu_pos

private lemma buchstab_le_two_thirds {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {u : ℝ} (hu : 2 ≤ u) : ω u ≤ 2 / 3 := by
  have h23 : ∀ v ∈ Icc (2 : ℝ) 3, ω v ≤ 2 / 3 := by
    intro v hv
    have heq := buchstab_integral_eq hω (le_refl 2) hv.1
    have hw2 : ω 2 = 1 / 2 := hω.2.1 2 (by norm_num) (by norm_num)
    have hcont : ContinuousOn ω (Icc 1 (v - 1)) := hω.1.mono (fun s hs => hs.1)
    have hint : ∫ s in (1 : ℝ)..(v - 1), ω s ≤ ∫ _ in (1 : ℝ)..(v - 1), (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith [hv.1])
        (hcont.intervalIntegrable_of_Icc (by linarith [hv.1]))
        intervalIntegrable_const
      intro s hs
      rw [hω.2.1 s hs.1 (by linarith [hs.2, hv.2])]
      exact div_le_one_of_le₀ hs.1 (by linarith [hs.1])
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    norm_num at heq
    have hv_pos : 0 < v := by linarith [hv.1]
    have hmul : v * ω v ≤ v - 1 := by linarith
    have : v * ω v ≤ v * (2 / 3) := by nlinarith [hv.1, hv.2]
    exact le_of_mul_le_mul_left this hv_pos
  have hprop := buchstab_max_propagate hω (a := 2) (M := 2 / 3) (le_refl 2)
    (by simpa [show (2 : ℝ) + 1 = 3 by norm_num] using h23)
  exact hprop (Nat.ceil u) u ⟨hu, by linarith [Nat.le_ceil u]⟩

lemma buchstab_le_max_inv_two_thirds {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    {u : ℝ} (hu : 1 ≤ u) : ω u ≤ max (1 / u) (2 / 3) := by
  by_cases h2 : u ≤ 2
  · rw [hω.2.1 u hu h2]; exact le_max_left _ _
  · exact le_trans (buchstab_le_two_thirds hω (le_of_not_ge h2)) (le_max_right _ _)

lemma buchstab_le_one {ω : ℝ → ℝ} (hω : IsBuchstabCore ω)
    (u : ℝ) : ω u ≤ 1 := by
  by_cases h1 : u < 1
  · rw [hω.2.2.2 u h1]; norm_num
  · push Not at h1
    exact le_trans (buchstab_le_max_inv_two_thirds hω h1) (max_le (div_le_one_of_le₀ h1 (by linarith)) (by norm_num))

/-! ### Part 3: General Log-Convexity, Hermite-Hadamard, and Jensen at Centroid -/

private lemma setIntegral_prod_symm' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} (f : α × β → ℝ) (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂(μ.prod ν) = ∫ y in t, ∫ x in s, f (x, y) ∂μ ∂ν := by
  have hf' : Integrable f ((μ.restrict s).prod (ν.restrict t)) := by rwa [Measure.prod_restrict]
  rw [← Measure.prod_restrict]
  exact MeasureTheory.integral_prod_symm f hf'

private lemma integrableOn_setIntegral_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} {f : α × β → ℝ} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (fun x => ∫ y in t, f (x, y) ∂ν) s μ := by
  have hf' : Integrable f ((μ.restrict s).prod (ν.restrict t)) := by rwa [Measure.prod_restrict]
  exact hf'.integral_prod_left

private lemma integrableOn_setIntegral_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} {f : α × β → ℝ} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (fun y => ∫ x in s, f (x, y) ∂μ) t ν := by
  have hf' : Integrable f ((μ.restrict s).prod (ν.restrict t)) := by rwa [Measure.prod_restrict]
  exact hf'.swap.integral_prod_left

private lemma integrableOn_indicator_of_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} {f : α → ℝ} (ht : MeasurableSet t) (hts : t ⊆ s) (hf : IntegrableOn f t μ) :
    IntegrableOn (t.indicator f) s μ := by
  rw [integrableOn_indicator_iff ht, inter_eq_self_of_subset_left hts]; exact hf

private def sw3 : ℝ × (ℝ × ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.prodAssoc).symm.trans (MeasurableEquiv.prodComm)

private lemma sw3_apply (x y z : ℝ) : sw3 (x, (y, z)) = (z, (x, y)) := rfl
private lemma sw3_symm_apply (z x y : ℝ) : sw3.symm (z, (x, y)) = (x, (y, z)) := rfl

private lemma measurePreserving_sw3 :
    MeasurePreserving sw3 (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume)) :=
  (MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ) volume volume).symm.trans
    Measure.measurePreserving_swap

private lemma convex_tri2 (a b : ℝ) :
    Convex ℝ {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2} := by
  intro p hp q hq u v hu hv huv
  exact ⟨by simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using convex_Icc a b hp.1 hq.1 hu hv huv,
         by simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using convex_Icc a b hp.2.1 hq.2.1 hu hv huv,
         add_le_add (mul_le_mul_of_nonneg_left hp.2.2 hu) (mul_le_mul_of_nonneg_left hq.2.2 hv)⟩

private lemma convex_simp3 (a b : ℝ) :
    Convex ℝ {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2} := by
  intro p hp q hq u v hu hv huv
  exact ⟨by simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using convex_Icc a b hp.1 hq.1 hu hv huv,
         by simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using convex_Icc a b hp.2.1 hq.2.1 hu hv huv,
         by simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using convex_Icc a b hp.2.2.1 hq.2.2.1 hu hv huv,
         add_le_add (mul_le_mul_of_nonneg_left hp.2.2.2.1 hu) (mul_le_mul_of_nonneg_left hq.2.2.2.1 hv),
         add_le_add (mul_le_mul_of_nonneg_left hp.2.2.2.2 hu) (mul_le_mul_of_nonneg_left hq.2.2.2.2 hv)⟩

lemma convexOn_inv_prod {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : Convex ℝ S) {k : ℕ} (L : Fin k → E → ℝ)
    (haff : ∀ i, ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      L i (a • x + b • y) = a * L i x + b * L i y)
    (hpos : ∀ i, ∀ x ∈ S, 0 < L i x) :
    ConvexOn ℝ S (fun x => (∏ i : Fin k, L i x)⁻¹) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmem : a • x + b • y ∈ S := hS hx hy ha hb hab
  have hlog_le : ∀ i : Fin k, -Real.log (L i (a • x + b • y)) ≤
      a * (-Real.log (L i x)) + b * (-Real.log (L i y)) := by
    intro i
    have hx_p : 0 < L i x := hpos i x hx
    have hy_p : 0 < L i y := hpos i y hy
    have hz_p : 0 < L i (a • x + b • y) := hpos i _ hmem
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx_p hz_p)
    have h2 := Real.log_le_sub_one_of_pos (div_pos hy_p hz_p)
    rw [Real.log_div (ne_of_gt hx_p) (ne_of_gt hz_p)] at h1
    rw [Real.log_div (ne_of_gt hy_p) (ne_of_gt hz_p)] at h2
    have hm1 := mul_le_mul_of_nonneg_left h1 ha
    have hm2 := mul_le_mul_of_nonneg_left h2 hb
    have hcomb : a * (L i x / L i (a • x + b • y) - 1) + b * (L i y / L i (a • x + b • y) - 1) = 0 := by
      have ha_eq := haff i x hx y hy a b ha hb hab
      have hne := ne_of_gt hz_p
      field_simp [hne]; nlinarith
    have hlhs : a * (Real.log (L i x) - Real.log (L i (a • x + b • y))) +
        b * (Real.log (L i y) - Real.log (L i (a • x + b • y))) =
        a * Real.log (L i x) + b * Real.log (L i y) - Real.log (L i (a • x + b • y)) := by
      linear_combination -Real.log (L i (a • x + b • y)) * hab
    linarith
  have hsum : ∑ i : Fin k, -Real.log (L i (a • x + b • y)) ≤
      a * (∑ i : Fin k, -Real.log (L i x)) + b * (∑ i : Fin k, -Real.log (L i y)) := by
    calc ∑ i : Fin k, -Real.log (L i (a • x + b • y))
        ≤ ∑ i : Fin k, (a * (-Real.log (L i x)) + b * (-Real.log (L i y))) :=
          Finset.sum_le_sum (fun i _ => hlog_le i)
      _ = a * (∑ i : Fin k, -Real.log (L i x)) + b * (∑ i : Fin k, -Real.log (L i y)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hexp_eq : ∀ z ∈ S, Real.exp (∑ i : Fin k, -Real.log (L i z)) = (∏ i : Fin k, L i z)⁻¹ := by
    intro z hz
    rw [Real.exp_sum, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_neg, Real.exp_log (hpos i z hz)]
  dsimp only
  simp only [smul_eq_mul]
  rw [← hexp_eq (a • x + b • y) hmem, ← hexp_eq x hx, ← hexp_eq y hy]
  calc Real.exp (∑ i : Fin k, -Real.log (L i (a • x + b • y)))
      ≤ Real.exp (a * (∑ i : Fin k, -Real.log (L i x)) + b * (∑ i : Fin k, -Real.log (L i y))) :=
        Real.exp_le_exp.mpr hsum
    _ ≤ a * Real.exp (∑ i : Fin k, -Real.log (L i x)) +
        b * Real.exp (∑ i : Fin k, -Real.log (L i y)) := by
        have hce := convexOn_exp.2 (mem_univ (∑ i : Fin k, -Real.log (L i x)))
          (mem_univ (∑ i : Fin k, -Real.log (L i y))) ha hb hab
        simpa only [smul_eq_mul] using hce

lemma hh1_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Icc a b) f) (hcont : ContinuousOn f (Icc a b)) :
    ∫ x in a..b, f x ≤ ((b - a) / 2) * (f a + f b) := by
  by_cases hlt : a = b
  · subst hlt; simp
  have hab' : a < b := lt_of_le_of_ne hab hlt
  have hba : 0 < b - a := sub_pos.mpr hab'
  have hlin_cont : ContinuousOn (fun x => ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) (Icc a b) :=
    (((continuousOn_const.sub continuousOn_id).div_const _).mul continuousOn_const).add
      (((continuousOn_id.sub continuousOn_const).div_const _).mul continuousOn_const)
  have hle : ∫ x in a..b, f x ≤
      ∫ x in a..b, (((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) := by
    apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab)
      (hlin_cont.intervalIntegrable_of_Icc hab)
    intro x hx
    have hw1 : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
    have hw2 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hba)
    have hw : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
    have hpt := hconv.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hw1 hw2 hw
    have hx_eq : ((b - x) / (b - a)) • a + ((x - a) / (b - a)) • b = x := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hx_eq] at hpt
    simpa [smul_eq_mul] using hpt
  have heval : ∫ x in a..b, (((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) =
      ((b - a) / 2) * (f a + f b) := by
    have hderiv : ∀ x ∈ uIcc a b,
        HasDerivAt (fun t : ℝ => (-((b - t) ^ 2) / (2 * (b - a))) * f a + (((t - a) ^ 2) / (2 * (b - a))) * f b)
          (((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -((b - t) ^ 2) / (2 * (b - a))) ((b - x) / (b - a)) x := by
        have hd := ((hasDerivAt_const x b).sub (hasDerivAt_id x)).pow 2
        refine ((hd.neg).div_const (2 * (b - a))).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      have h2 : HasDerivAt (fun t : ℝ => ((t - a) ^ 2) / (2 * (b - a))) ((x - a) / (b - a)) x := by
        have hd := ((hasDerivAt_id x).sub (hasDerivAt_const x a)).pow 2
        refine (hd.div_const (2 * (b - a))).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      exact (h1.mul_const (f a)).add (h2.mul_const (f b))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hlin_cont.intervalIntegrable_of_Icc hab)]
    field_simp; ring
  linarith

lemma jensen1_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Icc a b) f) (hcont : ContinuousOn f (Icc a b)) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := by
  have hint1 : IntervalIntegrable f volume a b := hcont.intervalIntegrable_of_Icc hab
  have hcont_ref : ContinuousOn (fun x => f (a + b - x)) (Icc a b) := by
    refine hcont.comp (continuousOn_const.sub continuousOn_id) ?_
    intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hint2 : IntervalIntegrable (fun x => f (a + b - x)) volume a b :=
    hcont_ref.intervalIntegrable_of_Icc hab
  have href_eq : ∫ x in a..b, f (a + b - x) = ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => f t) (a + b)]
    congr 1 <;> ring
  have hle : ∫ _ in a..b, f ((a + b) / 2) ≤ ∫ x in a..b, ((f x + f (a + b - x)) / 2) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const ((hint1.add hint2).div_const 2)
    intro x hx
    have href : a + b - x ∈ Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hpt := hconv.2 hx href (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (a + b - x) = (a + b) / 2 := by
      simp only [smul_eq_mul]; ring
    rw [hm] at hpt
    simp only [smul_eq_mul] at hpt
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_add hint1 hint2, href_eq] at hle
  linarith

private lemma hh2_tri {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hconv : ConvexOn ℝ {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2} f)
    (hcont : ContinuousOn f {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}) :
    ∫ y in a..b, ∫ x in a..y, f (x, y) ≤
      ((b - a) ^ 2 / 6) * (f (a, a) + f (a, b) + f (b, b)) := by
  by_cases hlt : a = b
  · subst hlt; simp
  have hab' : a < b := lt_of_le_of_ne hab hlt
  have hba : 0 < b - a := sub_pos.mpr hab'
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}
  have hv0 : (a, a) ∈ T := ⟨left_mem_Icc.mpr hab, left_mem_Icc.mpr hab, le_refl a⟩
  have hv1 : (a, b) ∈ T := ⟨left_mem_Icc.mpr hab, right_mem_Icc.mpr hab, hab⟩
  have hv2 : (b, b) ∈ T := ⟨right_mem_Icc.mpr hab, right_mem_Icc.mpr hab, le_refl b⟩
  let g : ℝ × ℝ → ℝ := fun p =>
    ((b - p.2) / (b - a)) * f (a, a) + ((p.2 - p.1) / (b - a)) * f (a, b) + ((p.1 - a) / (b - a)) * f (b, b)
  have hpt : ∀ p ∈ T, f p ≤ g p := by
    intro ⟨x, y⟩ hp
    have hw0 : 0 ≤ (b - y) / (b - a) := div_nonneg (sub_nonneg.mpr hp.2.1.2) (le_of_lt hba)
    have hw1 : 0 ≤ (y - x) / (b - a) := div_nonneg (sub_nonneg.mpr hp.2.2) (le_of_lt hba)
    have hw2 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hp.1.1) (le_of_lt hba)
    have hsum : (b - y) / (b - a) + (y - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
    by_cases h12 : (y - x) / (b - a) + (x - a) / (b - a) = 0
    · have hya : y = a := by
        have h0 : (y - a) / (b - a) = 0 := by
          have : (y - x) / (b - a) + (x - a) / (b - a) = (y - a) / (b - a) := by ring
          linarith
        have := (div_eq_zero_iff.mp h0).resolve_right (ne_of_gt hba)
        linarith
      have hxa : x = a := le_antisymm (by linarith [hp.2.2]) hp.1.1
      subst hxa; subst hya
      dsimp only [g]; field_simp; ring_nf; exact le_refl _
    · set s := (y - x) / (b - a) + (x - a) / (b - a)
      have hs_pos : 0 < s := lt_of_le_of_ne (add_nonneg hw1 hw2) (Ne.symm h12)
      have hs_sum : ((y - x) / (b - a)) / s + ((x - a) / (b - a)) / s = 1 := by
        rw [← add_div, div_self (ne_of_gt hs_pos)]
      set q : ℝ × ℝ := (((y - x) / (b - a)) / s) • (a, b) + (((x - a) / (b - a)) / s) • (b, b)
      have hq_mem : q ∈ T := hconv.1 hv1 hv2 (div_nonneg hw1 (le_of_lt hs_pos))
        (div_nonneg hw2 (le_of_lt hs_pos)) hs_sum
      have hq_le : f q ≤ (((y - x) / (b - a)) / s) * f (a, b) + (((x - a) / (b - a)) / s) * f (b, b) := by
        simpa only [smul_eq_mul] using hconv.2 hv1 hv2 (div_nonneg hw1 (le_of_lt hs_pos))
          (div_nonneg hw2 (le_of_lt hs_pos)) hs_sum
      have hxy_eq : ((b - y) / (b - a)) • (a, a) + s • q = (x, y) := by
        have hs_val : s * (b - a) = y - a := by dsimp only [s]; field_simp [ne_of_gt hba]; ring
        ext <;> dsimp only [q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        · have h1 : s * ((y - x) / (b - a) / s * a + (x - a) / (b - a) / s * b) =
              (y - x) / (b - a) * a + (x - a) / (b - a) * b := by field_simp [ne_of_gt hs_pos]
          rw [h1]; field_simp [ne_of_gt hba]; ring
        · have h2 : s * ((y - x) / (b - a) / s * b + (x - a) / (b - a) / s * b) =
              (y - x) / (b - a) * b + (x - a) / (b - a) * b := by field_simp [ne_of_gt hs_pos]
          rw [h2]; field_simp [ne_of_gt hba]; ring
      have hcomb := hconv.2 hv0 hq_mem hw0 (le_of_lt hs_pos) (by dsimp [s]; linarith)
      rw [hxy_eq] at hcomb
      simp only [smul_eq_mul] at hcomb
      have hmul := mul_le_mul_of_nonneg_left hq_le (le_of_lt hs_pos)
      dsimp only [g]
      have hcancel : s * (((y - x) / (b - a)) / s * f (a, b) + ((x - a) / (b - a)) / s * f (b, b)) =
          (y - x) / (b - a) * f (a, b) + (x - a) / (b - a) * f (b, b) := by
        field_simp [ne_of_gt hs_pos]
      linarith
  have hinner_le : ∀ y ∈ Icc a b, ∫ x in a..y, f (x, y) ≤ ∫ x in a..y, g (x, y) := by
    intro y hy
    have hf_cont : ContinuousOn (fun x => f (x, y)) (Icc a y) :=
      hcont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)
    have hg_cont : ContinuousOn (fun x => g (x, y)) (Icc a y) := by dsimp only [g]; fun_prop
    exact intervalIntegral.integral_mono_on hy.1 (hf_cont.intervalIntegrable_of_Icc hy.1)
      (hg_cont.intervalIntegrable_of_Icc hy.1) (fun x hx => hpt (x, y) ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)
  have hinner_eval : ∀ y ∈ Icc a b, ∫ x in a..y, g (x, y) =
      ((y - a) * (b - y) / (b - a)) * f (a, a) +
      (((y - a) ^ 2) / (2 * (b - a))) * f (a, b) +
      (((y - a) ^ 2) / (2 * (b - a))) * f (b, b) := by
    intro y hy
    have hg_cont : ContinuousOn (fun x => g (x, y)) (Icc a y) := by dsimp only [g]; fun_prop
    have hderiv : ∀ x ∈ uIcc a y,
        HasDerivAt (fun t : ℝ =>
          ((b - y) / (b - a) * t) * f (a, a) +
          (-((y - t) ^ 2) / (2 * (b - a))) * f (a, b) +
          (((t - a) ^ 2) / (2 * (b - a))) * f (b, b)) (g (x, y)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => (b - y) / (b - a) * t) ((b - y) / (b - a)) x := by
        simpa using (hasDerivAt_id x).const_mul ((b - y) / (b - a))
      have h2 : HasDerivAt (fun t : ℝ => -((y - t) ^ 2) / (2 * (b - a))) ((y - x) / (b - a)) x := by
        refine ((((hasDerivAt_const x y).sub (hasDerivAt_id x)).pow 2).neg.div_const _).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      have h3 : HasDerivAt (fun t : ℝ => ((t - a) ^ 2) / (2 * (b - a))) ((x - a) / (b - a)) x := by
        refine ((((hasDerivAt_id x).sub (hasDerivAt_const x a)).pow 2).div_const _).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      exact ((h1.mul_const _).add (h2.mul_const _)).add (h3.mul_const _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg_cont.intervalIntegrable_of_Icc hy.1)]
    field_simp; ring
  have houter_f_int : IntervalIntegrable (fun y => ∫ x in a..y, f (x, y)) volume a b := by
    have hT_comp : IsCompact T := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hT_meas : MeasurableSet T := hT_comp.isClosed.measurableSet
    have hint_prod : IntegrableOn (T.indicator f) (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
      refine integrableOn_indicator_of_subset hT_meas (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
      exact hcont.integrableOn_compact hT_comp
    have hint_snd := integrableOn_setIntegral_left hint_prod
    have h_ae : ∀ y ∈ Icc a b, ∫ x in a..y, f (x, y) = ∫ x in Icc a b, (T.indicator f) (x, y) := by
      intro y hy
      have heq_fn : ∀ x ∈ Icc a b, (T.indicator f) (x, y) = ({x : ℝ | x ≤ y}).indicator (fun x => f (x, y)) x := by
        intro x hx; by_cases hxy : x ≤ y <;> simp [T, hx.1, hx.2, hy.1, hy.2, hxy]
      rw [setIntegral_congr_fun measurableSet_Icc heq_fn,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a b ∩ {x : ℝ | x ≤ y} = Icc a y := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hy.2⟩, h2⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.1]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (IntegrableOn.congr_fun hint_snd
        (fun y hy => (h_ae y hy).symm) measurableSet_Icc)
  let hRHS : ℝ → ℝ := fun y =>
    ((y - a) * (b - y) / (b - a)) * f (a, a) +
    (((y - a) ^ 2) / (2 * (b - a))) * f (a, b) +
    (((y - a) ^ 2) / (2 * (b - a))) * f (b, b)
  have hhRHS_cont : ContinuousOn hRHS (Icc a b) := by dsimp only [hRHS]; fun_prop
  have houter_le : ∫ y in a..b, ∫ x in a..y, f (x, y) ≤ ∫ y in a..b, hRHS y := by
    apply intervalIntegral.integral_mono_on hab houter_f_int (hhRHS_cont.intervalIntegrable_of_Icc hab)
    intro y hy; dsimp only [hRHS]; rw [← hinner_eval y hy]; exact hinner_le y hy
  have houter_eval : ∫ y in a..b, hRHS y = ((b - a) ^ 2 / 6) * (f (a, a) + f (a, b) + f (b, b)) := by
    have hderiv : ∀ y ∈ uIcc a b,
        HasDerivAt (fun t : ℝ =>
          (((t - a) ^ 2 / 2 * (b - a) - (t - a) ^ 3 / 3) / (b - a)) * f (a, a) +
          (((t - a) ^ 3) / (6 * (b - a))) * f (a, b) +
          (((t - a) ^ 3) / (6 * (b - a))) * f (b, b)) (hRHS y) y := by
      intro y _
      have hd2 := ((hasDerivAt_id y).sub (hasDerivAt_const y a)).pow 2
      have hd3 := ((hasDerivAt_id y).sub (hasDerivAt_const y a)).pow 3
      have h1 : HasDerivAt (fun t : ℝ => ((t - a) ^ 2 / 2 * (b - a) - (t - a) ^ 3 / 3) / (b - a))
          ((y - a) * (b - y) / (b - a)) y := by
        refine ((((hd2.div_const 2).mul_const (b - a)).sub (hd3.div_const 3)).div_const (b - a)).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      have h2 : HasDerivAt (fun t : ℝ => (t - a) ^ 3 / (6 * (b - a))) ((y - a) ^ 2 / (2 * (b - a))) y := by
        refine (hd3.div_const (6 * (b - a))).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      exact ((h1.mul_const _).add (h2.mul_const _)).add (h2.mul_const _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hhRHS_cont.intervalIntegrable_of_Icc hab)]
    field_simp; ring
  linarith

private lemma tri2_cyclic_integral_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}) :
    ∫ y in a..b, ∫ x in a..y, f (a + b - y, b + x - y) =
      ∫ y in a..b, ∫ x in a..y, f (x, y) := by
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}
  have hT_comp : IsCompact T := by
    refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1⟩)
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
  have hT_meas : MeasurableSet T := hT_comp.isClosed.measurableSet
  have hinner : ∀ y ∈ Icc a b,
      ∫ x in a..y, f (a + b - y, b + x - y) = ∫ u in (a + b - y)..b, f (a + b - y, u) := by
    intro y _
    have hfun : (fun x : ℝ => f (a + b - y, b + x - y)) = (fun x : ℝ => f (a + b - y, x + (b - y))) := by
      ext x; ring_nf
    rw [hfun, intervalIntegral.integral_comp_add_right (fun u => f (a + b - y, u)) (b - y)]
    congr 1 <;> ring
  rw [intervalIntegral.integral_congr (fun y hy => hinner y (by rwa [uIcc_of_le hab] at hy))]
  rw [show (∫ y in a..b, ∫ u in (a + b - y)..b, f (a + b - y, u)) =
          ∫ v in a..b, ∫ u in v..b, f (v, u) by
        rw [intervalIntegral.integral_comp_sub_left (fun v => ∫ u in v..b, f (v, u)) (a + b)]
        congr 1 <;> ring]
  have hint_prod : IntegrableOn (T.indicator f) (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
    refine integrableOn_indicator_of_subset hT_meas (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
    exact hcont.integrableOn_compact hT_comp
  have hfub := MeasureTheory.setIntegral_prod (T.indicator f) hint_prod
  have hfub_s := setIntegral_prod_symm' (T.indicator f) hint_prod
  have hlhs : ∫ v in Icc a b, ∫ u in Icc a b, T.indicator f (v, u) =
      ∫ v in a..b, ∫ u in v..b, f (v, u) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le hab] at hv
    have heq : ∀ u ∈ Icc a b, T.indicator f (v, u) = ({u : ℝ | v ≤ u}).indicator (fun u => f (v, u)) u := by
      intro u hu; by_cases hvu : v ≤ u <;> simp [T, hv.1, hv.2, hu.1, hu.2, hvu]
    dsimp only; rw [setIntegral_congr_fun measurableSet_Icc heq,
        setIntegral_indicator (show MeasurableSet {x : ℝ | _ ≤ x} from measurableSet_Ici)]
    have hcap : Icc a b ∩ {u : ℝ | v ≤ u} = Icc v b := by
      ext u; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨le_trans hv.1 h1, h2⟩, h1⟩
    rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv.2]
  have hrhs : ∫ u in Icc a b, ∫ v in Icc a b, T.indicator f (v, u) =
      ∫ y in a..b, ∫ x in a..y, f (x, y) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_congr
    intro y hy; rw [uIcc_of_le hab] at hy
    have heq : ∀ x ∈ Icc a b, T.indicator f (x, y) = ({x : ℝ | x ≤ y}).indicator (fun x => f (x, y)) x := by
      intro x hx; by_cases hxy : x ≤ y <;> simp [T, hx.1, hx.2, hy.1, hy.2, hxy]
    dsimp only; rw [setIntegral_congr_fun measurableSet_Icc heq,
        setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
    have hcap : Icc a b ∩ {x : ℝ | x ≤ y} = Icc a y := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hy.2⟩, h2⟩
    rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.1]
  linarith

private lemma jensen2_tri {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hconv : ConvexOn ℝ {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2} f)
    (hcont : ContinuousOn f {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}) :
    ((b - a) ^ 2 / 2) * f ((2 * a + b) / 3, (a + 2 * b) / 3) ≤
      ∫ y in a..b, ∫ x in a..y, f (x, y) := by
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2}
  let P1 : ℝ × ℝ → ℝ × ℝ := fun p => (a + b - p.2, b + p.1 - p.2)
  let P2 : ℝ × ℝ → ℝ × ℝ := fun p => P1 (P1 p)
  have hP1_maps : ∀ p ∈ T, P1 p ∈ T := by
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, ⟨by linarith [hx.1, hy.2], by linarith⟩, by linarith [hx.1]⟩
  have hP1_cont : ContinuousOn (f ∘ P1) T :=
    hcont.comp (Continuous.continuousOn (by dsimp only [P1]; fun_prop)) hP1_maps
  have hP2_cont : ContinuousOn (f ∘ P2) T :=
    hP1_cont.comp (Continuous.continuousOn (by dsimp only [P1]; fun_prop)) hP1_maps
  have heq1 : ∫ y in a..b, ∫ x in a..y, f (P1 (x, y)) = ∫ y in a..b, ∫ x in a..y, f (x, y) :=
    tri2_cyclic_integral_eq hab hcont
  have heq2 : ∫ y in a..b, ∫ x in a..y, f (P2 (x, y)) = ∫ y in a..b, ∫ x in a..y, f (x, y) := by
    simpa [Function.comp_apply, P1, P2] using (tri2_cyclic_integral_eq hab hP1_cont).trans heq1
  have hpt : ∀ p ∈ T, f ((2 * a + b) / 3, (a + 2 * b) / 3) ≤ (f p + f (P1 p) + f (P2 p)) / 3 := by
    intro ⟨x, y⟩ hp
    have hp1 : P1 (x, y) ∈ T := hP1_maps _ hp
    have hp2 : P2 (x, y) ∈ T := hP1_maps _ hp1
    have hmid_mem : (1 / 2 : ℝ) • P1 (x, y) + (1 / 2 : ℝ) • P2 (x, y) ∈ T :=
      hconv.1 hp1 hp2 (by norm_num) (by norm_num) (by norm_num)
    have h12 := hconv.2 hp1 hp2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h012 := hconv.2 hp hmid_mem (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
    have hcent : (1 / 3 : ℝ) • (x, y) + (2 / 3 : ℝ) • ((1 / 2 : ℝ) • P1 (x, y) + (1 / 2 : ℝ) • P2 (x, y)) =
        ((2 * a + b) / 3, (a + 2 * b) / 3) := by
      ext <;> dsimp [P1, P2] <;> ring
    rw [hcent] at h012
    simp only [smul_eq_mul] at h12 h012
    linarith
  have h_int : ∀ g : ℝ × ℝ → ℝ, ContinuousOn g T →
      IntervalIntegrable (fun y => ∫ x in a..y, g (x, y)) volume a b := by
    intro g hg
    have hT_comp : IsCompact T := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hT_meas : MeasurableSet T := hT_comp.isClosed.measurableSet
    have hint_prod : IntegrableOn (T.indicator g) (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
      refine integrableOn_indicator_of_subset hT_meas (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
      exact hg.integrableOn_compact hT_comp
    have hint_snd := integrableOn_setIntegral_left hint_prod
    have h_ae : ∀ y ∈ Icc a b, ∫ x in a..y, g (x, y) = ∫ x in Icc a b, (T.indicator g) (x, y) := by
      intro y hy
      have heq_fn : ∀ x ∈ Icc a b, (T.indicator g) (x, y) = ({x : ℝ | x ≤ y}).indicator (fun x => g (x, y)) x := by
        intro x hx; by_cases hxy : x ≤ y <;> simp [T, hx.1, hx.2, hy.1, hy.2, hxy]
      rw [setIntegral_congr_fun measurableSet_Icc heq_fn,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a b ∩ {x : ℝ | x ≤ y} = Icc a y := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hy.2⟩, h2⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.1]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (IntegrableOn.congr_fun hint_snd
        (fun y hy => (h_ae y hy).symm) measurableSet_Icc)
  have hcomb_cont : ContinuousOn (fun p => (f p + f (P1 p) + f (P2 p)) / 3) T :=
    ((hcont.add hP1_cont).add hP2_cont).div_const 3
  have hle : ∫ y in a..b, ∫ _ in a..y, f ((2 * a + b) / 3, (a + 2 * b) / 3) ≤
      ∫ y in a..b, ∫ x in a..y, (f (x, y) + f (P1 (x, y)) + f (P2 (x, y))) / 3 := by
    apply intervalIntegral.integral_mono_on hab
      (by
        simp_rw [intervalIntegral.integral_const, smul_eq_mul]
        exact ((continuousOn_id.sub continuousOn_const).mul continuousOn_const).intervalIntegrable_of_Icc hab)
      (h_int _ hcomb_cont)
    intro y hy
    have hc0 : ContinuousOn (fun x => f (x, y)) (Icc a y) :=
      hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)
    have hc1 : ContinuousOn (fun x => f (P1 (x, y))) (Icc a y) :=
      hP1_cont.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)
    have hc2 : ContinuousOn (fun x => f (P2 (x, y))) (Icc a y) :=
      hP2_cont.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)
    apply intervalIntegral.integral_mono_on hy.1 intervalIntegrable_const
      (((hc0.add hc1).add hc2).div_const 3 |>.intervalIntegrable_of_Icc hy.1)
    intro x hx; exact hpt (x, y) ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩
  have hlhs_eval : ∫ y in a..b, ∫ _ in a..y, f ((2 * a + b) / 3, (a + 2 * b) / 3) =
      ((b - a) ^ 2 / 2) * f ((2 * a + b) / 3, (a + 2 * b) / 3) := by
    simp_rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have hd : ∀ y ∈ uIcc a b, HasDerivAt (fun t : ℝ => (t - a) ^ 2 / 2) (y - a) y := by
      intro y _
      refine ((((hasDerivAt_id y).sub (hasDerivAt_const y a)).pow 2).div_const 2).congr_deriv ?_; simp only [Pi.sub_apply, id_eq]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuousOn_id.sub continuousOn_const).intervalIntegrable_of_Icc hab)]
    ring
  have hrhs_eval : ∫ y in a..b, ∫ x in a..y, (f (x, y) + f (P1 (x, y)) + f (P2 (x, y))) / 3 =
      ∫ y in a..b, ∫ x in a..y, f (x, y) := by
    have hstep : ∀ y ∈ Icc a b,
        ∫ x in a..y, (f (x, y) + f (P1 (x, y)) + f (P2 (x, y))) / 3 =
        ((∫ x in a..y, f (x, y)) + (∫ x in a..y, f (P1 (x, y))) + (∫ x in a..y, f (P2 (x, y)))) / 3 := by
      intro y hy
      have i0 : IntervalIntegrable (fun x => f (x, y)) volume a y :=
        (hcont.comp (continuousOn_id.prodMk continuousOn_const)
          (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)).intervalIntegrable_of_Icc hy.1
      have i1 : IntervalIntegrable (fun x => f (P1 (x, y))) volume a y :=
        (hP1_cont.comp (continuousOn_id.prodMk continuousOn_const)
          (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)).intervalIntegrable_of_Icc hy.1
      have i2 : IntervalIntegrable (fun x => f (P2 (x, y))) volume a y :=
        (hP2_cont.comp (continuousOn_id.prodMk continuousOn_const)
          (fun x hx => ⟨⟨hx.1, le_trans hx.2 hy.2⟩, hy, hx.2⟩)).intervalIntegrable_of_Icc hy.1
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add (i0.add i1) i2,
          intervalIntegral.integral_add i0 i1]
    rw [intervalIntegral.integral_congr (fun y hy => hstep y (by rwa [uIcc_of_le hab] at hy)),
        intervalIntegral.integral_div,
        intervalIntegral.integral_add ((h_int _ hcont).add (h_int (fun p => f (P1 p)) hP1_cont)) (h_int (fun p => f (P2 p)) hP2_cont),
        intervalIntegral.integral_add (h_int _ hcont) (h_int (fun p => f (P1 p)) hP1_cont), heq1, heq2]
    ring
  linarith

/-! ### Part 3B: 3D Simplex Hermite-Hadamard & Jensen at Centroid -/

private lemma hh3_simp {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ × ℝ → ℝ}
    (hconv : ConvexOn ℝ {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2} f)
    (hcont : ContinuousOn f {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}) :
    ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) ≤
      ((b - a) ^ 3 / 24) * (f (a, a, a) + f (a, a, b) + f (a, b, b) + f (b, b, b)) := by
  by_cases hlt : a = b
  · subst hlt; simp
  have hab' : a < b := lt_of_le_of_ne hab hlt
  have hba : 0 < b - a := sub_pos.mpr hab'
  set S : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
  have hinner : ∀ z ∈ Icc a b,
      ∫ y in a..z, ∫ x in a..y, f (x, y, z) ≤
        ((z - a) ^ 2 / 6) * (f (a, a, z) + f (a, z, z) + f (z, z, z)) := by
    intro z hz
    refine hh2_tri hz.1 (f := fun p : ℝ × ℝ => f (p.1, p.2, z)) ?_ ?_
    · refine ⟨?_, ?_⟩
      · exact convex_tri2 _ _
      · intro p hp q hq u v hu hv huv
        have hpS : (p.1, p.2, z) ∈ S := ⟨⟨hp.1.1, le_trans hp.1.2 hz.2⟩, ⟨hp.2.1.1, le_trans hp.2.1.2 hz.2⟩, hz, hp.2.2, hp.2.1.2⟩
        have hqS : (q.1, q.2, z) ∈ S := ⟨⟨hq.1.1, le_trans hq.1.2 hz.2⟩, ⟨hq.2.1.1, le_trans hq.2.1.2 hz.2⟩, hz, hq.2.2, hq.2.1.2⟩
        have h := hconv.2 hpS hqS hu hv huv
        have hpt : (u • (p.1, p.2, z) + v • (q.1, q.2, z)) = (u * p.1 + v * q.1, u * p.2 + v * q.2, z) := by
          ext <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
        rw [hpt] at h; simpa [smul_eq_mul] using h
    · exact hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun p hp => ⟨⟨hp.1.1, le_trans hp.1.2 hz.2⟩, ⟨hp.2.1.1, le_trans hp.2.1.2 hz.2⟩, hz, hp.2.2, hp.2.1.2⟩)
  have hlin : ∀ z ∈ Icc a b,
      f (a, a, z) + f (a, z, z) + f (z, z, z) ≤
        ((b - z) / (b - a)) * (3 * f (a, a, a)) +
        ((z - a) / (b - a)) * (f (a, a, b) + f (a, b, b) + f (b, b, b)) := by
    intro z hz
    have w0 : 0 ≤ (b - z) / (b - a) := div_nonneg (sub_nonneg.mpr hz.2) (le_of_lt hba)
    have w1 : 0 ≤ (z - a) / (b - a) := div_nonneg (sub_nonneg.mpr hz.1) (le_of_lt hba)
    have hw : (b - z) / (b - a) + (z - a) / (b - a) = 1 := by field_simp; ring
    have haaa : (a, a, a) ∈ S := ⟨left_mem_Icc.mpr hab, left_mem_Icc.mpr hab, left_mem_Icc.mpr hab, le_refl a, le_refl a⟩
    have haab : (a, a, b) ∈ S := ⟨left_mem_Icc.mpr hab, left_mem_Icc.mpr hab, right_mem_Icc.mpr hab, le_refl a, hab⟩
    have habb : (a, b, b) ∈ S := ⟨left_mem_Icc.mpr hab, right_mem_Icc.mpr hab, right_mem_Icc.mpr hab, hab, le_refl b⟩
    have hbbb : (b, b, b) ∈ S := ⟨right_mem_Icc.mpr hab, right_mem_Icc.mpr hab, right_mem_Icc.mpr hab, le_refl b, le_refl b⟩
    have h1 := hconv.2 haaa haab w0 w1 hw
    have h2 := hconv.2 haaa habb w0 w1 hw
    have h3 := hconv.2 haaa hbbb w0 w1 hw
    have e1 : ((b - z) / (b - a)) • (a, a, a) + ((z - a) / (b - a)) • (a, a, b) = (a, a, z) := by
      ext <;> simp [smul_eq_mul] <;> field_simp <;> ring
    have e2 : ((b - z) / (b - a)) • (a, a, a) + ((z - a) / (b - a)) • (a, b, b) = (a, z, z) := by
      ext <;> simp [smul_eq_mul] <;> field_simp <;> ring
    have e3 : ((b - z) / (b - a)) • (a, a, a) + ((z - a) / (b - a)) • (b, b, b) = (z, z, z) := by
      ext <;> simp [smul_eq_mul] <;> field_simp <;> ring
    rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
    simp only [smul_eq_mul] at h1 h2 h3
    linarith
  have hS_comp : IsCompact S := by
    refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
        ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
          ((isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
            (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))))
  have hS_meas : MeasurableSet S := hS_comp.isClosed.measurableSet
  have houter_int : IntervalIntegrable (fun z => ∫ y in a..z, ∫ x in a..y, f (x, y, z)) volume a b := by
    have hint3 : IntegrableOn (S.indicator f) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) (volume.prod (volume.prod volume)) := by
      refine integrableOn_indicator_of_subset hS_meas (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
      exact hcont.integrableOn_compact hS_comp
    have hmp := measurePreserving_sw3
    have hint3' : IntegrableOn ((S.indicator f) ∘ sw3.symm) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b))
        (volume.prod (volume.prod volume)) := by
      have hpre : sw3.symm ⁻¹' (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) = Icc a b ×ˢ (Icc a b ×ˢ Icc a b) := by
        ext ⟨z, x, y⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
      rw [← hpre]
      exact (hmp.symm.integrableOn_comp_preimage sw3.symm.measurableEmbedding).mpr hint3
    have h_z := integrableOn_setIntegral_right hint3'
    have h_ae : ∀ z ∈ Icc a b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) =
        ∫ q in Icc a b ×ˢ Icc a b, ((S.indicator f) ∘ sw3.symm) (z, q) ∂(volume.prod volume) := by
      intro z hz
      have hsub_int : IntegrableOn (fun q : ℝ × ℝ => ((S.indicator f) ∘ sw3.symm) (z, q))
          (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
        set Tz : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ∈ Icc a z ∧ q.2 ∈ Icc a z ∧ q.1 ≤ q.2}
        have hTz_comp : IsCompact Tz := by
          refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
          exact (isClosed_Icc.preimage continuous_fst).inter
            ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
        have hEq : ∀ q ∈ Icc a b ×ˢ Icc a b, ((S.indicator f) ∘ sw3.symm) (z, q) =
            Tz.indicator (fun q => f (q.1, q.2, z)) q := by
          intro ⟨x, y⟩ ⟨hx, hy⟩
          by_cases h : x ≤ y ∧ y ≤ z
          · simp [sw3_apply, sw3_symm_apply, S, Tz, hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, h.1, h.2, le_trans h.1 h.2]
          · have h1 : (x, y, z) ∉ S := fun hs => h ⟨hs.2.2.2.1, hs.2.2.2.2⟩
            have h2 : (x, y) ∉ Tz := fun ht => h ⟨ht.2.2, ht.2.1.2⟩
            simp [sw3_apply, sw3_symm_apply, h1, h2]
        rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
        refine integrableOn_indicator_of_subset hTz_comp.isClosed.measurableSet (fun q hq => ⟨⟨hq.1.1, le_trans hq.1.2 hz.2⟩, ⟨hq.2.1.1, le_trans hq.2.1.2 hz.2⟩⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun q hq => ⟨⟨hq.1.1, le_trans hq.1.2 hz.2⟩, ⟨hq.2.1.1, le_trans hq.2.1.2 hz.2⟩, hz, hq.2.2, hq.2.1.2⟩)).integrableOn_compact hTz_comp
      rw [setIntegral_prod_symm' _ hsub_int, MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hab]
      have hint_y := integrableOn_setIntegral_left hsub_int
      have hiy : IntervalIntegrable (fun y => ∫ x in Icc a b, ((S.indicator f) ∘ sw3.symm) (z, x, y)) volume a b :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint_y
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hiy.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hab]; exact hz)))
        (hiy.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hab]; exact hz)))]
      have hzero : ∫ y in z..b, ∫ x in Icc a b, ((S.indicator f) ∘ sw3.symm) (z, x, y) = 0 := by
        rw [intervalIntegral.integral_of_le hz.2]
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro y hy; apply setIntegral_eq_zero_of_forall_eq_zero; intro x _
        have hnot : (x, y, z) ∉ S := fun hs => not_lt_of_ge hs.2.2.2.2 hy.1
        simp [sw3_apply, sw3_symm_apply, hnot]
      rw [hzero, add_zero]
      symm
      apply intervalIntegral.integral_congr
      intro y hy; rw [uIcc_of_le hz.1] at hy; dsimp only
      have heq : ∀ x ∈ Icc a b, ((S.indicator f) ∘ sw3.symm) (z, x, y) =
          ({x : ℝ | x ≤ y}).indicator (fun x => f (x, y, z)) x := by
        intro x hx
        by_cases hxy : x ≤ y
        · simp [sw3_apply, sw3_symm_apply, S, hx.1, hx.2, hy.1, le_trans hy.2 hz.2, hz.1, hz.2, hxy, hy.2]
        · have h1 : (x, y, z) ∉ S := fun hs => hxy hs.2.2.2.1
          simp [sw3_apply, sw3_symm_apply, h1, hxy]
      rw [setIntegral_congr_fun measurableSet_Icc heq,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a b ∩ {x : ℝ | x ≤ y} = Icc a y := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 (le_trans hy.2 hz.2)⟩, h2⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.1]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (IntegrableOn.congr_fun h_z
        (fun z hz => (h_ae z hz).symm) measurableSet_Icc)
  let hRHS : ℝ → ℝ := fun z =>
    ((z - a) ^ 2 / 6) * (((b - z) / (b - a)) * (3 * f (a, a, a)) +
      ((z - a) / (b - a)) * (f (a, a, b) + f (a, b, b) + f (b, b, b)))
  have hhRHS_cont : ContinuousOn hRHS (Icc a b) := by dsimp only [hRHS]; fun_prop
  have hle : ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) ≤ ∫ z in a..b, hRHS z := by
    apply intervalIntegral.integral_mono_on hab houter_int (hhRHS_cont.intervalIntegrable_of_Icc hab)
    intro z hz
    have h1 := hinner z hz
    have h2 := hlin z hz
    have hnn : 0 ≤ (z - a) ^ 2 / 6 := by positivity
    dsimp only [hRHS]; nlinarith
  have heval : ∫ z in a..b, hRHS z =
      ((b - a) ^ 3 / 24) * (f (a, a, a) + f (a, a, b) + f (a, b, b) + f (b, b, b)) := by
    have hderiv : ∀ z ∈ uIcc a b,
        HasDerivAt (fun t : ℝ =>
          (((t - a) ^ 3 / 3 * (b - a) - (t - a) ^ 4 / 4) / (2 * (b - a))) * f (a, a, a) +
          (((t - a) ^ 4) / (24 * (b - a))) * (f (a, a, b) + f (a, b, b) + f (b, b, b))) (hRHS z) z := by
      intro z _
      have hd3 := ((hasDerivAt_id z).sub (hasDerivAt_const z a)).pow 3
      have hd4 := ((hasDerivAt_id z).sub (hasDerivAt_const z a)).pow 4
      have h1 : HasDerivAt (fun t : ℝ => ((t - a) ^ 3 / 3 * (b - a) - (t - a) ^ 4 / 4) / (2 * (b - a)))
          (((z - a) ^ 2 / 6) * ((b - z) / (b - a) * 3)) z := by
        refine ((((hd3.div_const 3).mul_const (b - a)).sub (hd4.div_const 4)).div_const (2 * (b - a))).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      have h2 : HasDerivAt (fun t : ℝ => (t - a) ^ 4 / (24 * (b - a)))
          (((z - a) ^ 2 / 6) * ((z - a) / (b - a))) z := by
        refine (hd4.div_const (24 * (b - a))).congr_deriv ?_
        simp only [Pi.sub_apply, id_eq]; field_simp; ring
      refine ((h1.mul_const _).add (h2.mul_const _)).congr_deriv ?_
      dsimp only [hRHS]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hhRHS_cont.intervalIntegrable_of_Icc hab)]
    field_simp; ring
  linarith

private lemma simp3_eq_setIntegral {a b : ℝ} (hab : a ≤ b) {g : ℝ × ℝ × ℝ → ℝ}
    (hg : ContinuousOn g {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}) :
    ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, g (x, y, z) =
      ∫ p in {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2},
        g p ∂(volume.prod (volume.prod volume)) := by
  set S : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
  have hS_comp : IsCompact S := by
    refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
        ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
          ((isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
            (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))))
  have hS_meas : MeasurableSet S := hS_comp.isClosed.measurableSet
  have hint3 : IntegrableOn (S.indicator g) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) (volume.prod (volume.prod volume)) := by
    refine integrableOn_indicator_of_subset hS_meas (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
    exact hg.integrableOn_compact hS_comp
  rw [← inter_eq_self_of_subset_right (show S ⊆ Icc a b ×ˢ (Icc a b ×ˢ Icc a b) from fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩),
      ← setIntegral_indicator hS_meas]
  have hmp := measurePreserving_sw3
  have hpre : sw3 ⁻¹' (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) = Icc a b ×ˢ (Icc a b ×ˢ Icc a b) := by
    ext ⟨x, y, z⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
  have htr : ∫ p in Icc a b ×ˢ (Icc a b ×ˢ Icc a b), S.indicator g p ∂(volume.prod (volume.prod volume)) =
      ∫ q in Icc a b ×ˢ (Icc a b ×ˢ Icc a b), (S.indicator g ∘ sw3.symm) q ∂(volume.prod (volume.prod volume)) := by
    have htr' := hmp.setIntegral_preimage_emb sw3.measurableEmbedding (S.indicator g ∘ sw3.symm) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b))
    rw [hpre] at htr'
    convert htr' using 2
    ext p; simp
  rw [htr]
  have hint3' : IntegrableOn (S.indicator g ∘ sw3.symm) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b))
      (volume.prod (volume.prod volume)) := by
    have hpre' : sw3.symm ⁻¹' (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) = Icc a b ×ˢ (Icc a b ×ˢ Icc a b) := by
      ext ⟨z, x, y⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
    rw [← hpre']
    exact (hmp.symm.integrableOn_comp_preimage sw3.symm.measurableEmbedding).mpr hint3
  rw [MeasureTheory.setIntegral_prod _ hint3', MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro z hz; rw [uIcc_of_le hab] at hz; dsimp only
  have hsub_int : IntegrableOn (fun q : ℝ × ℝ => (S.indicator g ∘ sw3.symm) (z, q))
      (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
    set Tz : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a z ∧ q.2 ∈ Icc a z ∧ q.1 ≤ q.2}
    have hTz_comp : IsCompact Tz := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hEq : ∀ q ∈ Icc a b ×ˢ Icc a b, (S.indicator g ∘ sw3.symm) (z, q) = Tz.indicator (fun q => g (q.1, q.2, z)) q := by
      intro ⟨x, y⟩ ⟨hx, hy⟩
      by_cases h : x ≤ y ∧ y ≤ z
      · simp [sw3_apply, sw3_symm_apply, S, Tz, hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, h.1, h.2, le_trans h.1 h.2]
      · have h1 : (x, y, z) ∉ S := fun hs => h ⟨hs.2.2.2.1, hs.2.2.2.2⟩
        have h2 : (x, y) ∉ Tz := fun ht => h ⟨ht.2.2, ht.2.1.2⟩
        simp [sw3_apply, sw3_symm_apply, h1, h2]
    rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
    refine integrableOn_indicator_of_subset hTz_comp.isClosed.measurableSet (fun q hq => ⟨⟨hq.1.1, le_trans hq.1.2 hz.2⟩, ⟨hq.2.1.1, le_trans hq.2.1.2 hz.2⟩⟩) ?_
    exact (hg.comp (Continuous.continuousOn (by fun_prop))
      (fun q hq => ⟨⟨hq.1.1, le_trans hq.1.2 hz.2⟩, ⟨hq.2.1.1, le_trans hq.2.1.2 hz.2⟩, hz, hq.2.2, hq.2.1.2⟩)).integrableOn_compact hTz_comp
  rw [setIntegral_prod_symm' _ hsub_int, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  have hint_y := integrableOn_setIntegral_left hsub_int
  have hiy : IntervalIntegrable (fun y => ∫ x in Icc a b, (S.indicator g ∘ sw3.symm) (z, x, y)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint_y
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hiy.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hab]; exact hz)))
    (hiy.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hab]; exact hz)))]
  have hz0 : ∫ y in z..b, ∫ x in Icc a b, (S.indicator g ∘ sw3.symm) (z, x, y) = 0 := by
    rw [intervalIntegral.integral_of_le hz.2]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy; apply setIntegral_eq_zero_of_forall_eq_zero; intro x _
    have hnot : (x, y, z) ∉ S := fun hs => not_lt_of_ge hs.2.2.2.2 hy.1
    simp [sw3_apply, sw3_symm_apply, hnot]
  rw [hz0, add_zero]
  symm
  apply intervalIntegral.integral_congr
  intro y hy; rw [uIcc_of_le hz.1] at hy; dsimp only
  have heq : ∀ x ∈ Icc a b, (S.indicator g ∘ sw3.symm) (z, x, y) =
      ({x : ℝ | x ≤ y}).indicator (fun x => g (x, y, z)) x := by
    intro x hx
    by_cases hxy : x ≤ y
    · simp [sw3_apply, sw3_symm_apply, S, hx.1, hx.2, hy.1, le_trans hy.2 hz.2, hz.1, hz.2, hxy, hy.2]
    · have h1 : (x, y, z) ∉ S := fun hs => hxy hs.2.2.2.1
      simp [sw3_apply, sw3_symm_apply, h1, hxy]
  rw [setIntegral_congr_fun measurableSet_Icc heq,
      setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
  have hcap : Icc a b ∩ {x : ℝ | x ≤ y} = Icc a y := by
    ext x; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 (le_trans hy.2 hz.2)⟩, h2⟩
  rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.1]

private lemma simp3_cyclic_integral_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}) :
    ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (a + b - z, b + x - z, b + y - z) =
      ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) := by
  set S : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
  have hinner : ∀ z ∈ Icc a b,
      ∫ y in a..z, ∫ x in a..y, f (a + b - z, b + x - z, b + y - z) =
        ∫ v in (a + b - z)..b, ∫ u in (a + b - z)..v, f (a + b - z, u, v) := by
    intro z hz
    have hx_tr : ∀ y ∈ Icc a z,
        ∫ x in a..y, f (a + b - z, b + x - z, b + y - z) =
          ∫ u in (a + b - z)..(b + y - z), f (a + b - z, u, b + y - z) := by
      intro y _
      have hfn : (fun x : ℝ => f (a + b - z, b + x - z, b + y - z)) =
          (fun x : ℝ => f (a + b - z, x + (b - z), b + y - z)) := by ext x; ring_nf
      rw [hfn, intervalIntegral.integral_comp_add_right (fun u => f (a + b - z, u, b + y - z)) (b - z)]
      congr 1 <;> ring
    rw [intervalIntegral.integral_congr (fun y hy => hx_tr y (by rwa [uIcc_of_le hz.1] at hy))]
    have hy_fn : (fun y : ℝ => ∫ u in (a + b - z)..(b + y - z), f (a + b - z, u, b + y - z)) =
        (fun y : ℝ => ∫ u in (a + b - z)..(y + (b - z)), f (a + b - z, u, y + (b - z))) := by
      ext y; ring_nf
    rw [hy_fn, intervalIntegral.integral_comp_add_right (fun v => ∫ u in (a + b - z)..v, f (a + b - z, u, v)) (b - z)]
    congr 1 <;> ring
  rw [intervalIntegral.integral_congr (fun z hz => hinner z (by rwa [uIcc_of_le hab] at hz))]
  rw [show (∫ z in a..b, ∫ v in (a + b - z)..b, ∫ u in (a + b - z)..v, f (a + b - z, u, v)) =
          ∫ w in a..b, ∫ v in w..b, ∫ u in w..v, f (w, u, v) by
        rw [intervalIntegral.integral_comp_sub_left (fun w => ∫ v in w..b, ∫ u in w..v, f (w, u, v)) (a + b)]
        congr 1 <;> ring]
  rw [simp3_eq_setIntegral hab hcont]
  change _ = ∫ p in S, f p ∂(volume.prod (volume.prod volume))
  have hS_comp : IsCompact S := by
    refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
        ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
          ((isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
            (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))))
  have hS_meas : MeasurableSet S := hS_comp.isClosed.measurableSet
  have hint3 : IntegrableOn (S.indicator f) (Icc a b ×ˢ (Icc a b ×ˢ Icc a b)) (volume.prod (volume.prod volume)) := by
    refine integrableOn_indicator_of_subset hS_meas (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
    exact hcont.integrableOn_compact hS_comp
  rw [← inter_eq_self_of_subset_right (show S ⊆ Icc a b ×ˢ (Icc a b ×ˢ Icc a b) from fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩),
      ← setIntegral_indicator hS_meas, MeasureTheory.setIntegral_prod _ hint3,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro w hw; rw [uIcc_of_le hab] at hw; dsimp only
  have hint_uv : IntegrableOn (fun q : ℝ × ℝ => S.indicator f (w, q.1, q.2)) (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
    set Tw : Set (ℝ × ℝ) := {q | q.1 ∈ Icc w b ∧ q.2 ∈ Icc w b ∧ q.1 ≤ q.2}
    have hTw_comp : IsCompact Tw := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hEq : ∀ q ∈ Icc a b ×ˢ Icc a b, S.indicator f (w, q.1, q.2) = Tw.indicator (fun q => f (w, q.1, q.2)) q := by
      intro ⟨u, v⟩ ⟨hu, hv⟩
      by_cases h : w ≤ u ∧ u ≤ v
      · simp [S, Tw, hw.1, hw.2, hu.1, hu.2, hv.1, hv.2, h.1, h.2, le_trans h.1 h.2]
      · have h1 : (w, u, v) ∉ S := fun hs => h ⟨hs.2.2.2.1, hs.2.2.2.2⟩
        have h2 : (u, v) ∉ Tw := fun ht => h ⟨ht.1.1, ht.2.2⟩
        simp [h1, h2]
    rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
    refine integrableOn_indicator_of_subset hTw_comp.isClosed.measurableSet (fun q hq => ⟨⟨le_trans hw.1 hq.1.1, hq.1.2⟩, ⟨le_trans hw.1 hq.2.1.1, hq.2.1.2⟩⟩) ?_
    exact (hcont.comp (Continuous.continuousOn (by fun_prop))
      (fun q hq => ⟨hw, ⟨le_trans hw.1 hq.1.1, hq.1.2⟩, ⟨le_trans hw.1 hq.2.1.1, hq.2.1.2⟩, hq.1.1, hq.2.2⟩)).integrableOn_compact hTw_comp
  rw [setIntegral_prod_symm' _ hint_uv, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  have hint_v := integrableOn_setIntegral_left hint_uv
  have hiv : IntervalIntegrable (fun v => ∫ u in Icc a b, S.indicator f (w, u, v)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint_v
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hiv.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hab]; exact hw)))
    (hiv.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hab]; exact hw)))]
  have hz0 : ∫ v in a..w, ∫ u in Icc a b, S.indicator f (w, u, v) = 0 := by
    rw [intervalIntegral.integral_of_le hw.1]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    by_cases hvw : v = w
    · subst hvw
      have hsub : ∀ u ∈ Icc a b, u ≠ v → S.indicator f (v, u, v) = 0 := by
        intro u _ hne; have : (v, u, v) ∉ S := fun hs => hne (le_antisymm hs.2.2.2.2 hs.2.2.2.1); simp [this]
      have hae : ∀ᵐ u ∂volume, u ∈ Icc a b → S.indicator f (v, u, v) = 0 := by
        filter_upwards [show ∀ᵐ u : ℝ, u ≠ v by simp [ae_iff]] with u hne hu
        exact hsub u hu hne
      rw [setIntegral_congr_ae measurableSet_Icc hae]; simp
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro u _
      have hnot : (w, u, v) ∉ S := fun hs => hvw (le_antisymm hv.2 (le_trans hs.2.2.2.1 hs.2.2.2.2))
      simp [hnot]
  rw [hz0, zero_add]
  symm
  apply intervalIntegral.integral_congr
  intro v hv; rw [uIcc_of_le hw.2] at hv; dsimp only
  have heq : ∀ u ∈ Icc a b, S.indicator f (w, u, v) = (Icc w v).indicator (fun u => f (w, u, v)) u := by
    intro u hu
    by_cases h : w ≤ u ∧ u ≤ v
    · simp [S, hw.1, hw.2, hu.1, hu.2, le_trans hw.1 hv.1, hv.2, h.1, h.2]
    · have h1 : (w, u, v) ∉ S := fun hs => h ⟨hs.2.2.2.1, hs.2.2.2.2⟩
      have h2 : u ∉ Icc w v := fun hu' => h hu'
      simp [h1, h2]
  rw [setIntegral_congr_fun measurableSet_Icc heq, setIntegral_indicator measurableSet_Icc]
  have hcap : Icc a b ∩ Icc w v = Icc w v :=
    inter_eq_self_of_subset_right (fun u hu => ⟨le_trans hw.1 hu.1, le_trans hu.2 hv.2⟩)
  rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv.1]

private lemma jensen3_simp {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ × ℝ → ℝ}
    (hconv : ConvexOn ℝ {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2} f)
    (hcont : ContinuousOn f {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}) :
    ((b - a) ^ 3 / 6) * f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) ≤
      ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) := by
  set S : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2.1 ∈ Icc a b ∧ p.2.2 ∈ Icc a b ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
  let Q1 : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (a + b - p.2.2, b + p.1 - p.2.2, b + p.2.1 - p.2.2)
  let Q2 : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => Q1 (Q1 p)
  let Q3 : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => Q1 (Q2 p)
  have hQ1_maps : ∀ p ∈ S, Q1 p ∈ S := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz, hxy, hyz⟩
    exact ⟨⟨by linarith [hz.2], by linarith [hz.1]⟩,
           ⟨by linarith [hx.1, hz.2], by linarith⟩,
           ⟨by linarith [hy.1, hz.2], by linarith⟩,
           by linarith [hx.1], by linarith⟩
  have hQ1_cont : ContinuousOn (fun p => f (Q1 p)) S :=
    hcont.comp (Continuous.continuousOn (by dsimp only [Q1]; fun_prop)) hQ1_maps
  have hQ2_cont : ContinuousOn (fun p => f (Q2 p)) S :=
    hQ1_cont.comp (Continuous.continuousOn (by dsimp only [Q1]; fun_prop)) hQ1_maps
  have hQ3_cont : ContinuousOn (fun p => f (Q3 p)) S :=
    hQ2_cont.comp (Continuous.continuousOn (by dsimp only [Q1]; fun_prop)) hQ1_maps
  have heq1 := simp3_cyclic_integral_eq hab hcont
  have heq2 : ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (Q2 (x, y, z)) =
      ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) := by
    simpa [Function.comp_apply, Q1, Q2] using (simp3_cyclic_integral_eq hab hQ1_cont).trans heq1
  have heq3 : ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (Q3 (x, y, z)) =
      ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) := by
    simpa [Function.comp_apply, Q1, Q2, Q3] using (simp3_cyclic_integral_eq hab hQ2_cont).trans heq2
  have hpt : ∀ p ∈ S, f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) ≤
      (f p + f (Q1 p) + f (Q2 p) + f (Q3 p)) / 4 := by
    intro ⟨x, y, z⟩ hp
    have hp1 := hQ1_maps _ hp
    have hp2 := hQ1_maps _ hp1
    have hp3 := hQ1_maps _ hp2
    have hm01_mem := hconv.1 hp hp1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hm23_mem := hconv.1 hp2 hp3 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h01 := hconv.2 hp hp1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h23 := hconv.2 hp2 hp3 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hall := hconv.2 hm01_mem hm23_mem (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hcent : (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x, y, z) + (1 / 2 : ℝ) • Q1 (x, y, z)) +
        (1 / 2 : ℝ) • ((1 / 2 : ℝ) • Q2 (x, y, z) + (1 / 2 : ℝ) • Q3 (x, y, z)) =
        ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) := by
      ext <;> dsimp [Q1, Q2, Q3] <;> ring
    rw [hcent] at hall; simp only [smul_eq_mul] at h01 h23 hall; linarith
  have hS_comp : IsCompact S := by
    refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
        ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
          ((isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
            (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))))
  have hS_meas : MeasurableSet S := hS_comp.isClosed.measurableSet
  have hle_S : ∫ _ in S, f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) ∂(volume.prod (volume.prod volume)) ≤
      ∫ p in S, ((f p + f (Q1 p) + f (Q2 p) + f (Q3 p)) / 4) ∂(volume.prod (volume.prod volume)) :=
    setIntegral_mono_on (continuousOn_const.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp)
      ((((hcont.add hQ1_cont).add hQ2_cont).add hQ3_cont).div_const 4 |>.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp)
      hS_meas hpt
  have hlhs_S : ∫ _ in S, f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) ∂(volume.prod (volume.prod volume)) =
      ((b - a) ^ 3 / 6) * f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) := by
    rw [← simp3_eq_setIntegral hab continuousOn_const]
    simp_rw [intervalIntegral.integral_const, smul_eq_mul]
    have hmid : ∀ z ∈ Icc a b, ∫ y in a..z, (y - a) * f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) =
        ((z - a) ^ 2 / 2) * f ((3 * a + b) / 4, (a + b) / 2, (a + 3 * b) / 4) := by
      intro z hz
      rw [intervalIntegral.integral_mul_const]
      have hd : ∀ y ∈ uIcc a z, HasDerivAt (fun t : ℝ => (t - a) ^ 2 / 2) (y - a) y := by
        intro y _
        refine ((((hasDerivAt_id y).sub (hasDerivAt_const y a)).pow 2).div_const 2).congr_deriv ?_; simp only [Pi.sub_apply, id_eq]; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuousOn_id.sub continuousOn_const).intervalIntegrable_of_Icc hz.1)]; ring
    rw [intervalIntegral.integral_congr (fun z hz => hmid z (by rwa [uIcc_of_le hab] at hz)),
        intervalIntegral.integral_mul_const]
    have hd : ∀ z ∈ uIcc a b, HasDerivAt (fun t : ℝ => (t - a) ^ 3 / 6) ((z - a) ^ 2 / 2) z := by
      intro z _
      refine ((((hasDerivAt_id z).sub (hasDerivAt_const z a)).pow 3).div_const 6).congr_deriv ?_; simp only [Pi.sub_apply, id_eq]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((continuousOn_id.sub continuousOn_const).pow 2 |>.div_const 2).intervalIntegrable_of_Icc hab)]; ring
  have hrhs_S : ∫ p in S, ((f p + f (Q1 p) + f (Q2 p) + f (Q3 p)) / 4) ∂(volume.prod (volume.prod volume)) =
      ∫ z in a..b, ∫ y in a..z, ∫ x in a..y, f (x, y, z) := by
    have i0 := hcont.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp
    have i1 := hQ1_cont.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp
    have i2 := hQ2_cont.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp
    have i3 := hQ3_cont.integrableOn_compact (μ := volume.prod (volume.prod volume)) hS_comp
    have i01 : IntegrableOn (fun p => f p + f (Q1 p)) S (volume.prod (volume.prod volume)) := i0.add i1
    have i012 : IntegrableOn (fun p => f p + f (Q1 p) + f (Q2 p)) S (volume.prod (volume.prod volume)) := i01.add i2
    rw [integral_div, integral_add i012 i3, integral_add i01 i2, integral_add i0 i1,
        ← simp3_eq_setIntegral hab hcont, ← simp3_eq_setIntegral hab hQ1_cont,
        ← simp3_eq_setIntegral hab hQ2_cont, ← simp3_eq_setIntegral hab hQ3_cont]
    rw [heq1, heq2, heq3]; ring
  linarith

/-! ### Part 4: `cell3Set`, `cell4Set`, HH & Jensen for all 4 `CellKind`s -/

lemma volume_preserving_equivFin4_3 :
    MeasurePreserving equivFin4_3 (volume : Measure (Fin 4 → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ))) :=
  MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 3

private def equivFin3_prod : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow))

private lemma volume_preserving_equivFin3_prod :
    MeasurePreserving equivFin3_prod (volume : Measure (Fin 3 → ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
  (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_finTwoArrow ℝ))

private lemma equivFin3_prod_apply (x : Fin 3 → ℝ) :
    equivFin3_prod x = (x 0, (x 1, x 2)) := rfl

lemma equivFin4_3_apply (x : Fin 4 → ℝ) :
    equivFin4_3 x = (x 3, ![x 0, x 1, x 2]) := by
  ext
  · rfl
  · rename_i i; fin_cases i <;> rfl

lemma cell4Set_eq_preimage (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 =
      equivFin4_3 ⁻¹' (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2) := by
  ext x
  cases knd <;>
    simp only [cell4Set, cell3Set, mem_preimage, mem_prod, equivFin4_3_apply,
      mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> tauto

lemma cell3Set_isClosed (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    IsClosed (cell3Set knd a0 b0 a1 b1 a2 b2) := by
  have hc0 : ∀ l r : ℝ, IsClosed {x : Fin 3 → ℝ | x 0 ∈ Icc l r} := fun l r => isClosed_Icc.preimage (continuous_apply 0)
  have hc1 : ∀ l r : ℝ, IsClosed {x : Fin 3 → ℝ | x 1 ∈ Icc l r} := fun l r => isClosed_Icc.preimage (continuous_apply 1)
  have hc2 : ∀ l r : ℝ, IsClosed {x : Fin 3 → ℝ | x 2 ∈ Icc l r} := fun l r => isClosed_Icc.preimage (continuous_apply 2)
  have h01 : IsClosed {x : Fin 3 → ℝ | x 0 ≤ x 1} := isClosed_le (continuous_apply 0) (continuous_apply 1)
  have h12 : IsClosed {x : Fin 3 → ℝ | x 1 ≤ x 2} := isClosed_le (continuous_apply 1) (continuous_apply 2)
  cases knd with
  | box => exact (hc0 a0 b0).inter ((hc1 a1 b1).inter (hc2 a2 b2))
  | tri01 => exact (hc0 a0 b0).inter ((hc1 a0 b0).inter ((hc2 a2 b2).inter h01))
  | tri12 => exact (hc0 a0 b0).inter ((hc1 a1 b1).inter ((hc2 a1 b1).inter h12))
  | simp => exact (hc0 a0 b0).inter ((hc1 a0 b0).inter ((hc2 a0 b0).inter (h01.inter h12)))

lemma cell3Set_isCompact (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    IsCompact (cell3Set knd a0 b0 a1 b1 a2 b2) := by
  have hb : ∀ l0 r0 l1 r1 l2 r2 : ℝ, IsCompact (Set.univ.pi ![Icc l0 r0, Icc l1 r1, Icc l2 r2]) :=
    fun l0 r0 l1 r1 l2 r2 => isCompact_univ_pi fun j => by fin_cases j <;> exact isCompact_Icc
  cases knd with
  | box => refine (hb a0 b0 a1 b1 a2 b2).of_isClosed_subset (cell3Set_isClosed .box _ _ _ _ _ _) ?_
           intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2]
  | tri01 => refine (hb a0 b0 a0 b0 a2 b2).of_isClosed_subset (cell3Set_isClosed .tri01 _ _ _ _ _ _) ?_
             intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1]
  | tri12 => refine (hb a0 b0 a1 b1 a1 b1).of_isClosed_subset (cell3Set_isClosed .tri12 _ _ _ _ _ _) ?_
             intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1]
  | simp => refine (hb a0 b0 a0 b0 a0 b0).of_isClosed_subset (cell3Set_isClosed .simp _ _ _ _ _ _) ?_
            intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1]

lemma cell4Set_isClosed (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    IsClosed (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := by
  have hc : ∀ (i : Fin 4) (l r : ℝ), IsClosed {x : Fin 4 → ℝ | x i ∈ Icc l r} :=
    fun i l r => isClosed_Icc.preimage (continuous_apply i)
  have h01 : IsClosed {x : Fin 4 → ℝ | x 0 ≤ x 1} := isClosed_le (continuous_apply 0) (continuous_apply 1)
  have h12 : IsClosed {x : Fin 4 → ℝ | x 1 ≤ x 2} := isClosed_le (continuous_apply 1) (continuous_apply 2)
  cases knd with
  | box => exact (hc 0 a0 b0).inter ((hc 1 a1 b1).inter ((hc 2 a2 b2).inter (hc 3 a3 b3)))
  | tri01 => exact (hc 0 a0 b0).inter ((hc 1 a0 b0).inter ((hc 2 a2 b2).inter ((hc 3 a3 b3).inter h01)))
  | tri12 => exact (hc 0 a0 b0).inter ((hc 1 a1 b1).inter ((hc 2 a1 b1).inter ((hc 3 a3 b3).inter h12)))
  | simp => exact (hc 0 a0 b0).inter ((hc 1 a0 b0).inter ((hc 2 a0 b0).inter ((hc 3 a3 b3).inter (h01.inter h12))))

lemma cell4Set_isCompact (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    IsCompact (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := by
  have hb : ∀ l0 r0 l1 r1 l2 r2 l3 r3 : ℝ, IsCompact (Set.univ.pi ![Icc l0 r0, Icc l1 r1, Icc l2 r2, Icc l3 r3]) :=
    fun l0 r0 l1 r1 l2 r2 l3 r3 => isCompact_univ_pi fun j => by fin_cases j <;> exact isCompact_Icc
  have hcl := cell4Set_isClosed knd a0 b0 a1 b1 a2 b2 a3 b3
  cases knd with
  | box => refine (hb a0 b0 a1 b1 a2 b2 a3 b3).of_isClosed_subset hcl ?_
           intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1; simpa using hx.2.2.2]
  | tri01 => refine (hb a0 b0 a0 b0 a2 b2 a3 b3).of_isClosed_subset hcl ?_
             intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1; simpa using hx.2.2.2.1]
  | tri12 => refine (hb a0 b0 a1 b1 a1 b1 a3 b3).of_isClosed_subset hcl ?_
             intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1; simpa using hx.2.2.2.1]
  | simp => refine (hb a0 b0 a0 b0 a0 b0 a3 b3).of_isClosed_subset hcl ?_
            intro x hx j _; fin_cases j <;> [simpa using hx.1; simpa using hx.2.1; simpa using hx.2.2.1; simpa using hx.2.2.2.1]

lemma cell3Set_convex (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) :
    Convex ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) := by
  intro x hx y hy u v hu hv huv
  have hIcc : ∀ {l r p q : ℝ}, p ∈ Icc l r → q ∈ Icc l r → u * p + v * q ∈ Icc l r :=
    fun {l r _ _} hp hq => by simpa only [smul_eq_mul] using convex_Icc l r hp hq hu hv huv
  have hle : ∀ {p1 p2 q1 q2 : ℝ}, p1 ≤ p2 → q1 ≤ q2 → u * p1 + v * q1 ≤ u * p2 + v * q2 :=
    fun hp hq => add_le_add (mul_le_mul_of_nonneg_left hp hu) (mul_le_mul_of_nonneg_left hq hv)
  cases knd with
  | box => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2 hy.2.2⟩
  | tri01 => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hle hx.2.2.2 hy.2.2.2⟩
  | tri12 => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hle hx.2.2.2 hy.2.2.2⟩
  | simp => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hle hx.2.2.2.1 hy.2.2.2.1, hle hx.2.2.2.2 hy.2.2.2.2⟩

lemma cell4Set_convex (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) :
    Convex ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) := by
  intro x hx y hy u v hu hv huv
  have hIcc : ∀ {l r p q : ℝ}, p ∈ Icc l r → q ∈ Icc l r → u * p + v * q ∈ Icc l r :=
    fun {l r _ _} hp hq => by simpa only [smul_eq_mul] using convex_Icc l r hp hq hu hv huv
  have hle : ∀ {p1 p2 q1 q2 : ℝ}, p1 ≤ p2 → q1 ≤ q2 → u * p1 + v * q1 ≤ u * p2 + v * q2 :=
    fun hp hq => add_le_add (mul_le_mul_of_nonneg_left hp hu) (mul_le_mul_of_nonneg_left hq hv)
  cases knd with
  | box => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hIcc hx.2.2.2 hy.2.2.2⟩
  | tri01 => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hIcc hx.2.2.2.1 hy.2.2.2.1, hle hx.2.2.2.2 hy.2.2.2.2⟩
  | tri12 => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hIcc hx.2.2.2.1 hy.2.2.2.1, hle hx.2.2.2.2 hy.2.2.2.2⟩
  | simp => exact ⟨hIcc hx.1 hy.1, hIcc hx.2.1 hy.2.1, hIcc hx.2.2.1 hy.2.2.1, hIcc hx.2.2.2.1 hy.2.2.2.1, hle hx.2.2.2.2.1 hy.2.2.2.2.1, hle hx.2.2.2.2.2 hy.2.2.2.2.2⟩

lemma integral_cell3_eq_iter (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    {f : (Fin 3 → ℝ) → ℝ} (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :
    ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x =
      match knd with
      | .box => ∫ x0 in a0..b0, ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2]
      | .tri01 => ∫ x2 in a2..b2, ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2]
      | .tri12 => ∫ x0 in a0..b0, ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2]
      | .simp => ∫ x2 in a0..b0, ∫ x1 in a0..x2, ∫ x0 in a0..x1, f ![x0, x1, x2] := by
  let g : ℝ × (ℝ × ℝ) → ℝ := fun p => f ![p.1, p.2.1, p.2.2]
  have hf_eq : f = g ∘ equivFin3_prod := by
    ext x; dsimp only [g, Function.comp_apply, equivFin3_prod_apply]
    congr 1; ext i; fin_cases i <;> rfl
  cases knd with
  | box =>
    have hpre : cell3Set .box a0 b0 a1 b1 a2 b2 = equivFin3_prod ⁻¹' (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2)) := by
      ext x; simp [cell3Set, equivFin3_prod_apply]; tauto
    dsimp only
    rw [hpre]
    conv_lhs => rw [hf_eq]
    simp_rw [Function.comp_apply]
    rw [volume_preserving_equivFin3_prod.setIntegral_preimage_emb equivFin3_prod.measurableEmbedding]
    have hg_cont : ContinuousOn g (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2)) :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨x0, x1, x2⟩ ⟨hx0, hx1, hx2⟩ => ⟨by simpa using hx0, by simpa using hx1, by simpa using hx2⟩)
    have hint := hg_cont.integrableOn_compact (μ := volume.prod (volume.prod volume)) (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    rw [MeasureTheory.setIntegral_prod _ hint, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
    apply intervalIntegral.integral_congr
    intro x0 hx0; rw [uIcc_of_le h0] at hx0; dsimp only
    have hint2 : IntegrableOn (fun q : ℝ × ℝ => g (x0, q)) (Icc a1 b1 ×ˢ Icc a2 b2) (volume.prod volume) :=
      (hg_cont.comp (continuousOn_const.prodMk continuousOn_id) (fun q hq => ⟨hx0, hq⟩)).integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    rw [MeasureTheory.setIntegral_prod _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
    apply intervalIntegral.integral_congr
    intro x1 _; try dsimp only; rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
  | tri01 =>
    set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a0 b0 ∧ p.2.2 ∈ Icc a2 b2 ∧ p.1 ≤ p.2.1}
    have hpre : cell3Set .tri01 a0 b0 a1 b1 a2 b2 = equivFin3_prod ⁻¹' T := by
      ext x; simp [cell3Set, T, equivFin3_prod_apply]
    dsimp only
    rw [hpre]
    conv_lhs => rw [hf_eq]
    simp_rw [Function.comp_apply]
    rw [volume_preserving_equivFin3_prod.setIntegral_preimage_emb equivFin3_prod.measurableEmbedding]
    have hT_comp : IsCompact T := by
      refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
          ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
            (isClosed_le continuous_fst (continuous_fst.comp continuous_snd))))
    have hT_meas : MeasurableSet T := hT_comp.isClosed.measurableSet
    have hg_cont : ContinuousOn g T :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨x0, x1, x2⟩ ⟨hx0, hx1, hx2, h01⟩ => ⟨by simpa using hx0, by simpa using hx1, by simpa using hx2, by simpa using h01⟩)
    rw [← inter_eq_self_of_subset_right (show T ⊆ Icc a0 b0 ×ˢ (Icc a0 b0 ×ˢ Icc a2 b2) from fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩),
        ← setIntegral_indicator hT_meas]
    have hmp := measurePreserving_sw3
    have hpreB : sw3 ⁻¹' (Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0)) = Icc a0 b0 ×ˢ (Icc a0 b0 ×ˢ Icc a2 b2) := by
      ext ⟨x0, x1, x2⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
    have hfn : ∀ p, T.indicator g p = (T.indicator g ∘ sw3.symm) (sw3 p) := fun p => by simp
    rw [← hpreB]; simp_rw [hfn]
    rw [hmp.setIntegral_preimage_emb sw3.measurableEmbedding (T.indicator g ∘ sw3.symm)]
    have hint' : IntegrableOn (T.indicator g ∘ sw3.symm) (Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0))
        (volume.prod (volume.prod volume)) := by
      have hpreB' : sw3.symm ⁻¹' (Icc a0 b0 ×ˢ (Icc a0 b0 ×ˢ Icc a2 b2)) = Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0) := by
        ext ⟨x2, x0, x1⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
      rw [← hpreB']
      refine (hmp.symm.integrableOn_comp_preimage sw3.symm.measurableEmbedding).mpr ?_
      refine integrableOn_indicator_of_subset hT_meas (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
      exact hg_cont.integrableOn_compact hT_comp
    rw [MeasureTheory.setIntegral_prod _ hint', MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
    apply intervalIntegral.integral_congr
    intro x2 hx2; rw [uIcc_of_le h2] at hx2; dsimp only
    set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a0 b0 ∧ q.2 ∈ Icc a0 b0 ∧ q.1 ≤ q.2}
    have hT2_comp : IsCompact T2 := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hint2 : IntegrableOn (fun q : ℝ × ℝ => (T.indicator g ∘ sw3.symm) (x2, q)) (Icc a0 b0 ×ˢ Icc a0 b0) (volume.prod volume) := by
      have hEq : ∀ q ∈ Icc a0 b0 ×ˢ Icc a0 b0, (T.indicator g ∘ sw3.symm) (x2, q) = T2.indicator (fun q => g (q.1, q.2, x2)) q := by
        intro ⟨x0, x1⟩ ⟨hx0, hx1⟩; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
      rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
      refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
      exact (hg_cont.comp (Continuous.continuousOn (by fun_prop))
        (fun q hq => ⟨hq.1, hq.2.1, hx2, hq.2.2⟩)).integrableOn_compact hT2_comp
    rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
    apply intervalIntegral.integral_congr
    intro x1 hx1; rw [uIcc_of_le h0] at hx1; dsimp only
    have heq : ∀ x0 ∈ Icc a0 b0, (T.indicator g ∘ sw3.symm) (x2, x0, x1) =
        ({x0 : ℝ | x0 ≤ x1}).indicator (fun x0 => g (x0, x1, x2)) x0 := by
      intro x0 hx0; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
    rw [setIntegral_congr_fun measurableSet_Icc heq,
        setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
    have hcap : Icc a0 b0 ∩ {x0 : ℝ | x0 ≤ x1} = Icc a0 x1 := by
      ext x0; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
      · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
      · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx1.2⟩, h''⟩
    rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx1.1]
  | tri12 =>
    set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a1 b1 ∧ p.2.2 ∈ Icc a1 b1 ∧ p.2.1 ≤ p.2.2}
    have hpre : cell3Set .tri12 a0 b0 a1 b1 a2 b2 = equivFin3_prod ⁻¹' T := by
      ext x; simp [cell3Set, T, equivFin3_prod_apply]
    dsimp only
    rw [hpre]
    conv_lhs => rw [hf_eq]
    simp_rw [Function.comp_apply]
    rw [volume_preserving_equivFin3_prod.setIntegral_preimage_emb equivFin3_prod.measurableEmbedding]
    have hT_comp : IsCompact T := by
      refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
          ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
            (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    have hT_meas : MeasurableSet T := hT_comp.isClosed.measurableSet
    have hg_cont : ContinuousOn g T :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨x0, x1, x2⟩ ⟨hx0, hx1, hx2, h12⟩ => ⟨by simpa using hx0, by simpa using hx1, by simpa using hx2, by simpa using h12⟩)
    rw [← inter_eq_self_of_subset_right (show T ⊆ Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a1 b1) from fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩),
        ← setIntegral_indicator hT_meas]
    have hint : IntegrableOn (T.indicator g) (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a1 b1)) (volume.prod (volume.prod volume)) := by
      refine integrableOn_indicator_of_subset hT_meas (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
      exact hg_cont.integrableOn_compact hT_comp
    rw [MeasureTheory.setIntegral_prod _ hint, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
    apply intervalIntegral.integral_congr
    intro x0 hx0; rw [uIcc_of_le h0] at hx0; dsimp only
    set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a1 b1 ∧ q.2 ∈ Icc a1 b1 ∧ q.1 ≤ q.2}
    have hT2_comp : IsCompact T2 := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
      exact (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
    have hint2 : IntegrableOn (fun q : ℝ × ℝ => T.indicator g (x0, q)) (Icc a1 b1 ×ˢ Icc a1 b1) (volume.prod volume) := by
      have hEq : ∀ q ∈ Icc a1 b1 ×ˢ Icc a1 b1, T.indicator g (x0, q) = T2.indicator (fun q => g (x0, q)) q := by
        intro ⟨x1, x2⟩ ⟨hx1, hx2⟩; by_cases h12 : x1 ≤ x2 <;> simp [T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
      rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
      refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
      exact (hg_cont.comp (continuousOn_const.prodMk continuousOn_id)
        (fun q hq => ⟨hx0, hq.1, hq.2.1, hq.2.2⟩)).integrableOn_compact hT2_comp
    rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
    apply intervalIntegral.integral_congr
    intro x2 hx2; rw [uIcc_of_le h1] at hx2; dsimp only
    have heq : ∀ x1 ∈ Icc a1 b1, T.indicator g (x0, x1, x2) =
        ({x1 : ℝ | x1 ≤ x2}).indicator (fun x1 => g (x0, x1, x2)) x1 := by
      intro x1 hx1; by_cases h12 : x1 ≤ x2 <;> simp [T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
    rw [setIntegral_congr_fun measurableSet_Icc heq,
        setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
    have hcap : Icc a1 b1 ∩ {x1 : ℝ | x1 ≤ x2} = Icc a1 x2 := by
      ext x1; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
      · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
      · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx2.2⟩, h''⟩
    rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx2.1]
  | simp =>
    set S : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a0 b0 ∧ p.2.2 ∈ Icc a0 b0 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
    have hpre : cell3Set .simp a0 b0 a1 b1 a2 b2 = equivFin3_prod ⁻¹' S := by
      ext x; simp [cell3Set, S, equivFin3_prod_apply]
    dsimp only
    rw [hpre]
    conv_lhs => rw [hf_eq]
    simp_rw [Function.comp_apply]
    rw [volume_preserving_equivFin3_prod.setIntegral_preimage_emb equivFin3_prod.measurableEmbedding]
    have hg_cont : ContinuousOn g S :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun ⟨x0, x1, x2⟩ ⟨hx0, hx1, hx2, h01, h12⟩ => ⟨by simpa using hx0, by simpa using hx1, by simpa using hx2, by simpa using h01, by simpa using h12⟩)
    exact (simp3_eq_setIntegral h0 hg_cont).symm

lemma hh_cell3 (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2)
    {f : (Fin 3 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f)
    (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :
    ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x ≤
      ((b0 - a0) * (b1 - a1) * (b2 - a2) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ))) *
        sumVerts3R f knd a0 b0 a1 b1 a2 b2 := by
  rcases hok with ⟨h0, h1, h2, hkm⟩
  rw [integral_cell3_eq_iter knd h0 h1 h2 hcont]
  have hconv_slice : ∀ (g : ℝ → Fin 3 → ℝ) (I : Set ℝ),
      (∀ t ∈ I, g t ∈ cell3Set knd a0 b0 a1 b1 a2 b2) →
      (∀ t1 ∈ I, ∀ t2 ∈ I, ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v = 1 →
        g (u * t1 + v * t2) = u • g t1 + v • g t2) →
      Convex ℝ I → ConvexOn ℝ I (fun t => f (g t)) := by
    intro g I hmem haff hI
    refine ⟨hI, fun t1 ht1 t2 ht2 u v hu hv huv => ?_⟩
    simpa [smul_eq_mul, haff t1 ht1 t2 ht2 u v hu hv huv] using hconv.2 (hmem t1 ht1) (hmem t2 ht2) hu hv huv
  cases knd with
  | box =>
    have hstep2 : ∀ x0 ∈ Icc a0 b0, ∀ x1 ∈ Icc a1 b1,
        ∫ x2 in a2..b2, f ![x0, x1, x2] ≤ ((b2 - a2) / 2) * (f ![x0, x1, a2] + f ![x0, x1, b2]) := by
      intro x0 hx0 x1 hx1
      refine hh1_Icc h2 (hconv_slice (fun t => ![x0, x1, t]) (Icc a2 b2)
        (fun t ht => ⟨by simpa using hx0, by simpa using hx1, by simpa using ht⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a2 b2))
        (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun t ht => ⟨by simpa using hx0, by simpa using hx1, by simpa using ht⟩))
    have hstep1 : ∀ x0 ∈ Icc a0 b0,
        ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2] ≤
          ((b1 - a1) * (b2 - a2) / 4) *
            (f ![x0, a1, a2] + f ![x0, a1, b2] + f ![x0, b1, a2] + f ![x0, b1, b2]) := by
      intro x0 hx0
      have hi_l : IntervalIntegrable (fun x1 => ∫ x2 in a2..b2, f ![x0, x1, x2]) volume a1 b1 := by
        have hc2 : ContinuousOn (fun q : ℝ × ℝ => f ![x0, q.1, q.2]) (Icc a1 b1 ×ˢ Icc a2 b2) :=
          hcont.comp (Continuous.continuousOn (by fun_prop))
            (fun q hq => ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2⟩)
        have hint := integrableOn_setIntegral_right (hc2.integrableOn_compact (μ := volume.prod volume) (isCompact_Icc.prod isCompact_Icc))
        refine (intervalIntegrable_iff_integrableOn_Icc_of_le h1).mpr ?_
        refine IntegrableOn.congr_fun hint ?_ measurableSet_Icc
        intro x1 _; try dsimp only; rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
      have hca : ContinuousOn (fun x1 => f ![x0, x1, a2]) (Icc a1 b1) :=
        hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun x1 hx1 => ⟨by simpa using hx0, by simpa using hx1, by simpa using left_mem_Icc.mpr h2⟩)
      have hcb : ContinuousOn (fun x1 => f ![x0, x1, b2]) (Icc a1 b1) :=
        hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun x1 hx1 => ⟨by simpa using hx0, by simpa using hx1, by simpa using right_mem_Icc.mpr h2⟩)
      have hm := intervalIntegral.integral_mono_on h1 hi_l
        (((hca.add hcb).const_mul ((b2 - a2) / 2)).intervalIntegrable_of_Icc h1)
        (fun x1 hx1 => hstep2 x0 hx0 x1 hx1)
      simp only [Pi.add_apply] at hm
      rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (hca.intervalIntegrable_of_Icc h1) (hcb.intervalIntegrable_of_Icc h1)] at hm
      have ha1 := hh1_Icc h1 (hconv_slice (fun t => ![x0, t, a2]) (Icc a1 b1)
        (fun t ht => ⟨by simpa using hx0, by simpa using ht, by simpa using left_mem_Icc.mpr h2⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a1 b1)) hca
      have hb1 := hh1_Icc h1 (hconv_slice (fun t => ![x0, t, b2]) (Icc a1 b1)
        (fun t ht => ⟨by simpa using hx0, by simpa using ht, by simpa using right_mem_Icc.mpr h2⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a1 b1)) hcb
      have hnn : 0 ≤ (b2 - a2) / 2 := by linarith
      nlinarith
    have hi_0 : IntervalIntegrable (fun x0 => ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2]) volume a0 b0 := by
      have hc3 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2)) :=
        hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩)
      have hint := integrableOn_setIntegral_right (hc3.integrableOn_compact (μ := volume.prod (volume.prod volume)) (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h0).mpr ?_
      refine IntegrableOn.congr_fun hint ?_ measurableSet_Icc
      intro x0 hx0; dsimp only
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => f ![x0, q.1, q.2]) (Icc a1 b1 ×ˢ Icc a2 b2) (volume.prod volume) :=
        (hc3.comp (continuousOn_const.prodMk continuousOn_id) (fun q hq => ⟨hx0, hq⟩)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc)
      rw [MeasureTheory.setIntegral_prod _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
      apply intervalIntegral.integral_congr; intro x1 _; dsimp only
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
    have hcf : ∀ (y1 : ℝ) (_ : y1 ∈ Icc a1 b1) (y2 : ℝ) (_ : y2 ∈ Icc a2 b2),
        ContinuousOn (fun x0 => f ![x0, y1, y2]) (Icc a0 b0) := fun y1 hy1 y2 hy2 =>
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x0 hx0 => ⟨by simpa using hx0, by simpa using hy1, by simpa using hy2⟩)
    have hhh0 : ∀ (y1 : ℝ) (hy1 : y1 ∈ Icc a1 b1) (y2 : ℝ) (hy2 : y2 ∈ Icc a2 b2),
        ∫ x0 in a0..b0, f ![x0, y1, y2] ≤ ((b0 - a0) / 2) * (f ![a0, y1, y2] + f ![b0, y1, y2]) :=
      fun y1 hy1 y2 hy2 => hh1_Icc h0 (hconv_slice (fun t => ![t, y1, y2]) (Icc a0 b0)
        (fun t ht => ⟨by simpa using ht, by simpa using hy1, by simpa using hy2⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a0 b0)) (hcf y1 hy1 y2 hy2)
    have c00 := hcf a1 (left_mem_Icc.mpr h1) a2 (left_mem_Icc.mpr h2)
    have c01 := hcf a1 (left_mem_Icc.mpr h1) b2 (right_mem_Icc.mpr h2)
    have c10 := hcf b1 (right_mem_Icc.mpr h1) a2 (left_mem_Icc.mpr h2)
    have c11 := hcf b1 (right_mem_Icc.mpr h1) b2 (right_mem_Icc.mpr h2)
    have hm := intervalIntegral.integral_mono_on h0 hi_0
      ((((c00.add c01).add c10).add c11 |>.const_mul ((b1 - a1) * (b2 - a2) / 4)).intervalIntegrable_of_Icc h0)
      (fun x0 hx0 => hstep1 x0 hx0)
    simp only [Pi.add_apply] at hm
    rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((c00.intervalIntegrable_of_Icc h0 |>.add (c01.intervalIntegrable_of_Icc h0)).add (c10.intervalIntegrable_of_Icc h0)) (c11.intervalIntegrable_of_Icc h0),
        intervalIntegral.integral_add (c00.intervalIntegrable_of_Icc h0 |>.add (c01.intervalIntegrable_of_Icc h0)) (c10.intervalIntegrable_of_Icc h0),
        intervalIntegral.integral_add (c00.intervalIntegrable_of_Icc h0) (c01.intervalIntegrable_of_Icc h0)] at hm
    have k00 := hhh0 a1 (left_mem_Icc.mpr h1) a2 (left_mem_Icc.mpr h2)
    have k01 := hhh0 a1 (left_mem_Icc.mpr h1) b2 (right_mem_Icc.mpr h2)
    have k10 := hhh0 b1 (right_mem_Icc.mpr h1) a2 (left_mem_Icc.mpr h2)
    have k11 := hhh0 b1 (right_mem_Icc.mpr h1) b2 (right_mem_Icc.mpr h2)
    have hnn : 0 ≤ (b1 - a1) * (b2 - a2) / 4 := by nlinarith
    dsimp only; simp only [facDen, nVerts3, sumVerts3R]; push_cast; nlinarith
  | tri01 =>
    rcases hkm with ⟨rfl, rfl⟩
    have hinner : ∀ x2 ∈ Icc a2 b2,
        ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2] ≤
          ((b0 - a0) ^ 2 / 6) * (f ![a0, a0, x2] + f ![a0, b0, x2] + f ![b0, b0, x2]) := by
      intro x2 hx2
      refine hh2_tri h0 (f := fun p : ℝ × ℝ => f ![p.1, p.2, x2]) ?_ ?_
      · refine ⟨?_, ?_⟩
        · exact convex_tri2 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![p.1, p.2, x2] ∈ cell3Set .tri01 a0 b0 a0 b0 a2 b2 :=
            ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hx2, by simpa using hp.2.2⟩
          have hqS : ![q.1, q.2, x2] ∈ cell3Set .tri01 a0 b0 a0 b0 a2 b2 :=
            ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hx2, by simpa using hq.2.2⟩
          have h := hconv.2 hpS hqS hu hv huv
          have heq : u • ![p.1, p.2, x2] + v • ![q.1, q.2, x2] = ![u * p.1 + v * q.1, u * p.2 + v * q.2, x2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
          rw [heq] at h; simpa [smul_eq_mul] using h
      · exact hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hx2, by simpa using hp.2.2⟩)
    have hi_0 : IntervalIntegrable (fun x2 => ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2]) volume a2 b2 := by
      set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a0 b0 ∧ p.2.2 ∈ Icc a2 b2 ∧ p.1 ≤ p.2.1}
      have hT_comp : IsCompact T := by
        refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
            ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
              (isClosed_le continuous_fst (continuous_fst.comp continuous_snd))))
      have hmp := measurePreserving_sw3
      have hint' : IntegrableOn (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm)
          (Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0)) (volume.prod (volume.prod volume)) := by
        have hpreB' : sw3.symm ⁻¹' (Icc a0 b0 ×ˢ (Icc a0 b0 ×ˢ Icc a2 b2)) = Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0) := by
          ext ⟨x2, x0, x1⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
        rw [← hpreB']
        refine (hmp.symm.integrableOn_comp_preimage sw3.symm.measurableEmbedding).mpr ?_
        refine integrableOn_indicator_of_subset hT_comp.isClosed.measurableSet (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2⟩)).integrableOn_compact hT_comp
      have h_z := integrableOn_setIntegral_right hint'
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h2).mpr ?_
      refine IntegrableOn.congr_fun h_z ?_ measurableSet_Icc
      intro x2 hx2; dsimp only
      set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a0 b0 ∧ q.2 ∈ Icc a0 b0 ∧ q.1 ≤ q.2}
      have hT2_comp : IsCompact T2 := by
        refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, q))
          (Icc a0 b0 ×ˢ Icc a0 b0) (volume.prod volume) := by
        have hEq : ∀ q ∈ Icc a0 b0 ×ˢ Icc a0 b0,
            (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, q) = T2.indicator (fun q => f ![q.1, q.2, x2]) q := by
          intro ⟨x0, x1⟩ ⟨hx0, hx1⟩; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
        rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
        refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun q hq => ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hx2, by simpa using hq.2.2⟩)).integrableOn_compact hT2_comp
      rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
      apply intervalIntegral.integral_congr
      intro x1 hx1; rw [uIcc_of_le h0] at hx1; dsimp only
      have heq : ∀ x0 ∈ Icc a0 b0, (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, x0, x1) =
          ({x0 : ℝ | x0 ≤ x1}).indicator (fun x0 => f ![x0, x1, x2]) x0 := by
        intro x0 hx0; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
      rw [setIntegral_congr_fun measurableSet_Icc heq,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a0 b0 ∩ {x0 : ℝ | x0 ≤ x1} = Icc a0 x1 := by
        ext x0; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
        · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx1.2⟩, h''⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx1.1]
    have hcf : ∀ (y0 y1 : ℝ), y0 ∈ Icc a0 b0 → y1 ∈ Icc a0 b0 → y0 ≤ y1 →
        ContinuousOn (fun x2 => f ![y0, y1, x2]) (Icc a2 b2) := fun y0 y1 hy0 hy1 h01 =>
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x2 hx2 => ⟨by simpa using hy0, by simpa using hy1, by simpa using hx2, by simpa using h01⟩)
    have hhh2 : ∀ (y0 y1 : ℝ), y0 ∈ Icc a0 b0 → y1 ∈ Icc a0 b0 → y0 ≤ y1 →
        ∫ x2 in a2..b2, f ![y0, y1, x2] ≤ ((b2 - a2) / 2) * (f ![y0, y1, a2] + f ![y0, y1, b2]) :=
      fun y0 y1 hy0 hy1 h01 => hh1_Icc h2 (hconv_slice (fun t => ![y0, y1, t]) (Icc a2 b2)
        (fun t ht => ⟨by simpa using hy0, by simpa using hy1, by simpa using ht, by simpa using h01⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a2 b2)) (hcf y0 y1 hy0 hy1 h01)
    have c0 := hcf a0 a0 (left_mem_Icc.mpr h0) (left_mem_Icc.mpr h0) (le_refl a0)
    have c1 := hcf a0 b0 (left_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) h0
    have c2 := hcf b0 b0 (right_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) (le_refl b0)
    have hm := intervalIntegral.integral_mono_on h2 hi_0
      ((((c0.add c1).add c2).const_mul ((b0 - a0) ^ 2 / 6)).intervalIntegrable_of_Icc h2)
      (fun x2 hx2 => hinner x2 hx2)
    simp only [Pi.add_apply] at hm
    rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((c0.intervalIntegrable_of_Icc h2).add (c1.intervalIntegrable_of_Icc h2)) (c2.intervalIntegrable_of_Icc h2),
        intervalIntegral.integral_add (c0.intervalIntegrable_of_Icc h2) (c1.intervalIntegrable_of_Icc h2)] at hm
    have k0 := hhh2 a0 a0 (left_mem_Icc.mpr h0) (left_mem_Icc.mpr h0) (le_refl a0)
    have k1 := hhh2 a0 b0 (left_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) h0
    have k2 := hhh2 b0 b0 (right_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) (le_refl b0)
    have hnn : 0 ≤ (b0 - a0) ^ 2 / 6 := by positivity
    dsimp only; simp only [facDen, nVerts3, sumVerts3R]; push_cast; nlinarith
  | tri12 =>
    rcases hkm with ⟨rfl, rfl⟩
    have hinner : ∀ x0 ∈ Icc a0 b0,
        ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2] ≤
          ((b1 - a1) ^ 2 / 6) * (f ![x0, a1, a1] + f ![x0, a1, b1] + f ![x0, b1, b1]) := by
      intro x0 hx0
      refine hh2_tri h1 (f := fun p : ℝ × ℝ => f ![x0, p.1, p.2]) ?_ ?_
      · refine ⟨?_, ?_⟩
        · exact convex_tri2 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![x0, p.1, p.2] ∈ cell3Set .tri12 a0 b0 a1 b1 a1 b1 :=
            ⟨by simpa using hx0, by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩
          have hqS : ![x0, q.1, q.2] ∈ cell3Set .tri12 a0 b0 a1 b1 a1 b1 :=
            ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2⟩
          have h := hconv.2 hpS hqS hu hv huv
          have heq : u • ![x0, p.1, p.2] + v • ![x0, q.1, q.2] = ![x0, u * p.1 + v * q.1, u * p.2 + v * q.2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
          rw [heq] at h; simpa [smul_eq_mul] using h
      · exact hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hx0, by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩)
    have hi_0 : IntervalIntegrable (fun x0 => ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2]) volume a0 b0 := by
      set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a1 b1 ∧ p.2.2 ∈ Icc a1 b1 ∧ p.2.1 ≤ p.2.2}
      have hT_comp : IsCompact T := by
        refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
            ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
              (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
      have hint' : IntegrableOn (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]))
          (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a1 b1)) (volume.prod (volume.prod volume)) := by
        refine integrableOn_indicator_of_subset hT_comp.isClosed.measurableSet (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2⟩)).integrableOn_compact hT_comp
      have h_0 := integrableOn_setIntegral_right hint'
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h0).mpr ?_
      refine IntegrableOn.congr_fun h_0 ?_ measurableSet_Icc
      intro x0 hx0; dsimp only
      set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a1 b1 ∧ q.2 ∈ Icc a1 b1 ∧ q.1 ≤ q.2}
      have hT2_comp : IsCompact T2 := by
        refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, q))
          (Icc a1 b1 ×ˢ Icc a1 b1) (volume.prod volume) := by
        have hEq : ∀ q ∈ Icc a1 b1 ×ˢ Icc a1 b1,
            T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, q) = T2.indicator (fun q => f ![x0, q.1, q.2]) q := by
          intro ⟨x1, x2⟩ ⟨hx1, hx2⟩; by_cases h12 : x1 ≤ x2 <;> simp [T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
        rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
        refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun q hq => ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2⟩)).integrableOn_compact hT2_comp
      rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
      apply intervalIntegral.integral_congr
      intro x2 hx2; rw [uIcc_of_le h1] at hx2; dsimp only
      have heq : ∀ x1 ∈ Icc a1 b1, T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, x1, x2) =
          ({x1 : ℝ | x1 ≤ x2}).indicator (fun x1 => f ![x0, x1, x2]) x1 := by
        intro x1 hx1; by_cases h12 : x1 ≤ x2 <;> simp [T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
      rw [setIntegral_congr_fun measurableSet_Icc heq,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a1 b1 ∩ {x1 : ℝ | x1 ≤ x2} = Icc a1 x2 := by
        ext x1; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
        · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx2.2⟩, h''⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx2.1]
    have hcf : ∀ (y1 y2 : ℝ), y1 ∈ Icc a1 b1 → y2 ∈ Icc a1 b1 → y1 ≤ y2 →
        ContinuousOn (fun x0 => f ![x0, y1, y2]) (Icc a0 b0) := fun y1 y2 hy1 hy2 h12 =>
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x0 hx0 => ⟨by simpa using hx0, by simpa using hy1, by simpa using hy2, by simpa using h12⟩)
    have hhh0 : ∀ (y1 y2 : ℝ), y1 ∈ Icc a1 b1 → y2 ∈ Icc a1 b1 → y1 ≤ y2 →
        ∫ x0 in a0..b0, f ![x0, y1, y2] ≤ ((b0 - a0) / 2) * (f ![a0, y1, y2] + f ![b0, y1, y2]) :=
      fun y1 y2 hy1 hy2 h12 => hh1_Icc h0 (hconv_slice (fun t => ![t, y1, y2]) (Icc a0 b0)
        (fun t ht => ⟨by simpa using ht, by simpa using hy1, by simpa using hy2, by simpa using h12⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a0 b0)) (hcf y1 y2 hy1 hy2 h12)
    have c0 := hcf a1 a1 (left_mem_Icc.mpr h1) (left_mem_Icc.mpr h1) (le_refl a1)
    have c1 := hcf a1 b1 (left_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) h1
    have c2 := hcf b1 b1 (right_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) (le_refl b1)
    have hm := intervalIntegral.integral_mono_on h0 hi_0
      ((((c0.add c1).add c2).const_mul ((b1 - a1) ^ 2 / 6)).intervalIntegrable_of_Icc h0)
      (fun x0 hx0 => hinner x0 hx0)
    simp only [Pi.add_apply] at hm
    rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((c0.intervalIntegrable_of_Icc h0).add (c1.intervalIntegrable_of_Icc h0)) (c2.intervalIntegrable_of_Icc h0),
        intervalIntegral.integral_add (c0.intervalIntegrable_of_Icc h0) (c1.intervalIntegrable_of_Icc h0)] at hm
    have k0 := hhh0 a1 a1 (left_mem_Icc.mpr h1) (left_mem_Icc.mpr h1) (le_refl a1)
    have k1 := hhh0 a1 b1 (left_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) h1
    have k2 := hhh0 b1 b1 (right_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) (le_refl b1)
    have hnn : 0 ≤ (b1 - a1) ^ 2 / 6 := by positivity
    dsimp only; simp only [facDen, nVerts3, sumVerts3R]; push_cast; nlinarith
  | simp =>
    rcases hkm with ⟨rfl, rfl, rfl, rfl⟩
    have h := hh3_simp h0 (f := fun p : ℝ × ℝ × ℝ => f ![p.1, p.2.1, p.2.2])
      (by
        refine ⟨?_, ?_⟩
        · exact convex_simp3 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![p.1, p.2.1, p.2.2] ∈ cell3Set .simp a0 b0 a0 b0 a0 b0 :=
            ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2.1, by simpa using hp.2.2.2.2⟩
          have hqS : ![q.1, q.2.1, q.2.2] ∈ cell3Set .simp a0 b0 a0 b0 a0 b0 :=
            ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2.1, by simpa using hq.2.2.2.1, by simpa using hq.2.2.2.2⟩
          have hc := hconv.2 hpS hqS hu hv huv
          have heq : u • ![p.1, p.2.1, p.2.2] + v • ![q.1, q.2.1, q.2.2] =
              ![u * p.1 + v * q.1, u * p.2.1 + v * q.2.1, u * p.2.2 + v * q.2.2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul]
          rw [heq] at hc; simpa [smul_eq_mul] using hc)
      (hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2.1, by simpa using hp.2.2.2.2⟩))
    dsimp only; simp only [facDen, nVerts3, sumVerts3R]; push_cast; linarith

lemma jensen_cell3 (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2)
    {f : (Fin 3 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f)
    (hcont : ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2)) :
    ((b0 - a0) * (b1 - a1) * (b2 - a2) / (facDen knd : ℝ)) *
        f (centroid3R knd a0 b0 a1 b1 a2 b2) ≤
      ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x := by
  rcases hok with ⟨h0, h1, h2, hkm⟩
  rw [integral_cell3_eq_iter knd h0 h1 h2 hcont]
  have hconv_slice : ∀ (g : ℝ → Fin 3 → ℝ) (I : Set ℝ),
      (∀ t ∈ I, g t ∈ cell3Set knd a0 b0 a1 b1 a2 b2) →
      (∀ t1 ∈ I, ∀ t2 ∈ I, ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v = 1 →
        g (u * t1 + v * t2) = u • g t1 + v • g t2) →
      Convex ℝ I → ConvexOn ℝ I (fun t => f (g t)) := by
    intro g I hmem haff hI
    refine ⟨hI, fun t1 ht1 t2 ht2 u v hu hv huv => ?_⟩
    simpa [smul_eq_mul, haff t1 ht1 t2 ht2 u v hu hv huv] using hconv.2 (hmem t1 ht1) (hmem t2 ht2) hu hv huv
  cases knd with
  | box =>
    have hm2 : (a2 + b2) / 2 ∈ Icc a2 b2 := ⟨by linarith, by linarith⟩
    have hm1 : (a1 + b1) / 2 ∈ Icc a1 b1 := ⟨by linarith, by linarith⟩
    have hstep2 : ∀ x0 ∈ Icc a0 b0, ∀ x1 ∈ Icc a1 b1,
        (b2 - a2) * f ![x0, x1, (a2 + b2) / 2] ≤ ∫ x2 in a2..b2, f ![x0, x1, x2] := by
      intro x0 hx0 x1 hx1
      refine jensen1_Icc h2 (hconv_slice (fun t => ![x0, x1, t]) (Icc a2 b2)
        (fun t ht => ⟨by simpa using hx0, by simpa using hx1, by simpa using ht⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a2 b2))
        (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun t ht => ⟨by simpa using hx0, by simpa using hx1, by simpa using ht⟩))
    have hstep1 : ∀ x0 ∈ Icc a0 b0,
        (b1 - a1) * (b2 - a2) * f ![x0, (a1 + b1) / 2, (a2 + b2) / 2] ≤
          ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2] := by
      intro x0 hx0
      have hc1 : ContinuousOn (fun x1 => f ![x0, x1, (a2 + b2) / 2]) (Icc a1 b1) :=
        hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun x1 hx1 => ⟨by simpa using hx0, by simpa using hx1, by simpa using hm2⟩)
      have hj1 := jensen1_Icc h1 (hconv_slice (fun t => ![x0, t, (a2 + b2) / 2]) (Icc a1 b1)
        (fun t ht => ⟨by simpa using hx0, by simpa using ht, by simpa using hm2⟩)
        (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
        (convex_Icc a1 b1)) hc1
      have hi_r : IntervalIntegrable (fun x1 => ∫ x2 in a2..b2, f ![x0, x1, x2]) volume a1 b1 := by
        have hc2 : ContinuousOn (fun q : ℝ × ℝ => f ![x0, q.1, q.2]) (Icc a1 b1 ×ˢ Icc a2 b2) :=
          hcont.comp (Continuous.continuousOn (by fun_prop))
            (fun q hq => ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2⟩)
        have hint := integrableOn_setIntegral_right (hc2.integrableOn_compact (μ := volume.prod volume) (isCompact_Icc.prod isCompact_Icc))
        refine (intervalIntegrable_iff_integrableOn_Icc_of_le h1).mpr ?_
        refine IntegrableOn.congr_fun hint ?_ measurableSet_Icc
        intro x1 _; try dsimp only; rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
      have hm := intervalIntegral.integral_mono_on h1 ((hc1.const_mul (b2 - a2)).intervalIntegrable_of_Icc h1) hi_r
        (fun x1 hx1 => hstep2 x0 hx0 x1 hx1)
      rw [intervalIntegral.integral_const_mul] at hm
      have hnn : 0 ≤ b2 - a2 := by linarith
      nlinarith
    have hc0 : ContinuousOn (fun x0 => f ![x0, (a1 + b1) / 2, (a2 + b2) / 2]) (Icc a0 b0) :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x0 hx0 => ⟨by simpa using hx0, by simpa using hm1, by simpa using hm2⟩)
    have hj0 := jensen1_Icc h0 (hconv_slice (fun t => ![t, (a1 + b1) / 2, (a2 + b2) / 2]) (Icc a0 b0)
      (fun t ht => ⟨by simpa using ht, by simpa using hm1, by simpa using hm2⟩)
      (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
      (convex_Icc a0 b0)) hc0
    have hi_0 : IntervalIntegrable (fun x0 => ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2]) volume a0 b0 := by
      have hc3 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2)) :=
        hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩)
      have hint := integrableOn_setIntegral_right (hc3.integrableOn_compact (μ := volume.prod (volume.prod volume)) (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h0).mpr ?_
      refine IntegrableOn.congr_fun hint ?_ measurableSet_Icc
      intro x0 hx0; dsimp only
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => f ![x0, q.1, q.2]) (Icc a1 b1 ×ˢ Icc a2 b2) (volume.prod volume) :=
        (hc3.comp (continuousOn_const.prodMk continuousOn_id) (fun q hq => ⟨hx0, hq⟩)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc)
      rw [MeasureTheory.setIntegral_prod _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
      apply intervalIntegral.integral_congr; intro x1 _; dsimp only
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
    have hm := intervalIntegral.integral_mono_on h0
      ((hc0.const_mul ((b1 - a1) * (b2 - a2))).intervalIntegrable_of_Icc h0) hi_0
      (fun x0 hx0 => hstep1 x0 hx0)
    rw [intervalIntegral.integral_const_mul] at hm
    have hnn : 0 ≤ (b1 - a1) * (b2 - a2) := by nlinarith
    dsimp only; simp only [facDen, centroid3R]; push_cast; nlinarith
  | tri01 =>
    rcases hkm with ⟨rfl, rfl⟩
    have hinner : ∀ x2 ∈ Icc a2 b2,
        ((b0 - a0) ^ 2 / 2) * f ![(2 * a0 + b0) / 3, (a0 + 2 * b0) / 3, x2] ≤
          ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2] := by
      intro x2 hx2
      refine jensen2_tri h0 (f := fun p : ℝ × ℝ => f ![p.1, p.2, x2]) ?_ ?_
      · refine ⟨?_, ?_⟩
        · exact convex_tri2 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![p.1, p.2, x2] ∈ cell3Set .tri01 a0 b0 a0 b0 a2 b2 :=
            ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hx2, by simpa using hp.2.2⟩
          have hqS : ![q.1, q.2, x2] ∈ cell3Set .tri01 a0 b0 a0 b0 a2 b2 :=
            ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hx2, by simpa using hq.2.2⟩
          have h := hconv.2 hpS hqS hu hv huv
          have heq : u • ![p.1, p.2, x2] + v • ![q.1, q.2, x2] = ![u * p.1 + v * q.1, u * p.2 + v * q.2, x2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
          rw [heq] at h; simpa [smul_eq_mul] using h
      · exact hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hx2, by simpa using hp.2.2⟩)
    have hmc0 : (2 * a0 + b0) / 3 ∈ Icc a0 b0 := ⟨by linarith, by linarith⟩
    have hmc1 : (a0 + 2 * b0) / 3 ∈ Icc a0 b0 := ⟨by linarith, by linarith⟩
    have hmc01 : (2 * a0 + b0) / 3 ≤ (a0 + 2 * b0) / 3 := by linarith
    have hc2 : ContinuousOn (fun x2 => f ![(2 * a0 + b0) / 3, (a0 + 2 * b0) / 3, x2]) (Icc a2 b2) :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x2 hx2 => ⟨by simpa using hmc0, by simpa using hmc1, by simpa using hx2, by simpa using hmc01⟩)
    have hj2 := jensen1_Icc h2 (hconv_slice (fun t => ![(2 * a0 + b0) / 3, (a0 + 2 * b0) / 3, t]) (Icc a2 b2)
      (fun t ht => ⟨by simpa using hmc0, by simpa using hmc1, by simpa using ht, by simpa using hmc01⟩)
      (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
      (convex_Icc a2 b2)) hc2
    have hi_r : IntervalIntegrable (fun x2 => ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2]) volume a2 b2 := by
      set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a0 b0 ∧ p.2.2 ∈ Icc a2 b2 ∧ p.1 ≤ p.2.1}
      have hT_comp : IsCompact T := by
        refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
            ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
              (isClosed_le continuous_fst (continuous_fst.comp continuous_snd))))
      have hmp := measurePreserving_sw3
      have hint' : IntegrableOn (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm)
          (Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0)) (volume.prod (volume.prod volume)) := by
        have hpreB' : sw3.symm ⁻¹' (Icc a0 b0 ×ˢ (Icc a0 b0 ×ˢ Icc a2 b2)) = Icc a2 b2 ×ˢ (Icc a0 b0 ×ˢ Icc a0 b0) := by
          ext ⟨x2, x0, x1⟩; simp [sw3_apply, sw3_symm_apply, sw3_apply, sw3_symm_apply]; tauto
        rw [← hpreB']
        refine (hmp.symm.integrableOn_comp_preimage sw3.symm.measurableEmbedding).mpr ?_
        refine integrableOn_indicator_of_subset hT_comp.isClosed.measurableSet (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2⟩)).integrableOn_compact hT_comp
      have h_z := integrableOn_setIntegral_right hint'
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h2).mpr ?_
      refine IntegrableOn.congr_fun h_z ?_ measurableSet_Icc
      intro x2 hx2; dsimp only
      set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a0 b0 ∧ q.2 ∈ Icc a0 b0 ∧ q.1 ≤ q.2}
      have hT2_comp : IsCompact T2 := by
        refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, q))
          (Icc a0 b0 ×ˢ Icc a0 b0) (volume.prod volume) := by
        have hEq : ∀ q ∈ Icc a0 b0 ×ˢ Icc a0 b0,
            (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, q) = T2.indicator (fun q => f ![q.1, q.2, x2]) q := by
          intro ⟨x0, x1⟩ ⟨hx0, hx1⟩; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
        rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
        refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun q hq => ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hx2, by simpa using hq.2.2⟩)).integrableOn_compact hT2_comp
      rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
      apply intervalIntegral.integral_congr
      intro x1 hx1; rw [uIcc_of_le h0] at hx1; dsimp only
      have heq : ∀ x0 ∈ Icc a0 b0, (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) ∘ sw3.symm) (x2, x0, x1) =
          ({x0 : ℝ | x0 ≤ x1}).indicator (fun x0 => f ![x0, x1, x2]) x0 := by
        intro x0 hx0; by_cases h01 : x0 ≤ x1 <;> simp [sw3_apply, sw3_symm_apply, T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h01]
      rw [setIntegral_congr_fun measurableSet_Icc heq,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a0 b0 ∩ {x0 : ℝ | x0 ≤ x1} = Icc a0 x1 := by
        ext x0; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
        · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx1.2⟩, h''⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx1.1]
    have hm := intervalIntegral.integral_mono_on h2
      ((hc2.const_mul ((b0 - a0) ^ 2 / 2)).intervalIntegrable_of_Icc h2) hi_r
      (fun x2 hx2 => hinner x2 hx2)
    rw [intervalIntegral.integral_const_mul] at hm
    have hnn : 0 ≤ (b0 - a0) ^ 2 / 2 := by positivity
    dsimp only; simp only [facDen, centroid3R]; push_cast; nlinarith
  | tri12 =>
    rcases hkm with ⟨rfl, rfl⟩
    have hinner : ∀ x0 ∈ Icc a0 b0,
        ((b1 - a1) ^ 2 / 2) * f ![x0, (2 * a1 + b1) / 3, (a1 + 2 * b1) / 3] ≤
          ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2] := by
      intro x0 hx0
      refine jensen2_tri h1 (f := fun p : ℝ × ℝ => f ![x0, p.1, p.2]) ?_ ?_
      · refine ⟨?_, ?_⟩
        · exact convex_tri2 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![x0, p.1, p.2] ∈ cell3Set .tri12 a0 b0 a1 b1 a1 b1 :=
            ⟨by simpa using hx0, by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩
          have hqS : ![x0, q.1, q.2] ∈ cell3Set .tri12 a0 b0 a1 b1 a1 b1 :=
            ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2⟩
          have h := hconv.2 hpS hqS hu hv huv
          have heq : u • ![x0, p.1, p.2] + v • ![x0, q.1, q.2] = ![x0, u * p.1 + v * q.1, u * p.2 + v * q.2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
          rw [heq] at h; simpa [smul_eq_mul] using h
      · exact hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hx0, by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩)
    have hmc1 : (2 * a1 + b1) / 3 ∈ Icc a1 b1 := ⟨by linarith, by linarith⟩
    have hmc2 : (a1 + 2 * b1) / 3 ∈ Icc a1 b1 := ⟨by linarith, by linarith⟩
    have hmc12 : (2 * a1 + b1) / 3 ≤ (a1 + 2 * b1) / 3 := by linarith
    have hc0 : ContinuousOn (fun x0 => f ![x0, (2 * a1 + b1) / 3, (a1 + 2 * b1) / 3]) (Icc a0 b0) :=
      hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun x0 hx0 => ⟨by simpa using hx0, by simpa using hmc1, by simpa using hmc2, by simpa using hmc12⟩)
    have hj0 := jensen1_Icc h0 (hconv_slice (fun t => ![t, (2 * a1 + b1) / 3, (a1 + 2 * b1) / 3]) (Icc a0 b0)
      (fun t ht => ⟨by simpa using ht, by simpa using hmc1, by simpa using hmc2, by simpa using hmc12⟩)
      (fun t1 _ t2 _ u v _ _ huv => by ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul])))
      (convex_Icc a0 b0)) hc0
    have hi_r : IntervalIntegrable (fun x0 => ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2]) volume a0 b0 := by
      set T : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a0 b0 ∧ p.2.1 ∈ Icc a1 b1 ∧ p.2.2 ∈ Icc a1 b1 ∧ p.2.1 ≤ p.2.2}
      have hT_comp : IsCompact T := by
        refine (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage (continuous_fst.comp continuous_snd)).inter
            ((isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
              (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
      have hint' : IntegrableOn (T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]))
          (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a1 b1)) (volume.prod (volume.prod volume)) := by
        refine integrableOn_indicator_of_subset hT_comp.isClosed.measurableSet (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2⟩)).integrableOn_compact hT_comp
      have h_0 := integrableOn_setIntegral_right hint'
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le h0).mpr ?_
      refine IntegrableOn.congr_fun h_0 ?_ measurableSet_Icc
      intro x0 hx0; dsimp only
      set T2 : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a1 b1 ∧ q.2 ∈ Icc a1 b1 ∧ q.1 ≤ q.2}
      have hT2_comp : IsCompact T2 := by
        refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun q hq => ⟨hq.1, hq.2.1⟩)
        exact (isClosed_Icc.preimage continuous_fst).inter
          ((isClosed_Icc.preimage continuous_snd).inter (isClosed_le continuous_fst continuous_snd))
      have hint2 : IntegrableOn (fun q : ℝ × ℝ => T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, q))
          (Icc a1 b1 ×ˢ Icc a1 b1) (volume.prod volume) := by
        have hEq : ∀ q ∈ Icc a1 b1 ×ˢ Icc a1 b1,
            T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, q) = T2.indicator (fun q => f ![x0, q.1, q.2]) q := by
          intro ⟨x1, x2⟩ ⟨hx1, hx2⟩; by_cases h12 : x1 ≤ x2 <;> simp [T, T2, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
        rw [integrableOn_congr_fun hEq (measurableSet_Icc.prod measurableSet_Icc)]
        refine integrableOn_indicator_of_subset hT2_comp.isClosed.measurableSet (fun q hq => ⟨hq.1, hq.2.1⟩) ?_
        exact (hcont.comp (Continuous.continuousOn (by fun_prop))
          (fun q hq => ⟨by simpa using hx0, by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2⟩)).integrableOn_compact hT2_comp
      rw [setIntegral_prod_symm' _ hint2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
      apply intervalIntegral.integral_congr
      intro x2 hx2; rw [uIcc_of_le h1] at hx2; dsimp only
      have heq : ∀ x1 ∈ Icc a1 b1, T.indicator (fun p : ℝ × (ℝ × ℝ) => f ![p.1, p.2.1, p.2.2]) (x0, x1, x2) =
          ({x1 : ℝ | x1 ≤ x2}).indicator (fun x1 => f ![x0, x1, x2]) x1 := by
        intro x1 hx1; by_cases h12 : x1 ≤ x2 <;> simp [T, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, h12]
      rw [setIntegral_congr_fun measurableSet_Icc heq,
          setIntegral_indicator (show MeasurableSet {x : ℝ | x ≤ _} from measurableSet_Iic)]
      have hcap : Icc a1 b1 ∩ {x1 : ℝ | x1 ≤ x2} = Icc a1 x2 := by
        ext x1; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h', _⟩, h''⟩; exact ⟨h', h''⟩
        · rintro ⟨h', h''⟩; exact ⟨⟨h', le_trans h'' hx2.2⟩, h''⟩
      rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx2.1]
    have hm := intervalIntegral.integral_mono_on h0
      ((hc0.const_mul ((b1 - a1) ^ 2 / 2)).intervalIntegrable_of_Icc h0) hi_r
      (fun x0 hx0 => hinner x0 hx0)
    rw [intervalIntegral.integral_const_mul] at hm
    have hnn : 0 ≤ (b1 - a1) ^ 2 / 2 := by positivity
    dsimp only; simp only [facDen, centroid3R]; push_cast; nlinarith
  | simp =>
    rcases hkm with ⟨rfl, rfl, rfl, rfl⟩
    have h := jensen3_simp h0 (f := fun p : ℝ × ℝ × ℝ => f ![p.1, p.2.1, p.2.2])
      (by
        refine ⟨?_, ?_⟩
        · exact convex_simp3 _ _
        · intro p hp q hq u v hu hv huv
          have hpS : ![p.1, p.2.1, p.2.2] ∈ cell3Set .simp a0 b0 a0 b0 a0 b0 :=
            ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2.1, by simpa using hp.2.2.2.2⟩
          have hqS : ![q.1, q.2.1, q.2.2] ∈ cell3Set .simp a0 b0 a0 b0 a0 b0 :=
            ⟨by simpa using hq.1, by simpa using hq.2.1, by simpa using hq.2.2.1, by simpa using hq.2.2.2.1, by simpa using hq.2.2.2.2⟩
          have hc := hconv.2 hpS hqS hu hv huv
          have heq : u • ![p.1, p.2.1, p.2.2] + v • ![q.1, q.2.1, q.2.2] =
              ![u * p.1 + v * q.1, u * p.2.1 + v * q.2.1, u * p.2.2 + v * q.2.2] := by
            ext i; fin_cases i <;> simp [smul_eq_mul]
          rw [heq] at hc; simpa [smul_eq_mul] using hc)
      (hcont.comp (Continuous.continuousOn (by fun_prop))
        (fun p hp => ⟨by simpa using hp.1, by simpa using hp.2.1, by simpa using hp.2.2.1, by simpa using hp.2.2.2.1, by simpa using hp.2.2.2.2⟩))
    dsimp only; simp only [facDen, centroid3R]; push_cast; linarith

lemma hh_cell4 (knd : CellKind) {a0 b0 a1 b1 a2 b2 a3 b3 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2) (h3 : a3 ≤ b3)
    {f : (Fin 4 → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) f)
    (hcont : ContinuousOn f (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) :
    ∫ x in cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3, f x ≤
      ((b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3) / ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ)))) *
        sumVerts3R (fun y => f ![y 0, y 1, y 2, a3] + f ![y 0, y 1, y 2, b3]) knd a0 b0 a1 b1 a2 b2 := by
  let g : ℝ × (Fin 3 → ℝ) → ℝ := fun p => f ![p.2 0, p.2 1, p.2 2, p.1]
  have hf_eq : f = g ∘ equivFin4_3 := by
    ext x; dsimp only [g, Function.comp_apply, equivFin4_3_apply]
    congr 1; ext i; fin_cases i <;> rfl
  rw [cell4Set_eq_preimage]
  conv_lhs => rw [hf_eq]
  simp_rw [Function.comp_apply]
  rw [volume_preserving_equivFin4_3.setIntegral_preimage_emb equivFin4_3.measurableEmbedding]
  have hg_cont : ContinuousOn g (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2) := by
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro ⟨x3, y⟩ ⟨hx3, hy⟩
    rw [cell4Set_eq_preimage, mem_preimage]
    have heq : equivFin4_3 ![y 0, y 1, y 2, x3] = (x3, y) := by
      rw [equivFin4_3_apply]; exact Prod.ext rfl (by ext i; fin_cases i <;> rfl)
    rw [heq]; exact ⟨hx3, hy⟩
  have hint : IntegrableOn g (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2) (volume.prod volume) :=
    hg_cont.integrableOn_compact (isCompact_Icc.prod (cell3Set_isCompact knd a0 b0 a1 b1 a2 b2))
  rw [setIntegral_prod_symm' _ hint]
  have hinner : ∀ y ∈ cell3Set knd a0 b0 a1 b1 a2 b2,
      ∫ x3 in Icc a3 b3, g (x3, y) ≤ ((b3 - a3) / 2) * (g (a3, y) + g (b3, y)) := by
    intro y hy
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h3]
    refine hh1_Icc h3 ?_ ?_
    · refine ⟨convex_Icc a3 b3, fun t1 ht1 t2 ht2 u v hu hv huv => ?_⟩
      have hmem : ∀ t ∈ Icc a3 b3, ![y 0, y 1, y 2, t] ∈ cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 := by
        intro t ht; rw [cell4Set_eq_preimage, mem_preimage]
        have heq : equivFin4_3 ![y 0, y 1, y 2, t] = (t, y) := by
          rw [equivFin4_3_apply]; exact Prod.ext rfl (by ext i; fin_cases i <;> rfl)
        rw [heq]; exact ⟨ht, hy⟩
      have h := hconv.2 (hmem t1 ht1) (hmem t2 ht2) hu hv huv
      have heq : u • ![y 0, y 1, y 2, t1] + v • ![y 0, y 1, y 2, t2] = ![y 0, y 1, y 2, u * t1 + v * t2] := by
        ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
      rw [heq] at h; simpa [g, smul_eq_mul] using h
    · exact hg_cont.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht, hy⟩)
  have hga_cont : ContinuousOn (fun y => g (a3, y)) (cell3Set knd a0 b0 a1 b1 a2 b2) :=
    hg_cont.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨left_mem_Icc.mpr h3, hy⟩)
  have hgb_cont : ContinuousOn (fun y => g (b3, y)) (cell3Set knd a0 b0 a1 b1 a2 b2) :=
    hg_cont.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨right_mem_Icc.mpr h3, hy⟩)
  have hle1 : ∫ y in cell3Set knd a0 b0 a1 b1 a2 b2, ∫ x3 in Icc a3 b3, g (x3, y) ≤
      ∫ y in cell3Set knd a0 b0 a1 b1 a2 b2, ((b3 - a3) / 2) * (g (a3, y) + g (b3, y)) := by
    apply setIntegral_mono_on
      (integrableOn_setIntegral_left hint)
      (((hga_cont.add hgb_cont).const_mul ((b3 - a3) / 2)).integrableOn_compact
        (cell3Set_isCompact knd a0 b0 a1 b1 a2 b2))
      (cell3Set_isClosed knd a0 b0 a1 b1 a2 b2).measurableSet
      hinner
  rw [integral_const_mul] at hle1
  have hconv_sum : ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) (fun y => g (a3, y) + g (b3, y)) := by
    have hconv_at : ∀ t ∈ Icc a3 b3, ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) (fun y => g (t, y)) := by
      intro t ht
      refine ⟨cell3Set_convex knd a0 b0 a1 b1 a2 b2, fun y1 hy1 y2 hy2 u v hu hv huv => ?_⟩
      have hmem : ∀ y ∈ cell3Set knd a0 b0 a1 b1 a2 b2, ![y 0, y 1, y 2, t] ∈ cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 := by
        intro y hy; rw [cell4Set_eq_preimage, mem_preimage]
        have heq : equivFin4_3 ![y 0, y 1, y 2, t] = (t, y) := by
          rw [equivFin4_3_apply]; exact Prod.ext rfl (by ext i; fin_cases i <;> rfl)
        rw [heq]; exact ⟨ht, hy⟩
      have h := hconv.2 (hmem y1 hy1) (hmem y2 hy2) hu hv huv
      have heq : u • ![y1 0, y1 1, y1 2, t] + v • ![y2 0, y2 1, y2 2, t] =
          ![(u • y1 + v • y2) 0, (u • y1 + v • y2) 1, (u • y1 + v • y2) 2, t] := by
        ext i; fin_cases i <;> simp [smul_eq_mul] <;> (first | rfl | (rw [← add_mul, huv, one_mul]))
      rw [heq] at h; simpa [g, smul_eq_mul] using h
    exact (hconv_at a3 (left_mem_Icc.mpr h3)).add (hconv_at b3 (right_mem_Icc.mpr h3))
  have h3d := hh_cell3 knd hok hconv_sum (hga_cont.add hgb_cont)
  have hnn : 0 ≤ (b3 - a3) / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left h3d hnn
  have hring : ((b3 - a3) / 2) *
      ((b0 - a0) * (b1 - a1) * (b2 - a2) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ))) =
      (b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3) / ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ))) := by ring
  have hcongr : sumVerts3R (fun y => g (a3, y) + g (b3, y)) knd a0 b0 a1 b1 a2 b2 =
      sumVerts3R (fun y => f ![y 0, y 1, y 2, a3] + f ![y 0, y 1, y 2, b3]) knd a0 b0 a1 b1 a2 b2 := rfl
  rw [hcongr, ← mul_assoc, hring] at hmul; linarith

/-! ### Part 4C: Exact 3D/4D Box Cut Volumes, Ramp Integrals, and `S_3` Symmetry -/

lemma integral_ind_le_sub {c h R : ℝ} (hc : 0 < c) (hh : 0 ≤ h) :
    ∫ t in Icc (0 : ℝ) h, ({t : ℝ | c * t ≤ R}).indicator (fun _ => (1 : ℝ)) t =
      (max 0 R - max 0 (R - c * h)) / c := by
  have hm : MeasurableSet {t : ℝ | c * t ≤ R} :=
    (isClosed_le (continuous_const.mul continuous_id) continuous_const).measurableSet
  rw [setIntegral_indicator hm, setIntegral_const, smul_eq_mul, mul_one]
  by_cases hR0 : R ≤ 0
  · have hemp : Icc (0 : ℝ) h ∩ {t : ℝ | c * t ≤ R} ⊆ ({0} : Set ℝ) := by
      intro t ⟨ht, hle⟩; simp only [mem_singleton_iff]
      have : c * t ≤ 0 := le_trans hle hR0
      have : t ≤ 0 := nonpos_of_mul_nonpos_right this hc
      linarith [ht.1]
    have hvol : volume (Icc (0 : ℝ) h ∩ {t : ℝ | c * t ≤ R}) = 0 :=
      measure_mono_null hemp Real.volume_singleton
    rw [Measure.real, hvol, ENNReal.toReal_zero, max_eq_left hR0, max_eq_left (by nlinarith : R - c * h ≤ 0)]
    ring
  · push Not at hR0
    by_cases hRh : c * h ≤ R
    · have hcap : Icc (0 : ℝ) h ∩ {t : ℝ | c * t ≤ R} = Icc 0 h :=
        inter_eq_self_of_subset_left (fun t ht => by change c * t ≤ R; nlinarith [ht.2])
      rw [hcap, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
          max_eq_right (le_of_lt hR0), max_eq_right (by linarith : 0 ≤ R - c * h)]
      field_simp [ne_of_gt hc]; ring
    · push Not at hRh
      have hcap : Icc (0 : ℝ) h ∩ {t : ℝ | c * t ≤ R} = Icc 0 (R / c) := by
        ext t; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]; constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, (le_div_iff₀' hc).mpr h2⟩
        · rintro ⟨h1, h2⟩
          have hlt : R / c ≤ h := (div_le_iff₀' hc).mpr (le_of_lt hRh)
          exact ⟨⟨h1, le_trans h2 hlt⟩, (le_div_iff₀' hc).mp h2⟩
      rw [hcap, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by have : 0 ≤ R / c := div_nonneg (le_of_lt hR0) (le_of_lt hc); linarith),
          max_eq_right (le_of_lt hR0), max_eq_left (by linarith : R - c * h ≤ 0)]
      ring

private lemma integral_posPow_sub {c h R : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (k : ℕ) :
    ∫ t in (0 : ℝ)..h, (max 0 (R - c * t)) ^ (k + 1) =
      ((max 0 R) ^ (k + 2) - (max 0 (R - c * h)) ^ (k + 2)) / (c * ((k : ℝ) + 2)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => (max 0 (R - c * t)) ^ (k + 1)) (Icc 0 h) := by fun_prop
  by_cases hR0 : R ≤ 0
  · have hz : ∀ t ∈ uIcc 0 h, (max 0 (R - c * t)) ^ (k + 1) = 0 := by
      intro t ht; rw [uIcc_of_le hh] at ht
      rw [max_eq_left (by nlinarith [ht.1] : R - c * t ≤ 0), zero_pow (Nat.succ_ne_zero k)]
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero,
        max_eq_left hR0, max_eq_left (by nlinarith : R - c * h ≤ 0),
        zero_pow (Nat.succ_ne_zero _), sub_self, zero_div]
  · push Not at hR0
    have hpow_int : ∀ (u : ℝ), 0 ≤ u → u ≤ R / c →
        ∫ t in (0 : ℝ)..u, (R - c * t) ^ (k + 1) =
          (R ^ (k + 2) - (R - c * u) ^ (k + 2)) / (c * ((k : ℝ) + 2)) := by
      intro u hu _
      have hd : ∀ t ∈ uIcc 0 u,
          HasDerivAt (fun s : ℝ => -((R - c * s) ^ (k + 2)) / (c * ((k : ℝ) + 2)))
            ((R - c * t) ^ (k + 1)) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => R - c * s) (-c) t :=
          ((hasDerivAt_const t R).sub ((hasDerivAt_id t).const_mul c)).congr_deriv (by ring)
        have h2 := (h1.pow (k + 2)).neg.div_const (c * ((k : ℝ) + 2))
        refine h2.congr_deriv ?_
        push_cast; field_simp [hcne, ne_of_gt hkpos]; try ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (Continuous.intervalIntegrable (by fun_prop) 0 u)]
      field_simp [hcne, ne_of_gt hkpos]; try ring
    by_cases hRh : c * h ≤ R
    · have hcongr : ∀ t ∈ uIcc 0 h, (max 0 (R - c * t)) ^ (k + 1) = (R - c * t) ^ (k + 1) := by
        intro t ht; rw [uIcc_of_le hh] at ht
        rw [max_eq_right (by nlinarith [ht.2] : 0 ≤ R - c * t)]
      rw [intervalIntegral.integral_congr hcongr, hpow_int h hh ((le_div_iff₀' hc).mpr hRh),
          max_eq_right (le_of_lt hR0), max_eq_right (by linarith : 0 ≤ R - c * h)]
    · push Not at hRh
      have hrc_pos : 0 ≤ R / c := le_of_lt (div_pos hR0 hc)
      have hrc_le : R / c ≤ h := (div_le_iff₀' hc).mpr (le_of_lt hRh)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hcont.intervalIntegrable_of_Icc hh).mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hh]; exact ⟨hrc_pos, hrc_le⟩)))
        ((hcont.intervalIntegrable_of_Icc hh).mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hh]; exact ⟨hrc_pos, hrc_le⟩)))]
      have hleft : ∀ t ∈ uIcc 0 (R / c), (max 0 (R - c * t)) ^ (k + 1) = (R - c * t) ^ (k + 1) := by
        intro t ht; rw [uIcc_of_le hrc_pos] at ht
        have : c * t ≤ R := (le_div_iff₀' hc).mp ht.2
        rw [max_eq_right (by linarith)]
      have hright : ∀ t ∈ uIcc (R / c) h, (max 0 (R - c * t)) ^ (k + 1) = 0 := by
        intro t ht; rw [uIcc_of_le hrc_le] at ht
        have : R ≤ c * t := (div_le_iff₀' hc).mp ht.1
        rw [max_eq_left (by linarith), zero_pow (Nat.succ_ne_zero k)]
      rw [intervalIntegral.integral_congr hleft, intervalIntegral.integral_congr hright,
          intervalIntegral.integral_zero, add_zero, hpow_int (R / c) hrc_pos (le_refl _),
          mul_div_cancel₀ R hcne, sub_self, zero_pow (Nat.succ_ne_zero _),
          max_eq_right (le_of_lt hR0), max_eq_left (by linarith : R - c * h ≤ 0),
          zero_pow (Nat.succ_ne_zero _)]

lemma vol_cut_box3_eq {a0 b0 a1 b1 a2 b2 L : ℝ}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :
    ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2,
        ({x : Fin 3 → ℝ | x 0 + x 1 + 2 * x 2 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
      cut3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 12 := by
  let S : Set (ℝ × (ℝ × ℝ)) := {p | p.1 + p.2.1 + 2 * p.2.2 ≤ L}
  have hSm : MeasurableSet S := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hpre : cell3Set .box a0 b0 a1 b1 a2 b2 = equivFin3_prod ⁻¹' (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2)) := by
    ext x; simp [cell3Set, equivFin3_prod_apply]; tauto
  have hfun : ({x : Fin 3 → ℝ | x 0 + x 1 + 2 * x 2 ≤ L}).indicator (fun _ => (1 : ℝ)) =
      (S.indicator (fun _ => (1 : ℝ))) ∘ equivFin3_prod := by
    ext x; simp only [S, equivFin3_prod_apply, Set.indicator, Function.comp_apply, mem_ofPred_eq]; rfl
  rw [hpre, hfun]; simp_rw [Function.comp_apply]
  rw [volume_preserving_equivFin3_prod.setIntegral_preimage_emb equivFin3_prod.measurableEmbedding]
  have hint3 : IntegrableOn (S.indicator (fun _ => (1 : ℝ))) (Icc a0 b0 ×ˢ (Icc a1 b1 ×ˢ Icc a2 b2))
      (volume.prod (volume.prod volume)) :=
    (continuousOn_const.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).indicator hSm
  rw [MeasureTheory.setIntegral_prod _ hint3]
  have hstep1 : ∀ x0 ∈ Icc a0 b0,
      ∫ q in Icc a1 b1 ×ˢ Icc a2 b2, S.indicator (fun _ => (1 : ℝ)) (x0, q) ∂(volume.prod volume) =
        ((max 0 (L - x0 - a1 - 2 * a2)) ^ 2 - (max 0 (L - x0 - b1 - 2 * a2)) ^ 2 -
         (max 0 (L - x0 - a1 - 2 * b2)) ^ 2 + (max 0 (L - x0 - b1 - 2 * b2)) ^ 2) / 4 := by
    intro x0 _
    have hint2 : IntegrableOn (fun q : ℝ × ℝ => S.indicator (fun _ => (1 : ℝ)) (x0, q))
        (Icc a1 b1 ×ˢ Icc a2 b2) (volume.prod volume) := by
      have hm2 : MeasurableSet {q : ℝ × ℝ | x0 + q.1 + 2 * q.2 ≤ L} :=
        (isClosed_le (by fun_prop) continuous_const).measurableSet
      have heq : (fun q : ℝ × ℝ => S.indicator (fun _ => (1 : ℝ)) (x0, q)) =
          ({q : ℝ × ℝ | x0 + q.1 + 2 * q.2 ≤ L}).indicator (fun _ => (1 : ℝ)) := by
        ext ⟨x1, x2⟩; simp [S, Set.indicator]
      rw [heq]
      exact (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).indicator hm2
    rw [MeasureTheory.setIntegral_prod _ hint2]
    have hinner : ∀ x1 ∈ Icc a1 b1,
        ∫ x2 in Icc a2 b2, S.indicator (fun _ => (1 : ℝ)) (x0, x1, x2) =
          (max 0 (L - x0 - x1 - 2 * a2) - max 0 (L - x0 - x1 - 2 * b2)) / 2 := by
      intro x1 _
      have htr : ∫ x2 in Icc a2 b2, S.indicator (fun _ => (1 : ℝ)) (x0, x1, x2) =
          ∫ t in Icc (0 : ℝ) (b2 - a2), ({t : ℝ | 2 * t ≤ L - x0 - x1 - 2 * a2}).indicator (fun _ => (1 : ℝ)) t := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2,
            MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (sub_nonneg.mpr h2)]
        rw [show a2 = 0 + a2 by ring, show b2 = (b2 - a2) + a2 by ring, ← intervalIntegral.integral_comp_add_right (fun x2 => S.indicator (fun _ => (1 : ℝ)) (x0, x1, x2)) a2]
        have heq_fn : (fun t : ℝ => S.indicator (fun _ => (1 : ℝ)) (x0, x1, t + a2)) =
            ({t : ℝ | 2 * t ≤ L - x0 - x1 - 2 * a2}).indicator (fun _ => (1 : ℝ)) := by
          ext t; simp only [Set.indicator, S, mem_ofPred_eq]; split_ifs with h' h'' <;> try rfl
          · exfalso; apply h''; linarith
          · exfalso; apply h'; linarith
        rw [heq_fn]; congr 1 <;> ring
      rw [htr, integral_ind_le_sub (by norm_num : (0 : ℝ) < 2) (sub_nonneg.mpr h2)]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Icc hinner,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
    have hsh : ∫ x1 in a1..b1, (max 0 (L - x0 - x1 - 2 * a2) - max 0 (L - x0 - x1 - 2 * b2)) / 2 =
        ((∫ t in (0 : ℝ)..(b1 - a1), (max 0 ((L - x0 - a1 - 2 * a2) - 1 * t)) ^ 1) -
         (∫ t in (0 : ℝ)..(b1 - a1), (max 0 ((L - x0 - a1 - 2 * b2) - 1 * t)) ^ 1)) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) a1 b1)
        (Continuous.intervalIntegrable (by fun_prop) a1 b1)]
      congr 1; congr 1
      · rw [show a1 = 0 + a1 by ring, show b1 = (b1 - a1) + a1 by ring, ← intervalIntegral.integral_comp_add_right (fun x1 => max 0 (L - x0 - x1 - 2 * a2)) a1]
        have : (fun t : ℝ => max 0 (L - x0 - (t + a1) - 2 * a2)) =
            (fun t : ℝ => (max 0 ((L - x0 - a1 - 2 * a2) - 1 * t)) ^ 1) := by ext t; simp; ring_nf
        rw [this]; congr 1 <;> ring
      · rw [show a1 = 0 + a1 by ring, show b1 = (b1 - a1) + a1 by ring, ← intervalIntegral.integral_comp_add_right (fun x1 => max 0 (L - x0 - x1 - 2 * b2)) a1]
        have : (fun t : ℝ => max 0 (L - x0 - (t + a1) - 2 * b2)) =
            (fun t : ℝ => (max 0 ((L - x0 - a1 - 2 * b2) - 1 * t)) ^ 1) := by ext t; simp; ring_nf
        rw [this]; congr 1 <;> ring
    rw [hsh, integral_posPow_sub (by norm_num : (0 : ℝ) < 1) (sub_nonneg.mpr h1) 0,
        integral_posPow_sub (by norm_num : (0 : ℝ) < 1) (sub_nonneg.mpr h1) 0]
    norm_num; ring_nf
  rw [setIntegral_congr_fun measurableSet_Icc hstep1,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0]
  have hsh0 : ∀ C : ℝ, ∫ x0 in a0..b0, (max 0 (C - x0)) ^ 2 =
      ((max 0 (C - a0)) ^ 3 - (max 0 (C - b0)) ^ 3) / 3 := by
    intro C
    rw [show a0 = 0 + a0 by ring, show b0 = (b0 - a0) + a0 by ring, ← intervalIntegral.integral_comp_add_right (fun x0 => (max 0 (C - x0)) ^ 2) a0]
    have : (fun t : ℝ => (max 0 (C - (t + a0))) ^ 2) = (fun t : ℝ => (max 0 ((C - a0) - 1 * t)) ^ 2) := by
      ext t; ring_nf
    rw [this, integral_posPow_sub (by norm_num : (0 : ℝ) < 1) (sub_nonneg.mpr h0) 1]
    norm_num; try ring_nf
  have hi : ∀ C : ℝ, IntervalIntegrable (fun x0 => (max 0 (C - x0)) ^ 2) volume a0 b0 :=
    fun C => Continuous.intervalIntegrable (by fun_prop) a0 b0
  have hre : (fun x0 : ℝ => ((max 0 (L - x0 - a1 - 2 * a2)) ^ 2 - (max 0 (L - x0 - b1 - 2 * a2)) ^ 2 -
       (max 0 (L - x0 - a1 - 2 * b2)) ^ 2 + (max 0 (L - x0 - b1 - 2 * b2)) ^ 2) / 4) =
      (fun x0 : ℝ => (((max 0 ((L - a1 - 2 * a2) - x0)) ^ 2 - (max 0 ((L - b1 - 2 * a2) - x0)) ^ 2) -
       (max 0 ((L - a1 - 2 * b2) - x0)) ^ 2 + (max 0 ((L - b1 - 2 * b2) - x0)) ^ 2) / 4) := by
    ext x0; ring_nf
  rw [hre, intervalIntegral.integral_div,
      intervalIntegral.integral_add (((hi _).sub (hi _)).sub (hi _)) (hi _),
      intervalIntegral.integral_sub ((hi _).sub (hi _)) (hi _),
      intervalIntegral.integral_sub (hi _) (hi _),
      hsh0, hsh0, hsh0, hsh0]
  dsimp only [cut3SumR]; ring_nf

lemma int_ramp_box3_eq {a0 b0 a1 b1 a2 b2 L : ℝ}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :
    ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, max 0 (L - (x 0 + x 1 + 2 * x 2)) =
      ramp3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 48 := by
  have hcont : ContinuousOn (fun x : Fin 3 → ℝ => max 0 (L - (x 0 + x 1 + 2 * x 2))) (cell3Set .box a0 b0 a1 b1 a2 b2) := by
    fun_prop
  rw [integral_cell3_eq_iter .box h0 h1 h2 hcont]
  have hpow_sh : ∀ (k : ℕ) (c a b C : ℝ), 0 < c → a ≤ b →
      ∫ t in a..b, (max 0 (C - c * t)) ^ (k + 1) =
        ((max 0 (C - c * a)) ^ (k + 2) - (max 0 (C - c * b)) ^ (k + 2)) / (c * ((k : ℝ) + 2)) := by
    intro k c a b C hc hab
    rw [show a = 0 + a by ring, show b = (b - a) + a by ring, ← intervalIntegral.integral_comp_add_right (fun t => (max 0 (C - c * t)) ^ (k + 1)) a]
    have : (fun t : ℝ => (max 0 (C - c * (t + a))) ^ (k + 1)) =
        (fun t : ℝ => (max 0 ((C - c * a) - c * t)) ^ (k + 1)) := by ext t; ring_nf
    rw [this, integral_posPow_sub hc (sub_nonneg.mpr hab) k]
    ring_nf
  have hstep2 : ∀ x0 x1 : ℝ,
      ∫ x2 in a2..b2, max 0 (L - (x0 + x1 + 2 * x2)) =
        ((max 0 ((L - x0 - x1) - 2 * a2)) ^ 2 - (max 0 ((L - x0 - x1) - 2 * b2)) ^ 2) / 4 := by
    intro x0 x1
    have : (fun x2 : ℝ => max 0 (L - (x0 + x1 + 2 * x2))) =
        (fun x2 : ℝ => (max 0 ((L - x0 - x1) - 2 * x2)) ^ 1) := by ext x2; simp; ring_nf
    rw [this, hpow_sh 0 2 a2 b2 (L - x0 - x1) (by norm_num) h2]; norm_num
  simp_rw [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hstep2]
  have hstep1 : ∀ x0 : ℝ,
      ∫ x1 in a1..b1, ((max 0 (L - x0 - x1 - 2 * a2)) ^ 2 - (max 0 (L - x0 - x1 - 2 * b2)) ^ 2) / 4 =
        (((max 0 ((L - x0 - 2 * a2) - a1)) ^ 3 - (max 0 ((L - x0 - 2 * a2) - b1)) ^ 3) -
         ((max 0 ((L - x0 - 2 * b2) - a1)) ^ 3 - (max 0 ((L - x0 - 2 * b2) - b1)) ^ 3)) / 12 := by
    intro x0
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) a1 b1)
      (Continuous.intervalIntegrable (by fun_prop) a1 b1)]
    have e1 : (fun x1 : ℝ => (max 0 (L - x0 - x1 - 2 * a2)) ^ 2) =
        (fun x1 : ℝ => (max 0 ((L - x0 - 2 * a2) - 1 * x1)) ^ 2) := by ext x1; ring_nf
    have e2 : (fun x1 : ℝ => (max 0 (L - x0 - x1 - 2 * b2)) ^ 2) =
        (fun x1 : ℝ => (max 0 ((L - x0 - 2 * b2) - 1 * x1)) ^ 2) := by ext x1; ring_nf
    rw [e1, e2, hpow_sh 1 1 a1 b1 _ (by norm_num) h1, hpow_sh 1 1 a1 b1 _ (by norm_num) h1]
    norm_num; ring_nf
  simp_rw [hstep1]
  have hi : ∀ C : ℝ, IntervalIntegrable (fun x0 => (max 0 (C - 1 * x0)) ^ 3) volume a0 b0 :=
    fun C => Continuous.intervalIntegrable (by fun_prop) a0 b0
  have hre : (fun x0 : ℝ =>
      (((max 0 (L - x0 - 2 * a2 - a1)) ^ 3 - (max 0 (L - x0 - 2 * a2 - b1)) ^ 3) -
       ((max 0 (L - x0 - 2 * b2 - a1)) ^ 3 - (max 0 (L - x0 - 2 * b2 - b1)) ^ 3)) / 12) =
      (fun x0 : ℝ =>
      (((max 0 ((L - 2 * a2 - a1) - 1 * x0)) ^ 3 - (max 0 ((L - 2 * a2 - b1) - 1 * x0)) ^ 3) -
       ((max 0 ((L - 2 * b2 - a1) - 1 * x0)) ^ 3 - (max 0 ((L - 2 * b2 - b1) - 1 * x0)) ^ 3)) / 12) := by
    ext x0; ring_nf
  rw [hre, intervalIntegral.integral_div,
      intervalIntegral.integral_sub ((hi _).sub (hi _)) ((hi _).sub (hi _)),
      intervalIntegral.integral_sub (hi _) (hi _),
      intervalIntegral.integral_sub (hi _) (hi _),
      hpow_sh 2 1 a0 b0 _ (by norm_num) h0, hpow_sh 2 1 a0 b0 _ (by norm_num) h0,
      hpow_sh 2 1 a0 b0 _ (by norm_num) h0, hpow_sh 2 1 a0 b0 _ (by norm_num) h0]
  dsimp only [ramp3SumR]; norm_num; ring_nf

lemma vol_cut_box4_eq {a0 b0 a1 b1 a2 b2 a3 b3 L : ℝ}
    (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) :
    ∫ x in cell4Set .box a0 b0 a1 b1 a2 b2 a3 b3,
        ({x : Fin 4 → ℝ | x 0 + x 1 + 2 * x 2 + x 3 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
      cut4SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (b3 - a3) (L - (a0 + a1 + 2 * a2 + a3)) / 48 := by
  let S : Set (ℝ × (Fin 3 → ℝ)) := {p | p.2 0 + p.2 1 + 2 * p.2 2 + p.1 ≤ L}
  have hSm : MeasurableSet S := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hfun : ({x : Fin 4 → ℝ | x 0 + x 1 + 2 * x 2 + x 3 ≤ L}).indicator (fun _ => (1 : ℝ)) =
      (S.indicator (fun _ => (1 : ℝ))) ∘ equivFin4_3 := by
    ext x; simp [S, equivFin4_3_apply, Set.indicator]
  rw [cell4Set_eq_preimage, hfun]; simp_rw [Function.comp_apply]
  rw [volume_preserving_equivFin4_3.setIntegral_preimage_emb equivFin4_3.measurableEmbedding]
  have hint4 : IntegrableOn (S.indicator (fun _ => (1 : ℝ))) (Icc a3 b3 ×ˢ cell3Set .box a0 b0 a1 b1 a2 b2)
      (volume.prod volume) :=
    (continuousOn_const.integrableOn_compact (isCompact_Icc.prod (cell3Set_isCompact .box _ _ _ _ _ _))).indicator hSm
  rw [MeasureTheory.setIntegral_prod _ hint4]
  have hinner : ∀ x3 ∈ Icc a3 b3,
      ∫ y in cell3Set .box a0 b0 a1 b1 a2 b2, S.indicator (fun _ => (1 : ℝ)) (x3, y) =
        cut3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) ((L - x3) - (a0 + a1 + 2 * a2)) / 12 := by
    intro x3 _
    have heq : (fun y : Fin 3 → ℝ => S.indicator (fun _ => (1 : ℝ)) (x3, y)) =
        ({y : Fin 3 → ℝ | y 0 + y 1 + 2 * y 2 ≤ L - x3}).indicator (fun _ => (1 : ℝ)) := by
      ext y; simp only [Set.indicator, S, mem_ofPred_eq]; split_ifs with h' h'' <;> try rfl
      · exfalso; apply h''; linarith
      · exfalso; apply h'; linarith
    rw [heq, vol_cut_box3_eq h0 h1 h2]
  rw [setIntegral_congr_fun measurableSet_Icc hinner,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h3]
  have hsh3 : ∀ C : ℝ, ∫ x3 in a3..b3, (max 0 (C - x3)) ^ 3 =
      ((max 0 (C - a3)) ^ 4 - (max 0 (C - b3)) ^ 4) / 4 := by
    intro C
    rw [show a3 = 0 + a3 by ring, show b3 = (b3 - a3) + a3 by ring, ← intervalIntegral.integral_comp_add_right (fun x3 => (max 0 (C - x3)) ^ 3) a3]
    have : (fun t : ℝ => (max 0 (C - (t + a3))) ^ 3) = (fun t : ℝ => (max 0 ((C - a3) - 1 * t)) ^ 3) := by
      ext t; ring_nf
    rw [this, integral_posPow_sub (by norm_num : (0 : ℝ) < 1) (sub_nonneg.mpr h3) 2]
    norm_num
  have hi : ∀ C : ℝ, IntervalIntegrable (fun x3 => (max 0 (C - x3)) ^ 3) volume a3 b3 :=
    fun C => Continuous.intervalIntegrable (by fun_prop) a3 b3
  have hre : (fun x3 : ℝ => cut3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - x3 - (a0 + a1 + 2 * a2)) / 12) =
      (fun x3 : ℝ =>
        (((max 0 ((L - (a0 + a1 + 2 * a2)) - x3)) ^ 3 +
          (max 0 ((L - (b0 + b1 + 2 * a2)) - x3)) ^ 3 +
          (max 0 ((L - (b0 + a1 + 2 * b2)) - x3)) ^ 3 +
          (max 0 ((L - (a0 + b1 + 2 * b2)) - x3)) ^ 3) -
         ((max 0 ((L - (b0 + a1 + 2 * a2)) - x3)) ^ 3 +
          (max 0 ((L - (a0 + b1 + 2 * a2)) - x3)) ^ 3 +
          (max 0 ((L - (a0 + a1 + 2 * b2)) - x3)) ^ 3 +
          (max 0 ((L - (b0 + b1 + 2 * b2)) - x3)) ^ 3)) / 12) := by
    ext x3; dsimp only [cut3SumR]; ring_nf
  rw [hre, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        (((hi _).add (hi _)).add (hi _) |>.add (hi _))
        (((hi _).add (hi _)).add (hi _) |>.add (hi _)),
      intervalIntegral.integral_add (((hi _).add (hi _)).add (hi _)) (hi _),
      intervalIntegral.integral_add ((hi _).add (hi _)) (hi _),
      intervalIntegral.integral_add (hi _) (hi _),
      intervalIntegral.integral_add (((hi _).add (hi _)).add (hi _)) (hi _),
      intervalIntegral.integral_add ((hi _).add (hi _)) (hi _),
      intervalIntegral.integral_add (hi _) (hi _),
      hsh3, hsh3, hsh3, hsh3, hsh3, hsh3, hsh3, hsh3]
  dsimp only [cut4SumR]; ring_nf

lemma volume_fin3_coord_eq_zero (i : Fin 3) (m : ℝ) :
    volume ({x : Fin 3 → ℝ | x i = m}) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hpre : {x : Fin 3 → ℝ | x i = m} = e ⁻¹' ({m} ×ˢ Set.univ) := by
    ext x; simp [e]
  rw [hpre, hmp.measure_preimage (MeasurableSet.prod (measurableSet_singleton m) MeasurableSet.univ).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private lemma setIntegral_biUnion_finset_ae {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [DecidableEq ι] (t : Finset ι) {s : ι → Set α} {f : α → ℝ}
    (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hd : Set.Pairwise (t : Set ι) (fun i j => AEDisjoint μ (s i) (s j)))
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hdu : AEDisjoint μ (s a) (⋃ i ∈ u, s i) := by
      rw [AEDisjoint, inter_iUnion₂]
      exact (measure_biUnion_null_iff u.countable_toSet).mpr (fun i hi =>
        hd (Finset.mem_insert_self a u) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
    have hmu : MeasurableSet (⋃ i ∈ u, s i) :=
      Finset.measurableSet_biUnion u (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hfu : IntegrableOn f (⋃ i ∈ u, s i) μ :=
      integrableOn_finset_iUnion.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [setIntegral_union₀ hdu hmu.nullMeasurableSet (hf a (Finset.mem_insert_self a u)) hfu]
    rw [ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (hd.mono (Finset.coe_subset.mpr (Finset.subset_insert a u)))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma volume_fin3_eq_coord_zero {i j : Fin 3} (hij : i ≠ j) :
    volume ({x : Fin 3 → ℝ | x i = x j}) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  obtain ⟨k, rfl⟩ : ∃ k : Fin 2, i.succAbove k = j := Fin.exists_succAbove_eq hij.symm
  let S : Set (ℝ × (Fin 2 → ℝ)) := {p | p.1 = p.2 k}
  have hSm : MeasurableSet S := (isClosed_eq continuous_fst (by fun_prop : Continuous fun p : ℝ × (Fin 2 → ℝ) => p.2 k)).measurableSet
  have hpre : {x : Fin 3 → ℝ | x i = x (i.succAbove k)} = e ⁻¹' S := by
    ext x; rfl
  rw [hpre, hmp.measure_preimage hSm.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply_symm hSm]
  have hslice : ∀ y : Fin 2 → ℝ, volume ((Prod.mk · y) ⁻¹' S) = 0 := by
    intro y
    have : (Prod.mk · y) ⁻¹' S = {y k} := by ext t; simp [S]
    rw [this, Real.volume_singleton]
  simp [hslice]

lemma s3_antitone_le (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hok : cell3Ok knd a0 b0 a1 b1 a2 b2)
    {g : ℝ → ℝ} (hgnn : ∀ s, 0 ≤ g s) (hganti : Antitone g)
    (hint : IntegrableOn (fun x : Fin 3 → ℝ => g (x 0 + x 1 + 2 * x 2)) (cell3Set .box a0 b0 a1 b1 a2 b2) volume) :
    ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2) ≤
      (1 / (facDen knd : ℝ)) * ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2) := by
  rcases hok with ⟨_, _, _, hkm⟩
  let F : (Fin 3 → ℝ) → ℝ := fun x => g (x 0 + x 1 + 2 * x 2)
  have hFnn : ∀ x, 0 ≤ F x := fun x => hgnn _
  cases knd with
  | box => simp [facDen]
  | tri01 =>
    rcases hkm with ⟨rfl, rfl⟩
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) σ
    have hmp : MeasurePreserving e volume volume :=
      MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) σ
    set A := cell3Set .tri01 a0 b0 a0 b0 a2 b2
    set B : Set (Fin 3 → ℝ) := {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a0 b0 ∧ x 2 ∈ Icc a2 b2 ∧ x 1 ≤ x 0}
    have hAm : MeasurableSet A := (cell3Set_isClosed .tri01 _ _ _ _ _ _).measurableSet
    have hBm : MeasurableSet B := ((isClosed_Icc.preimage (continuous_apply 0)).inter
      ((isClosed_Icc.preimage (continuous_apply 1)).inter
        ((isClosed_Icc.preimage (continuous_apply 2)).inter
          (isClosed_le (continuous_apply 1) (continuous_apply 0))))).measurableSet
    have hpre : B = e ⁻¹' A := by
      ext x; simp only [A, B, cell3Set, mem_preimage, mem_ofPred_eq, e, σ]
      have h0 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 0 = x 1 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 1; rwa [show Equiv.swap (0 : Fin 3) 1 1 = 0 by decide] at h
      have h1 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 1 = x 0 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 0; rwa [show Equiv.swap (0 : Fin 3) 1 0 = 1 by decide] at h
      have h2 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 2 = x 2 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 2; rwa [show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide] at h
      rw [h0, h1, h2]; tauto
    have hFeq : F ∘ e = F := by
      ext x; dsimp only [Function.comp_apply, F, e, σ]
      have h0 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 0 = x 1 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 1; rwa [show Equiv.swap (0 : Fin 3) 1 1 = 0 by decide] at h
      have h1 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 1 = x 0 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 0; rwa [show Equiv.swap (0 : Fin 3) 1 0 = 1 by decide] at h
      have h2 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1) x) 2 = x 2 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 3) 1) (β := fun _ => ℝ) x 2; rwa [show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide] at h
      rw [h0, h1, h2]; congr 1; ring
    have heqAB : ∫ x in B, F x = ∫ x in A, F x := by
      rw [hpre]; conv_lhs => rw [← hFeq]
      simp_rw [Function.comp_apply]; exact hmp.setIntegral_preimage_emb e.measurableEmbedding F A
    have hcov : cell3Set .box a0 b0 a0 b0 a2 b2 = A ∪ B := by
      ext x; simp only [cell3Set, A, B, mem_union, mem_ofPred_eq]; constructor
      · rintro ⟨h0x, h1x, h2x⟩; rcases le_total (x 0) (x 1) with h | h
        · left; exact ⟨h0x, h1x, h2x, h⟩
        · right; exact ⟨h0x, h1x, h2x, h⟩
      · rintro (⟨h0x, h1x, h2x, _⟩ | ⟨h0x, h1x, h2x, _⟩) <;> exact ⟨h0x, h1x, h2x⟩
    have hdisj : AEDisjoint volume A B := by
      rw [AEDisjoint]
      refine measure_mono_null (fun x ⟨hxA, hxB⟩ => le_antisymm hxA.2.2.2 hxB.2.2.2)
        (volume_fin3_eq_coord_zero (by decide : (0 : Fin 3) ≠ 1))
    have hsum : ∫ x in cell3Set .box a0 b0 a0 b0 a2 b2, F x = (∫ x in A, F x) + (∫ x in B, F x) := by
      rw [hcov]
      exact setIntegral_union₀ hdisj hBm.nullMeasurableSet (hint.mono_set (by rw [hcov]; exact subset_union_left))
        (hint.mono_set (by rw [hcov]; exact subset_union_right))
    simp only [facDen]; push_cast; linarith
  | tri12 =>
    rcases hkm with ⟨rfl, rfl⟩
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) σ
    have hmp : MeasurePreserving e volume volume :=
      MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) σ
    set A := cell3Set .tri12 a0 b0 a1 b1 a1 b1
    set B : Set (Fin 3 → ℝ) := {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a1 b1 ∧ x 2 ∈ Icc a1 b1 ∧ x 2 ≤ x 1}
    have hBm : MeasurableSet B := ((isClosed_Icc.preimage (continuous_apply 0)).inter
      ((isClosed_Icc.preimage (continuous_apply 1)).inter
        ((isClosed_Icc.preimage (continuous_apply 2)).inter
          (isClosed_le (continuous_apply 2) (continuous_apply 1))))).measurableSet
    have hpre : B = e ⁻¹' A := by
      ext x; simp only [A, B, cell3Set, mem_preimage, mem_ofPred_eq, e, σ]
      have h0 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 0 = x 0 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 0; rwa [show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide] at h
      have h1 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 1 = x 2 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 2; rwa [show Equiv.swap (1 : Fin 3) 2 2 = 1 by decide] at h
      have h2 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 2 = x 1 := by
        have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 1; rwa [show Equiv.swap (1 : Fin 3) 2 1 = 2 by decide] at h
      rw [h0, h1, h2]; tauto
    have hcov : cell3Set .box a0 b0 a1 b1 a1 b1 = A ∪ B := by
      ext x; simp only [cell3Set, A, B, mem_union, mem_ofPred_eq]; constructor
      · rintro ⟨h0x, h1x, h2x⟩; rcases le_total (x 1) (x 2) with h | h
        · left; exact ⟨h0x, h1x, h2x, h⟩
        · right; exact ⟨h0x, h1x, h2x, h⟩
      · rintro (⟨h0x, h1x, h2x, _⟩ | ⟨h0x, h1x, h2x, _⟩) <;> exact ⟨h0x, h1x, h2x⟩
    have hintA : IntegrableOn F A volume := hint.mono_set (by rw [hcov]; exact subset_union_left)
    have hintB : IntegrableOn F B volume := hint.mono_set (by rw [hcov]; exact subset_union_right)
    have hleAB : ∫ x in A, F x ≤ ∫ x in B, F x := by
      have htr : ∫ x in A, F x = ∫ x in B, (F ∘ e) x := by
        rw [hpre]; exact (hmp.setIntegral_preimage_emb e.measurableEmbedding F A).symm
      rw [htr]
      refine setIntegral_mono_on ?_ hintB hBm ?_
      · rw [hpre]; exact (hmp.integrableOn_comp_preimage e.measurableEmbedding).mpr hintA
      · intro x hxB
        dsimp only [Function.comp_apply, F, e, σ]
        have h0 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 0 = x 0 := by
          have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 0; rwa [show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide] at h
        have h1 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 1 = x 2 := by
          have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 2; rwa [show Equiv.swap (1 : Fin 3) 2 2 = 1 by decide] at h
        have h2 : (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 1 2) x) 2 = x 1 := by
          have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (1 : Fin 3) 2) (β := fun _ => ℝ) x 1; rwa [show Equiv.swap (1 : Fin 3) 2 1 = 2 by decide] at h
        rw [h0, h1, h2]
        exact hganti (by linarith [hxB.2.2.2])
    have hdisj : AEDisjoint volume A B := by
      rw [AEDisjoint]
      refine measure_mono_null (fun x ⟨hxA, hxB⟩ => le_antisymm hxA.2.2.2 hxB.2.2.2)
        (volume_fin3_eq_coord_zero (by decide : (1 : Fin 3) ≠ 2))
    have hsum : ∫ x in cell3Set .box a0 b0 a1 b1 a1 b1, F x = (∫ x in A, F x) + (∫ x in B, F x) := by
      rw [hcov]; exact setIntegral_union₀ hdisj hBm.nullMeasurableSet hintA hintB
    simp only [facDen]; push_cast; linarith
  | simp =>
    rcases hkm with ⟨rfl, rfl, rfl, rfl⟩
    set A := cell3Set .simp a0 b0 a0 b0 a0 b0
    set Bbox := cell3Set .box a0 b0 a0 b0 a0 b0
    let eP : Equiv.Perm (Fin 3) → ((Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ)) :=
      fun σ => MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) σ
    let Sσ : Equiv.Perm (Fin 3) → Set (Fin 3 → ℝ) := fun σ => (eP σ) ⁻¹' A
    have hmpP : ∀ σ, MeasurePreserving (eP σ) volume volume :=
      fun σ => MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) σ
    have hSσ_meas : ∀ σ, MeasurableSet (Sσ σ) := fun σ =>
      (eP σ).measurable (cell3Set_isClosed .simp _ _ _ _ _ _).measurableSet
    have hSσ_sub : ∀ σ, Sσ σ ⊆ Bbox := by
      intro σ x hx
      have hmem : ∀ i : Fin 3, x i ∈ Icc a0 b0 := by
        intro i
        have hi : (eP σ x) (σ i) = x i := MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ => ℝ) x i
        rw [← hi]
        have : σ i = 0 ∨ σ i = 1 ∨ σ i = 2 := by generalize hsi : σ i = j; fin_cases j <;> simp
        rcases this with h | h | h <;> rw [h]
        · exact hx.1
        · exact hx.2.1
        · exact hx.2.2.1
      exact ⟨hmem 0, hmem 1, hmem 2⟩
    have hle_each : ∀ σ : Equiv.Perm (Fin 3), ∫ x in A, F x ≤ ∫ x in Sσ σ, F x := by
      intro σ
      have htr : ∫ x in A, F x = ∫ x in Sσ σ, (F ∘ eP σ) x :=
        ((hmpP σ).setIntegral_preimage_emb (eP σ).measurableEmbedding F A).symm
      rw [htr]
      refine setIntegral_mono_on ?_ (hint.mono_set (hSσ_sub σ)) (hSσ_meas σ) ?_
      · exact ((hmpP σ).integrableOn_comp_preimage (eP σ).measurableEmbedding).mpr
          (hint.mono_set (hSσ_sub 1))
      · intro x hx
        dsimp only [Function.comp_apply, F]
        have hsum_eq : (eP σ x) 0 + (eP σ x) 1 + (eP σ x) 2 = x 0 + x 1 + x 2 := by
          have h1 : ∑ i : Fin 3, (eP σ x) i = ∑ i : Fin 3, x i := by
            have : ∀ i : Fin 3, (eP σ x) i = x (σ.symm i) := fun i => by
              simp [eP, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
            simp_rw [this]
            exact Equiv.sum_comp σ.symm x
          simpa [Fin.sum_univ_three] using h1
        have h2_ge : x 2 ≤ (eP σ x) 2 := by
          have h2eq : x 2 = (eP σ x) (σ 2) := (MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ => ℝ) x 2).symm
          rw [h2eq]
          have : σ 2 = 0 ∨ σ 2 = 1 ∨ σ 2 = 2 := by generalize hs2 : σ 2 = j; fin_cases j <;> simp
          rcases this with h | h | h <;> rw [h]
          · exact le_trans hx.2.2.2.1 hx.2.2.2.2
          · exact hx.2.2.2.2
        exact hganti (by linarith)
    have hpair : Pairwise (fun σ τ : Equiv.Perm (Fin 3) => AEDisjoint volume (Sσ σ) (Sσ τ)) := by
      intro σ τ hne
      rw [AEDisjoint]
      -- If σ ≠ τ, there exist distinct i ≠ j such that x i = x j on Sσ σ ∩ Sσ τ!
      have hex : ∃ i j : Fin 3, i ≠ j ∧ Sσ σ ∩ Sσ τ ⊆ {x : Fin 3 → ℝ | x i = x j} := by
        -- Since σ ≠ τ, σ.symm ≠ τ.symm, so ∃ a b, a < b ∧ σ.symm a > ...
        -- Even simpler: if x ∈ Sσ σ ∩ Sσ τ and x is strictly injective (x i ≠ x j for i ≠ j),
        -- then sorting x uniquely determines the permutation, contradicting σ ≠ τ!
        by_contra hno
        push Not at hno
        -- Pick i ≠ j such that σ.symm i < σ.symm j is reversed? No, use Fin 3 decidability:
        have hex_pair : ∃ i j : Fin 3, i ≠ j ∧ σ i < σ j ∧ τ j < τ i :=
          (show ∀ σ' τ' : Equiv.Perm (Fin 3), σ' ≠ τ' → ∃ i j : Fin 3, i ≠ j ∧ σ' i < σ' j ∧ τ' j < τ' i by decide) σ τ hne
        rcases hex_pair with ⟨i, j, hij, hσ, hτ⟩
        apply hno i j hij
        intro x ⟨hxσ, hxτ⟩
        have hle1 : x i ≤ x j := by
          have hi : x i = (eP σ x) (σ i) := by simp [eP, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          have hj : x j = (eP σ x) (σ j) := by simp [eP, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          rw [hi, hj]
          have : ∀ u v : Fin 3, u < v → (eP σ x) u ≤ (eP σ x) v := by
            intro u v huv; fin_cases u <;> fin_cases v <;> simp at huv ⊢
            · exact hxσ.2.2.2.1
            · exact le_trans hxσ.2.2.2.1 hxσ.2.2.2.2
            · exact hxσ.2.2.2.2
          exact this _ _ hσ
        have hle2 : x j ≤ x i := by
          have hi : x i = (eP τ x) (τ i) := by simp [eP, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          have hj : x j = (eP τ x) (τ j) := by simp [eP, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          rw [hi, hj]
          have : ∀ u v : Fin 3, u < v → (eP τ x) u ≤ (eP τ x) v := by
            intro u v huv; fin_cases u <;> fin_cases v <;> simp at huv ⊢
            · exact hxτ.2.2.2.1
            · exact le_trans hxτ.2.2.2.1 hxτ.2.2.2.2
            · exact hxτ.2.2.2.2
          exact this _ _ hτ
        exact le_antisymm hle1 hle2
      rcases hex with ⟨i, j, hij, hsub⟩
      exact measure_mono_null hsub (volume_fin3_eq_coord_zero hij)
    have hun_sub : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))), Sσ σ) ⊆ Bbox := by
      intro x hx; simp only [mem_iUnion, Finset.mem_univ, true_and, exists_prop] at hx
      rcases hx with ⟨σ, hσ⟩; exact hSσ_sub σ hσ
    have hsum_eq := setIntegral_biUnion_finset_ae (Finset.univ : Finset (Equiv.Perm (Fin 3)))
      (fun σ _ => hSσ_meas σ) (fun σ _ τ _ hne => hpair hne) (fun σ _ => hint.mono_set (hSσ_sub σ))
    have hsum_le : ∑ σ : Equiv.Perm (Fin 3), ∫ x in Sσ σ, F x ≤ ∫ x in Bbox, F x := by
      rw [← hsum_eq]
      exact setIntegral_mono_set hint (ae_restrict_of_forall_mem (cell3Set_isClosed .box _ _ _ _ _ _).measurableSet (fun x _ => hFnn x))
        (Filter.Eventually.of_forall hun_sub)
    have h6 : (6 : ℝ) * (∫ x in A, F x) ≤ ∑ σ : Equiv.Perm (Fin 3), ∫ x in Sσ σ, F x := by
      calc (6 : ℝ) * (∫ x in A, F x)
          = ∑ _σ : Equiv.Perm (Fin 3), ∫ x in A, F x := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]; norm_num
        _ ≤ ∑ σ : Equiv.Perm (Fin 3), ∫ x in Sσ σ, F x := Finset.sum_le_sum (fun σ _ => hle_each σ)
    simp only [facDen]; push_cast; linarith



end Sol_Buchstab4DT_Geom

theorem solution :
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ u, 0 ≤ ω u) ∧
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {u : ℝ}, 1 ≤ u → ω u ≤ max (1 / u) (2 / 3)) ∧
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ u, ω u ≤ 1) ∧
(∀ {E : Type} [AddCommGroup E] [Module ℝ E] {S : Set E}, Convex ℝ S →
  ∀ {k : ℕ} (L : Fin k → E → ℝ),
    (∀ i, ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      L i (a • x + b • y) = a * L i x + b * L i y) →
    (∀ i, ∀ x ∈ S, 0 < L i x) →
    ConvexOn ℝ S (fun x => (∏ i : Fin k, L i x)⁻¹)) ∧
(∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ}, ConvexOn ℝ (Icc a b) f → ContinuousOn f (Icc a b) →
  ∫ x in a..b, f x ≤ ((b - a) / 2) * (f a + f b)) ∧
(∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ}, ConvexOn ℝ (Icc a b) f → ContinuousOn f (Icc a b) →
  (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x) ∧
(MeasurePreserving equivFin4_3 (volume : Measure (Fin 4 → ℝ))
  ((volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ)))) ∧
(∀ x : Fin 4 → ℝ, equivFin4_3 x = (x 3, ![x 0, x 1, x 2])) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3,
  cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 =
    equivFin4_3 ⁻¹' (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, IsClosed (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, IsCompact (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, IsClosed (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, IsCompact (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, Convex ℝ (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, Convex ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x =
    match knd with
    | .box => ∫ x0 in a0..b0, ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2]
    | .tri01 => ∫ x2 in a2..b2, ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2]
    | .tri12 => ∫ x0 in a0..b0, ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2]
    | .simp => ∫ x2 in a0..b0, ∫ x1 in a0..x2, ∫ x0 in a0..x1, f ![x0, x1, x2]) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f →
  ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x ≤
    ((b0 - a0) * (b1 - a1) * (b2 - a2) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ))) *
      sumVerts3R f knd a0 b0 a1 b1 a2 b2) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f →
  ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ((b0 - a0) * (b1 - a1) * (b2 - a2) / (facDen knd : ℝ)) *
      f (centroid3R knd a0 b0 a1 b1 a2 b2) ≤
    ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 a3 b3 : ℝ},
  cell3Ok knd a0 b0 a1 b1 a2 b2 → a3 ≤ b3 →
  ∀ {f : (Fin 4 → ℝ) → ℝ}, ConvexOn ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) f →
  ContinuousOn f (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) →
  ∫ x in cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3, f x ≤
    ((b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3) / ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ)))) *
      sumVerts3R (fun y => f ![y 0, y 1, y 2, a3] + f ![y 0, y 1, y 2, b3]) knd a0 b0 a1 b1 a2 b2) ∧
(∀ {c h R : ℝ}, 0 < c → 0 ≤ h →
  ∫ t in Icc (0 : ℝ) h, ({t : ℝ | c * t ≤ R}).indicator (fun _ => (1 : ℝ)) t =
    (max 0 R - max 0 (R - c * h)) / c) ∧
(∀ {a0 b0 a1 b1 a2 b2 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2,
    ({x : Fin 3 → ℝ | x 0 + x 1 + 2 * x 2 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
    cut3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 12) ∧
(∀ {a0 b0 a1 b1 a2 b2 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, max 0 (L - (x 0 + x 1 + 2 * x 2)) =
    ramp3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 48) ∧
(∀ {a0 b0 a1 b1 a2 b2 a3 b3 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 → a3 ≤ b3 →
  ∫ x in cell4Set .box a0 b0 a1 b1 a2 b2 a3 b3,
    ({x : Fin 4 → ℝ | x 0 + x 1 + 2 * x 2 + x 3 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
    cut4SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (b3 - a3) (L - (a0 + a1 + 2 * a2 + a3)) / 48) ∧
(∀ (i : Fin 3) (m : ℝ), volume ({x : Fin 3 → ℝ | x i = m}) = 0) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ},
  cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {g : ℝ → ℝ}, (∀ s, 0 ≤ g s) → Antitone g →
  IntegrableOn (fun x : Fin 3 → ℝ => g (x 0 + x 1 + 2 * x 2)) (cell3Set .box a0 b0 a1 b1 a2 b2) volume →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2) ≤
    (1 / (facDen knd : ℝ)) * ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2)) :=
  ⟨@Sol_Buchstab4DT_Geom.buchstab_nonneg,
   @Sol_Buchstab4DT_Geom.buchstab_le_max_inv_two_thirds,
   @Sol_Buchstab4DT_Geom.buchstab_le_one,
   @Sol_Buchstab4DT_Geom.convexOn_inv_prod,
   @Sol_Buchstab4DT_Geom.hh1_Icc,
   @Sol_Buchstab4DT_Geom.jensen1_Icc,
   Sol_Buchstab4DT_Geom.volume_preserving_equivFin4_3,
   Sol_Buchstab4DT_Geom.equivFin4_3_apply,
   Sol_Buchstab4DT_Geom.cell4Set_eq_preimage,
   Sol_Buchstab4DT_Geom.cell3Set_isClosed,
   Sol_Buchstab4DT_Geom.cell3Set_isCompact,
   Sol_Buchstab4DT_Geom.cell4Set_isClosed,
   Sol_Buchstab4DT_Geom.cell4Set_isCompact,
   Sol_Buchstab4DT_Geom.cell3Set_convex,
   Sol_Buchstab4DT_Geom.cell4Set_convex,
   (fun knd _ _ _ _ _ _ h0 h1 h2 _ hcont => by
     cases knd <;> exact Sol_Buchstab4DT_Geom.integral_cell3_eq_iter _ h0 h1 h2 hcont),
   @Sol_Buchstab4DT_Geom.hh_cell3,
   @Sol_Buchstab4DT_Geom.jensen_cell3,
   @Sol_Buchstab4DT_Geom.hh_cell4,
   @Sol_Buchstab4DT_Geom.integral_ind_le_sub,
   @Sol_Buchstab4DT_Geom.vol_cut_box3_eq,
   @Sol_Buchstab4DT_Geom.int_ramp_box3_eq,
   @Sol_Buchstab4DT_Geom.vol_cut_box4_eq,
   Sol_Buchstab4DT_Geom.volume_fin3_coord_eq_zero,
   @Sol_Buchstab4DT_Geom.s3_antitone_le⟩
