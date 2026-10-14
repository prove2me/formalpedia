-- Prove2me | solution 1 for StochApproxDyn.Interpolation.interpAffine_sub_interpConst_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:12:36.331827+00:00
-- url     : https://prove2.me/submissions/a4b9fa43-a28f-4fcf-be07-cec8507b539c

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter


namespace StochApproxDyn.Interpolation

section Base
variable {γ : ℕ → ℝ}

lemma d44_tau_zero : tau γ 0 = 0 := by simp [tau]

lemma d44_tau_succ (n : ℕ) : tau γ (n + 1) = tau γ n + γ (n + 1) := by
  simp [tau, Finset.sum_range_succ]

lemma d44_tau_mono (hγ : IsStepSizeSeq γ) : Monotone (tau γ) :=
  monotone_nat_of_le_succ (fun n => by rw [d44_tau_succ]; linarith [hγ.1 n])

lemma d44_tau_nonneg (hγ : IsStepSizeSeq γ) (n : ℕ) : 0 ≤ tau γ n := by
  have := d44_tau_mono hγ (Nat.zero_le n); rwa [d44_tau_zero] at this

lemma d44_bdd (hγ : IsStepSizeSeq γ) (t : ℝ) : BddAbove {k : ℕ | tau γ k ≤ t} := by
  obtain ⟨N, hN⟩ := (hγ.2.1.eventually_gt_atTop t).exists_forall_of_atTop
  refine ⟨N, fun k hk => ?_⟩
  by_contra h
  push_neg at h
  have := hN k h.le
  simp only [Set.mem_setOf_eq] at hk
  linarith

lemma d44_le_mIdx (hγ : IsStepSizeSeq γ) {k : ℕ} {t : ℝ} (h : tau γ k ≤ t) : k ≤ mIdx γ t :=
  le_csSup (d44_bdd hγ t) h

lemma d44_mIdx_spec (hγ : IsStepSizeSeq γ) {t : ℝ} (ht : 0 ≤ t) :
    tau γ (mIdx γ t) ≤ t ∧ t < tau γ (mIdx γ t + 1) := by
  have hne : ({k : ℕ | tau γ k ≤ t}).Nonempty := ⟨0, by simp [d44_tau_zero, ht]⟩
  refine ⟨Nat.sSup_mem hne (d44_bdd hγ t), ?_⟩
  by_contra h
  push_neg at h
  have := d44_le_mIdx hγ h
  omega

lemma d44_mIdx_eq (hγ : IsStepSizeSeq γ) {n : ℕ} {t : ℝ} (h1 : tau γ n ≤ t)
    (h2 : t < tau γ (n + 1)) : mIdx γ t = n := by
  have ht : 0 ≤ t := le_trans (d44_tau_nonneg hγ n) h1
  apply le_antisymm
  · by_contra h
    push_neg at h
    have := (d44_mIdx_spec hγ ht).1
    have := d44_tau_mono hγ (show n + 1 ≤ mIdx γ t by omega)
    linarith
  · exact d44_le_mIdx hγ h1

lemma d44_mIdx_mono (hγ : IsStepSizeSeq γ) {s t : ℝ} (hst : s ≤ t) : mIdx γ s ≤ mIdx γ t := by
  rcases le_or_gt 0 s with hs | hs
  · exact d44_le_mIdx hγ (le_trans (d44_mIdx_spec hγ hs).1 hst)
  · have : {k : ℕ | tau γ k ≤ s} = ∅ := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      linarith [d44_tau_nonneg hγ k]
    simp [mIdx, this]

lemma d44_gamma_pos (hγ : IsStepSizeSeq γ) {t : ℝ} (ht : 0 ≤ t) : 0 < γ (mIdx γ t + 1) := by
  have := d44_mIdx_spec hγ ht
  rw [d44_tau_succ] at this
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma d44_piece (hγ : IsStepSizeSeq γ) (G : ℕ → E) (n : ℕ) {t : ℝ} (h1 : tau γ n ≤ t)
    (h2 : t ≤ tau γ (n + 1)) :
    IntervalIntegrable (fun s => G (mIdx γ s)) MeasureTheory.volume (tau γ n) t ∧
      ∫ s in tau γ n..t, G (mIdx γ s) = (t - tau γ n) • G n := by
  have heq : Set.EqOn (fun s => G (mIdx γ s)) (fun _ => G n) (Set.Ioo (tau γ n) t) := by
    intro s hs
    simp only
    rw [d44_mIdx_eq hγ hs.1.le (lt_of_lt_of_le hs.2 h2)]
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le h1]
    have : MeasureTheory.IntegrableOn (fun _ : ℝ => G n) (Set.Ioo (tau γ n) t) := by
      have := (intervalIntegrable_const (μ := MeasureTheory.volume) (c := G n) (a := tau γ n)
        (b := t))
      rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le h1] at this
    exact this.congr_fun heq.symm measurableSet_Ioo
  · rw [intervalIntegral.integral_of_le h1, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo heq]
    simp [h1]

lemma d44_int_tau (hγ : IsStepSizeSeq γ) (G : ℕ → E) (N : ℕ) :
    IntervalIntegrable (fun s => G (mIdx γ s)) MeasureTheory.volume 0 (tau γ N) ∧
      ∫ s in (0:ℝ)..tau γ N, G (mIdx γ s) =
        ∑ k ∈ Finset.range N, γ (k + 1) • G k := by
  have hp : ∀ k, IntervalIntegrable (fun s => G (mIdx γ s)) MeasureTheory.volume
      (tau γ k) (tau γ (k + 1)) :=
    fun k => (d44_piece hγ G k (d44_tau_mono hγ (Nat.le_succ k)) le_rfl).1
  constructor
  · have := IntervalIntegrable.trans_iterate (a := tau γ) (n := N) (fun k _ => hp k)
    rwa [d44_tau_zero] at this
  · have := intervalIntegral.sum_integral_adjacent_intervals (a := tau γ) (n := N)
      (f := fun s => G (mIdx γ s)) (μ := MeasureTheory.volume) (fun k _ => hp k)
    rw [d44_tau_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [(d44_piece hγ G k (d44_tau_mono hγ (Nat.le_succ k)) le_rfl).2, d44_tau_succ]
    congr 1; ring

lemma d44_intInt (hγ : IsStepSizeSeq γ) (G : ℕ → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => G (mIdx γ s)) MeasureTheory.volume a b := by
  obtain ⟨N, hN⟩ := (hγ.2.1.eventually_ge_atTop (max a b)).exists_forall_of_atTop
  have h := (d44_int_tau hγ G N).1
  have hN' := hN N le_rfl
  refine h.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
  · rw [Set.uIcc_of_le (le_trans ha (le_trans (le_max_left a b) hN'))]
    exact ⟨ha, le_trans (le_max_left a b) hN'⟩
  · rw [Set.uIcc_of_le (le_trans ha (le_trans (le_max_left a b) hN'))]
    exact ⟨hb, le_trans (le_max_right a b) hN'⟩

lemma d44_int_formula (hγ : IsStepSizeSeq γ) (G : ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, G (mIdx γ s) =
      ∑ k ∈ Finset.range (mIdx γ t), γ (k + 1) • G k + (t - tau γ (mIdx γ t)) • G (mIdx γ t) := by
  have hs := d44_mIdx_spec hγ ht
  have hp := d44_piece hγ G (mIdx γ t) hs.1 hs.2.le
  have h0 := d44_int_tau hγ G (mIdx γ t)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0.1 hp.1, h0.2, hp.2]

/-- the scheme in terms of `G`. -/
lemma d44_x_sub (F : E → E) (x U : ℕ → E) (hx : SatisfiesScheme F γ x U) (n : ℕ) :
    x n - x 0 = ∑ k ∈ Finset.range n, γ (k + 1) • (F (x k) + U (k + 1)) := by
  rw [← Finset.sum_range_sub (fun k => x k)]
  exact Finset.sum_congr rfl (fun k _ => hx k)

lemma d44_interpAffine_eq (hγ : IsStepSizeSeq γ) (F : E → E) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) {t : ℝ} (ht : 0 ≤ t) :
    interpAffine γ x t = x (mIdx γ t) + (t - tau γ (mIdx γ t)) •
      (F (x (mIdx γ t)) + U (mIdx γ t + 1)) := by
  unfold interpAffine
  rw [hx, smul_smul, div_mul_cancel₀ _ (d44_gamma_pos hγ ht).ne']

lemma d44_x_m0 (hγ : IsStepSizeSeq γ) (F : E → E) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) : x (mIdx γ 0) = x 0 := by
  have h := d44_mIdx_spec hγ le_rfl
  have h0 : tau γ (mIdx γ 0) = 0 := le_antisymm h.1 (d44_tau_nonneg hγ _)
  have hz : ∀ i ∈ Finset.range (mIdx γ 0), γ (i + 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hγ.1 i)).1 h0
  have := d44_x_sub F x U hx (mIdx γ 0)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_smul])] at this
  exact sub_eq_zero.1 this

lemma d44_interpAffine_zero (hγ : IsStepSizeSeq γ) (F : E → E) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) : interpAffine γ x 0 = x 0 := by
  rw [d44_interpAffine_eq hγ F x U hx le_rfl]
  have h := d44_mIdx_spec hγ le_rfl
  have h0 : tau γ (mIdx γ 0) = 0 := le_antisymm h.1 (d44_tau_nonneg hγ _)
  rw [h0, sub_zero, zero_smul, add_zero, d44_x_m0 hγ F x U hx]

theorem d44_sub_eq_integral_core (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) (t : ℝ) (ht : 0 ≤ t) :
    interpAffine γ x t - interpAffine γ x 0 =
      ∫ s in (0 : ℝ)..t, (F (interpConst γ x s) + noiseInterp γ U s) := by
  have := d44_int_formula hγ (fun k => F (x k) + U (k + 1)) ht
  unfold interpConst noiseInterp
  rw [this, d44_interpAffine_zero hγ F x U hx, d44_interpAffine_eq hγ F x U hx ht,
    ← d44_x_sub F x U hx]
  abel

end Base

section Part2
variable {γ : ℕ → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma d44_noise_bound (hγ : IsStepSizeSeq γ) (U : ℕ → E) (a T : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ s, s ≤ a + T → ‖U (mIdx γ s + 1)‖ ≤ B :=
  ⟨∑ k ∈ Finset.range (mIdx γ (a + T) + 2), ‖U k‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun s hs => by
    have := d44_mIdx_mono hγ hs
    exact Finset.single_le_sum (f := fun k => ‖U k‖) (fun k _ => norm_nonneg _)
      (Finset.mem_range.2 (by omega))⟩

lemma d44_delta_bdd (hγ : IsStepSizeSeq γ) (U : ℕ → E) (a T : ℝ) :
    BddAbove (Set.range fun h : Set.Icc (0:ℝ) T => ‖∫ s in a..a + (h:ℝ), U (mIdx γ s + 1)‖) := by
  obtain ⟨B, hB0, hB⟩ := d44_noise_bound hγ U a T
  refine ⟨B * T, ?_⟩
  rintro _ ⟨⟨h, h0, h1⟩, rfl⟩
  simp only
  calc _ ≤ B * |a + h - a| := intervalIntegral.norm_integral_le_of_norm_le_const
          (fun s hs => hB s (by
            rw [Set.uIoc_of_le (by linarith)] at hs
            linarith [hs.2]))
    _ ≤ B * T := by
      rw [add_sub_cancel_left, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left h1 hB0

lemma d44_delta_le (hγ : IsStepSizeSeq γ) (U : ℕ → E) {a T h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ T) :
    ‖∫ s in a..a + h, U (mIdx γ s + 1)‖ ≤ Delta γ U a T :=
  le_ciSup (f := fun h : Set.Icc (0:ℝ) T => ‖∫ s in a..a + (h:ℝ), U (mIdx γ s + 1)‖)
    (d44_delta_bdd hγ U a T) ⟨h, h0, h1⟩

lemma d44_delta_nonneg (U : ℕ → E) (a T : ℝ) : 0 ≤ Delta γ U a T :=
  Real.iSup_nonneg (fun _ => norm_nonneg _)

theorem d44_const_le_core (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) (K : ℝ) (hK : ∀ n : ℕ, ‖F (x n)‖ ≤ K) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ T : ℝ, 0 < T → ∀ u ∈ Set.Icc t (t + T),
      ‖interpAffine γ x u - interpConst γ x u‖ ≤
        2 * Delta γ U (t - 1) (T + 1) +
          sSup ((fun v => K * stepInterp γ v) '' Set.Icc t (t + T)) := by
  obtain ⟨N, hN⟩ := (hγ.2.2.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
  obtain ⟨B, hB⟩ := hγ.2.2.bddAbove_range
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  refine ⟨max 1 (tau γ N), le_max_left _ _, ?_⟩
  intro t ht T hT u hu
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hnN : N ≤ mIdx γ u := d44_le_mIdx hγ (by linarith [le_max_right 1 (tau γ N), hu.1])
  have hg1 := hN _ hnN
  have hs := d44_mIdx_spec hγ hu0
  have hτ := d44_tau_succ (γ := γ) (mIdx γ u)
  rw [d44_interpAffine_eq hγ F x U hx hu0]
  unfold interpConst
  rw [add_sub_cancel_left, smul_add]
  have h1 : ‖(u - tau γ (mIdx γ u)) • F (x (mIdx γ u))‖ ≤
      sSup ((fun v => K * stepInterp γ v) '' Set.Icc t (t + T)) := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    calc _ ≤ γ (mIdx γ u + 1) * K := mul_le_mul (by linarith) (hK _) (norm_nonneg _) (hγ.1 _)
      _ = K * stepInterp γ u := by unfold stepInterp; ring
      _ ≤ _ := by
        refine le_csSup ⟨K * B, ?_⟩ ⟨u, hu, rfl⟩
        rintro _ ⟨v, _, rfl⟩
        exact mul_le_mul_of_nonneg_left (hB ⟨mIdx γ v, rfl⟩) hK0
  have h2 : ‖(u - tau γ (mIdx γ u)) • U (mIdx γ u + 1)‖ ≤ 2 * Delta γ U (t - 1) (T + 1) := by
    have hp := d44_piece hγ (fun k => U (k + 1)) (mIdx γ u) hs.1 hs.2.le
    have hA := d44_intInt hγ (fun k => U (k + 1)) (a := t - 1) (b := u) (by linarith) hu0
    have hB' := d44_intInt hγ (fun k => U (k + 1)) (a := t - 1) (b := tau γ (mIdx γ u))
      (by linarith) (d44_tau_nonneg hγ _)
    rw [← hp.2, ← intervalIntegral.integral_interval_sub_left hA hB']
    have e1 : u = (t - 1) + (u - (t - 1)) := by ring
    have e2 : tau γ (mIdx γ u) = (t - 1) + (tau γ (mIdx γ u) - (t - 1)) := by ring
    have i1 : ‖∫ s in (t - 1)..u, U (mIdx γ s + 1)‖ ≤ Delta γ U (t - 1) (T + 1) := by
      rw [e1]; exact d44_delta_le hγ U (by linarith [hu.1]) (by linarith [hu.2])
    have i2 : ‖∫ s in (t - 1)..tau γ (mIdx γ u), U (mIdx γ s + 1)‖ ≤
        Delta γ U (t - 1) (T + 1) := by
      rw [e2]; exact d44_delta_le hγ U (by linarith [hu.1, hs.2]) (by linarith [hu.2])
    linarith [norm_sub_le (∫ s in (t - 1)..u, U (mIdx γ s + 1))
      (∫ s in (t - 1)..tau γ (mIdx γ u), U (mIdx γ s + 1))]
  linarith [norm_add_le ((u - tau γ (mIdx γ u)) • F (x (mIdx γ u)))
    ((u - tau γ (mIdx γ u)) • U (mIdx γ u + 1))]

def d44S (γ : ℕ → ℝ) (U : ℕ → E) (k : ℕ) : E := ∑ i ∈ Finset.range k, γ (i + 1) • U (i + 1)

lemma d44_key (A a B b : E) : ‖(A + a) - (B + b)‖ ≤ ‖A - B‖ + ‖a‖ + ‖b‖ := by
  calc ‖(A + a) - (B + b)‖ = ‖(A - B) + a - b‖ := by congr 1; abel
    _ ≤ ‖(A - B) + a‖ + ‖b‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [norm_add_le (A - B) a]

theorem d44_a1_core (hγ : IsStepSizeSeq γ) (U : ℕ → E) (T : ℝ) (hT : 0 < T) :
    A1At γ U T ↔ Tendsto (fun t : ℝ => Delta γ U t T) atTop (𝓝 0) := by
  constructor
  · intro hA
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N1, hN1⟩ := hA (ε / 10) (by positivity)
    obtain ⟨N2, hN2⟩ := (hγ.2.2.eventually (eventually_le_nhds hT)).exists_forall_of_atTop
    have hAA : ∀ n k, max N1 N2 ≤ n → n ≤ k → tau γ k ≤ tau γ n + T →
        ‖d44S γ U k - d44S γ U n‖ ≤ ε / 10 := by
      intro n k hn hk hτ
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · simp; positivity
      · have := hN1 n (le_trans (le_max_left _ _) hn) k hlt (d44_le_mIdx hγ hτ)
        rwa [Finset.sum_Ico_eq_sub _ hk] at this
    have hBB : ∀ k, max N1 N2 ≤ k → ‖γ (k + 1) • U (k + 1)‖ ≤ ε / 10 := by
      intro k hk
      have := hAA k (k + 1) hk (Nat.le_succ k)
        (by rw [d44_tau_succ]; linarith [hN2 k (le_trans (le_max_right _ _) hk)])
      rwa [d44S, d44S, Finset.sum_range_succ, add_sub_cancel_left] at this
    have hCC : ∀ n k, max N1 N2 ≤ n → n ≤ k → tau γ k ≤ tau γ n + 2 * T →
        ‖d44S γ U k - d44S γ U n‖ ≤ 3 * (ε / 10) := by
      intro n k hn hk hτ
      have hnT : 0 ≤ tau γ n + T := by linarith [d44_tau_nonneg hγ n]
      have hj := d44_mIdx_spec hγ hnT
      have hjn : n ≤ mIdx γ (tau γ n + T) := d44_le_mIdx hγ (by linarith)
      obtain ⟨j, hjdef⟩ : ∃ j, j = mIdx γ (tau γ n + T) := ⟨_, rfl⟩
      rw [← hjdef] at hj hjn
      rcases le_or_gt k j with hkj | hkj
      · have := hAA n k hn hk (le_trans (d44_tau_mono hγ hkj) hj.1); linarith
      · have e1 := hAA (j + 1) k (by omega) hkj (by linarith [hj.2])
        have e2 := hBB j (by omega)
        have e3 := hAA n j hn hjn hj.1
        have : d44S γ U (j + 1) - d44S γ U j = γ (j + 1) • U (j + 1) := by
          rw [d44S, d44S, Finset.sum_range_succ, add_sub_cancel_left]
        have hsplit : d44S γ U k - d44S γ U n = (d44S γ U k - d44S γ U (j + 1)) +
            (d44S γ U (j + 1) - d44S γ U j) + (d44S γ U j - d44S γ U n) := by abel
        rw [hsplit]
        refine le_trans (norm_add₃_le) ?_
        rw [this]; linarith
    refine ⟨max 0 (tau γ (max N1 N2)), fun t ht => ?_⟩
    have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
    have hnN : max N1 N2 ≤ mIdx γ t := d44_le_mIdx hγ (le_trans (le_max_right _ _) ht)
    have hr : ∀ s, 0 ≤ s → max N1 N2 ≤ mIdx γ s →
        ‖(s - tau γ (mIdx γ s)) • U (mIdx γ s + 1)‖ ≤ ε / 10 := by
      intro s hs hsN
      have sp := d44_mIdx_spec hγ hs
      rw [d44_tau_succ] at sp
      refine le_trans ?_ (hBB _ hsN)
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
        Real.norm_of_nonneg (hγ.1 _)]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hbound : Delta γ U t T ≤ 5 * (ε / 10) := by
      haveI : Nonempty (Set.Icc (0:ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
      unfold Delta noiseInterp
      refine ciSup_le (fun ⟨h, h0, h1⟩ => ?_)
      simp only
      have hth : 0 ≤ t + h := by linarith
      rw [← intervalIntegral.integral_interval_sub_left
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl hth)
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl ht0),
        d44_int_formula hγ (fun k => U (k + 1)) hth, d44_int_formula hγ (fun k => U (k + 1)) ht0]
      have hk := d44_mIdx_mono hγ (show t ≤ t + h by linarith)
      have hsp1 := d44_mIdx_spec hγ hth
      have hsp0 := d44_mIdx_spec hγ ht0
      rw [d44_tau_succ] at hsp0
      have hC := hCC (mIdx γ t) (mIdx γ (t + h)) hnN hk
        (by linarith [hN2 _ (le_trans (le_max_right _ _) hnN)])
      have e1 := hr (t + h) hth (le_trans hnN hk)
      have e2 := hr t ht0 hnN
      unfold d44S at hC
      refine le_trans (d44_key _ _ _ _) ?_
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (d44_delta_nonneg U t T)]
    linarith
  · intro hD ε hε
    rw [Metric.tendsto_atTop] at hD
    obtain ⟨t₀, ht₀⟩ := hD ε hε
    obtain ⟨N, hN⟩ := (hγ.2.1.eventually_ge_atTop t₀).exists_forall_of_atTop
    refine ⟨N, fun n hn k hk1 hk2 => ?_⟩
    have hnT : 0 ≤ tau γ n + T := by linarith [d44_tau_nonneg hγ n]
    have hτk : tau γ k ≤ tau γ n + T := le_trans (d44_tau_mono hγ hk2) (d44_mIdx_spec hγ hnT).1
    have hτnk : tau γ n ≤ tau γ k := d44_tau_mono hγ (by omega)
    have hd := ht₀ (tau γ n) (hN n hn)
    rw [Real.dist_eq, sub_zero] at hd
    have hle := d44_delta_le hγ U (a := tau γ n) (T := T) (h := tau γ k - tau γ n)
      (by linarith) (by linarith)
    rw [show tau γ n + (tau γ k - tau γ n) = tau γ k by ring,
      ← intervalIntegral.integral_interval_sub_left
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl (d44_tau_nonneg hγ k))
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl (d44_tau_nonneg hγ n)),
      (d44_int_tau hγ (fun k => U (k + 1)) k).2, (d44_int_tau hγ (fun k => U (k + 1)) n).2,
      ← Finset.sum_Ico_eq_sub _ (by omega)] at hle
    linarith [le_abs_self (Delta γ U (tau γ n) T)]

end Part2

end StochApproxDyn.Interpolation

open StochApproxDyn.Interpolation


theorem solution {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (K : ℝ) (hK : ∀ n : ℕ, ‖F (x n)‖ ≤ K) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ T : ℝ, 0 < T → ∀ u ∈ Set.Icc t (t + T),
      ‖interpAffine γ x u - interpConst γ x u‖ ≤
        2 * Delta γ U (t - 1) (T + 1) +
          sSup ((fun v => K * stepInterp γ v) '' Set.Icc t (t + T)) := by
  exact d44_const_le_core F hγ x U hx K hK
