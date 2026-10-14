-- Prove2me | solution 1 for StochApproxDyn.Interpolation.interpAffine_isAsymptoticPseudotrajectory
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:38:35.038469+00:00
-- url     : https://prove2.me/submissions/174992b4-8771-472d-9d27-700383d5d25f

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_Interpolation_VectorFieldFlow
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter
open scoped BoundedContinuousFunction

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

section Part3
variable {γ : ℕ → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem d44_const_pt (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) (K : ℝ) (hK : ∀ n : ℕ, ‖F (x n)‖ ≤ K) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ T : ℝ, 0 < T → ∀ u ∈ Set.Icc t (t + T),
      ‖interpAffine γ x u - x (mIdx γ u)‖ ≤
        2 * Delta γ U (t - 1) (T + 1) + K * stepInterp γ u := by
  obtain ⟨N, hN⟩ := (hγ.2.2.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
  refine ⟨max 1 (tau γ N), le_max_left _ _, ?_⟩
  intro t ht T hT u hu
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hnN : N ≤ mIdx γ u := d44_le_mIdx hγ (by linarith [le_max_right 1 (tau γ N), hu.1])
  have hg1 := hN _ hnN
  have hs := d44_mIdx_spec hγ hu0
  have hτ := d44_tau_succ (γ := γ) (mIdx γ u)
  rw [d44_interpAffine_eq hγ F x U hx hu0]
  rw [add_sub_cancel_left, smul_add]
  have h1 : ‖(u - tau γ (mIdx γ u)) • F (x (mIdx γ u))‖ ≤ K * stepInterp γ u := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    calc _ ≤ γ (mIdx γ u + 1) * K := mul_le_mul (by linarith) (hK _) (norm_nonneg _) (hγ.1 _)
      _ = K * stepInterp γ u := by unfold stepInterp; ring
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

lemma d44_prim_cont (hγ : IsStepSizeSeq γ) (G : ℕ → E) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (fun v => ∫ s in (0:ℝ)..v, G (mIdx γ s)) (Set.Icc 0 b) := by
  have hi := d44_intInt hγ G (le_refl (0:ℝ)) hb
  have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
    (f := fun s => G (mIdx γ s)) (a := 0) (b := b)
    (by rw [Set.uIcc_of_le hb]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb).1 hi)
  rwa [Set.uIcc_of_le hb] at this

lemma d44_prim_deriv (hγ : IsStepSizeSeq γ) (G : ℕ → E) (c : E) {t h : ℝ} (ht : 0 ≤ t)
    (hth : 0 ≤ t + h) :
    HasDerivWithinAt (fun v => c + ((∫ s in (0:ℝ)..t + v, G (mIdx γ s)) -
      ∫ s in (0:ℝ)..t, G (mIdx γ s))) (G (mIdx γ (t + h))) (Set.Ici h) h := by
  obtain ⟨n, hn⟩ : ∃ n, n = mIdx γ (t + h) := ⟨_, rfl⟩
  have hs := d44_mIdx_spec hγ hth
  rw [← hn] at hs ⊢
  have hd : HasDerivAt (fun v => c + ((∑ k ∈ Finset.range n, γ (k + 1) • G k +
      (t + v - tau γ n) • G n) - ∫ s in (0:ℝ)..t, G (mIdx γ s))) (G n) h :=
    HasDerivAt.congr_deriv (((((((hasDerivAt_id' h).const_add t).sub_const (tau γ n)).smul_const
      (G n)).const_add (∑ k ∈ Finset.range n, γ (k + 1) • G k)).sub_const
      (∫ s in (0:ℝ)..t, G (mIdx γ s))).const_add c) (one_smul ℝ _)
  refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Ico_mem_nhdsGE (show h < tau γ (n + 1) - t by linarith [hs.2])] with v hv
    have hv0 : 0 ≤ t + v := by linarith [hv.1]
    rw [d44_int_formula hγ G hv0, d44_mIdx_eq hγ (n := n) (by linarith [hv.1, hs.1]) (by linarith [hv.2])]
  · try dsimp only
    rw [d44_int_formula hγ G hth, ← hn]

lemma d44_X_decomp (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) {u : ℝ} (hu : 0 ≤ u) :
    interpAffine γ x u = x 0 + (∫ s in (0:ℝ)..u, F (x (mIdx γ s))) +
      ∫ s in (0:ℝ)..u, U (mIdx γ s + 1) := by
  have h := d44_sub_eq_integral_core F hγ x U hx u hu
  rw [d44_interpAffine_zero hγ F x U hx] at h
  unfold interpConst noiseInterp at h
  rw [intervalIntegral.integral_add (d44_intInt hγ (fun k => F (x k)) le_rfl hu)
    (d44_intInt hγ (fun k => U (k + 1)) le_rfl hu)] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]; abel

lemma d44_gron_est (L : ℝ≥0) {ε x T : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxT : x ≤ T) :
    gronwallBound 0 L ε x ≤ ε * T * Real.exp (L * T) := by
  rcases eq_or_ne (L : ℝ) 0 with hL | hL
  · rw [hL, gronwallBound_K0]
    simp only [zero_add, zero_mul, Real.exp_zero, mul_one]
    exact mul_le_mul_of_nonneg_left hxT hε
  · rw [gronwallBound_of_K_ne_0 hL]
    simp only [zero_mul, zero_add]
    have hLp : 0 < (L : ℝ) := lt_of_le_of_ne L.2 (Ne.symm hL)
    have h1 := Real.add_one_le_exp (-(L * x))
    have h2 : Real.exp (-(L * x)) * Real.exp (L * x) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp (L * x) - 1 ≤ L * x * Real.exp (L * x) := by
      nlinarith [Real.exp_pos (L * x)]
    have h4 : Real.exp (L * x) ≤ Real.exp (L * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxT hLp.le)
    calc ε / L * (Real.exp (L * x) - 1) ≤ ε / L * (L * x * Real.exp (L * x)) :=
          mul_le_mul_of_nonneg_left h3 (div_nonneg hε hLp.le)
      _ = ε * x * Real.exp (L * x) := by field_simp
      _ ≤ ε * T * Real.exp (L * T) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hxT hε) h4 (Real.exp_pos _).le
        nlinarith

end Part3

section Part4
variable {γ : ℕ → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem d44_shadow_core (F : E → E) (Φ : ℝ → E → E) (hΦ : IsFlowOf F Φ) (T : ℝ) (hT : 0 < T)
    (L : ℝ≥0) (K : ℝ) : ∃ C : ℝ,
      ∀ (γ : ℕ → ℝ) (x U : ℕ → E) (r : ℝ),
        IsStepSizeSeq γ → SatisfiesScheme F γ x U → SatisfiesA1 γ U → 0 < r →
        LipschitzOnWith L F (Metric.thickening r (Set.range x)) →
        (∀ y ∈ Metric.thickening r (Set.range x), ‖F y‖ ≤ K) →
        ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ h ∈ Set.Icc (0 : ℝ) T,
          ‖interpAffine γ x (t + h) - Φ h (interpAffine γ x t)‖ ≤
            C * (Delta γ U (t - 1) (T + 1) + sSup (stepInterp γ '' Set.Icc t (t + T))) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (L : ℝ) * T * Real.exp ((L : ℝ) * T) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨2 + M * (4 + |K|), ?_⟩
  intro γ x U r hγ hx hA1 hr hLip hKb
  have hxmem : ∀ n, x n ∈ Metric.thickening r (Set.range x) :=
    fun n => Metric.self_subset_thickening hr _ ⟨n, rfl⟩
  have hK : ∀ n, ‖F (x n)‖ ≤ K := fun n => hKb _ (hxmem n)
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  rw [abs_of_nonneg hK0]
  have hMp : 0 < 1 + M := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = r / (16 * (1 + M)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδM : δ * (1 + M) = r / 16 := by rw [hδ]; field_simp
  obtain ⟨η, hη⟩ : ∃ η, η = δ / (K + 1) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hKη : K * η ≤ δ := by
    rw [hη, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have hDt := (d44_a1_core hγ U (T + 1) (by linarith)).1 (hA1 (T + 1) (by linarith))
  obtain ⟨t1, ht1⟩ := (Metric.tendsto_atTop.1 hDt) δ hδ0
  obtain ⟨N, hN⟩ := (hγ.2.2.eventually (eventually_le_nhds hη0)).exists_forall_of_atTop
  obtain ⟨t2, ht2, hc⟩ := d44_const_pt F hγ x U hx K hK
  refine ⟨max t2 (max (t1 + 1) (tau γ N)), le_trans ht2 (le_max_left _ _), ?_⟩
  intro t ht h hh
  have htt2 : t2 ≤ t := le_trans (le_max_left _ _) ht
  have ht1' : t1 + 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htN : tau γ N ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨D, hD⟩ : ∃ D, D = Delta γ U (t - 1) (T + 1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = sSup (stepInterp γ '' Set.Icc t (t + T)) := ⟨_, rfl⟩
  rw [← hD, ← hs]
  have hD0 : 0 ≤ D := hD ▸ d44_delta_nonneg U _ _
  have hDδ : D < δ := by
    have := ht1 (t - 1) (by linarith)
    rw [Real.dist_eq, sub_zero] at this
    rw [hD]; exact lt_of_le_of_lt (le_abs_self _) this
  have hbdd : BddAbove (stepInterp γ '' Set.Icc t (t + T)) := by
    obtain ⟨B, hB⟩ := hγ.2.2.bddAbove_range
    exact ⟨B, by rintro _ ⟨v, _, rfl⟩; exact hB ⟨_, rfl⟩⟩
  have hsv : ∀ v ∈ Set.Icc t (t + T), stepInterp γ v ≤ s :=
    fun v hv => hs ▸ le_csSup hbdd ⟨v, hv, rfl⟩
  have hs0 : 0 ≤ s := le_trans (hγ.1 _) (hsv t ⟨le_rfl, by linarith⟩)
  have hsη : s ≤ η := hs ▸ csSup_le ⟨_, t, ⟨le_rfl, by linarith⟩, rfl⟩
    (by rintro _ ⟨v, hv, rfl⟩; exact hN _ (d44_le_mIdx hγ (by linarith [hv.1])))
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * D + K * s := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hQsmall : Q + M * Q < r / 2 := by
    have h1 : Q ≤ 4 * δ + δ := by rw [hQ]; nlinarith [mul_le_mul_of_nonneg_left hsη hK0]
    have h2 : Q * (1 + M) ≤ 5 * (δ * (1 + M)) := by nlinarith
    nlinarith
  -- the comparison curve
  obtain ⟨p, hp⟩ : ∃ p, p = interpAffine γ x t := ⟨_, rfl⟩
  rw [← hp]
  obtain ⟨W, hW⟩ : ∃ W : ℝ → E, W = fun v => p + ((∫ s in (0:ℝ)..t + v, F (x (mIdx γ s))) -
      ∫ s in (0:ℝ)..t, F (x (mIdx γ s))) := ⟨_, rfl⟩
  have hXc : ∀ h' ∈ Set.Icc (0:ℝ) T,
      ‖interpAffine γ x (t + h') - x (mIdx γ (t + h'))‖ ≤ 2 * D + K * s := by
    intro h' hh'
    have hin : t + h' ∈ Set.Icc t (t + T) := ⟨by linarith [hh'.1], by linarith [hh'.2]⟩
    have := hc t htt2 T hT (t + h') hin
    rw [← hD] at this
    nlinarith [mul_le_mul_of_nonneg_left (hsv _ hin) hK0]
  have hXW : ∀ h' ∈ Set.Icc (0:ℝ) T, ‖interpAffine γ x (t + h') - W h'‖ ≤ 2 * D := by
    intro h' hh'
    have hth : 0 ≤ t + h' := by linarith [hh'.1]
    have hX1 := d44_X_decomp F hγ x U hx hth
    have hX0 := d44_X_decomp F hγ x U hx ht0
    have e : interpAffine γ x (t + h') - W h' =
        (∫ s in (0:ℝ)..t + h', U (mIdx γ s + 1)) - ∫ s in (0:ℝ)..t, U (mIdx γ s + 1) := by
      rw [hW, hX1, hp, hX0]
      beta_reduce
      abel
    have f1 : (∫ s in (0:ℝ)..t + h', U (mIdx γ s + 1)) - ∫ s in (0:ℝ)..t, U (mIdx γ s + 1) =
        ∫ s in t..t + h', U (mIdx γ s + 1) :=
      intervalIntegral.integral_interval_sub_left
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl hth)
        (d44_intInt hγ (fun k => U (k + 1)) le_rfl ht0)
    have f2 : (∫ s in (t - 1)..t + h', U (mIdx γ s + 1)) - ∫ s in (t - 1)..t, U (mIdx γ s + 1) =
        ∫ s in t..t + h', U (mIdx γ s + 1) :=
      intervalIntegral.integral_interval_sub_left
        (d44_intInt hγ (fun k => U (k + 1)) (by linarith) hth)
        (d44_intInt hγ (fun k => U (k + 1)) (by linarith) ht0)
    rw [e, f1, ← f2]
    have i1 : ‖∫ s in (t - 1)..t + h', U (mIdx γ s + 1)‖ ≤ D := by
      rw [hD, show t + h' = (t - 1) + (h' + 1) by ring]
      exact d44_delta_le hγ U (by linarith [hh'.1]) (by linarith [hh'.2])
    have i2 : ‖∫ s in (t - 1)..t, U (mIdx γ s + 1)‖ ≤ D := by
      have := d44_delta_le hγ U (a := t - 1) (T := T + 1) (h := 1) (by norm_num) (by linarith)
      rw [show t - 1 + 1 = t by ring] at this
      rw [hD]; exact this
    linarith [norm_sub_le (∫ s in (t - 1)..t + h', U (mIdx γ s + 1))
      (∫ s in (t - 1)..t, U (mIdx γ s + 1))]
  have hxW : ∀ h' ∈ Set.Icc (0:ℝ) T, ‖x (mIdx γ (t + h')) - W h'‖ ≤ Q := by
    intro h' hh'
    have := norm_sub_le_norm_sub_add_norm_sub (x (mIdx γ (t + h'))) (interpAffine γ x (t + h'))
      (W h')
    have h2 := norm_sub_rev (x (mIdx γ (t + h'))) (interpAffine γ x (t + h'))
    rw [hQ]
    linarith [hXc h' hh', hXW h' hh']
  have hycont : Continuous (fun h' => Φ h' p) :=
    continuous_iff_continuousAt.2 (fun h' => ((hΦ p).2 h').continuousAt)
  have gron : ∀ b, 0 ≤ b → b ≤ T →
      (∀ h' ∈ Set.Ico 0 b, Φ h' p ∈ Metric.thickening r (Set.range x)) →
      ∀ h' ∈ Set.Icc 0 b, dist (W h') (Φ h' p) ≤ M * Q := by
    intro b hb0 hbT hyb
    have hWc : ContinuousOn W (Set.Icc 0 b) := by
      rw [hW]
      have hP := d44_prim_cont hγ (fun k => F (x k)) (b := t + b) (by linarith)
      refine continuousOn_const.add ((hP.comp (by fun_prop) ?_).sub continuousOn_const)
      intro v hv; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hWd : ∀ h' ∈ Set.Ico 0 b,
        HasDerivWithinAt W (F (x (mIdx γ (t + h')))) (Set.Ici h') h' := by
      intro h' hh'
      rw [hW]
      exact d44_prim_deriv hγ (fun k => F (x k)) p ht0 (by linarith [hh'.1])
    have hfb : ∀ h' ∈ Set.Ico 0 b,
        dist (F (x (mIdx γ (t + h')))) ((fun _ => F) h' (W h')) ≤ L * Q := by
      intro h' hh'
      have hh'' : h' ∈ Set.Icc 0 T := ⟨hh'.1, by linarith [hh'.2]⟩
      have hWin : W h' ∈ Metric.thickening r (Set.range x) := by
        rw [Metric.mem_thickening_iff]
        refine ⟨x (mIdx γ (t + h')), ⟨_, rfl⟩, ?_⟩
        rw [dist_eq_norm, norm_sub_rev]; linarith [hxW h' hh'', hQsmall, mul_nonneg hM0 hQ0]
      refine le_trans (hLip.dist_le_mul _ (hxmem _) _ hWin) ?_
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (hxW h' hh'') L.2
    have hfs : ∀ h' ∈ Set.Ico 0 b, W h' ∈ Metric.thickening r (Set.range x) := by
      intro h' hh'
      have hh'' : h' ∈ Set.Icc 0 T := ⟨hh'.1, by linarith [hh'.2]⟩
      rw [Metric.mem_thickening_iff]
      refine ⟨x (mIdx γ (t + h')), ⟨_, rfl⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_rev]; linarith [hxW h' hh'', hQsmall, mul_nonneg hM0 hQ0]
    have hgd : ∀ h' ∈ Set.Ico 0 b,
        HasDerivWithinAt (fun h' => Φ h' p) (F (Φ h' p)) (Set.Ici h') h' :=
      fun h' _ => ((hΦ p).2 h').hasDerivWithinAt
    have hgb : ∀ h' ∈ Set.Ico 0 b,
        dist (F (Φ h' p)) ((fun _ => F) h' (Φ h' p)) ≤ 0 := by intro h' _; simp
    have ha : dist (W 0) (Φ 0 p) ≤ 0 := by
      rw [hW, (hΦ p).1]; simp
    have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => F)
      (s := fun _ => Metric.thickening r (Set.range x)) (K := L) (f := W)
      (g := fun h' => Φ h' p) (f' := fun h' => F (x (mIdx γ (t + h'))))
      (g' := fun h' => F (Φ h' p)) (a := 0) (b := b) (εf := L * Q) (εg := 0) (δ := 0)
      (fun _ _ => hLip) hWc hWd hfb hfs hycont.continuousOn hgd hgb hyb ha
    intro h' hh'
    refine le_trans (key h' hh') ?_
    rw [sub_zero, add_zero]
    refine le_trans (d44_gron_est L (ε := (L : ℝ) * Q) (mul_nonneg L.2 hQ0) hh'.1 (le_trans hh'.2 hbT)) ?_
    rw [hM]; nlinarith [Real.exp_pos ((L : ℝ) * T)]
  have hall : ∀ h' ∈ Set.Icc (0:ℝ) T, Metric.infDist (Φ h' p) (Set.range x) < r / 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, hh0, hge⟩ := hcon
    obtain ⟨Bs, hBs⟩ : ∃ Bs : Set ℝ,
        Bs = Set.Icc 0 T ∩ {h' | r / 2 ≤ Metric.infDist (Φ h' p) (Set.range x)} := ⟨_, rfl⟩
    have hcl : IsClosed Bs := by
      rw [hBs]
      exact isClosed_Icc.inter (isClosed_le continuous_const
        ((Metric.continuous_infDist_pt _).comp hycont))
    have hne : Bs.Nonempty := ⟨h0, by rw [hBs]; exact ⟨hh0, hge⟩⟩
    have hbb : BddBelow Bs := ⟨0, fun z hz => by rw [hBs] at hz; exact hz.1.1⟩
    have hmem := (Set.ext_iff.1 hBs _).1 (hcl.csInf_mem hne hbb)
    have hgood : ∀ h' ∈ Set.Ico 0 (sInf Bs), Φ h' p ∈ Metric.thickening r (Set.range x) := by
      intro h' hh'
      have hnot : h' ∉ Bs := fun hin => absurd (csInf_le hbb hin) (not_le.2 hh'.2)
      have hin : h' ∈ Set.Icc 0 T := ⟨hh'.1, by linarith [hmem.1.2, hh'.2]⟩
      have hlt : Metric.infDist (Φ h' p) (Set.range x) < r / 2 := by
        by_contra hc'
        push_neg at hc'
        exact hnot (by rw [hBs]; exact ⟨hin, hc'⟩)
      exact (Metric.mem_thickening_iff_infDist_lt (Set.range_nonempty x)).2 (by linarith)
    have hg := gron (sInf Bs) hmem.1.1 hmem.1.2 hgood (sInf Bs) ⟨hmem.1.1, le_rfl⟩
    have hq := hxW (sInf Bs) hmem.1
    have h1 : Metric.infDist (Φ (sInf Bs) p) (Set.range x) ≤
        dist (Φ (sInf Bs) p) (x (mIdx γ (t + sInf Bs))) :=
      Metric.infDist_le_dist_of_mem ⟨_, rfl⟩
    have h2 := dist_triangle (Φ (sInf Bs) p) (W (sInf Bs)) (x (mIdx γ (t + sInf Bs)))
    rw [dist_comm] at hg
    rw [dist_eq_norm (W (sInf Bs)), norm_sub_rev] at h2
    have h3 := hmem.2
    simp only [Set.mem_setOf_eq] at h3
    linarith
  have hg := gron T hT.le le_rfl (fun h' hh' =>
    (Metric.mem_thickening_iff_infDist_lt (Set.range_nonempty x)).2
      (by linarith [hall h' ⟨hh'.1, hh'.2.le⟩])) h hh
  rw [dist_eq_norm] at hg
  have := norm_sub_le_norm_sub_add_norm_sub (interpAffine γ x (t + h)) (W h) (Φ h p)
  have hXWh := hXW h hh
  rw [hQ] at hg
  nlinarith [mul_nonneg hM0 hs0, mul_nonneg (mul_nonneg hM0 hK0) hD0, mul_nonneg hM0 hD0]

end Part4

section Goal1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma d44_AA [ProperSpace E] {M R T : ℝ} (g : ℕ → ℝ → E)
    (hL : ∀ k, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T, ‖g k s - g k s'‖ ≤ M * |s - s'|)
    (hR : ∀ k, ∀ s ∈ Set.Icc 0 T, ‖g k s‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Y : ℝ → E, ContinuousOn Y (Set.Icc 0 T) ∧
      ∀ ε > 0, ∃ k₀, ∀ k ≥ k₀, ∀ s ∈ Set.Icc 0 T, ‖g (φ k) s - Y s‖ < ε := by
  have hM : ∀ k, ∀ s s' : Set.Icc (0:ℝ) T, dist (g k s) (g k s') ≤ (max M 0) * dist s s' := by
    intro k s s'
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq]
    exact le_trans (hL k s s.2 s' s'.2)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hcont : ∀ k, Continuous (fun s : Set.Icc (0:ℝ) T => g k s) := by
    intro k
    have : LipschitzWith (Real.toNNReal (max M 0)) (fun s : Set.Icc (0:ℝ) T => g k s) :=
      LipschitzWith.of_dist_le_mul (fun s s' => by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]; exact hM k s s')
    exact this.continuous
  let G : ℕ → (Set.Icc (0:ℝ) T →ᵇ E) :=
    fun k => BoundedContinuousFunction.mkOfCompact ⟨fun s : Set.Icc (0:ℝ) T => g k s, hcont k⟩
  have hGapp : ∀ k s, G k s = g k s := fun k s => rfl
  have hA := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:E) R)
    (isCompact_closedBall 0 R) (Set.range G) ?in_s ?equi
  case in_s =>
    rintro _ x ⟨k, rfl⟩
    rw [hGapp, mem_closedBall_zero_iff]
    exact hR k x x.2
  case equi =>
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hpos : 0 < ε / (max M 0 + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds x₀ hpos] with x hx
    rintro ⟨_, k, rfl⟩
    show dist (G k x₀) (G k x) < ε
    rw [hGapp, hGapp]
    have hd : dist x₀ x < ε / (max M 0 + 1) := by rw [dist_comm]; exact hx
    calc dist (g k x₀) (g k x) ≤ max M 0 * dist x₀ x := hM k x₀ x
      _ ≤ max M 0 * (ε / (max M 0 + 1)) :=
          mul_le_mul_of_nonneg_left hd.le (le_max_right _ _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [le_max_right M 0]
  obtain ⟨f, _, φ, hφ, hlim⟩ := hA.tendsto_subseq (x := G) (fun k => subset_closure ⟨k, rfl⟩)
  refine ⟨φ, hφ, fun s => if h : s ∈ Set.Icc 0 T then f ⟨s, h⟩ else 0, ?_, ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    convert f.continuous using 1
    funext s
    exact dif_pos s.2
  · intro ε hε
    obtain ⟨k₀, hk₀⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
    refine ⟨k₀, fun k hk s hs => ?_⟩
    have h1 := hk₀ k hk
    have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := (G ∘ φ) k) (g := f) ⟨s, hs⟩
    simp only [dif_pos hs]
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt h2 h1

lemma d44_lim [ProperSpace E] (F : E → E) (hF : Continuous F) {R s : ℝ} (hs : 0 ≤ s)
    (q : ℕ → ℝ → E) (Y : ℝ → E)
    (hq : ∀ k, IntervalIntegrable (fun u => F (q k u)) MeasureTheory.volume 0 s)
    (hR : ∀ k, ∀ u ∈ Set.Icc 0 s, ‖q k u‖ ≤ R)
    (hlim : ∀ u ∈ Set.Icc 0 s, Tendsto (fun k => q k u) atTop (𝓝 (Y u))) :
    Tendsto (fun k => ∫ u in (0:ℝ)..s, F (q k u)) atTop (𝓝 (∫ u in (0:ℝ)..s, F (Y u))) := by
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hF.continuousOn
  have hmem : ∀ u, u ∈ Set.uIoc 0 s → u ∈ Set.Icc 0 s := by
    intro u hu
    rw [Set.uIoc_of_le hs] at hu
    exact ⟨hu.1.le, hu.2⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => MF)
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun k => (hq k).def'.aestronglyMeasurable)
  · exact Eventually.of_forall (fun k => Eventually.of_forall (fun u hu =>
      hMF _ (mem_closedBall_zero_iff.2 (hR k u (hmem u hu)))))
  · exact Eventually.of_forall (fun u hu => (hF.tendsto _).comp (hlim u (hmem u hu)))

lemma d44_ident (F : E → E) (hF : Continuous F) (hint : IsGloballyIntegrable F)
    (Φ : ℝ → E → E) (hΦ : IsFlowOf F Φ) {a : ℝ} (ha : 0 ≤ a) (Y : ℝ → E) (p : E)
    (hYc : ContinuousOn Y (Set.Icc 0 a))
    (hY : ∀ s ∈ Set.Icc 0 a, Y s = p + ∫ u in (0:ℝ)..s, F (Y u)) :
    ∀ s ∈ Set.Icc 0 a, Y s = Φ s p := by
  have hY0 : Y 0 = p := by have := hY 0 ⟨le_rfl, ha⟩; simpa using this
  rcases ha.eq_or_lt with h0 | hpos
  · intro s hs
    have : s = 0 := by rw [← h0] at hs; linarith [hs.1, hs.2]
    rw [this, hY0, (hΦ p).1]
  let Yh : ℝ → E := Set.IccExtend hpos.le (Set.restrict (Set.Icc 0 a) Y)
  have hYhc : Continuous Yh := (continuousOn_iff_continuous_restrict.1 hYc).Icc_extend'
  have hYhY : ∀ s ∈ Set.Icc 0 a, Yh s = Y s := fun s hs => Set.IccExtend_of_mem _ _ hs
  let Yt : ℝ → E := fun s => p + ∫ u in (0:ℝ)..s, F (Yh u)
  have hYt : ∀ s, HasDerivAt Yt (F (Yh s)) s :=
    fun s => ((hF.comp hYhc).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add p
  have hYtY : ∀ s ∈ Set.Icc 0 a, Yt s = Y s := by
    intro s hs
    rw [hY s hs]
    simp only [Yt]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hs.1] at hu
    simp only [Function.comp]
    rw [hYhY u ⟨hu.1, le_trans hu.2 hs.2⟩]
  have hYt0 : Yt 0 = p := by simp [Yt]
  have hFYt : ∀ s ∈ Set.Icc 0 a, F (Yh s) = F (Yt s) := by
    intro s hs; rw [hYhY s hs, hYtY s hs]
  let Z : ℝ → E := fun s => if s ≤ 0 then Φ s p else if s ≤ a then Yt s else Φ (s - a) (Yt a)
  have hZ : IsIntegralCurveOf F Z := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have heq : Z =ᶠ[𝓝 s] fun s => Φ s p := by
        filter_upwards [Iio_mem_nhds hs] with v hv
        simp [Z, le_of_lt (show v < 0 from hv)]
      have hZs : Z s = Φ s p := by simp [Z, hs.le]
      rw [hZs]; exact ((hΦ p).2 s).congr_of_eventuallyEq heq
    · subst hs
      have hZ0 : Z 0 = p := by simp [Z, (hΦ p).1]
      rw [hZ0]
      have h1 : HasDerivWithinAt Z (F p) (Set.Iic 0) 0 := by
        have := ((hΦ p).2 0).hasDerivWithinAt (s := Set.Iic 0)
        simp only [(hΦ p).1] at this
        refine this.congr (fun v hv => ?_) ?_
        · simp [Z, show v ≤ 0 from hv]
        · simp [Z]
      have h2 : HasDerivWithinAt Z (F p) (Set.Ici 0) 0 := by
        have := (hYt 0).hasDerivWithinAt (s := Set.Ici 0)
        rw [hYhY 0 ⟨le_rfl, hpos.le⟩, hY0] at this
        refine this.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [Ico_mem_nhdsGE hpos] with v hv
          rcases hv.1.eq_or_lt with h | h
          · subst h; simp [Z, hYt0, (hΦ p).1]
          · simp [Z, not_le.2 h, hv.2.le]
        · simp [Z, hYt0, (hΦ p).1]
      have := h1.union h2
      rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rcases lt_trichotomy s a with hsa | hsa | hsa
      · have heq : Z =ᶠ[𝓝 s] Yt := by
          filter_upwards [Ioo_mem_nhds hs hsa] with v hv
          simp [Z, not_le.2 hv.1, hv.2.le]
        have hZs : Z s = Yt s := by simp [Z, not_le.2 hs, hsa.le]
        rw [hZs, ← hFYt s ⟨hs.le, hsa.le⟩]
        exact (hYt s).congr_of_eventuallyEq heq
      · subst hsa
        have hZs : Z s = Yt s := by simp [Z, not_le.2 hs]
        rw [hZs]
        have h1 : HasDerivWithinAt Z (F (Yt s)) (Set.Iic s) s := by
          have := (hYt s).hasDerivWithinAt (s := Set.Iic s)
          rw [hFYt s ⟨hs.le, le_rfl⟩] at this
          refine this.congr_of_eventuallyEq ?_ hZs
          filter_upwards [Ioc_mem_nhdsLE hs] with v hv
          simp [Z, not_le.2 hv.1, hv.2]
        have h2 : HasDerivWithinAt Z (F (Yt s)) (Set.Ici s) s := by
          have := (((hΦ (Yt s)).2 (s - s)).comp_sub_const s s).hasDerivWithinAt (s := Set.Ici s)
          simp only [sub_self, (hΦ (Yt s)).1] at this
          refine this.congr (fun v hv => ?_) ?_
          · rcases (show s ≤ v from hv).eq_or_lt with h | h
            · subst h; simp [Z, not_le.2 hs, (hΦ (Yt s)).1]
            · simp [Z, not_le.2 (lt_trans hs h), not_le.2 h]
          · simp [Z, not_le.2 hs, (hΦ (Yt s)).1]
        have := h1.union h2
        rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      · have heq : Z =ᶠ[𝓝 s] fun v => Φ (v - a) (Yt a) := by
          filter_upwards [Ioi_mem_nhds hsa] with v hv
          simp [Z, not_le.2 (lt_trans hpos (show a < v from hv)), not_le.2 (show a < v from hv)]
        have hZs : Z s = Φ (s - a) (Yt a) := by simp [Z, not_le.2 hs, not_le.2 hsa]
        rw [hZs]
        exact (((hΦ (Yt a)).2 (s - a)).comp_sub_const s a).congr_of_eventuallyEq heq
  have hZ0 : Z 0 = (fun s => Φ s p) 0 := by simp [Z]
  have hZΦ := hint.2 Z (fun s => Φ s p) hZ (hΦ p).2 hZ0
  intro s hs
  have hZs := congrFun hZΦ s
  rcases hs.1.eq_or_lt with h | h
  · subst h; rw [hY0, (hΦ p).1]
  · simp only [Z, not_le.2 h, hs.2, if_true, if_false] at hZs
    rw [← hYtY s hs, hZs]

lemma d44_flow_ftc (F : E → E) (hF : Continuous F) (Φ : ℝ → E → E) (hΦ : IsFlowOf F Φ)
    (q : E) (s : ℝ) : Φ s q = q + ∫ u in (0:ℝ)..s, F (Φ u q) := by
  have hc : Continuous (fun u => Φ u q) :=
    continuous_iff_continuousAt.2 (fun u => ((hΦ q).2 u).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => (hΦ q).2 u)
    ((hF.comp hc).intervalIntegrable _ _), (hΦ q).1]
  abel

lemma d44_flow_cont [ProperSpace E] (F : E → E) (hF : Continuous F)
    (hint : IsGloballyIntegrable F) (Φ : ℝ → E → E) (hΦ : IsFlowOf F Φ) {T : ℝ} (hT : 0 ≤ T)
    (p : E) (pk : ℕ → E) (hpk : Tendsto pk atTop (𝓝 p)) :
    ∀ δ > 0, ∃ k₀, ∀ k ≥ k₀, ∀ s ∈ Set.Icc 0 T, ‖Φ s (pk k) - Φ s p‖ < δ := by
  have hcf : ∀ q, Continuous (fun s => Φ s q) :=
    fun q => continuous_iff_continuousAt.2 (fun s => ((hΦ q).2 s).continuousAt)
  intro δ0 hδ0
  by_contra hcon
  push_neg at hcon
  have hfreq : ∃ᶠ k in atTop, (‖pk k - p‖ < δ0 ∧
      ∃ s ∈ Set.Icc 0 T, δ0 ≤ ‖Φ s (pk k) - Φ s p‖) := by
    rw [Filter.frequently_atTop]
    intro k₀
    obtain ⟨k1, hk1⟩ := (Metric.tendsto_atTop.1 hpk) δ0 hδ0
    obtain ⟨k, hk, s, hs, hbad⟩ := hcon (max k₀ k1)
    exact ⟨k, le_trans (le_max_left _ _) hk,
      by rw [← dist_eq_norm]; exact hk1 k (le_trans (le_max_right _ _) hk), s, hs, hbad⟩
  obtain ⟨ψ, hψ, hP⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hq : Tendsto (fun k => pk (ψ k)) atTop (𝓝 p) := hpk.comp hψ.tendsto_atTop
  obtain ⟨Bad, hBad⟩ : ∃ Bad : ℕ → Set ℝ, Bad = fun k =>
      Set.Icc 0 T ∩ {s | δ0 ≤ ‖Φ s (pk (ψ k)) - Φ s p‖} := ⟨_, rfl⟩
  have hBcl : ∀ k, IsClosed (Bad k) := fun k => by
    rw [hBad]
    exact isClosed_Icc.inter (isClosed_le continuous_const (((hcf _).sub (hcf _)).norm))
  have hBne : ∀ k, (Bad k).Nonempty := fun k => by
    obtain ⟨s, hs, hb⟩ := (hP k).2
    exact ⟨s, by rw [hBad]; exact ⟨hs, hb⟩⟩
  have hBsub : ∀ k, ∀ s ∈ Bad k, s ∈ Set.Icc 0 T ∧ δ0 ≤ ‖Φ s (pk (ψ k)) - Φ s p‖ := by
    intro k s hs; rw [hBad] at hs; exact hs
  have hBbdd : ∀ k, BddBelow (Bad k) := fun k => ⟨0, fun z hz => (hBsub k z hz).1.1⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, σ = fun k => sInf (Bad k) := ⟨_, rfl⟩
  have hσmem : ∀ k, σ k ∈ Set.Icc 0 T ∧ δ0 ≤ ‖Φ (σ k) (pk (ψ k)) - Φ (σ k) p‖ := fun k => by
    rw [hσ]; exact hBsub k _ ((hBcl k).csInf_mem (hBne k) (hBbdd k))
  have hσpos : ∀ k, 0 < σ k := by
    intro k
    rcases (hσmem k).1.1.eq_or_lt with h | h
    · exfalso
      have := (hσmem k).2
      rw [← h, (hΦ _).1, (hΦ _).1] at this
      linarith [(hP k).1]
    · exact h
  have hgood : ∀ k, ∀ s ∈ Set.Icc 0 (σ k), ‖Φ s (pk (ψ k)) - Φ s p‖ ≤ δ0 := by
    intro k
    have hsub : Set.Ico 0 (σ k) ⊆ {s | ‖Φ s (pk (ψ k)) - Φ s p‖ ≤ δ0} := by
      intro s hs
      by_contra hc
      simp only [Set.mem_setOf_eq, not_le] at hc
      have hin : s ∈ Bad k := by
        rw [hBad]; exact ⟨⟨hs.1, by linarith [hs.2, (hσmem k).1.2]⟩, hc.le⟩
      have := csInf_le (hBbdd k) hin
      rw [hσ] at hs
      linarith [hs.2]
    have hcl : IsClosed {s | ‖Φ s (pk (ψ k)) - Φ s p‖ ≤ δ0} :=
      isClosed_le (((hcf _).sub (hcf _)).norm) continuous_const
    intro s hs
    exact hcl.closure_subset_iff.2 hsub (by rw [closure_Ico (hσpos k).ne]; exact hs)
  obtain ⟨R0, hR0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
    (hcf p).continuousOn
  have hR00 : 0 ≤ R0 := le_trans (norm_nonneg _) (hR0 0 ⟨le_rfl, hT⟩)
  have hinball : ∀ k, ∀ s ∈ Set.Icc 0 (σ k), ‖Φ s (pk (ψ k))‖ ≤ R0 + δ0 := by
    intro k s hs
    have h1 := hgood k s hs
    have h2 := hR0 s ⟨hs.1, le_trans hs.2 (hσmem k).1.2⟩
    calc ‖Φ s (pk (ψ k))‖ = ‖(Φ s (pk (ψ k)) - Φ s p) + Φ s p‖ := by rw [sub_add_cancel]
      _ ≤ ‖Φ s (pk (ψ k)) - Φ s p‖ + ‖Φ s p‖ := norm_add_le _ _
      _ ≤ R0 + δ0 := by linarith
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0:E) (R0 + δ0)).exists_bound_of_continuousOn
    hF.continuousOn
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → E, g = fun k s => Φ (min s (σ k)) (pk (ψ k)) := ⟨_, rfl⟩
  have hgL : ∀ k, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T,
      ‖g k s - g k s'‖ ≤ MF * |s - s'| := by
    intro k s hs s' hs'
    rw [hg]
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => Φ u (pk (ψ k))) (f' := fun u => F (Φ u (pk (ψ k))))
      (s := Set.Icc 0 (σ k)) (C := MF)
      (fun u _ => ((hΦ _).2 u).hasDerivWithinAt)
      (fun u hu => hMF _ (mem_closedBall_zero_iff.2 (hinball k u hu))) (convex_Icc _ _)
      (x := min s' (σ k)) (y := min s (σ k))
      ⟨le_min hs'.1 (hσpos k).le, min_le_right _ _⟩ ⟨le_min hs.1 (hσpos k).le, min_le_right _ _⟩
    have hMF0 : 0 ≤ MF := le_trans (norm_nonneg _) (hMF 0 (mem_closedBall_zero_iff.2
      (by simp; linarith)))
    refine le_trans hmv (mul_le_mul_of_nonneg_left ?_ hMF0)
    rw [Real.norm_eq_abs]
    refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
    simp
  have hgR : ∀ k, ∀ s ∈ Set.Icc 0 T, ‖g k s‖ ≤ R0 + δ0 := by
    intro k s hs
    rw [hg]
    exact hinball k _ ⟨le_min hs.1 (hσpos k).le, min_le_right _ _⟩
  have hgc : ∀ k, Continuous (g k) := by
    intro k; rw [hg]
    exact (hcf _).comp (continuous_id.min continuous_const)
  obtain ⟨σs, hσs, φ1, hφ1, hσlim⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).tendsto_subseq
    (fun k => (hσmem k).1)
  obtain ⟨φ2, hφ2, Y, hYc, hYu⟩ := d44_AA (fun k => g (φ1 k)) (fun k => hgL (φ1 k))
    (fun k => hgR (φ1 k))
  -- K = φ1 ∘ φ2
  have hσK : Tendsto (fun k => σ (φ1 (φ2 k))) atTop (𝓝 σs) := hσlim.comp hφ2.tendsto_atTop
  have hqK : Tendsto (fun k => pk (ψ (φ1 (φ2 k)))) atTop (𝓝 p) :=
    hq.comp ((hφ1.comp hφ2).tendsto_atTop)
  have hpt : ∀ s ∈ Set.Icc 0 T, Tendsto (fun k => g (φ1 (φ2 k)) s) atTop (𝓝 (Y s)) := by
    intro s hs
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := hYu ε hε
    exact ⟨k₀, fun k hk => by rw [dist_eq_norm]; exact hk₀ k hk s hs⟩
  have hint_eq : ∀ s ∈ Set.Ico 0 σs, Y s = p + ∫ u in (0:ℝ)..s, F (Y u) := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, by linarith [hs.2, hσs.2]⟩
    have hL := d44_lim F hF (R := R0 + δ0) hs.1 (fun k => g (φ1 (φ2 k))) Y
      (fun k => (hF.comp (hgc _)).intervalIntegrable _ _)
      (fun k u hu => hgR _ u ⟨hu.1, le_trans hu.2 hsT.2⟩)
      (fun u hu => hpt u ⟨hu.1, le_trans hu.2 hsT.2⟩)
    have hev : ∀ᶠ k in atTop, g (φ1 (φ2 k)) s =
        pk (ψ (φ1 (φ2 k))) + ∫ u in (0:ℝ)..s, F (g (φ1 (φ2 k)) u) := by
      filter_upwards [hσK.eventually (eventually_gt_nhds hs.2)] with k hk
      rw [hg]
      simp only
      rw [min_eq_left hk.le, d44_flow_ftc F hF Φ hΦ]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hs.1] at hu
      simp only
      rw [min_eq_left (le_trans hu.2 hk.le)]
    exact tendsto_nhds_unique (hpt s hsT) ((hqK.add hL).congr' (hev.mono fun k hk => hk.symm))
  have hY0 : Y 0 = p := by
    have hev : ∀ᶠ k in atTop, g (φ1 (φ2 k)) 0 = pk (ψ (φ1 (φ2 k))) := by
      refine Eventually.of_forall (fun k => ?_)
      rw [hg]; simp only
      rw [min_eq_left (hσpos _).le, (hΦ _).1]
    exact tendsto_nhds_unique (hpt 0 ⟨le_rfl, hT⟩) (hqK.congr' (hev.mono fun k hk => hk.symm))
  have hint_eq' : ∀ s ∈ Set.Icc 0 σs, Y s = p + ∫ u in (0:ℝ)..s, F (Y u) := by
    rcases hσs.1.eq_or_lt with h0 | hpos
    · intro s hs
      have : s = 0 := by rw [← h0] at hs; linarith [hs.1, hs.2]
      rw [this, hY0]; simp
    · have hYc' : ContinuousOn Y (Set.Icc 0 σs) := hYc.mono (Set.Icc_subset_Icc le_rfl hσs.2)
      have hIc : ContinuousOn (fun s => p + ∫ u in (0:ℝ)..s, F (Y u)) (Set.Icc 0 σs) := by
        have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
          (f := fun u => F (Y u)) (a := 0) (b := σs)
          (by rw [Set.uIcc_of_le hpos.le]
              exact (hF.comp_continuousOn hYc').integrableOn_Icc)
        rw [Set.uIcc_of_le hpos.le] at this
        exact continuousOn_const.add this
      exact Set.EqOn.of_subset_closure hint_eq hYc' hIc Set.Ico_subset_Icc_self
        (by rw [closure_Ico hpos.ne])
  have hYΦ := d44_ident F hF hint Φ hΦ hσs.1 Y p
    (hYc.mono (Set.Icc_subset_Icc le_rfl hσs.2)) hint_eq'
  -- contradiction
  have hδ3 : 0 < δ0 / 3 := by positivity
  obtain ⟨k1, hk1⟩ := hYu (δ0 / 3) hδ3
  have hYt : Tendsto (fun k => Y (σ (φ1 (φ2 k)))) atTop (𝓝 (Y σs)) :=
    (hYc σs hσs).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hσK, Eventually.of_forall (fun k => (hσmem _).1)⟩)
  obtain ⟨k2, hk2⟩ := (Metric.tendsto_atTop.1 hYt) (δ0 / 3) hδ3
  obtain ⟨k3, hk3⟩ := (Metric.tendsto_atTop.1 (((hcf p).tendsto σs).comp hσK)) (δ0 / 3) hδ3
  set k := max k1 (max k2 k3)
  have e1 := hk1 k (le_max_left _ _) (σ (φ1 (φ2 k))) (hσmem _).1
  have e2 := hk2 k (le_trans (le_max_left _ _) (le_max_right _ _))
  have e3 := hk3 k (le_trans (le_max_right _ _) (le_max_right _ _))
  rw [dist_eq_norm] at e2 e3
  simp only [Function.comp] at e3
  have hgσ : g (φ1 (φ2 k)) (σ (φ1 (φ2 k))) = Φ (σ (φ1 (φ2 k))) (pk (ψ (φ1 (φ2 k)))) := by
    rw [hg]; simp
  rw [hgσ] at e1
  rw [hYΦ σs ⟨hσs.1, le_rfl⟩] at e2
  have hbad := (hσmem (φ1 (φ2 k))).2
  have : ‖Φ (σ (φ1 (φ2 k))) (pk (ψ (φ1 (φ2 k)))) - Φ (σ (φ1 (φ2 k))) p‖ < δ0 := by
    calc _ = ‖(Φ (σ (φ1 (φ2 k))) (pk (ψ (φ1 (φ2 k)))) - Y (σ (φ1 (φ2 k)))) +
          (Y (σ (φ1 (φ2 k))) - Φ σs p) + (Φ σs p - Φ (σ (φ1 (φ2 k))) p)‖ := by
            congr 1; abel
      _ ≤ _ := norm_add₃_le
      _ < δ0 / 3 + δ0 / 3 + δ0 / 3 := by
          rw [norm_sub_rev (Φ σs p)]
          linarith
      _ = δ0 := by ring
  linarith

end Goal1

section Part5
variable {γ : ℕ → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma d44_prim_contNN (hγ : IsStepSizeSeq γ) (G : ℕ → E) :
    Continuous (fun t : ℝ≥0 => ∫ s in (0:ℝ)..(t:ℝ), G (mIdx γ s)) := by
  have hco : ContinuousOn (fun v => ∫ s in (0:ℝ)..v, G (mIdx γ s)) (Set.Ici 0) := by
    intro v hv
    have hv0 : (0:ℝ) ≤ v := hv
    have := (d44_prim_cont hγ G (b := v + 1) (by linarith)) v ⟨hv0, by linarith⟩
    refine this.mono_of_mem_nhdsWithin ?_
    refine Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici 0)
      (Iio_mem_nhds (show v < v + 1 by linarith))) ?_
    intro w hw
    exact ⟨hw.1, le_of_lt hw.2⟩
  exact hco.comp_continuous NNReal.continuous_coe (fun t => t.2)

lemma d44_XW (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E) (hx : SatisfiesScheme F γ x U)
    {t T h' : ℝ} (ht : 1 ≤ t) (hh' : h' ∈ Set.Icc (0:ℝ) T) :
    ‖interpAffine γ x (t + h') - (interpAffine γ x t + ((∫ s in (0:ℝ)..t + h', F (x (mIdx γ s))) -
      ∫ s in (0:ℝ)..t, F (x (mIdx γ s))))‖ ≤ 2 * Delta γ U (t - 1) (T + 1) := by
  have ht0 : 0 ≤ t := by linarith
  have hth : 0 ≤ t + h' := by linarith [hh'.1]
  have hX1 := d44_X_decomp F hγ x U hx hth
  have hX0 := d44_X_decomp F hγ x U hx ht0
  have e : interpAffine γ x (t + h') - (interpAffine γ x t +
      ((∫ s in (0:ℝ)..t + h', F (x (mIdx γ s))) - ∫ s in (0:ℝ)..t, F (x (mIdx γ s)))) =
      (∫ s in (0:ℝ)..t + h', U (mIdx γ s + 1)) - ∫ s in (0:ℝ)..t, U (mIdx γ s + 1) := by
    rw [hX1, hX0]
    abel
  have f1 : (∫ s in (0:ℝ)..t + h', U (mIdx γ s + 1)) - ∫ s in (0:ℝ)..t, U (mIdx γ s + 1) =
      ∫ s in t..t + h', U (mIdx γ s + 1) :=
    intervalIntegral.integral_interval_sub_left
      (d44_intInt hγ (fun k => U (k + 1)) le_rfl hth)
      (d44_intInt hγ (fun k => U (k + 1)) le_rfl ht0)
  have f2 : (∫ s in (t - 1)..t + h', U (mIdx γ s + 1)) - ∫ s in (t - 1)..t, U (mIdx γ s + 1) =
      ∫ s in t..t + h', U (mIdx γ s + 1) :=
    intervalIntegral.integral_interval_sub_left
      (d44_intInt hγ (fun k => U (k + 1)) (by linarith) hth)
      (d44_intInt hγ (fun k => U (k + 1)) (by linarith) ht0)
  rw [e, f1, ← f2]
  have i1 : ‖∫ s in (t - 1)..t + h', U (mIdx γ s + 1)‖ ≤ Delta γ U (t - 1) (T + 1) := by
    rw [show t + h' = (t - 1) + (h' + 1) by ring]
    exact d44_delta_le hγ U (by linarith [hh'.1]) (by linarith [hh'.2])
  have i2 : ‖∫ s in (t - 1)..t, U (mIdx γ s + 1)‖ ≤ Delta γ U (t - 1) (T + 1) := by
    have := d44_delta_le hγ U (a := t - 1) (T := T + 1) (h := 1) (by norm_num)
      (by linarith [hh'.1, hh'.2])
    rwa [show t - 1 + 1 = t by ring] at this
  linarith [norm_sub_le (∫ s in (t - 1)..t + h', U (mIdx γ s + 1))
    (∫ s in (t - 1)..t, U (mIdx γ s + 1))]

/-- smallness of the noise and of the jump for large `t`. -/
lemma d44_small (F : E → E) (hγ : IsStepSizeSeq γ) (x U : ℕ → E) (hx : SatisfiesScheme F γ x U)
    (hA1 : SatisfiesA1 γ U) (K : ℝ) (hK : ∀ n, ‖F (x n)‖ ≤ K) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t ≥ t₀, ∀ u ∈ Set.Icc (0:ℝ) T,
      ‖interpAffine γ x (t + u) - (interpAffine γ x t + ((∫ s in (0:ℝ)..t + u, F (x (mIdx γ s))) -
        ∫ s in (0:ℝ)..t, F (x (mIdx γ s))))‖ < η ∧
      ‖x (mIdx γ (t + u)) - (interpAffine γ x t + ((∫ s in (0:ℝ)..t + u, F (x (mIdx γ s))) -
        ∫ s in (0:ℝ)..t, F (x (mIdx γ s))))‖ < η := by
  intro η hη
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hDt := (d44_a1_core hγ U (T + 1) (by linarith)).1 (hA1 (T + 1) (by linarith))
  obtain ⟨t1, ht1⟩ := (Metric.tendsto_atTop.1 hDt) (η / 8) (by positivity)
  obtain ⟨N, hN⟩ := (hγ.2.2.eventually (eventually_le_nhds
    (show (0:ℝ) < η / (8 * (K + 1)) by positivity))).exists_forall_of_atTop
  obtain ⟨t2, ht2, hc⟩ := d44_const_pt F hγ x U hx K hK
  refine ⟨max t2 (max (t1 + 1) (tau γ N)), le_trans ht2 (le_max_left _ _), ?_⟩
  intro t ht u hu
  have htt2 : t2 ≤ t := le_trans (le_max_left _ _) ht
  have ht1' : t1 + 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htN : tau γ N ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hD : Delta γ U (t - 1) (T + 1) < η / 8 := by
    have := ht1 (t - 1) (by linarith)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hXW := d44_XW F hγ x U hx (le_trans ht2 htt2) hu
  have hin : t + u ∈ Set.Icc t (t + T) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hXc := hc t htt2 T hT (t + u) hin
  have hst : stepInterp γ (t + u) ≤ η / (8 * (K + 1)) :=
    hN _ (d44_le_mIdx hγ (by linarith [hu.1]))
  have hKs : K * stepInterp γ (t + u) ≤ η / 8 := by
    calc K * stepInterp γ (t + u) ≤ K * (η / (8 * (K + 1))) :=
          mul_le_mul_of_nonneg_left hst hK0
      _ ≤ η / 8 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  constructor
  · linarith
  · have := norm_sub_le_norm_sub_add_norm_sub (x (mIdx γ (t + u))) (interpAffine γ x (t + u))
      (interpAffine γ x t + ((∫ s in (0:ℝ)..t + u, F (x (mIdx γ s))) -
        ∫ s in (0:ℝ)..t, F (x (mIdx γ s))))
    have h2 := norm_sub_rev (x (mIdx γ (t + u))) (interpAffine γ x (t + u))
    linarith

lemma d44_X_bound (hγ : IsStepSizeSeq γ) (x : ℕ → E) {B : ℝ} (hB : ∀ n, ‖x n‖ ≤ B) {u : ℝ}
    (hu : 0 ≤ u) : ‖interpAffine γ x u‖ ≤ B := by
  have hs := d44_mIdx_spec hγ hu
  have hg := d44_gamma_pos hγ hu
  have hτ := d44_tau_succ (γ := γ) (mIdx γ u)
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = (u - tau γ (mIdx γ u)) / γ (mIdx γ u + 1) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) hg.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hg]; linarith
  unfold interpAffine
  rw [← hθ]
  have : x (mIdx γ u) + θ • (x (mIdx γ u + 1) - x (mIdx γ u)) =
      (1 - θ) • x (mIdx γ u) + θ • x (mIdx γ u + 1) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  calc _ ≤ ‖(1 - θ) • x (mIdx γ u)‖ + ‖θ • x (mIdx γ u + 1)‖ := norm_add_le _ _
    _ = (1 - θ) * ‖x (mIdx γ u)‖ + θ * ‖x (mIdx γ u + 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hθ0]
    _ ≤ (1 - θ) * B + θ * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hB _) (by linarith))
          (mul_le_mul_of_nonneg_left (hB _) hθ0)
    _ = B := by ring

theorem d44_goal_core [ProperSpace E] (F : E → E) (hF : Continuous F)
    (hint : IsGloballyIntegrable F) (Φ : ℝ → E → E) (hΦ : IsFlowOf F Φ)
    (hγ : IsStepSizeSeq γ) (x U : ℕ → E)
    (hx : SatisfiesScheme F γ x U) (hA1 : SatisfiesA1 γ U)
    (hA2 : SatisfiesA2 x ∨ SatisfiesA2' F x) :
    IsAsymptoticPseudotrajectory Φ (fun t : ℝ≥0 => interpAffine γ x (t : ℝ)) := by
  have hXc : Continuous (fun t : ℝ≥0 => interpAffine γ x (t : ℝ)) := by
    have : (fun t : ℝ≥0 => interpAffine γ x (t : ℝ)) = fun t : ℝ≥0 =>
        x 0 + (∫ s in (0:ℝ)..(t:ℝ), F (x (mIdx γ s))) + ∫ s in (0:ℝ)..(t:ℝ), U (mIdx γ s + 1) := by
      funext t; exact d44_X_decomp F hγ x U hx t.2
    rw [this]
    exact (continuous_const.add (d44_prim_contNN hγ (fun k => F (x k)))).add
      (d44_prim_contNN hγ (fun k => U (k + 1)))
  refine ⟨hXc, ?_⟩
  intro T hT ε hε
  have hT' : (0:ℝ) < T := hT
  rcases hA2 with ⟨B, hB⟩ | ⟨r, hr, L, K, hLip, hKb⟩
  · -- Case A2
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    obtain ⟨K, hK'⟩ := (isCompact_closedBall (0:E) B).exists_bound_of_continuousOn hF.continuousOn
    have hK : ∀ n, ‖F (x n)‖ ≤ K := fun n => hK' _ (mem_closedBall_zero_iff.2 (hB n))
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
    by_contra hcon
    push_neg at hcon
    choose tf htf hf hhf hdist using hcon
    obtain ⟨tr, htr⟩ : ∃ tr : ℕ → ℝ, tr = fun k : ℕ => ((tf ((k : ℕ) : ℝ≥0)) : ℝ) := ⟨_, rfl⟩
    have htrk : ∀ k : ℕ, (k : ℝ) ≤ tr k := by
      intro k; rw [htr]; exact_mod_cast htf (k : ℝ≥0)
    have htr0 : ∀ k, 0 ≤ tr k := fun k => le_trans (Nat.cast_nonneg k) (htrk k)
    obtain ⟨W, hW⟩ : ∃ W : ℕ → ℝ → E, W = fun k v => interpAffine γ x (tr k) +
        ((∫ s in (0:ℝ)..tr k + v, F (x (mIdx γ s))) - ∫ s in (0:ℝ)..tr k, F (x (mIdx γ s))) :=
      ⟨_, rfl⟩
    have hWL : ∀ k, ∀ s ∈ Set.Icc 0 (T:ℝ), ∀ s' ∈ Set.Icc 0 (T:ℝ),
        ‖W k s - W k s'‖ ≤ K * |s - s'| := by
      intro k s hs s' hs'
      have f : (∫ v in (0:ℝ)..tr k + s, F (x (mIdx γ v))) -
          (∫ v in (0:ℝ)..tr k + s', F (x (mIdx γ v))) =
          ∫ v in tr k + s'..tr k + s, F (x (mIdx γ v)) :=
        intervalIntegral.integral_interval_sub_left
          (d44_intInt hγ (fun k => F (x k)) le_rfl (by linarith [htr0 k, hs.1]))
          (d44_intInt hγ (fun k => F (x k)) le_rfl (by linarith [htr0 k, hs'.1]))
      have e : W k s - W k s' = ∫ v in tr k + s'..tr k + s, F (x (mIdx γ v)) := by
        rw [← f, hW]
        beta_reduce
        abel
      rw [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := tr k + s') (b := tr k + s) (f := fun v => F (x (mIdx γ v))) (C := K)
        (fun v _ => hK _)
      rwa [show tr k + s - (tr k + s') = s - s' by ring] at this
    have hWR : ∀ k, ∀ s ∈ Set.Icc 0 (T:ℝ), ‖W k s‖ ≤ B + K * T := by
      intro k s hs
      have h0 : W k s - W k 0 = W k s - W k 0 := rfl
      have := hWL k s hs 0 ⟨le_rfl, hT'.le⟩
      have hW0 : W k 0 = interpAffine γ x (tr k) := by rw [hW]; simp
      rw [hW0, sub_zero, abs_of_nonneg hs.1] at this
      have hXb := d44_X_bound hγ x hB (htr0 k)
      calc ‖W k s‖ = ‖(W k s - interpAffine γ x (tr k)) + interpAffine γ x (tr k)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖W k s - interpAffine γ x (tr k)‖ + ‖interpAffine γ x (tr k)‖ := norm_add_le _ _
        _ ≤ K * s + B := add_le_add this hXb
        _ ≤ B + K * T := by nlinarith [hs.2]
    obtain ⟨φ, hφ, Y, hYc, hYu⟩ := d44_AA W hWL hWR
    have hφk : ∀ k : ℕ, (k : ℝ) ≤ tr (φ k) :=
      fun k => le_trans (by exact_mod_cast hφ.id_le k) (htrk (φ k))
    have hge : ∀ (c : ℝ) (k k₂ : ℕ), k₂ ≤ k → c ≤ (k₂ : ℝ) → c ≤ tr (φ k) :=
      fun c k k₂ h1 h2 => le_trans h2 (le_trans (by exact_mod_cast h1) (hφk k))
    have hsm := d44_small F hγ x U hx hA1 K hK hT'
    -- convergence of the pieces
    have hW0 : ∀ k, W k 0 = interpAffine γ x (tr k) := fun k => by rw [hW]; simp
    have hp : Tendsto (fun k => interpAffine γ x (tr (φ k))) atTop (𝓝 (Y 0)) := by
      rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨k₀, hk₀⟩ := hYu η hη
      exact ⟨k₀, fun k hk => by
        rw [dist_eq_norm, ← hW0]; exact hk₀ k hk 0 ⟨le_rfl, hT'.le⟩⟩
    have hxbar : ∀ u ∈ Set.Icc 0 (T:ℝ),
        Tendsto (fun k => x (mIdx γ (tr (φ k) + u))) atTop (𝓝 (Y u)) := by
      intro u hu
      rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨t₀, _, ht₀⟩ := hsm (η / 2) (by positivity)
      obtain ⟨k₁, hk₁⟩ := hYu (η / 2) (by positivity)
      obtain ⟨k₂, hk₂⟩ := exists_nat_ge t₀
      refine ⟨max k₁ k₂, fun k hk => ?_⟩
      have h1 := (ht₀ (tr (φ k)) (hge t₀ k k₂ (le_trans (le_max_right _ _) hk) hk₂) u hu).2
      have h2 := hk₁ k (le_trans (le_max_left _ _) hk) u hu
      rw [hW] at h2
      simp only at h2
      rw [dist_eq_norm]
      calc _ = ‖(x (mIdx γ (tr (φ k) + u)) - (interpAffine γ x (tr (φ k)) +
            ((∫ s in (0:ℝ)..tr (φ k) + u, F (x (mIdx γ s))) -
              ∫ s in (0:ℝ)..tr (φ k), F (x (mIdx γ s))))) +
            ((interpAffine γ x (tr (φ k)) + ((∫ s in (0:ℝ)..tr (φ k) + u, F (x (mIdx γ s))) -
              ∫ s in (0:ℝ)..tr (φ k), F (x (mIdx γ s)))) - Y u)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ < η / 2 + η / 2 := add_lt_add h1 h2
        _ = η := by ring
    have hYeq : ∀ s ∈ Set.Icc 0 (T:ℝ), Y s = Y 0 + ∫ u in (0:ℝ)..s, F (Y u) := by
      intro s hs
      have hL := d44_lim F hF (R := B) hs.1 (fun k u => x (mIdx γ (tr (φ k) + u))) Y
        (fun k => by
          have := (d44_intInt hγ (fun k => F (x k)) (a := tr (φ k)) (b := tr (φ k) + s)
            (htr0 _) (by linarith [htr0 (φ k), hs.1])).comp_add_left (tr (φ k))
          rwa [sub_self, add_sub_cancel_left] at this)
        (fun k u _ => hB _)
        (fun u hu => hxbar u ⟨hu.1, le_trans hu.2 hs.2⟩)
      have hev : ∀ k, W (φ k) s = interpAffine γ x (tr (φ k)) +
          ∫ u in (0:ℝ)..s, F (x (mIdx γ (tr (φ k) + u))) := by
        intro k
        rw [hW]; simp only
        congr 1
        rw [intervalIntegral.integral_comp_add_left (fun v => F (x (mIdx γ v))) (tr (φ k)),
          add_zero, intervalIntegral.integral_interval_sub_left
          (d44_intInt hγ (fun k => F (x k)) le_rfl (by linarith [htr0 (φ k), hs.1]))
          (d44_intInt hγ (fun k => F (x k)) le_rfl (htr0 _))]
      have hWs : Tendsto (fun k => W (φ k) s) atTop (𝓝 (Y s)) := by
        rw [Metric.tendsto_atTop]
        intro η hη
        obtain ⟨k₀, hk₀⟩ := hYu η hη
        exact ⟨k₀, fun k hk => by rw [dist_eq_norm]; exact hk₀ k hk s hs⟩
      refine tendsto_nhds_unique hWs ?_
      have := hp.add hL
      refine this.congr (fun k => ?_)
      rw [hev k]
    have hYΦ := d44_ident F hF hint Φ hΦ hT'.le Y (Y 0) hYc hYeq
    have hfc := d44_flow_cont F hF hint Φ hΦ hT'.le (Y 0) _ hp
    -- final contradiction
    obtain ⟨t₀, _, ht₀⟩ := hsm (ε / 3) (by positivity)
    obtain ⟨k₁, hk₁⟩ := hYu (ε / 3) (by positivity)
    obtain ⟨k₂, hk₂⟩ := exists_nat_ge t₀
    obtain ⟨k₃, hk₃⟩ := hfc (ε / 3) (by positivity)
    set k := max k₁ (max k₂ k₃)
    have hh : ((hf (φ k : ℝ≥0)) : ℝ) ∈ Set.Icc 0 (T:ℝ) :=
      ⟨(hf _).2, by exact_mod_cast hhf (φ k : ℝ≥0)⟩
    have e1 := (ht₀ (tr (φ k)) (hge t₀ k k₂ (le_trans (le_max_left _ _) (le_max_right _ _))
      hk₂) _ hh).1
    have e2 := hk₁ k (le_max_left _ _) _ hh
    have e3 := hk₃ k (le_trans (le_max_right _ _) (le_max_right _ _)) _ hh
    rw [hW] at e2
    simp only at e2
    rw [hYΦ _ hh] at e2
    have hd := hdist (φ k : ℝ≥0)
    beta_reduce at hd
    rw [htr] at e1 e2 e3
    simp only at e1 e2 e3
    rw [dist_eq_norm, NNReal.coe_add] at hd
    have : ‖interpAffine γ x ((tf (φ k : ℝ≥0) : ℝ) + (hf (φ k : ℝ≥0) : ℝ)) -
        Φ (hf (φ k : ℝ≥0)) (interpAffine γ x (tf (φ k : ℝ≥0)))‖ < ε := by
      set A := interpAffine γ x ((tf (φ k : ℝ≥0) : ℝ) + (hf (φ k : ℝ≥0) : ℝ))
      set Wv := interpAffine γ x (tf (φ k : ℝ≥0)) +
        ((∫ s in (0:ℝ)..(tf (φ k : ℝ≥0) : ℝ) + (hf (φ k : ℝ≥0) : ℝ), F (x (mIdx γ s))) -
          ∫ s in (0:ℝ)..(tf (φ k : ℝ≥0) : ℝ), F (x (mIdx γ s)))
      set P := Φ (hf (φ k : ℝ≥0)) (Y 0)
      set Q := Φ (hf (φ k : ℝ≥0)) (interpAffine γ x (tf (φ k : ℝ≥0)))
      calc ‖A - Q‖ = ‖(A - Wv) + (Wv - P) + (P - Q)‖ := by congr 1; abel
        _ ≤ ‖A - Wv‖ + ‖Wv - P‖ + ‖P - Q‖ := norm_add₃_le
        _ < ε / 3 + ε / 3 + ε / 3 := by
            rw [norm_sub_rev P Q]
            linarith
        _ = ε := by ring
    linarith
  · -- Case A2'
    obtain ⟨C, hC⟩ := d44_shadow_core F Φ hΦ T hT' L K
    obtain ⟨t₀, ht₀1, ht₀⟩ := hC γ x U r hγ hx hA1 hr hLip hKb
    have hxmem : ∀ n, x n ∈ Metric.thickening r (Set.range x) :=
      fun n => Metric.self_subset_thickening hr _ ⟨n, rfl⟩
    have hK : ∀ n, ‖F (x n)‖ ≤ K := fun n => hKb _ (hxmem n)
    have hC1 : 0 < |C| + 1 := by positivity
    obtain ⟨η, hη⟩ : ∃ η, η = ε / (2 * (|C| + 1)) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hη]; positivity
    have hDt := (d44_a1_core hγ U (T + 1) (by linarith)).1 (hA1 (T + 1) (by linarith))
    obtain ⟨t1, ht1⟩ := (Metric.tendsto_atTop.1 hDt) η hη0
    obtain ⟨N, hN⟩ := (hγ.2.2.eventually (eventually_le_nhds hη0)).exists_forall_of_atTop
    refine ⟨Real.toNNReal (max t₀ (max (t1 + 1) (tau γ N))), fun t ht h hh => ?_⟩
    have ht' : max t₀ (max (t1 + 1) (tau γ N)) ≤ (t : ℝ) := Real.toNNReal_le_iff_le_coe.1 ht
    have htt0 : t₀ ≤ (t:ℝ) := le_trans (le_max_left _ _) ht'
    have ht1' : t1 + 1 ≤ (t:ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht'
    have htN : tau γ N ≤ (t:ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht'
    have hhI : (h : ℝ) ∈ Set.Icc 0 (T:ℝ) := ⟨h.2, by exact_mod_cast hh⟩
    have hbound := ht₀ t htt0 h hhI
    have hD0 : 0 ≤ Delta γ U ((t:ℝ) - 1) (T + 1) := d44_delta_nonneg U _ _
    have hD : Delta γ U ((t:ℝ) - 1) (T + 1) < η := by
      have := ht1 ((t:ℝ) - 1) (by linarith)
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    have hbdd : BddAbove (stepInterp γ '' Set.Icc (t:ℝ) (t + T)) := by
      obtain ⟨B, hB⟩ := hγ.2.2.bddAbove_range
      exact ⟨B, by rintro _ ⟨v, _, rfl⟩; exact hB ⟨_, rfl⟩⟩
    have hs0 : 0 ≤ sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T)) :=
      le_trans (hγ.1 _) (le_csSup hbdd ⟨t, ⟨le_rfl, by linarith⟩, rfl⟩)
    have hsη : sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T)) ≤ η :=
      csSup_le ⟨_, t, ⟨le_rfl, by linarith⟩, rfl⟩
        (by rintro _ ⟨v, hv, rfl⟩; exact hN _ (d44_le_mIdx hγ (by linarith [hv.1])))
    beta_reduce
    rw [dist_eq_norm, NNReal.coe_add]
    have hsum0 : 0 ≤ Delta γ U ((t:ℝ) - 1) (T + 1) + sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T)) :=
      by linarith
    have hCle : C * (Delta γ U ((t:ℝ) - 1) (T + 1) + sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T)))
        ≤ (|C| + 1) * (Delta γ U ((t:ℝ) - 1) (T + 1) +
          sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T))) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hsum0
    have hlt : (|C| + 1) * (Delta γ U ((t:ℝ) - 1) (T + 1) +
        sSup (stepInterp γ '' Set.Icc (t:ℝ) (t + T))) < (|C| + 1) * (2 * η) :=
      mul_lt_mul_of_pos_left (by linarith) hC1
    have h2η : (|C| + 1) * (2 * η) = ε := by rw [hη]; field_simp
    linarith

end Part5

end StochApproxDyn.Interpolation

open StochApproxDyn.Interpolation


theorem solution {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (hint : IsGloballyIntegrable F)
    (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : IsFlowOf F Φ)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (hA1 : SatisfiesA1 γ U)
    (hA2 : SatisfiesA2 x ∨ SatisfiesA2' F x) :
    IsAsymptoticPseudotrajectory Φ (fun t : ℝ≥0 => interpAffine γ x (t : ℝ)) := by
  exact d44_goal_core F hF hint Φ hΦ hγ x U hx hA1 hA2
