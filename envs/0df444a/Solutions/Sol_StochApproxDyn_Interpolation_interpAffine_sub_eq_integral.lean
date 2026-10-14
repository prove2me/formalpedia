-- Prove2me | solution 1 for StochApproxDyn.Interpolation.interpAffine_sub_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:09:16.738804+00:00
-- url     : https://prove2.me/submissions/11dfbc59-ce25-4bcb-af68-3b2a05fbbf0f

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

end StochApproxDyn.Interpolation

open StochApproxDyn.Interpolation


theorem solution {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (t : ℝ) (ht : 0 ≤ t) :
    interpAffine γ x t - interpAffine γ x 0 =
      ∫ s in (0 : ℝ)..t, (F (interpConst γ x s) + noiseInterp γ U s) := by
  exact d44_sub_eq_integral_core F hγ x U hx t ht
