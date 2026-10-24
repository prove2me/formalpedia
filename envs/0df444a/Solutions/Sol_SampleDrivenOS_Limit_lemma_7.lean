-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:51:06.438987+00:00
-- url     : https://prove2.me/submissions/72c58590-822b-49ef-aac1-0ea1c4d58e8c

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace Lemma7Aux

/-- `b_i(p) = (i+2)p^{i+1} - (i+1)p^{i+2} ∈ [0,1]` for `p ∈ [0,1]`. -/
lemma b_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    0 ≤ ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) := by
  have h : ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)
      = p ^ (i + 1) * (((i : ℝ) + 2) - ((i : ℝ) + 1) * p) := by ring
  rw [h]
  apply mul_nonneg (pow_nonneg hp0 _)
  have : ((i : ℝ) + 1) * p ≤ (i : ℝ) + 1 := by
    have : (0:ℝ) ≤ (i : ℝ) + 1 := by positivity
    nlinarith
  linarith

lemma b_le_one (p : ℝ) (hp0 : 0 ≤ p) (i : ℕ) :
    ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) ≤ 1 := by
  induction i with
  | zero =>
    simp
    nlinarith [sq_nonneg (p - 1)]
  | succ n ih =>
    have key : (((n + 1 : ℕ) : ℝ) + 2) * p ^ (n + 1 + 1) - (((n + 1 : ℕ) : ℝ) + 1) * p ^ (n + 1 + 2)
        = (((n : ℝ) + 2) * p ^ (n + 1) - ((n : ℝ) + 1) * p ^ (n + 2))
          - ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 ≤ ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by positivity
    linarith

/-- the summand of (19) -/
noncomputable def term (p η : ℝ) (i : ℕ) : ℝ :=
  Real.log (1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))) /
    (((i : ℝ) + 1) * ((i : ℝ) + 2))

lemma summable_w : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  have h2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma arg_bounds (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (i : ℕ) :
    1 - η ≤ 1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) ∧
    1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) ≤ 1 := by
  have h0 := b_nonneg p hp0 hp1 i
  have h1 := b_le_one p hp0 i
  constructor
  · nlinarith
  · nlinarith

lemma term_bound (p η e : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hηe : η ≤ e)
    (he1 : e < 1) (i : ℕ) :
    ‖term p η i‖ ≤ (-Real.log (1 - e)) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  obtain ⟨hlo, hhi⟩ := arg_bounds p η hp0 hp1 hη0 i
  have hpos : 0 < 1 - e := by linarith
  set x := 1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))
  have hx0 : 0 < x := by linarith
  have hlogle : Real.log x ≤ 0 := Real.log_nonpos hx0.le hhi
  have hloglo : Real.log (1 - e) ≤ Real.log x := Real.log_le_log hpos (by linarith)
  have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  unfold term
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonpos hlogle, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma summable_term (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    Summable (term p η) :=
  Summable.of_norm_bounded (summable_w.mul_left _)
    (fun i => term_bound p η η hp0 hp1 hη0 le_rfl hη1 i)

lemma term_nonpos (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hη1 : η < 1) (i : ℕ) :
    term p η i ≤ 0 := by
  obtain ⟨hlo, hhi⟩ := arg_bounds p η hp0 hp1 hη0 i
  unfold term
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  exact Real.log_nonpos (by linarith) hhi

lemma tsum_anti (p η η' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η) (hηη' : η ≤ η')
    (hη'1 : η' < 1) : ∑' i, term p η' i ≤ ∑' i, term p η i := by
  apply Summable.tsum_le_tsum _ (summable_term p η' hp0 hp1 (by linarith) hη'1)
    (summable_term p η hp0 hp1 hη0 (by linarith))
  intro i
  unfold term
  have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  apply div_le_div_of_nonneg_right _ hd.le
  obtain ⟨hlo, -⟩ := arg_bounds p η' hp0 hp1 (by linarith) i
  have h1 := b_le_one p hp0 i
  apply Real.log_le_log (by linarith)
  nlinarith

/-- `G p η = RHS(19) - LHS(19)`. -/
noncomputable def G (p η : ℝ) : ℝ := ∑' i, term p η i - (Real.log p + η * (1 - p) ^ 2 / p)

lemma G_strictAnti (p η η' : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hη0 : 0 ≤ η) (hηη' : η < η')
    (hη'1 : η' < 1) : G p η' < G p η := by
  have h1 := tsum_anti p η η' hp0.le hp1.le hη0 hηη'.le hη'1
  have h2 : η * (1 - p) ^ 2 / p < η' * (1 - p) ^ 2 / p := by
    apply div_lt_div_of_pos_right _ hp0
    have : 0 < (1 - p) ^ 2 := by have : 0 < 1 - p := by linarith
                                 positivity
    nlinarith
  unfold G; linarith

lemma isAlphaTilde_iff (p a : ℝ) :
    SampleDrivenOS.Limit.IsAlphaTilde p a ↔ 0 < a ∧ a < 1 ∧ G p a = 0 := by
  unfold SampleDrivenOS.Limit.IsAlphaTilde G term
  constructor
  · rintro ⟨h0, h1, h⟩; exact ⟨h0, h1, by rw [← h]; ring⟩
  · rintro ⟨h0, h1, h⟩; exact ⟨h0, h1, by linarith⟩

lemma G_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 < G p 0 := by
  unfold G term
  simp only [sub_zero, zero_mul, add_zero, Real.log_one, zero_div, tsum_zero, zero_sub]
  have := Real.log_neg hp0 hp1
  simp; linarith

lemma G_contOn_eta (p e : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (he1 : e < 1) :
    ContinuousOn (fun η => G p η) (Set.Icc 0 e) := by
  unfold G
  apply ContinuousOn.sub
  · apply continuousOn_tsum (u := fun i : ℕ => (-Real.log (1 - e)) *
        (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) _ (summable_w.mul_left _)
    · intro i η hη
      exact term_bound p η e hp0.le hp1.le hη.1 hη.2 he1 i
    · intro i
      unfold term
      apply ContinuousOn.div_const
      apply ContinuousOn.log (by fun_prop)
      intro η hη
      obtain ⟨hlo, -⟩ := arg_bounds p η hp0.le hp1.le hη.1 i
      have : 0 < 1 - η := by linarith [hη.2]
      exact (lt_of_lt_of_le this hlo).ne'
  · fun_prop

lemma G_contAt_p (η p0 : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ContinuousAt (fun p => G p η) p0 := by
  unfold G
  apply ContinuousAt.sub
  · have hc : ContinuousOn (fun p => ∑' i, term p η i) (Set.Ioo 0 1) := by
      apply continuousOn_tsum (u := fun i : ℕ => (-Real.log (1 - η)) *
          (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) _ (summable_w.mul_left _)
      · intro i p hp
        exact term_bound p η η hp.1.le hp.2.le hη0 le_rfl hη1 i
      · intro i
        unfold term
        apply ContinuousOn.div_const
        apply ContinuousOn.log (by fun_prop)
        intro p hp
        obtain ⟨hlo, -⟩ := arg_bounds p η hp.1.le hp.2.le hη0 i
        have : 0 < 1 - η := by linarith
        exact (lt_of_lt_of_le this hlo).ne'
    exact hc.continuousAt (Ioo_mem_nhds hp0 hp1)
  · apply ContinuousAt.add (Real.continuousAt_log hp0.ne')
    apply ContinuousAt.div (by fun_prop) continuousAt_id hp0.ne'

/-- some `α' < 1` with `G p α' < 0` -/
lemma exists_G_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : ∃ e, 0 < e ∧ e < 1 ∧ G p e < 0 := by
  -- c = ln p + 1 - p < 0
  set c := Real.log p + 1 - p with hc
  have hcneg : c < 0 := by
    have := Real.log_lt_sub_one_of_pos hp0 hp1.ne
    linarith
  -- bound on the α = 1 terms
  have hb : ∀ i : ℕ, Real.log (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)) /
      (((i : ℝ) + 1) * ((i : ℝ) + 2)) ≤ c * (1 / ((i : ℝ) + 2)) := by
    intro i
    have hfac : ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) =
        p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by ring
    have h1 : 0 < 1 + ((i : ℝ) + 1) * (1 - p) := by
      have : 0 ≤ ((i : ℝ) + 1) * (1 - p) := mul_nonneg (by positivity) (by linarith)
      linarith
    rw [hfac, Real.log_mul (pow_pos hp0 _).ne' h1.ne', Real.log_pow]
    have h2 : Real.log (1 + ((i : ℝ) + 1) * (1 - p)) ≤ ((i : ℝ) + 1) * (1 - p) := by
      have := Real.log_le_sub_one_of_pos h1; linarith
    have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    rw [div_le_iff₀ hd]
    have : c * (1 / ((i : ℝ) + 2)) * (((i : ℝ) + 1) * ((i : ℝ) + 2)) = c * ((i : ℝ) + 1) := by
      field_simp
    rw [this, hc]
    push_cast
    nlinarith
  -- harmonic divergence: find M with c * Σ_{i<M} 1/(i+2) < ln p - 1
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨M, hM⟩ := (hH.eventually_gt_atTop ((Real.log p - 1) / c + 1)).exists
  set S : ℝ → ℝ := fun η => ∑ i ∈ Finset.range M, term p η i
  have hS1 : S 1 < Real.log p - 1 := by
    have hle : S 1 ≤ c * ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have := hb i
      unfold term; simpa using this
    have hsum : ∑ i ∈ Finset.range (M + 1), (1 / ((i : ℝ) + 1)) =
        ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 2)) + 1 := by
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf
      · simp
    have hM' : (Real.log p - 1) / c < ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 2)) := by
      have : ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 1)) ≤
          ∑ i ∈ Finset.range (M + 1), (1 / ((i : ℝ) + 1)) := by
        rw [Finset.sum_range_succ]; have : (0:ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
        linarith
      linarith
    have : c * ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 2)) < Real.log p - 1 := by
      have := (div_lt_iff_of_neg hcneg).1 hM'
      linarith
    linarith
  -- continuity of S at 1
  have hScont : ContinuousAt S 1 := by
    show Tendsto (fun η => ∑ i ∈ Finset.range M, term p η i) (𝓝 1)
      (𝓝 (∑ i ∈ Finset.range M, term p 1 i))
    apply tendsto_finset_sum
    intro i _
    apply ContinuousAt.tendsto
    unfold term
    apply ContinuousAt.div_const
    apply ContinuousAt.log (by fun_prop)
    have := b_nonneg p hp0.le hp1.le i
    have hfac : ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2) =
        p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by ring
    have h1 : 0 < 1 + ((i : ℝ) + 1) * (1 - p) := by
      have : 0 ≤ ((i : ℝ) + 1) * (1 - p) := mul_nonneg (by positivity) (by linarith)
      linarith
    simp only [sub_self, one_mul, zero_add]
    rw [hfac]; exact (mul_pos (pow_pos hp0 _) h1).ne'
  have hev : ∀ᶠ η in 𝓝[<] (1:ℝ), S η < Real.log p - 1 ∧ η ∈ Set.Ioo (0:ℝ) 1 := by
    refine Filter.Eventually.and ?_ (Ioo_mem_nhdsLT (by norm_num))
    exact (hScont.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hS1)
  obtain ⟨e, he, he01⟩ := hev.exists
  refine ⟨e, he01.1, he01.2, ?_⟩
  -- tsum ≤ partial sum since all terms are nonpositive
  have hsumm := summable_term p e hp0.le hp1.le he01.1.le he01.2
  have htle : ∑' i, term p e i ≤ S e := by
    have h := (hsumm.neg).sum_le_tsum (Finset.range M)
      (fun i _ => by have := term_nonpos p e hp0.le hp1.le he01.1.le he01.2 i; linarith)
    rw [tsum_neg, Finset.sum_neg_distrib] at h
    show ∑' i, term p e i ≤ ∑ i ∈ Finset.range M, term p e i
    linarith
  have hD : Real.log p ≤ Real.log p + e * (1 - p) ^ 2 / p := by
    have : 0 ≤ e * (1 - p) ^ 2 / p := by have := he01.1.le; positivity
    linarith
  unfold G; linarith

end Lemma7Aux

open Lemma7Aux in
theorem solution :
    (∀ p ∈ Set.Ioo (0:ℝ) 1, ∃! a : ℝ, SampleDrivenOS.Limit.IsAlphaTilde p a) ∧
      ∀ aT : ℝ → ℝ, (∀ p ∈ Set.Ioo (0:ℝ) 1, SampleDrivenOS.Limit.IsAlphaTilde p (aT p)) →
        ContinuousOn aT (Set.Ioo 0 1) := by
  refine ⟨fun p hp => ?_, fun aT haT => ?_⟩
  · obtain ⟨e, he0, he1, hGe⟩ := exists_G_neg p hp.1 hp.2
    have hG0 := G_zero p hp.1 hp.2
    obtain ⟨a, ha, hGa⟩ := intermediate_value_Icc' he0.le (G_contOn_eta p e hp.1 hp.2 he1)
      ⟨hGe.le, hG0.le⟩
    have ha0 : 0 < a := by
      rcases ha.1.eq_or_lt with h | h
      · subst h; simp at hGa; linarith
      · exact h
    have ha1 : a < 1 := lt_of_le_of_lt ha.2 he1
    refine ⟨a, (isAlphaTilde_iff p a).2 ⟨ha0, ha1, hGa⟩, fun b hb => ?_⟩
    obtain ⟨hb0, hb1, hGb⟩ := (isAlphaTilde_iff p b).1 hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := G_strictAnti p b a hp.1 hp.2 hb0.le h ha1; linarith
    · have := G_strictAnti p a b hp.1 hp.2 ha0.le h hb1; linarith
  · intro p0 hp0
    apply ContinuousAt.continuousWithinAt
    obtain ⟨a00, a01, hG0⟩ := (isAlphaTilde_iff p0 (aT p0)).1 (haT p0 hp0)
    have hev : ∀ᶠ p in 𝓝 p0, p ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhds hp0.1 hp0.2
    show Tendsto aT (𝓝 p0) (𝓝 (aT p0))
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · set η := max a (aT p0 / 2)
      have hη0 : 0 < η := lt_max_of_lt_right (by linarith)
      have hηa : η < aT p0 := max_lt ha (by linarith)
      have hpos : 0 < G p0 η := by
        have := G_strictAnti p0 η (aT p0) hp0.1 hp0.2 hη0.le hηa a01; linarith
      have hc := G_contAt_p η p0 hη0.le (by linarith) hp0.1 hp0.2
      filter_upwards [hev, hc.eventually (lt_mem_nhds hpos)] with p hp hGp
      obtain ⟨b0, b1, hGb⟩ := (isAlphaTilde_iff p (aT p)).1 (haT p hp)
      by_contra hcon
      push Not at hcon
      have h1 : aT p ≤ η := le_trans hcon (le_max_left _ _)
      rcases h1.eq_or_lt with h | h
      · rw [h] at hGb; linarith
      · have := G_strictAnti p (aT p) η hp.1 hp.2 b0.le h (by linarith); linarith
    · set η := min b ((aT p0 + 1) / 2)
      have hηb : aT p0 < η := lt_min hb (by linarith)
      have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hneg : G p0 η < 0 := by
        have := G_strictAnti p0 (aT p0) η hp0.1 hp0.2 a00.le hηb hη1; linarith
      have hc := G_contAt_p η p0 (by linarith) hη1 hp0.1 hp0.2
      filter_upwards [hev, hc.eventually (gt_mem_nhds hneg)] with p hp hGp
      obtain ⟨b0, b1, hGb⟩ := (isAlphaTilde_iff p (aT p)).1 (haT p hp)
      by_contra hcon
      push Not at hcon
      have h1 : η ≤ aT p := le_trans (min_le_left _ _) hcon
      rcases h1.eq_or_lt with h | h
      · rw [← h] at hGb; linarith
      · have := G_strictAnti p η (aT p) hp.1 hp.2 (by linarith) h b1; linarith
