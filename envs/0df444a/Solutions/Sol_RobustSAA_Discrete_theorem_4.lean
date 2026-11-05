-- Prove2me | solution 1 for RobustSAA.Discrete.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:33:16.166756+00:00
-- url     : https://prove2.me/submissions/dd60ca93-5bec-4106-9073-8b765fbf633a

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting
import Theorems.Thm_RobustSAA_Discrete_tv_weak
import Theorems.Thm_RobustSAA_Discrete_empirical_tv
import Theorems.Thm_RobustSAA_Discrete_chi_tv_bound
import Theorems.Thm_RobustSAA_Discrete_g_tv_bound

namespace RobustSAA.Discrete

open Filter MeasureTheory Topology

/-- Triangle inequality for `dTV` through the empirical vector. -/
lemma dTV_triangle {n : ℕ} (a b c : Fin n → ℝ) :
    dTV a c ≤ dTV b a + dTV b c := by
  unfold dTV
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => ?_)) (by norm_num)
  calc |a j - c j| = |(b j - c j) - (b j - a j)| := by ring_nf
    _ ≤ |b j - c j| + |b j - a j| := abs_sub _ _
    _ = |b j - a j| + |b j - c j| := add_comm _ _

lemma dTV_nonneg {n : ℕ} (a b : Fin n → ℝ) : 0 ≤ dTV a b := by
  unfold dTV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => abs_nonneg _))

/-- Generic reduction: if membership in the region forces `dTV(p̂_N, p₀) ≤ r N` with
`r N → 0`, the region map is uniformly consistent (§10.6, p. 38). -/
lemma uc_of_tv_bound {n : ℕ}
    (region : (N : ℕ) → (Fin N → Fin n) → Set (ProbabilityMeasure (Fin n)))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hb : ∀ N : ℕ, 0 < N → ∀ (s : Fin N → Fin n) (F₀ : ProbabilityMeasure (Fin n)),
      F₀ ∈ region N s → dTV (phat s) (pvec F₀) ≤ r N) :
    IsUniformlyConsistent region := by
  intro F
  filter_upwards [empirical_tv n F] with ω hω G hG
  by_contra h
  rw [not_frequently] at h
  apply hG
  rw [tv_weak]
  have hup : Tendsto (fun N => r N + dTV (phat (sample ω N)) (pvec F)) atTop (𝓝 0) := by
    simpa using hr.add hω
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall (fun N => dTV_nonneg _ _)
  · filter_upwards [h, eventually_gt_atTop 0] with N hN hNpos
    have h1 := hb N hNpos (sample ω N) (G N) (by simpa using hN)
    have h2 := dTV_triangle (pvec (G N)) (phat (sample ω N)) (pvec F)
    linarith

lemma tendsto_sqrt_Q_div (Q : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (Q / N)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => Q / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat Q
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

lemma chi_uc (n : ℕ) (Q : ℝ) : IsUniformlyConsistent (chiRegion (n := n) Q) := by
  refine uc_of_tv_bound _ (fun N => Real.sqrt (Q / N) / 2) ?_ ?_
  · simpa using (tendsto_sqrt_Q_div Q).div_const 2
  · intro N _ s F₀ hF
    have hb := chi_tv_bound F₀ s
    have hc : chiStat F₀ s ≤ ENNReal.ofReal (Real.sqrt (Q / N)) := hF
    have h3 : ENNReal.ofReal (dTV (phat s) (pvec F₀)) ≤
        ENNReal.ofReal (Real.sqrt (Q / N) / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simpa using hb.trans (ENNReal.div_le_div_right hc 2)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

lemma g_uc (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) : IsUniformlyConsistent (gRegion (n := n) Q) := by
  refine uc_of_tv_bound _ (fun N => Real.sqrt (Q / N) / 2) ?_ ?_
  · simpa using (tendsto_sqrt_Q_div Q).div_const 2
  · intro N hN s F₀ hF
    have hb := g_tv_bound hN F₀ s
    have hc : gStatSq F₀ s ≤ ((Q / N : ℝ) : EReal) := hF
    unfold gStatSq at hc
    set S : EReal := ∑ j : Fin n, gTerm F₀ s j with hS
    set t : ℝ := dTV (phat s) (pvec F₀) with ht
    have ht0 : 0 ≤ t := dTV_nonneg _ _
    -- reduce to a real `S`
    clear_value S
    clear hS
    revert hb hc
    induction S using EReal.rec with
    | bot =>
      intro hc hb
      exfalso
      have : ((t : EReal) ^ 2) ≤ ⊥ := by
        rwa [EReal.bot_div_of_pos_ne_top (a := 2) (by norm_num)
          (by simpa using EReal.natCast_ne_top 2)] at hb
      rw [← EReal.coe_pow] at this
      exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
    | top =>
      intro hc hb
      exfalso
      have h2 : (2 : EReal) * ⊤ = ⊤ := EReal.mul_top_of_pos (by norm_num)
      rw [h2] at hc
      exact EReal.coe_ne_top _ (top_le_iff.1 hc)
    | coe x =>
      intro hc hb
      have hc' : 2 * x ≤ Q / N := by
        rw [show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, ← EReal.coe_mul] at hc
        exact EReal.coe_le_coe_iff.1 hc
      have hb' : t ^ 2 ≤ x / 2 := by
        rw [← EReal.coe_pow, show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
          ← EReal.coe_div] at hb
        exact EReal.coe_le_coe_iff.1 hb
      have hsq : t ^ 2 ≤ (Real.sqrt (Q / N) / 2) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
        linarith
      exact (pow_le_pow_iff_left₀ ht0 (by positivity) (by norm_num)).1 hsq

end RobustSAA.Discrete

open RobustSAA.Discrete MeasureTheory in
theorem solution (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    IsUniformlyConsistent (chiRegion (n := n) Q) ∧
      IsUniformlyConsistent (gRegion (n := n) Q) :=
  ⟨chi_uc n Q, g_uc n Q hQ⟩
