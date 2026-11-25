-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:35.797799+00:00
-- url     : https://prove2.me/submissions/7a2568c7-5590-49a6-b1aa-b84bbb3eaf57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_norm_add_eq_left_e1f654c14de4
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_norm_two_le_ac676a0a19a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PI PI.Landherr₃
namespace PI.Landherr₃
theorem _root_.solution {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (α β γ a : K) (hα : ‖α‖ ≤ 1) (h : ‖α * a ^ 2 + β * a + γ‖ < ‖2 * α * a + β‖ ^ 2) :
    ∃ x : K, α * x ^ 2 + β * x + γ = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : K → K, ∀ x, f x = α * x ^ 2 + β * x + γ := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : K → K, ∀ x, g x = 2 * α * x + β := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℕ → K, s 0 = a ∧ ∀ n, s (n + 1) = s n - f (s n) / g (s n) :=
    ⟨fun n => Nat.rec a (fun _ b => b - f b / g b) n, rfl, fun _ => rfl⟩
  have alg : ∀ b q : K, g b * q = f b → f (b - q) = α * q ^ 2 := by
    intro b q hq
    rw [hg b, hf b] at hq
    rw [hf (b - q)]
    linear_combination (-1 : K) * hq
  have galg : ∀ b q : K, g (b - q) = g b + -(2 * α * q) := by
    intro b q
    rw [hg, hg]
    ring
  rw [← hf a, ← hg a] at h
  obtain ⟨d, hd⟩ : ∃ d, d = ‖g a‖ := ⟨_, rfl⟩
  rw [← hd] at h
  have hd0 : 0 < d := by
    have h1 : 0 < d ^ 2 := lt_of_le_of_lt (norm_nonneg _) h
    by_contra hc
    have h3 : d = 0 := le_antisymm (not_lt.1 hc) (hd ▸ norm_nonneg _)
    rw [h3] at h1
    norm_num at h1
  have hdne : d ≠ 0 := hd0.ne'
  obtain ⟨t, ht⟩ : ∃ t, t = ‖f a‖ / d ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by positivity)]; exact h
  have h2 : ‖(2 : K)‖ ≤ 1 := unitNormLoc_norm_two_le
  have inv : ∀ n, ‖g (s n)‖ = d ∧ ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [hs0, hd], ?_⟩
      rw [hs0, zero_add, pow_one, ht]
      exact le_of_eq (by field_simp)
    | succ n ih =>
      obtain ⟨hgn, hfn⟩ := ih
      have hne : g (s n) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hgn
        exact hdne hgn.symm
      have hft : ‖f (s n)‖ ≤ d ^ 2 * t := by
        refine hfn.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact pow_le_of_le_one ht0 ht1.le (Nat.succ_ne_zero n)
      have hh : ‖f (s n) / g (s n)‖ = ‖f (s n)‖ / d := by rw [norm_div, hgn]
      have hhd : ‖f (s n) / g (s n)‖ < d := by
        rw [hh, div_lt_iff₀ hd0]
        calc ‖f (s n)‖ ≤ d ^ 2 * t := hft
          _ < d ^ 2 * 1 := mul_lt_mul_of_pos_left ht1 (by positivity)
          _ = d * d := by ring
      have h2a : ‖-(2 * α * (f (s n) / g (s n)))‖ < ‖g (s n)‖ := by
        rw [norm_neg, norm_mul, norm_mul, hgn]
        calc ‖(2 : K)‖ * ‖α‖ * ‖f (s n) / g (s n)‖ ≤ 1 * 1 * ‖f (s n) / g (s n)‖ := by gcongr
          _ < d := by rw [one_mul, one_mul]; exact hhd
      have e1 : g (s n) * (f (s n) / g (s n)) = f (s n) := by field_simp
      refine ⟨?_, ?_⟩
      · rw [hs, galg, unitNormLoc_norm_add_eq_left _ _ h2a, hgn]
      · rw [hs, alg _ _ e1, norm_mul, norm_pow, hh]
        have e4 : (‖f (s n)‖ / d) ^ 2 = ‖f (s n)‖ * (‖f (s n)‖ / d ^ 2) := by field_simp
        have e5 : ‖f (s n)‖ / d ^ 2 ≤ t := by
          rw [div_le_iff₀ (by positivity)]
          linarith [hft]
        calc ‖α‖ * (‖f (s n)‖ / d) ^ 2 ≤ 1 * (‖f (s n)‖ / d) ^ 2 :=
              mul_le_mul_of_nonneg_right hα (sq_nonneg _)
          _ = ‖f (s n)‖ * (‖f (s n)‖ / d ^ 2) := by rw [one_mul, e4]
          _ ≤ ‖f (s n)‖ * t := mul_le_mul_of_nonneg_left e5 (norm_nonneg _)
          _ ≤ d ^ 2 * t ^ (n + 1) * t := mul_le_mul_of_nonneg_right hfn ht0
          _ = d ^ 2 * t ^ (n + 1 + 1) := by ring
  have hdist : ∀ n, dist (s n) (s (n + 1)) ≤ (d * t) * t ^ n := by
    intro n
    obtain ⟨hgn, hfn⟩ := inv n
    rw [dist_eq_norm, hs, sub_sub_cancel, norm_div, hgn, div_le_iff₀ hd0]
    calc ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := hfn
      _ = d * t * t ^ n * d := by ring
  have hc : CauchySeq s := cauchySeq_of_le_geometric t (d * t) ht1 hdist
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hcont : Continuous f := by
    have e : f = fun x => α * x ^ 2 + β * x + γ := funext hf
    rw [e]
    fun_prop
  have h1 : Tendsto (fun n => f (s n)) atTop (𝓝 (f L)) := (hcont.tendsto L).comp hL
  have hlim : Tendsto (fun n : ℕ => d ^ 2 * t * t ^ n) atTop (𝓝 0) := by
    have h3 := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul (d ^ 2 * t)
    rwa [mul_zero] at h3
  have h0 : Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hlim
    calc ‖f (s n)‖ ≤ d ^ 2 * t ^ (n + 1) := (inv n).2
      _ = d ^ 2 * t * t ^ n := by ring
  have hfL : f L = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, by rw [← hf]; exact hfL⟩
end PI.Landherr₃
