-- Prove2me | solution 1 for ReinfRegGames.TimeAvg.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T04:41:14.081896+00:00
-- url     : https://prove2.me/submissions/93463024-1641-46b4-84e8-fe75d6dde02e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_TimeAvg_TimeAverage

section

namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology
open ReinfRegGames.Extinction
end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set
open ReinfRegGames.Extinction
variable {B : Type*} [Fintype B]

theorem choice_gap {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    {y x z : B → ℝ} (hx : IsChoice h y x) (hz : z ∈ stdSimplex ℝ B) :
    K / 4 * sqDist x z ≤ (y ⬝ᵥ x - h x) - (y ⬝ᵥ z - h z) := by
  have hm := (convex_stdSimplex ℝ B) hx.1 hz
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  have hc := hp.2.2.2 x hx.1 z hz (1/2) (by constructor <;> norm_num)
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at hc
  have ho := hx.2 _ hm
  have he : y ⬝ᵥ ((1/2:ℝ) • x + (1/2:ℝ) • z) =
      (y ⬝ᵥ x)/2 + (y ⬝ᵥ z)/2 := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at ho
  nlinarith

theorem choice_strong_monotone {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    {y z x w : B → ℝ} (hx : IsChoice h y x) (hw : IsChoice h z w) :
    K / 2 * sqDist x w ≤ (y-z) ⬝ᵥ (x-w) := by
  have h1 := choice_gap hp hx hw.1
  have h2 := choice_gap hp hw hx.1
  have hs : sqDist w x = sqDist x w := by
    unfold sqDist
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs] at h2
  have he : (y-z) ⬝ᵥ (x-w) = (y ⬝ᵥ x - y ⬝ᵥ w) + (z ⬝ᵥ w - z ⬝ᵥ x) := by
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  linarith
end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set
open ReinfRegGames.Extinction
variable {B : Type*} [Fintype B]

theorem norm_sq_le_sqDist (x w : B → ℝ) : ‖x-w‖^2 ≤ sqDist x w := by
  classical
  have hs : 0 ≤ sqDist x w := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn : ‖x-w‖ ≤ Real.sqrt (sqDist x w) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hs).2
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs, sqDist] using
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j-w j)) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt hs, norm_nonneg (x-w), Real.sqrt_nonneg (sqDist x w)]

theorem dotProduct_le_sup_norm (a b : B → ℝ) :
    a ⬝ᵥ b ≤ (Fintype.card B : ℝ) * ‖a‖ * ‖b‖ := by
  calc
    a ⬝ᵥ b ≤ ∑ i, ‖a‖ * ‖b‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        a i*b i ≤ |a i*b i| := le_abs_self _
        _ = ‖a i‖ * ‖b i‖ := by simp [abs_mul]
        _ ≤ ‖a‖ * ‖b‖ := mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i)
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem choice_lipschitz {h : (B → ℝ) → ℝ} {K : ℝ} (hp : IsPenalty h K)
    {y z x w : B → ℝ} (hx : IsChoice h y x) (hw : IsChoice h z w) :
    ‖x-w‖ ≤ (2*(Fintype.card B : ℝ)/K)*‖y-z‖ := by
  have hk := hp.2.2.1
  have h1 := choice_strong_monotone hp hx hw
  have h2 := norm_sq_le_sqDist x w
  have h3 := dotProduct_le_sup_norm (y-z) (x-w)
  have hn := norm_nonneg (x-w)
  have hy := norm_nonneg (y-z)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hk).2
  by_cases hz : ‖x-w‖=0
  · rw [hz, zero_mul]; positivity
  · have hpw : 0 < ‖x-w‖ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith [mul_nonneg (show 0 ≤ K/2 by positivity) (sub_nonneg.mpr h2)]
end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology
open ReinfRegGames.Extinction
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
variable {u : Fin 2 → (∀ k, A k) → ℝ} {h : ∀ k, (A k → ℝ) → ℝ}
variable {y x : ℝ → ∀ k, A k → ℝ}

theorem orbit_score_continuous (ho : IsRLOrbit u h y x) : ContinuousOn y (Ici 0) := by
  intro t ht
  apply continuousWithinAt_pi.2
  intro k
  apply continuousWithinAt_pi.2
  intro a
  exact ((ho t ht k).2 a).continuousWithinAt

theorem orbit_choice_continuous {K : Fin 2 → ℝ} (hp : ∀ k, IsPenalty (h k) (K k))
    (ho : IsRLOrbit u h y x) : ContinuousOn x (Ici 0) := by
  intro t ht
  apply continuousWithinAt_pi.2
  intro k
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hy : Tendsto (fun s => ‖y s k-y t k‖) (𝓝[Ici 0] t) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      ((continuousWithinAt_pi.1 (orbit_score_continuous ho t ht)) k)
  have hb := hy.const_mul (2*(Fintype.card (A k):ℝ)/K k)
  simp only [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hb
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact choice_lipschitz (hp k) (ho s hs k).1 (ho t ht k).1
end ReinfRegGames.TimeAvg.Fresh
end

section
open scoped BigOperators
open ReinfRegGames.Extinction
namespace ReinfRegGames.TimeAvg.Fresh
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

def joint (a : A 0) (b : A 1) : ∀ k, A k := (piFinTwoEquiv A).symm (a, b)

omit [∀ k, DecidableEq (A k)] in
theorem expected_expansion (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (k : Fin 2) :
    AGT.expectedPayoff u z k = ∑ a : A 0, ∑ b : A 1,
      z 0 a * z 1 b * u k (joint a b) := by
  classical
  unfold AGT.expectedPayoff AGT.profileProb
  rw [← (piFinTwoEquiv A).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.prod_univ_two]
  rfl

theorem payoff_zero (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (a : A 0) :
    payoffVec u z 0 a = ∑ b : A 1, z 1 b * u 0 (joint a b) := by
  classical
  unfold payoffVec
  rw [expected_expansion]
  simp [Pi.single_apply, ite_mul]

theorem payoff_one (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (b : A 1) :
    payoffVec u z 1 b = ∑ a : A 0, z 0 a * u 1 (joint a b) := by
  classical
  unfold payoffVec
  rw [expected_expansion]
  simp [Pi.single_apply, mul_ite, ite_mul]

theorem continuous_payoff (u : Fin 2 → (∀ k, A k) → ℝ)
    (k : Fin 2) (a : A k) : Continuous (fun z : ∀ k, A k → ℝ => payoffVec u z k a) := by
  fin_cases k
  · change Continuous (fun z => payoffVec u z 0 a)
    simp_rw [payoff_zero]
    fun_prop
  · change Continuous (fun z => payoffVec u z 1 a)
    simp_rw [payoff_one]
    fun_prop

end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology MeasureTheory
open ReinfRegGames.Extinction
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
variable {u : Fin 2 → (∀ k, A k) → ℝ} {h : ∀ k, (A k → ℝ) → ℝ}
variable {y x : ℝ → ∀ k, A k → ℝ}

omit [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)] in
theorem coordinate_integrable (hx : ContinuousOn x (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    (k : Fin 2) (a : A k) : IntervalIntegrable (fun s => x s k a) volume 0 t := by
  apply ContinuousOn.intervalIntegrable_of_Icc ht
  exact ((continuous_apply a).comp_continuousOn ((continuous_apply k).comp_continuousOn hx)).mono
    (fun _ hs => hs.1)

theorem payoff_integrable (hx : ContinuousOn x (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    (k : Fin 2) (a : A k) : IntervalIntegrable (fun s => payoffVec u (x s) k a) volume 0 t := by
  apply ContinuousOn.intervalIntegrable_of_Icc ht
  exact ((continuous_payoff u k a).comp_continuousOn hx).mono (fun _ hs => hs.1)

theorem score_integral {K : Fin 2 → ℝ} (hp : ∀ k, IsPenalty (h k) (K k))
    (ho : IsRLOrbit u h y x) {t : ℝ} (ht : 0 ≤ t) (k : Fin 2) (a : A k) :
    (∫ s in 0..t, payoffVec u (x s) k a) = y t k a-y 0 k a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
  · exact ((continuous_apply a).comp_continuousOn
      ((continuous_apply k).comp_continuousOn (orbit_score_continuous ho))).mono (fun _ hs => hs.1)
  · intro s hs
    have hd := (ho s hs.1.le k).2 a
    simp only [one_mul] at hd
    exact hd.mono (fun v hv => le_trans hs.1.le hv.le)
  · exact payoff_integrable (orbit_choice_continuous hp ho) ht k a

theorem payoff_average (hx : ContinuousOn x (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    (k : Fin 2) (a : A k) :
    payoffVec u (timeAvg x t) k a = t⁻¹ * ∫ s in 0..t, payoffVec u (x s) k a := by
  classical
  fin_cases k
  · change payoffVec u (timeAvg x t) 0 a = t⁻¹ * ∫ s in 0..t, payoffVec u (x s) 0 a
    simp_rw [payoff_zero]
    rw [intervalIntegral.integral_finsetSum (fun b _ =>
      (coordinate_integrable hx ht 1 b).mul_const _)]
    simp only [timeAvg, intervalIntegral.integral_mul_const, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · change payoffVec u (timeAvg x t) 1 a = t⁻¹ * ∫ s in 0..t, payoffVec u (x s) 1 a
    simp_rw [payoff_one]
    rw [intervalIntegral.integral_finsetSum (fun b _ =>
      (coordinate_integrable hx ht 0 b).mul_const _)]
    simp only [timeAvg, intervalIntegral.integral_mul_const, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology MeasureTheory
open ReinfRegGames.Extinction
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
variable {u : Fin 2 → (∀ k, A k) → ℝ} {h : ∀ k, (A k → ℝ) → ℝ}
variable {y x : ℝ → ∀ k, A k → ℝ}

theorem average_profile {K : Fin 2 → ℝ} (hp : ∀ k, IsPenalty (h k) (K k))
    (ho : IsRLOrbit u h y x) {t : ℝ} (ht : 0 < t) : AGT.IsMixedProfile (timeAvg x t) := by
  intro k
  constructor
  · intro a
    apply mul_nonneg (inv_nonneg.mpr ht.le)
    apply intervalIntegral.integral_nonneg ht.le
    intro s hs
    exact (ho s hs.1 k).1.1.1 a
  · change ∑ a, t⁻¹ * (∫ s in 0..t, x s k a) = 1
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum
      (fun a _ => coordinate_integrable (orbit_choice_continuous hp ho) ht.le k a)]
    have he : (∫ s in 0..t, ∑ a, x s k a) = ∫ _s in 0..t, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact (ho s ((uIcc_of_le ht.le) ▸ hs).1 k).1.1.2
    rw [he]
    simp [ht.ne']
end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh

theorem lottery_nonempty {B : Type*} [Fintype B] {p : B → ℝ}
    (hp : AGT.IsLottery p) : Nonempty B := by
  cases isEmpty_or_nonempty B with
  | inl h =>
    let := h
    have hs := hp.2
    simp at hs
  | inr h => exact h

theorem compact_profiles {A : Fin 2 → Type*} [∀ k, Fintype (A k)] :
    IsCompact {z : ∀ k, A k → ℝ | AGT.IsMixedProfile z} := by
  exact isCompact_pi_infinite (fun k => isCompact_stdSimplex ℝ (A k))

theorem orbit_action_nonempty {A : Fin 2 → Type*} [∀ k, Fintype (A k)]
    [∀ k, DecidableEq (A k)] {u : Fin 2 → (∀ k, A k) → ℝ}
    {h : ∀ k, (A k → ℝ) → ℝ} {y x : ℝ → ∀ k, A k → ℝ}
    (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x) (k : Fin 2) : Nonempty (A k) :=
  lottery_nonempty (horb 0 (by norm_num) k).1.1

end ReinfRegGames.TimeAvg.Fresh
end

section
open scoped BigOperators
open ReinfRegGames.Extinction
namespace ReinfRegGames.TimeAvg.Fresh
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

theorem expected_decompose (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (k : Fin 2) :
    AGT.expectedPayoff u z k = ∑ a : A k, z k a * payoffVec u z k a := by
  classical
  fin_cases k
  · change AGT.expectedPayoff u z 0 = ∑ a : A 0, z 0 a * payoffVec u z 0 a
    rw [expected_expansion]
    simp only [payoff_zero, Finset.mul_sum, mul_assoc]
  · change AGT.expectedPayoff u z 1 = ∑ a : A 1, z 1 a * payoffVec u z 1 a
    rw [expected_expansion, Finset.sum_comm]
    simp only [payoff_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem payoff_update_self (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (k : Fin 2) (τ : A k → ℝ) (a : A k) :
    payoffVec u (Function.update z k τ) k a = payoffVec u z k a := by
  classical
  fin_cases k <;> simp [payoff_zero, payoff_one]

theorem nash_of_indifference (u : Fin 2 → (∀ k, A k) → ℝ)
    (z : ∀ k, A k → ℝ) (hz : AGT.IsMixedProfile z)
    (hind : ∀ k (a b : A k), payoffVec u z k a = payoffVec u z k b) :
    AGT.IsMixedNash u z := by
  classical
  refine ⟨hz, ?_⟩
  intro k τ hτ
  obtain ⟨a⟩ := lottery_nonempty (hz k)
  rw [expected_decompose, expected_decompose]
  simp only [payoff_update_self, Function.update_self]
  have hs (p : A k → ℝ) (hp : AGT.IsLottery p) :
      (∑ b, p b * payoffVec u z k b) = payoffVec u z k a := by
    simp_rw [hind k _ a]
    rw [← Finset.sum_mul, hp.2, one_mul]
  rw [hs τ hτ, hs (z k) (hz k)]

end ReinfRegGames.TimeAvg.Fresh
end

section
open Filter Topology
open ReinfRegGames.Extinction
namespace ReinfRegGames.TimeAvg.Fresh
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

theorem nash_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    (u : Fin 2 → (∀ k, A k) → ℝ) {w : ι → ∀ k, A k → ℝ}
    {z : ∀ k, A k → ℝ} (hz : Tendsto w l (𝓝 z))
    (hprof : ∀ᶠ i in l, AGT.IsMixedProfile (w i))
    (hdiff : ∀ k (a b : A k),
      Tendsto (fun i => payoffVec u (w i) k a - payoffVec u (w i) k b) l (𝓝 0)) :
    AGT.IsMixedNash u z := by
  have hp : AGT.IsMixedProfile z := compact_profiles.isClosed.mem_of_tendsto hz hprof
  apply nash_of_indifference u z hp
  intro k a b
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((((continuous_payoff u k a).tendsto z).comp hz).sub
      (((continuous_payoff u k b).tendsto z).comp hz))
    (hdiff k a b)

end ReinfRegGames.TimeAvg.Fresh
end

section

open Filter Topology
namespace ReinfRegGames.TimeAvg.Fresh

lemma compact_cluster_infDist {X : Type*} [MetricSpace X]
    (z : ℝ → X) (K S : Set X) (hK : IsCompact K)
    (hz : ∀ᶠ t in atTop, z t ∈ K)
    (hcl : ∀ (u : ℕ → ℝ), Tendsto u atTop atTop → ∀ p ∈ K,
      Tendsto (fun n => z (u n)) atTop (𝓝 p) → p ∈ S) :
    S.Nonempty ∧ Tendsto (fun t => Metric.infDist (z t) S) atTop (𝓝 0) := by
  classical
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hz
  have cluster (u : ℕ → ℝ) (huT : ∀ n, T ≤ u n) (hu : Tendsto u atTop atTop) :
      ∃ p ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => z (u (φ n))) atTop (𝓝 p) := by
    obtain ⟨p, hp, φ, hφ, hconv⟩ := hK.tendsto_subseq (fun n => hT (u n) (huT n))
    have hpS : p ∈ S := hcl (u ∘ φ) (hu.comp hφ.tendsto_atTop) p hp hconv
    exact ⟨p, hpS, φ, hφ, hconv⟩
  constructor
  · have hu : Tendsto (fun n : ℕ => max T (n : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun n => le_max_right T (n : ℝ)) tendsto_natCast_atTop_atTop
    obtain ⟨p, hp, _⟩ := cluster (fun n : ℕ => max T (n : ℝ))
      (fun n => le_max_left T (n : ℝ)) hu
    exact ⟨p, hp⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hev : ∀ᶠ t in atTop, Metric.infDist (z t) S < ε := by
      by_contra hbad
      rw [Filter.eventually_atTop] at hbad
      push Not at hbad
      choose u hu hu_bad using (fun n : ℕ => hbad (max T (n : ℝ)))
      have htu : Tendsto u atTop atTop :=
        tendsto_atTop_mono (fun n => (le_max_right T (n : ℝ)).trans (hu n))
          tendsto_natCast_atTop_atTop
      obtain ⟨p, hp, φ, hφ, hconv⟩ := cluster u
        (fun n => (le_max_left T (n : ℝ)).trans (hu n)) htu
      have hclose : ∀ᶠ n in atTop, dist (z (u (φ n))) p < ε :=
        (Metric.tendsto_nhds.mp hconv) ε hε
      obtain ⟨n, hn⟩ := hclose.exists
      have hle := Metric.infDist_le_dist_of_mem (x := z (u (φ n))) hp
      exact (not_lt_of_ge ((hu_bad (φ n)).trans hle)) hn
    filter_upwards [hev] with t ht
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] using ht

lemma compact_constraints_infDist {X ι : Type*} [MetricSpace X]
    (z : ℝ → X) (K S : Set X) (hK : IsCompact K)
    (hz : ∀ᶠ t in atTop, z t ∈ K) (g : ι → X → ℝ)
    (hg : ∀ i, Continuous (g i))
    (hzero : ∀ i, Tendsto (fun t => g i (z t)) atTop (𝓝 0))
    (hS : ∀ p ∈ K, (∀ i, g i p = 0) → p ∈ S) :
    S.Nonempty ∧ Tendsto (fun t => Metric.infDist (z t) S) atTop (𝓝 0) := by
  apply compact_cluster_infDist z K S hK hz
  intro u hu p hp hconv
  apply hS p hp
  intro i
  exact tendsto_nhds_unique (((hg i).tendsto p).comp hconv) ((hzero i).comp hu)

end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology MeasureTheory
open ReinfRegGames.Extinction
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
variable {u : Fin 2 → (∀ k, A k) → ℝ} {h : ∀ k, (A k → ℝ) → ℝ}
variable {y x : ℝ → ∀ k, A k → ℝ}

theorem payoff_difference_eq {K : Fin 2 → ℝ} (hp : ∀ k, IsPenalty (h k) (K k))
    (ho : IsRLOrbit u h y x) {t : ℝ} (ht : 0 ≤ t) (k : Fin 2) (a b : A k) :
    payoffVec u (timeAvg x t) k a-payoffVec u (timeAvg x t) k b =
      ((y t k a-y t k b)-(y 0 k a-y 0 k b))/t := by
  rw [payoff_average (orbit_choice_continuous hp ho) ht,
    payoff_average (orbit_choice_continuous hp ho) ht, score_integral hp ho ht,
    score_integral hp ho ht]
  ring
end ReinfRegGames.TimeAvg.Fresh
end

section

open Filter Topology
namespace ReinfRegGames.TimeAvg.Fresh

lemma bounded_difference_div_tendsto (a : ℝ → ℝ) (M : ℝ)
    (ha : ∀ t, 0 ≤ t → |a t| ≤ M) :
    Tendsto (fun t : ℝ => (a t-a 0)/t) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => (2*M)/t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  apply div_le_div_of_nonneg_right _ ht0.le
  calc
    |a t-a 0| ≤ |a t|+|a 0| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a t) (-(a 0))
    _ ≤ M+M := add_le_add (ha t ht0.le) (ha 0 le_rfl)
    _ = _ := by ring

end ReinfRegGames.TimeAvg.Fresh
end

section
namespace ReinfRegGames.TimeAvg.Fresh
open Finset Set Filter Topology MeasureTheory
open ReinfRegGames.Extinction
variable {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
variable {u : Fin 2 → (∀ k, A k) → ℝ} {h : ∀ k, (A k → ℝ) → ℝ}
variable {y x : ℝ → ∀ k, A k → ℝ}

theorem payoff_difference_tendsto {K : Fin 2 → ℝ} (hp : ∀ k, IsPenalty (h k) (K k))
    (ho : IsRLOrbit u h y x)
    (hbdd : ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ k (a b : A k), |y t k a-y t k b| ≤ M)
    (k : Fin 2) (a b : A k) :
    Tendsto (fun t => payoffVec u (timeAvg x t) k a-payoffVec u (timeAvg x t) k b)
      atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := hbdd
  apply (bounded_difference_div_tendsto (fun t => y t k a-y t k b) M
    (fun t ht => hM t ht k a b)).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (payoff_difference_eq hp ho ht k a b).symm
end ReinfRegGames.TimeAvg.Fresh
end

section
open Filter Topology
namespace ReinfRegGames.TimeAvg.Fresh

theorem native_theorem_6_1 {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x)
    (hbdd : ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ k (α β : A k), |y t k α - y t k β| ≤ M) :
    {z : ∀ k, A k → ℝ | AGT.IsMixedNash u z}.Nonempty ∧
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by
  have havg : ∀ᶠ t in atTop, AGT.IsMixedProfile (timeAvg x t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact average_profile hpen horb ht
  apply compact_cluster_infDist (timeAvg x) {z | AGT.IsMixedProfile z}
    {z | AGT.IsMixedNash u z} compact_profiles havg
  intro v hv z _ hz
  apply nash_of_tendsto u hz (hv.eventually havg)
  intro k a b
  exact (payoff_difference_tendsto hpen horb hbdd k a b).comp hv

end ReinfRegGames.TimeAvg.Fresh
end

open ReinfRegGames.TimeAvg

theorem solution {A : Fin 2 → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : Fin 2 → (∀ k, A k) → ℝ)
    (h : ∀ k, (A k → ℝ) → ℝ) (K : Fin 2 → ℝ) (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : ReinfRegGames.Extinction.IsRLOrbit u h y x)
    (hbdd : ∃ M : ℝ, ∀ t, 0 ≤ t → ∀ k (α β : A k), |y t k α - y t k β| ≤ M) :
    {z : ∀ k, A k → ℝ | AGT.IsMixedNash u z}.Nonempty ∧
    Filter.Tendsto (fun t => Metric.infDist (timeAvg x t) {z | AGT.IsMixedNash u z})
      Filter.atTop (nhds 0) := by
  exact Fresh.native_theorem_6_1 u h K hpen y x horb hbdd
