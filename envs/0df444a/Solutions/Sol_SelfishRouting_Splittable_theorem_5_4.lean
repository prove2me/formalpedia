-- Prove2me | solution 1 for SelfishRouting.Splittable.theorem_5_4
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:04:36.294631+00:00
-- url     : https://prove2.me/submissions/98eac337-1c85-45aa-84b7-8620437eeb07

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Splittable_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

set_option autoImplicit false

namespace FCex4fcce07a

open KellyStochasticNetworks SelfishRouting.Splittable

/-- Edges: `0` (shared, flat at `1` up to load `1`, then slope `36`), `1` (constant `1`),
`2` (constant `10`).  Routes: `0` = agent 0 on edge 0, `1` = agent 0 on edge 1,
`2` = agent 1 on edge 0, `3` = agent 1 on edge 2. -/
def A0 : Fin 3 → Fin 4 → ℝ := ![![1, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]

def s0 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

noncomputable def rate0 : Fin 2 → ℝ := ![1, 1 / 2]

noncomputable def lat0 : Fin 3 → ℝ → ℝ :=
  ![fun t => max 1 (36 * t - 35), fun _ => 1, fun _ => 10]

noncomputable def x0 : Fin 4 → ℝ := ![3 / 4, 1 / 4, 1 / 4, 1 / 4]

noncomputable def y0 : Fin 4 → ℝ := ![0, 2, 1, 0]

lemma x0_0 : x0 0 = 3 / 4 := rfl
lemma x0_1 : x0 1 = 1 / 4 := rfl
lemma x0_2 : x0 2 = 1 / 4 := rfl
lemma x0_3 : x0 3 = 1 / 4 := rfl
lemma y0_0 : y0 0 = 0 := rfl
lemma y0_1 : y0 1 = 2 := rfl
lemma y0_2 : y0 2 = 1 := rfl
lemma y0_3 : y0 3 = 0 := rfl

lemma hA : ∀ j r, A0 j r = 0 ∨ A0 j r = 1 := by
  intro j r
  fin_cases j <;> fin_cases r <;> simp [A0]

lemma hrate : ∀ i, 0 < rate0 i := by
  intro i
  fin_cases i <;> norm_num [rate0]

lemma hnn : ∀ j t, 0 ≤ t → 0 ≤ lat0 j t := by
  intro j t _
  fin_cases j <;> simp [lat0]

lemma hmono : ∀ j, MonotoneOn (lat0 j) (Set.Ici 0) := by
  intro j
  fin_cases j
  · intro a _ b _ hab
    simp only [lat0, Fin.zero_eta, Matrix.cons_val_zero]
    exact max_le_max le_rfl (by linarith)
  · simpa [lat0] using (monotoneOn_const : MonotoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici 0))
  · simpa [lat0] using (monotoneOn_const : MonotoneOn (fun _ : ℝ => (10 : ℝ)) (Set.Ici 0))

lemma hcont : ∀ j, ContinuousOn (lat0 j) (Set.Ici 0) := by
  intro j
  fin_cases j
  · simp only [lat0, Fin.zero_eta, Matrix.cons_val_zero]
    exact (continuous_const.max (by fun_prop)).continuousOn
  · simpa [lat0] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici 0))
  · simpa [lat0] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (10 : ℝ)) (Set.Ici 0))

lemma conv_lin (c : ℝ) : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t * c) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro u _ v _ a b _ _ _
  simp only [smul_eq_mul]
  nlinarith

lemma conv_kink : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t * max 1 (36 * t - 35)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro u hu v hv a b ha hb hab
  simp only [smul_eq_mul, Set.mem_Ici] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hw : 0 ≤ a * u + (1 - a) * v := by positivity
  have key : a * u ^ 2 + (1 - a) * v ^ 2 - (a * u + (1 - a) * v) ^ 2
      = a * (1 - a) * (u - v) ^ 2 := by ring
  have hab2 : 0 ≤ a * (1 - a) * (u - v) ^ 2 := by positivity
  have hu1 : u ≤ u * max 1 (36 * u - 35) := le_mul_of_one_le_right hu (le_max_left _ _)
  have hv1 : v ≤ v * max 1 (36 * v - 35) := le_mul_of_one_le_right hv (le_max_left _ _)
  have hu2 : u * (36 * u - 35) ≤ u * max 1 (36 * u - 35) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hu
  have hv2 : v * (36 * v - 35) ≤ v * max 1 (36 * v - 35) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hv
  have ha1 := mul_le_mul_of_nonneg_left hu1 ha
  have hb1 := mul_le_mul_of_nonneg_left hv1 hb
  have ha2 := mul_le_mul_of_nonneg_left hu2 ha
  have hb2 := mul_le_mul_of_nonneg_left hv2 hb
  rcases le_total (36 * (a * u + (1 - a) * v) - 35) 1 with h | h
  · rw [max_eq_left h]
    nlinarith
  · rw [max_eq_right h]
    nlinarith

lemma hconv : ∀ j, ConvexOn ℝ (Set.Ici 0) (fun t => t * lat0 j t) := by
  intro j
  fin_cases j
  · simpa [lat0] using conv_kink
  · simpa [lat0] using conv_lin 1
  · simpa [lat0] using conv_lin 10

lemma fsum0 (z : Fin 4 → ℝ) :
    (∑ r ∈ Finset.univ.filter (fun r => s0 r = 0), z r) = z 0 + z 1 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_four, s0]

lemma fsum1 (z : Fin 4 → ℝ) :
    (∑ r ∈ Finset.univ.filter (fun r => s0 r = 1), z r) = z 2 + z 3 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_four, s0]

lemma agentCost_0 (z : Fin 4 → ℝ) :
    agentCost A0 s0 lat0 z 0 = max 1 (36 * (z 0 + z 2) - 35) * z 0 + z 1 := by
  unfold agentCost
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_four, Fin.sum_univ_three, s0, A0, lat0,
    SelfishRouting.Bicriteria.pathLatency, linkFlow]

lemma agentCost_1 (z : Fin 4 → ℝ) :
    agentCost A0 s0 lat0 z 1 = max 1 (36 * (z 0 + z 2) - 35) * z 2 + 10 * z 3 := by
  unfold agentCost
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_four, Fin.sum_univ_three, s0, A0, lat0,
    SelfishRouting.Bicriteria.pathLatency, linkFlow]

lemma cost_eq (z : Fin 4 → ℝ) :
    SelfishRouting.Bicriteria.cost A0 lat0 z
      = max 1 (36 * (z 0 + z 2) - 35) * z 0 + z 1
        + (max 1 (36 * (z 0 + z 2) - 35) * z 2 + 10 * z 3) := by
  simp [SelfishRouting.Bicriteria.cost, Fin.sum_univ_four, Fin.sum_univ_three, A0, lat0,
    SelfishRouting.Bicriteria.pathLatency, linkFlow]
  ring

lemma x0_feas : x0 ∈ wardropFeasible s0 rate0 := by
  refine ⟨?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [x0]
  · intro σ
    fin_cases σ
    · rw [Fin.zero_eta, fsum0]; norm_num [x0_0, x0_1, x0_2, x0_3, rate0]
    · rw [Fin.mk_one, fsum1]; norm_num [x0_0, x0_1, x0_2, x0_3, rate0]

lemma y0_feas : y0 ∈ wardropFeasible s0 (fun i => 2 * rate0 i) := by
  refine ⟨?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [y0]
  · intro σ
    fin_cases σ
    · rw [Fin.zero_eta, fsum0]; norm_num [y0_0, y0_1, y0_2, y0_3, rate0]
    · rw [Fin.mk_one, fsum1]; norm_num [y0_0, y0_1, y0_2, y0_3, rate0]

lemma x0_nash : IsSplittableNash A0 s0 lat0 rate0 x0 := by
  refine ⟨x0_feas, ?_⟩
  intro i y hy hyo
  obtain ⟨hnn, hsum⟩ := hy
  fin_cases i
  · -- agent 0: its cost is at least its rate, since every latency is at least 1
    have h2 : y 2 = x0 2 := hyo 2 (by decide)
    have hs := hsum 0
    rw [fsum0] at hs
    simp only [Fin.zero_eta]
    rw [agentCost_0, agentCost_0]
    have hm : y 0 ≤ max 1 (36 * (y 0 + y 2) - 35) * y 0 :=
      le_mul_of_one_le_left (hnn 0) (le_max_left _ _)
    rw [x0_2] at h2
    rw [h2] at hm ⊢
    norm_num [x0_0, x0_1, x0_2, x0_3, rate0] at hs hm ⊢
    linarith
  · -- agent 1: `36 (y₂ - 1/4)² ≥ 0`
    have h0 : y 0 = x0 0 := hyo 0 (by decide)
    have hs := hsum 1
    rw [fsum1] at hs
    simp only [Fin.mk_one]
    rw [agentCost_1, agentCost_1]
    have hm : (36 * (y 0 + y 2) - 35) * y 2 ≤ max 1 (36 * (y 0 + y 2) - 35) * y 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (hnn 2)
    rw [x0_0] at h0
    rw [h0] at hm ⊢
    norm_num [x0_0, x0_1, x0_2, x0_3, rate0] at hs hm ⊢
    nlinarith [sq_nonneg (y 2 - 1 / 4)]

lemma cost_x0 : SelfishRouting.Bicriteria.cost A0 lat0 x0 = 15 / 4 := by
  rw [cost_eq]; norm_num [x0_0, x0_1, x0_2, x0_3]

lemma cost_y0 : SelfishRouting.Bicriteria.cost A0 lat0 y0 = 3 := by
  rw [cost_eq]; norm_num [y0_0, y0_1, y0_2, y0_3]

end FCex4fcce07a

open KellyStochasticNetworks SelfishRouting.Splittable in
theorem solution : ¬ (∀ {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (hconv : ∀ j, ConvexOn ℝ (Set.Ici 0) (fun t => t * ℓ j t))
    (x : Fin R → ℝ) (hx : IsSplittableNash A s ℓ rate x)
    (y : Fin R → ℝ) (hy : y ∈ wardropFeasible s (fun i => 2 * rate i)),
    SelfishRouting.Bicriteria.cost A ℓ x ≤ SelfishRouting.Bicriteria.cost A ℓ y) := by
  intro h
  have h1 := @h 3 4 2 FCex4fcce07a.A0 FCex4fcce07a.hA FCex4fcce07a.s0 FCex4fcce07a.rate0
    FCex4fcce07a.hrate FCex4fcce07a.lat0 FCex4fcce07a.hnn FCex4fcce07a.hmono
    FCex4fcce07a.hcont FCex4fcce07a.hconv FCex4fcce07a.x0 FCex4fcce07a.x0_nash
    FCex4fcce07a.y0 FCex4fcce07a.y0_feas
  rw [FCex4fcce07a.cost_x0, FCex4fcce07a.cost_y0] at h1
  norm_num at h1
