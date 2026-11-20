-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.hub_stability_threshold
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T15:26:06.049881+00:00
-- url     : https://prove2.me/submissions/752fe4ac-0f2a-42b7-9d48-e6246d29d1de

import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_StableMSR_Recovery_Supplement_hub_runner_up
import Theorems.Thm_StableMSR_Recovery_Supplement_hub_inflation_costs

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Supplement

private theorem cost_le_scaled_cost {n : ℕ} (d p : Point n → Point n → ℝ)
    (Q : Partition n) (u : ℝ) (hu : 0 ≤ u) (h : ∀ x y, p x y ≤ u * d x y) :
    cost p Q ≤ u * cost d Q := by
  unfold cost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  by_cases hC : C.Nonempty
  · obtain ⟨c, hc, hmin⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
    rw [radius, dif_pos hC, radius, dif_pos hC, hmin]
    refine (Finset.inf'_le (eccentricity p C) hc).trans ?_
    rw [eccentricity, dif_pos hC, eccentricity, dif_pos hC]
    exact Finset.sup'_le hC _ (fun x hx =>
      (h c x).trans (mul_le_mul_of_nonneg_left (Finset.le_sup' (d c) hx) hu))
  · simp [radius, hC]

private theorem array_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  let _ : MetricSpace (Point n) := m
  rw [← hm]
  exact dist_nonneg

private theorem optimum_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (k : ℕ) : 0 ≤ optimumValue d k := by
  unfold optimumValue
  dsimp only
  split
  · apply Finset.le_inf'
    intro Q _
    apply Finset.sum_nonneg
    intro C _
    unfold radius
    split
    · rename_i hC
      apply Finset.le_inf'
      intro c _
      unfold eccentricity
      rw [dif_pos hC]
      obtain ⟨x, hx⟩ := hC
      exact (array_nonneg hd c x).trans (Finset.le_sup' (d c) hx)
    · exact le_rfl
  · exact le_rfl

private theorem inflation_is_metric {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ s : ℝ)
    (hR : 0 < hubRadius d γ τ) (hs : hubRadius d γ τ ≤ s)
    (hsL : s ≤ crossDistance d γ τ) :
    let dp := hubDistance d k γ τ
    let p := fun (x y : Point (n + k + 2)) =>
      if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n) then s else dp x y
    IsMetricArray dp → MetricPerturbation dp (s / hubRadius d γ τ) p := by
  let dp := hubDistance d k γ τ
  let changed (x y : Point (n + k + 2)) :=
    (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n)
  let p (x y : Point (n + k + 2)) := if changed x y then s else dp x y
  change IsMetricArray dp → MetricPerturbation dp _ p
  intro hmetric
  obtain ⟨m, hm⟩ := hmetric
  let _ : MetricSpace (Point (n + k + 2)) := m
  have hsym (x y : Point (n + k + 2)) : dp x y = dp y x := by
    rw [← hm x y, ← hm y x]
    exact dist_comm x y
  have hnonneg (x y : Point (n + k + 2)) : 0 ≤ dp x y := by
    rw [← hm x y]
    exact dist_nonneg
  have hub_source (x y : Point (n + k + 2)) (hx : x.val = n) (hy : y.val < n) :
      dp x y = hubRadius d γ τ := by
    have hne : x ≠ y := by
      intro h
      subst y
      omega
    simp [dp, hubDistance, hne, hy, hx]
  have original (x y : Point (n + k + 2)) (h : changed x y) :
      dp x y = hubRadius d γ τ := by
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact hub_source x y hx hy
    · rw [hsym x y]
      exact hub_source y x hy hx
  have psymm (x y : Point (n + k + 2)) : p x y = p y x := by
    simp only [p, changed, hsym x y, or_comm]
  have hp_ge (x y : Point (n + k + 2)) : dp x y ≤ p x y := by
    by_cases h : changed x y
    · simpa only [p, if_pos h, original x y h] using hs
    · simp only [p, if_neg h]
      exact le_rfl
  have hp0 (x y : Point (n + k + 2)) : 0 ≤ p x y := (hnonneg x y).trans (hp_ge x y)
  have hscale : 1 ≤ s / hubRadius d γ τ :=
    (le_div_iff₀ hR).2 (by simpa only [one_mul] using hs)
  have changed_tri (x y z : Point (n + k + 2)) (hx : x.val = n) (hz : z.val < n) :
      s ≤ p x y + p y z := by
    rcases lt_trichotomy y.val n with hy | hy | hy
    · have hxy : p x y = s := if_pos (Or.inl ⟨hx, hy⟩)
      linarith [hp0 y z]
    · have hyz : p y z = s := if_pos (Or.inl ⟨hy, hz⟩)
      linarith [hp0 x y]
    · have hne : x ≠ y := by
        intro h
        subst y
        omega
      have hys : ¬ y.val < n := by omega
      have hxy : dp x y = crossDistance d γ τ := by
        simp [dp, hubDistance, hne, hys, hx]
      linarith [hp_ge x y, hp0 y z]
  refine ⟨⟨psymm, fun x y => ⟨hp_ge x y, ?_⟩⟩, ?_⟩
  · by_cases h : changed x y
    · rw [original x y h, div_mul_cancel₀ _ hR.ne']
      exact le_of_eq (if_pos h)
    · change (if changed x y then s else dp x y) ≤ _
      rw [if_neg h]
      exact le_mul_of_one_le_left (hnonneg x y) hscale
  · intro x y z
    by_cases h : changed x z
    · change (if changed x z then s else dp x z) ≤ _
      rw [if_pos h]
      rcases h with ⟨hx, hz⟩ | ⟨hz, hx⟩
      · exact changed_tri x y z hx hz
      · simpa only [psymm z y, psymm y x, add_comm] using changed_tri z y x hz hx
    · have htri : dp x z ≤ dp x y + dp y z := by
        rw [← hm x z, ← hm x y, ← hm y z]
        exact dist_triangle x y z
      change (if changed x z then s else dp x z) ≤ _
      rw [if_neg h]
      exact htri.trans (add_le_add (hp_ge x y) (hp_ge y z))

theorem solution {n k : ℕ} (d : Point n → Point n → ℚ) (γ τ : ℚ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray (fun x y => (d x y : ℝ)))
    (hγ : 1 < γ) (hτ : 0 < τ) :
    let dr := fun x y => (d x y : ℝ)
    let dp := hubDistance dr k γ τ
    let O₀ := suppliedPartition n k
    let ellStar := stabilityThreshold dr k γ τ
    ellStar = (γ : ℝ) + (optimumValue dr k - τ) / hubRadius dr γ τ ∧
    (∀ ell : ℝ, 1 ≤ ell →
      (Stable dp (k + 2) ell O₀ ↔ ell < ellStar) ∧
      (StableMetric dp (k + 2) ell O₀ ↔ ell < ellStar)) ∧
    ∃ p : Point (n + k + 2) → Point (n + k + 2) → ℝ,
      MetricPerturbation dp ellStar p ∧ Optimal p Finset.univ (k + 2) O₀ ∧
      ∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ O₀ ∧ cost p Q = cost p O₀ := by
  dsimp only
  let dr := fun x y => (d x y : ℝ)
  let dp := hubDistance dr k γ τ
  let O := suppliedPartition n k
  let R := hubRadius dr γ τ
  let S := dummyDistance dr γ τ + optimumValue dr k
  let L := stabilityThreshold dr k γ τ
  change L = (γ : ℝ) + (optimumValue dr k - τ) / R ∧
    (∀ ell : ℝ, 1 ≤ ell →
      (Stable dp (k + 2) ell O ↔ ell < L) ∧
      (StableMetric dp (k + 2) ell O ↔ ell < L)) ∧
    ∃ p, MetricPerturbation dp L p ∧ Optimal p Finset.univ (k + 2) O ∧
      ∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ O ∧ cost p Q = cost p O
  obtain ⟨haD, hDR, hmetric, hcost, _, hrunner, huniq⟩ :=
    hub_runner_up d γ τ hk hkn hd hγ hτ
  change diameter dr Finset.univ < R at hDR
  change cost dp O = R at hcost
  have hfeasible : Feasible Finset.univ (k + 2) O := huniq.1.1
  have ha0 := optimum_nonneg hd k
  have hR : 0 < R := lt_of_le_of_lt (ha0.trans haD) hDR
  have hg : 0 < (γ : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hγ)
  have ht : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hD : 0 ≤ diameter dr Finset.univ := ha0.trans haD
  have hbase : 0 < 1 + diameter dr Finset.univ + (τ : ℝ) := by linarith
  have hmul : (τ : ℝ) < R * ((γ : ℝ) - 1) := by
    calc
      (τ : ℝ) = ((τ : ℝ) / ((γ : ℝ) - 1)) * ((γ : ℝ) - 1) :=
        (div_mul_cancel₀ _ (ne_of_gt hg)).symm
      _ < R * ((γ : ℝ) - 1) := by
        apply mul_lt_mul_of_pos_right _ hg
        change (τ : ℝ) / ((γ : ℝ) - 1) <
          1 + diameter dr Finset.univ + (τ : ℝ) + (τ : ℝ) / ((γ : ℝ) - 1)
        linarith
  have hδ : 0 ≤ dummyDistance dr γ τ := by
    change 0 ≤ (γ : ℝ) * R - (τ : ℝ)
    linarith
  have hRS : R ≤ S := by
    change R ≤ (γ : ℝ) * R - (τ : ℝ) + optimumValue dr k
    linarith
  have hScross : S ≤ crossDistance dr γ τ := by
    change dummyDistance dr γ τ + optimumValue dr k ≤ dummyDistance dr γ τ + R + 1
    linarith [haD.trans hDR.le]
  have hlform : L = (γ : ℝ) + (optimumValue dr k - τ) / R := by
    change ((γ : ℝ) * R - (τ : ℝ) + optimumValue dr k) / R = _
    apply (div_eq_iff hR.ne').mpr
    field_simp [hR.ne']
    <;> ring
  let p := fun (x y : Point (n + k + 2)) =>
    if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n) then S else dp x y
  have hpert : MetricPerturbation dp L p :=
    inflation_is_metric dr γ τ S hR hRS hScross hmetric
  obtain ⟨hpO, Q, hQ, hQne, hpQ⟩ :=
    hub_inflation_costs dr γ τ S hk hkn hd hDR.le hRS hδ
  change cost p O = S at hpO
  change cost p Q = S at hpQ
  have hlower (q : Point (n + k + 2) → Point (n + k + 2) → ℝ) (ell : ℝ)
      (hq : Perturbation dp ell q) (B : Partition (n + k + 2))
      (hB : Feasible Finset.univ (k + 2) B) (hBne : B ≠ O) : S ≤ cost q B := by
    have hc := cost_le_scaled_cost q dp B 1 zero_le_one (fun x y => by
      simpa only [one_mul] using (hq.2 x y).1)
    rw [one_mul] at hc
    exact (hrunner B hB hBne).trans hc
  have hopt : Optimal p Finset.univ (k + 2) O := by
    refine ⟨hfeasible, fun B hB => ?_⟩
    by_cases hBO : B = O
    · subst B
      exact le_rfl
    · rw [hpO]
      exact hlower p L hpert.1 B hB hBO
  have hoptQ : Optimal p Finset.univ (k + 2) Q := by
    refine ⟨hQ, fun B hB => ?_⟩
    rw [hpQ, ← hpO]
    exact hopt.2 B hB
  have hgrowth (ell : ℝ) (hell : 1 ≤ ell) (hlt : ell < L) : Stable dp (k + 2) ell O := by
    refine ⟨hfeasible, fun q hq => ?_⟩
    have hsmall : cost q O < S := by
      have hb := cost_le_scaled_cost dp q O ell (zero_le_one.trans hell) (fun x y => (hq.2 x y).2)
      rw [hcost] at hb
      exact hb.trans_lt ((lt_div_iff₀ hR).mp hlt)
    refine ⟨⟨hfeasible, fun B hB => ?_⟩, fun B hB => ?_⟩
    · by_cases hBO : B = O
      · subst B
        exact le_rfl
      · exact (hsmall.trans_le (hlower q ell hq B hB hBO)).le
    · by_contra hBO
      exact (not_lt_of_ge (hB.2 O hfeasible)) (hsmall.trans_le (hlower q ell hq B hB.1 hBO))
  have htie (ell : ℝ) (hell : L ≤ ell) : ¬ StableMetric dp (k + 2) ell O := by
    intro hstable
    have hextend : MetricPerturbation dp ell p := by
      refine ⟨⟨hpert.1.1, fun x y => ⟨(hpert.1.2 x y).1, ?_⟩⟩, hpert.2⟩
      exact (hpert.1.2 x y).2.trans
        (mul_le_mul_of_nonneg_right hell (array_nonneg hmetric x y))
    exact hQne ((hstable.2 p hextend).2 Q hoptQ)
  have hrestrict (ell : ℝ) (h : Stable dp (k + 2) ell O) : StableMetric dp (k + 2) ell O :=
    ⟨h.1, fun q hq => h.2 q hq.1⟩
  refine ⟨hlform, ?_, p, hpert, hopt, Q, hQ, hQne, hpQ.trans hpO.symm⟩
  intro ell hell
  exact ⟨⟨fun h => lt_of_not_ge (fun hge => htie ell hge (hrestrict ell h)),
      hgrowth ell hell⟩,
    ⟨fun h => lt_of_not_ge (fun hge => htie ell hge h),
      fun hlt => hrestrict ell (hgrowth ell hell hlt)⟩⟩
