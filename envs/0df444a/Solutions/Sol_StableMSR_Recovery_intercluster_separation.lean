-- Prove2me | solution 1 for StableMSR.Recovery.intercluster_separation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:02:42.829717+00:00
-- url     : https://prove2.me/submissions/5fb3a7a3-ee8c-42a9-a10a-551103e869d0

import Theorems.Thm_StableMSR_Recovery_merge_split_inequality

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

private lemma metric_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_nonneg

private lemma metric_symm {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm]
  exact dist_comm x y

private lemma metric_triangle {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm, ← hm]
  exact dist_triangle x y z

private lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  refine ⟨c, hc, ?_⟩
  simp only [radius, dif_pos hC]
  exact he.symm

private lemma distance_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  have hC : C.Nonempty := ⟨c, hc.1⟩
  rw [← hc.2]
  simp only [eccentricity, dif_pos hC]
  exact Finset.le_sup' (d c) hx

private lemma radius_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) : 0 ≤ radius d C := by
  obtain ⟨c, hc⟩ := exists_center d hC
  exact (metric_nonneg hd c c).trans (distance_le_radius hc hc.1)

private lemma radius_le_center_bound {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c : Point n} {r : ℝ} (hc : c ∈ C)
    (hbound : ∀ x ∈ C, d c x ≤ r) : radius d C ≤ r := by
  have hC : C.Nonempty := ⟨c, hc⟩
  simp only [radius, dif_pos hC]
  apply (Finset.inf'_le (eccentricity d C) hc).trans
  simp only [eccentricity, dif_pos hC]
  exact Finset.sup'_le hC (d c) hbound

private lemma union_radius_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {D E : Cluster n} (hD : D.Nonempty) (hE : E.Nonempty)
    {x y : Point n} (hx : x ∈ D) (hy : y ∈ E) :
    radius d (D ∪ E) ≤ radius d D + d x y + 2 * radius d E := by
  classical
  obtain ⟨c, hc⟩ := exists_center d hD
  obtain ⟨e, he⟩ := exists_center d hE
  apply radius_le_center_bound (Finset.mem_union_left E hc.1)
  intro z hz
  rcases Finset.mem_union.mp hz with hzD | hzE
  · have hcz := distance_le_radius hc hzD
    have hxy := metric_nonneg hd x y
    have hE0 := radius_nonneg hd hE
    linarith
  · have hcx := distance_le_radius hc hx
    have hey := distance_le_radius he hy
    have hez := distance_le_radius he hzE
    have h1 := metric_triangle hd c x z
    have h2 := metric_triangle hd x y z
    have h3 := metric_triangle hd y e z
    rw [metric_symm hd y e] at h3
    linarith

private lemma setDistance_attained {n : ℕ} (d : Point n → Point n → ℝ)
    {D E : Cluster n} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∃ x ∈ D, ∃ y ∈ E, setDistance d D E = (d x y : EReal) := by
  classical
  have hp : (D ×ˢ E).Nonempty := hD.product hE
  obtain ⟨p, hpDE, hmin⟩ := Finset.exists_mem_eq_inf' hp (fun p => d p.1 p.2)
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpDE
  refine ⟨p.1, hx, p.2, hy, ?_⟩
  apply le_antisymm
  · exact sInf_le ⟨p.1, hx, p.2, hy, rfl⟩
  · apply le_sInf
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    apply EReal.coe_le_coe_iff.mpr
    have hab : (a, b) ∈ D ×ˢ E := Finset.mem_product.mpr ⟨ha, hb⟩
    have h := Finset.inf'_le (fun p : Point n × Point n => d p.1 p.2) hab
    rw [hmin] at h
    exact h

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (C D E : Cluster n) (hC : C ∈ O) (hD : D ∈ O) (hE : E ∈ O)
    (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) (hns : 2 ≤ C.card) :
    ((γ - 1) * radius d C : EReal) <
      setDistance d D E + (min (radius d D) (radius d E) : EReal) := by
  classical
  have hDne : D.Nonempty := hO.1.2.1 D hD
  have hEne : E.Nonempty := hO.1.2.1 E hE
  have hsubDE : ({D, E} : Partition n) ⊆ O := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hD, hE⟩
  have hsubC : ({C} : Partition n) ⊆ O := by simp [hC]
  have hdisj : Disjoint ({D, E} : Partition n) {C} := by
    simp [Finset.disjoint_left, hCD.symm, hCE.symm]
  have hsize : 2 ≤ ({D, E} : Partition n).card := by simp [hDE]
  have hcount : ({C} : Partition n).card + 1 = ({D, E} : Partition n).card := by
    simp [hDE]
  have hnonsingleton : ∀ X ∈ ({C} : Partition n), 2 ≤ X.card := by
    simpa using hns
  have hmerge := merge_split_inequality d hd k hk γ hγ O hO {D, E} {C}
    hsubDE hsubC hdisj hsize hcount hnonsingleton
  simp [cost, hDE] at hmerge
  obtain ⟨x, hx, y, hy, hdist⟩ := setDistance_attained d hDne hEne
  have hforward := union_radius_bound hd hDne hEne hx hy
  have hbackward := union_radius_bound hd hEne hDne hy hx
  rw [Finset.union_comm E D, metric_symm hd y x] at hbackward
  rw [hdist]
  rcases le_total (radius d D) (radius d E) with hle | hle
  · rw [min_eq_left (EReal.coe_le_coe_iff.mpr hle)]
    have hreal : (γ - 1) * radius d C < d x y + radius d D := by linarith
    simpa only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using
      (EReal.coe_lt_coe_iff.mpr hreal)
  · rw [min_eq_right (EReal.coe_le_coe_iff.mpr hle)]
    have hreal : (γ - 1) * radius d C < d x y + radius d E := by linarith
    simpa only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using
      (EReal.coe_lt_coe_iff.mpr hreal)
