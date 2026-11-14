-- Prove2me | solution 1 for StableMSR.Recovery.small_cluster_components
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:18:50.50174+00:00
-- url     : https://prove2.me/submissions/d7b2dff2-4085-4213-8905-2fdf93c4e0a2

import Theorems.Thm_StableMSR_Recovery_center_separation
import Theorems.Thm_StableMSR_Recovery_intercluster_separation

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace ComponentsAux

lemma metric_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_nonneg

lemma metric_symm {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm]
  exact dist_comm x y

lemma metric_self {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x : Point n) : d x x = 0 := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_self x

lemma metric_triangle {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm, ← hm]
  exact dist_triangle x y z

lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using he.symm⟩

lemma distance_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  have hC : C.Nonempty := ⟨c, hc.1⟩
  rw [← hc.2]
  simp only [eccentricity, dif_pos hC]
  exact Finset.le_sup' (d c) hx

lemma radius_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) : 0 ≤ radius d C := by
  obtain ⟨c, hc⟩ := exists_center d hC
  exact (metric_nonneg hd c c).trans (distance_le_radius hc hc.1)

lemma radius_singleton {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x : Point n) : radius d {x} = 0 := by
  simp [radius, eccentricity, metric_self hd]

lemma positive_radius_card {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) (hpos : 0 < radius d C) :
    2 ≤ C.card := by
  by_contra hn
  have hc : C.card = 1 := by have := Finset.card_pos.mpr hC; omega
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
  rw [radius_singleton hd] at hpos
  exact lt_irrefl _ hpos

lemma largest_attained {n k : ℕ} (d : Point n → Point n → ℝ)
    {O : Partition n} (hk : 1 ≤ k) (hO : Feasible Finset.univ k O) :
    ∃ C ∈ O, radius d C = largestRadius d O := by
  classical
  have hOn : O.Nonempty := Finset.card_pos.mp (by rw [hO.1]; omega)
  obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup' hOn (radius d)
  exact ⟨C, hC, by simpa [largestRadius, hOn] using he.symm⟩

lemma pair_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty)
    {x y : Point n} (hx : x ∈ C) (hy : y ∈ C) : d x y ≤ 2 * radius d C := by
  obtain ⟨c, hc⟩ := exists_center d hC
  have hx' := distance_le_radius hc hx
  have hy' := distance_le_radius hc hy
  have ht := metric_triangle hd x c y
  rw [metric_symm hd x c] at ht
  linarith

lemma reachable_closed {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ {x y}, G.Adj x y → x ∈ S → y ∈ S)
    {x y : V} (hx : x ∈ S) (hxy : G.Reachable x y) : y ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact hx
  | tail _ ha ih => exact hclosed ha ih

end ComponentsAux

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) :
    (∀ C ∈ smallClusters d O (γ - 1),
      C ∈ components d (2 * smallThreshold d O (γ - 1)) Finset.univ) ∧
    (∀ K ∈ components d (2 * smallThreshold d O (γ - 1)) Finset.univ,
      K ∉ smallClusters d O (γ - 1) → K ⊆ (largeClusters d O (γ - 1)).biUnion id) := by
  classical
  let b := smallThreshold d O (γ - 1)
  let G := thresholdGraph d (2 * b) Finset.univ
  have hsmall : ∀ C ∈ smallClusters d O (γ - 1), ∀ x ∈ C,
      component d (2 * b) Finset.univ x = C := by
    intro C hCs x hx
    obtain ⟨hCO, hCr⟩ := Finset.mem_filter.mp hCs
    have hCn := hO.1.2.1 C hCO
    have hC0 := ComponentsAux.radius_nonneg hd hCn
    have hb : 0 < b := lt_of_le_of_lt hC0 hCr
    obtain ⟨A, hAO, hAr⟩ := ComponentsAux.largest_attained d hk.1 hO.1
    have hAn := hO.1.2.1 A hAO
    have heps : 0 < γ - 1 := by linarith [hγ.1]
    have hRpos : 0 < largestRadius d O := by
      dsimp [b, smallThreshold] at hb
      nlinarith
    have hArpos : 0 < radius d A := by rw [hAr]; exact hRpos
    have hAns : 2 ≤ A.card := ComponentsAux.positive_radius_card hd hAn hArpos
    have hbR : b < radius d A := by
      dsimp [b, smallThreshold]
      rw [hAr]
      nlinarith [hγ.2]
    have hCA : C ≠ A := by intro h; subst A; linarith
    have hseparate : ∀ u ∈ C, ∀ v, v ∉ C → 2 * b < d u v := by
      intro u hu v hv
      have hvcover : v ∈ O.biUnion id := by rw [hO.1.2.2.2]; exact Finset.mem_univ v
      obtain ⟨E, hEO, hvE⟩ := Finset.mem_biUnion.mp hvcover
      have hCE : C ≠ E := by intro h; subst E; exact hv hvE
      by_cases hEA : E = A
      · subst E
        obtain ⟨a, ha⟩ := ComponentsAux.exists_center d hAn
        have hs := (center_separation d hd k hk γ hγ.1 O hO A hAO a ha).2.1
        have huA : u ∉ A := fun huA =>
          Finset.disjoint_left.mp (hO.1.2.2.1 hCO hAO hCA) hu huA
        have hdle : setDistance d A (Finset.univ \ A) ≤ (d v u : EReal) :=
          sInf_le ⟨v, hvE, u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huA⟩, rfl⟩
        have hr : (γ - 1) * radius d A < d v u := by
          apply EReal.coe_lt_coe_iff.mp
          simpa only [EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using hs.trans_le hdle
        rw [ComponentsAux.metric_symm hd v u, hAr] at hr
        dsimp [b, smallThreshold] at *
        nlinarith
      · have hs := intercluster_separation d hd k hk γ hγ.1 O hO A C E
          hAO hCO hEO hCA.symm (Ne.symm hEA) hCE hAns
        have hdle : setDistance d C E ≤ (d u v : EReal) :=
          sInf_le ⟨u, hu, v, hvE, rfl⟩
        have hh := hs.trans_le (add_le_add hdle
          (min_le_left (radius d C : EReal) (radius d E : EReal)))
        have hr : (γ - 1) * radius d A < d u v + radius d C := by
          apply EReal.coe_lt_coe_iff.mp
          simpa only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using hh
        rw [hAr] at hr
        change radius d C < b at hCr
        have hb4 : (γ - 1) * largestRadius d O = 4 * b := by dsimp [b, smallThreshold]; ring
        rw [hb4] at hr
        linarith
    have hclosed : ∀ {u v}, G.Adj u v → u ∈ C → v ∈ C := by
      intro u v huv hu
      by_contra hv
      exact (not_lt_of_ge huv.2.2.2.1) (hseparate u hu v hv)
    apply Finset.ext
    intro y
    constructor
    · intro hy
      have hyR : G.Reachable x y := (Finset.mem_filter.mp hy).2
      exact ComponentsAux.reachable_closed G (C : Set (Point n)) hclosed hx hyR
    · intro hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ y, ?_⟩
      change G.Reachable x y
      by_cases hxy : x = y
      · subst y; exact SimpleGraph.Reachable.refl x
      · apply SimpleGraph.Adj.reachable
        have hxyb := ComponentsAux.pair_bound hd hCn hx hy
        have hyxb := ComponentsAux.pair_bound hd hCn hy hx
        refine ⟨hxy, Finset.mem_univ x, Finset.mem_univ y, ?_, ?_⟩ <;> linarith
  constructor
  · intro C hC
    have hCO := (Finset.mem_filter.mp hC).1
    obtain ⟨x, hx⟩ := hO.1.2.1 C hCO
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_univ x, hsmall C hC x hx⟩
  · intro K hK hKn y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hK
    have hyR : G.Reachable x y := (Finset.mem_filter.mp hy).2
    have hycover : y ∈ O.biUnion id := by rw [hO.1.2.2.2]; exact Finset.mem_univ y
    obtain ⟨C, hCO, hyC⟩ := Finset.mem_biUnion.mp hycover
    have hlarge : b ≤ radius d C := by
      by_contra hn
      have hCs : C ∈ smallClusters d O (γ - 1) :=
        Finset.mem_filter.mpr ⟨hCO, lt_of_not_ge hn⟩
      have hcomp : component d (2 * b) Finset.univ x = C := by
        rw [← hsmall C hCs y hyC]
        apply Finset.ext
        intro z
        simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => hyR.symm.trans h, fun h => hyR.trans h⟩
      apply hKn
      change component d (2 * b) Finset.univ x ∈ smallClusters d O (γ - 1)
      rw [hcomp]
      exact hCs
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_filter.mpr ⟨hCO, hlarge⟩, hyC⟩
