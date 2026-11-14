-- Prove2me | solution 1 for StableMSR.Recovery.interaction_subgraph_radius_growth
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:49:35.223841+00:00
-- url     : https://prove2.me/submissions/58ae4ee5-c142-4dc7-9e92-9c8d8fd08fd2

import Theorems.Thm_StableMSR_Recovery_local_cluster_density
import Definitions.Def_StableMSR_Recovery_Parameters


set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace GrowthAux

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
  refine ⟨c, hc, ?_⟩
  simp only [radius, dif_pos hC]
  exact he.symm

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

lemma radius_le_center_bound {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c : Point n} {r : ℝ} (hc : c ∈ C)
    (hbound : ∀ x ∈ C, d c x ≤ r) : radius d C ≤ r := by
  have hC : C.Nonempty := ⟨c, hc⟩
  simp only [radius, dif_pos hC]
  apply (Finset.inf'_le (eccentricity d C) hc).trans
  simp only [eccentricity, dif_pos hC]
  exact Finset.sup'_le hC (d c) hbound


lemma radius_nonneg_all {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (C : Cluster n) : 0 ≤ radius d C := by
  classical
  by_cases hC : C.Nonempty
  · exact radius_nonneg hd hC
  · simp [radius, hC]

lemma radius_pos {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : 2 ≤ C.card) : 0 < radius d C := by
  classical
  have hne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := exists_center d hne
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hcy : 0 < d c y := by rw [← hm]; exact dist_pos.mpr hyc.symm
  exact hcy.trans_le (distance_le_radius hc hy)

lemma radius_singleton {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x : Point n) : radius d {x} = 0 := by
  classical
  obtain ⟨m, hm⟩ := hd
  letI := m
  simp [radius, eccentricity, ← hm]

lemma card_two_of_radius_pos {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) (hr : 0 < radius d C) :
    2 ≤ C.card := by
  classical
  by_contra h
  have he : C.card = 1 := by have := Finset.card_pos.mpr hC; omega
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp he
  rw [radius_singleton hd] at hr
  exact lt_irrefl _ hr

lemma diameter_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} {x y : Point n} (hx : x ∈ C) (hy : y ∈ C) :
    d x y ≤ 2 * radius d C := by
  obtain ⟨c, hc⟩ := exists_center d ⟨x, hx⟩
  have hcx := distance_le_radius hc hx
  have hcy := distance_le_radius hc hy
  have htri := metric_triangle hd x c y
  rw [metric_symm hd x c] at htri
  linarith

lemma nonempty_union {n : ℕ} {F : Partition n} (hF : F.Nonempty)
    (hne : ∀ C ∈ F, C.Nonempty) : (F.biUnion id).Nonempty := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨x, hx⟩ := hne C hC
  exact ⟨x, Finset.mem_biUnion.mpr ⟨C, hC, hx⟩⟩

lemma cost_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (F : Partition n) : 0 ≤ cost d F :=
  Finset.sum_nonneg (fun C _ => radius_nonneg_all hd C)

lemma radius_le_largest {n : ℕ} {d : Point n → Point n → ℝ}
    {O : Partition n} {C : Cluster n} (hC : C ∈ O) : radius d C ≤ largestRadius d O := by
  classical
  rw [largestRadius, dif_pos ⟨C, hC⟩]
  exact Finset.le_sup' _ hC

lemma largest_pos {n k : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {O : Partition n} (hO : Feasible Finset.univ k O) (hkn : k < n) :
    0 < largestRadius d O := by
  classical
  have hex : ∃ C ∈ O, 2 ≤ C.card := by
    by_contra hn
    have hc : ∀ C ∈ O, C.card ≤ 1 := by
      intro C hC
      by_contra hnC
      exact hn ⟨C, hC, by omega⟩
    have hsum : (∑ C ∈ O, C.card) ≤ O.card := by
      calc
        (∑ C ∈ O, C.card) ≤ ∑ C ∈ O, 1 := Finset.sum_le_sum hc
        _ = _ := by simp
    have hncard : (∑ C ∈ O, C.card) = n := by
      rw [← Finset.card_biUnion hO.2.2.1]
      change (O.biUnion id).card = n
      rw [hO.2.2.2]
      simp
    rw [hncard, hO.1] at hsum
    omega
  obtain ⟨C, hC, hC2⟩ := hex
  exact (radius_pos hd hC2).trans_le (radius_le_largest hC)

lemma exists_largest {n : ℕ} (d : Point n → Point n → ℝ)
    {O : Partition n} (hO : O.Nonempty) :
    ∃ C ∈ O, radius d C = largestRadius d O := by
  classical
  obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup' hO (radius d)
  exact ⟨C, hC, by simpa [largestRadius, hO] using he.symm⟩

end GrowthAux

namespace GrowthAux

/- Strictly separated points occupy different optimal clusters. -/
lemma separated_card_le_meeting {n k : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {O : Partition n} (hO : Feasible Finset.univ k O)
    (B : Cluster n) (x : Point n) (u : ℝ)
    (hsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → 2 * largestRadius d O < d a b)
    (hball : ∀ y ∈ B, d x y ≤ u) :
    B.card ≤ (meeting O (ball d x u)).card := by
  classical
  have hcover : ∀ y : Point n, ∃ C ∈ O, y ∈ C := by
    intro y
    have hy : y ∈ O.biUnion id := by rw [hO.2.2.2]; simp
    exact Finset.mem_biUnion.mp hy
  choose owner hownerO howner using hcover
  apply Finset.card_le_card_of_injOn owner
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨hownerO y, y, ?_⟩
    exact Finset.mem_inter.mpr ⟨howner y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hball y hy⟩⟩
  · intro a ha b hb hab
    by_contra hne
    have hbC : b ∈ owner a := by rw [hab]; exact howner b
    have hdiam := diameter_bound hd (howner a) hbC
    have hmax := radius_le_largest (d := d) (hownerO a)
    have hstrict := hsep a ha b hb hne
    linarith

/- The meeting family splits into its small and large subfamilies. -/
lemma meeting_card_split {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) (A : Cluster n) :
    (meeting O A).card = (meeting (smallClusters d O ε) A).card +
      (meeting (largeClusters d O ε) A).card := by
  classical
  have hunion : meeting O A = meeting (smallClusters d O ε) A ∪
      meeting (largeClusters d O ε) A := by
    ext C
    simp only [meeting, smallClusters, largeClusters, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hCO, hmeet⟩
      rcases lt_or_ge (radius d C) (smallThreshold d O ε) with h | h
      · exact Or.inl ⟨⟨hCO, h⟩, hmeet⟩
      · exact Or.inr ⟨⟨hCO, h⟩, hmeet⟩
    · rintro (⟨⟨hCO, _⟩, hmeet⟩ | ⟨⟨hCO, _⟩, hmeet⟩) <;> exact ⟨hCO, hmeet⟩
  have hdis : Disjoint (meeting (smallClusters d O ε) A) (meeting (largeClusters d O ε) A) := by
    apply Finset.disjoint_left.mpr
    intro C hCS hCL
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hCS).1).2
    have hl := (Finset.mem_filter.mp (Finset.mem_filter.mp hCL).1).2
    exact not_lt_of_ge hl hs
  rw [hunion, Finset.card_union_of_disjoint hdis]

/- The diameter definition bounds every ordered pair in a nonempty set. -/
lemma distance_le_diameter {n : ℕ} (d : Point n → Point n → ℝ)
    {W : Cluster n} {x y : Point n} (hx : x ∈ W) (hy : y ∈ W) :
    d x y ≤ diameter d W := by
  have hW : W.Nonempty := ⟨x, hx⟩
  have h1 : d x y ≤ eccentricity d W x := by
    rw [eccentricity, dif_pos hW]
    exact Finset.le_sup' _ hy
  have h2 : eccentricity d W x ≤ diameter d W := by
    rw [diameter, dif_pos hW]
    exact Finset.le_sup' _ hx
  exact h1.trans h2

lemma diameter_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (W : Cluster n) : 0 ≤ diameter d W := by
  classical
  by_cases hW : W.Nonempty
  · obtain ⟨x, hx⟩ := hW
    exact (metric_nonneg hd x x).trans (distance_le_diameter d hx hx)
  · simp [diameter, hW]

/- The numerical estimate in Lemma 4.4, with exactly its growth constant. -/
lemma density_growth_arithmetic (ε R u j : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : 0 < R) (hj : 1 ≤ j) (hu : u ≤ 8 * j * R) :
    1 + (2 * u + 2 * (ε * R / 4)) / (ε * (ε * R / 4)) +
      (u + 2 * R) / (ε * R / 4) ≤ (1 + 80 / ε + 80 / ε ^ 2) * j := by
  have hb : 0 < ε * R / 4 := by positivity
  have hd : 0 < ε * (ε * R / 4) := mul_pos hε hb
  have hfirst := div_le_div_of_nonneg_right
    (show 2 * u + 2 * (ε * R / 4) ≤ 2 * (8 * j * R) + 2 * (ε * R / 4) by linarith) hd.le
  have hsecond := div_le_div_of_nonneg_right
    (show u + 2 * R ≤ 8 * j * R + 2 * R by linarith) hb.le
  have heq : 1 + (2 * (8 * j * R) + 2 * (ε * R / 4)) / (ε * (ε * R / 4)) +
      (8 * j * R + 2 * R) / (ε * R / 4) = 1 + (32 * j + 10) / ε + 64 * j / ε ^ 2 := by
    field_simp
    <;> ring
  have hfin : 1 + (32 * j + 10) / ε + 64 * j / ε ^ 2 ≤
      (1 + 80 / ε + 80 / ε ^ 2) * j := by
    have hnum : 32 * j + 10 ≤ 80 * j := by linarith
    have h1 := div_le_div_of_nonneg_right hnum hε.le
    have h2 := div_le_div_of_nonneg_right (show 64 * j ≤ 80 * j by linarith) (sq_nonneg ε)
    have h3 : 80 * j / ε = (80 / ε) * j := by ring
    have h4 : 80 * j / ε ^ 2 = (80 / ε ^ 2) * j := by ring
    rw [h3] at h1
    rw [h4] at h2
    nlinarith
  linarith

/- Linear metric growth of every strictly 2R-separated subset of a bounded region.
No alignment or maximality hypothesis is needed for this part of Lemma 4.4. -/
theorem separated_region_growth {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W B : Cluster n) (hBW : B ⊆ W) (x : Point n) (hx : x ∈ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → 2 * largestRadius d O < d a b)
    (j : ℕ) (hj : 1 ≤ j)
    (hnear : ∀ y ∈ B, d x y ≤ 8 * (j : ℝ) * largestRadius d O) :
    (B.card : ℝ) ≤ growthConstant (γ - 1) * (j : ℝ) := by
  classical
  let R := largestRadius d O
  let ε := γ - 1
  let u := min (8 * (j : ℝ) * R) (diameter d W)
  have hR : 0 < R := largest_pos hd hO.1 hkn
  have hε : 0 < ε := by dsimp [ε]; linarith [hγ.1]
  have hε1 : ε < 1 := by dsimp [ε]; linarith [hγ.2]
  have hu : 0 ≤ u := le_min (by positivity) (diameter_nonneg hd W)
  have huρ : u ≤ densityScale d O (γ - 1) := (min_le_right _ _).trans hdiam
  have hu8 : u ≤ 8 * (j : ℝ) * R := min_le_left _ _
  have hball : ∀ y ∈ B, d x y ≤ u := by
    intro y hy
    exact le_min (hnear y hy) (distance_le_diameter d hx (hBW hy))
  have hcount := separated_card_le_meeting hd hO.1 B x u hsep hball
  rw [meeting_card_split d O (γ - 1)] at hcount
  have hcast : (B.card : ℝ) ≤ ((meeting (smallClusters d O (γ - 1)) (ball d x u)).card : ℝ) +
      ((meeting (largeClusters d O (γ - 1)) (ball d x u)).card : ℝ) := by exact_mod_cast hcount
  obtain ⟨_, hsmall, hlarge⟩ := local_cluster_density d hd k hk γ hγ hkn O hO
  have hs := hsmall x u hu huρ
  have hl := hlarge x u hu
  have harith := density_growth_arithmetic ε R u (j : ℝ) hε hε1 hR
    (by exact_mod_cast hj) hu8
  change (B.card : ℝ) ≤ (1 + 80 / ε + 80 / ε ^ 2) * (j : ℝ)
  change _ ≤ 1 + (2 * u + 2 * (ε * R / 4)) / (ε * (ε * R / 4)) at hs
  change _ ≤ (u + 2 * R) / (ε * R / 4) at hl
  linarith

/- Every threshold-graph walk has metric length bounded by its edge count. -/
lemma threshold_walk_distance {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (N : Cluster n) (r : ℝ) {x y : Point n}
    (p : (thresholdGraph d r N).Walk x y) : d x y ≤ (p.length : ℝ) * r := by
  induction p with
  | nil =>
      obtain ⟨m, hm⟩ := hd
      letI := m
      simp only [SimpleGraph.Walk.length_nil, Nat.cast_zero, zero_mul]
      rw [← hm]
      exact le_of_eq (dist_self _)
  | @cons a b c hab p ih =>
      have hedge : d a b ≤ r := hab.2.2.2.1
      have htri := metric_triangle hd a b c
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

/- The exact graph-growth premise needed by Campbell's theorem: any vertex set
in the net reachable from a center in at most j interaction edges has at most cj vertices. -/
theorem interaction_walk_radius_growth {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N B : Cluster n) (hNW : N ⊆ W) (hBN : B ⊆ N)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → 2 * largestRadius d O < d a b)
    (x : Point n) (hx : x ∈ N) (j : ℕ) (hj : 1 ≤ j)
    (hwalk : ∀ y ∈ B, ∃ p : (thresholdGraph d (8 * largestRadius d O) N).Walk x y,
      p.length ≤ j) :
    (B.card : ℝ) ≤ growthConstant (γ - 1) * (j : ℝ) := by
  have hR : 0 ≤ largestRadius d O := (largest_pos hd hO.1 hkn).le
  apply separated_region_growth d hd k hk γ hγ hkn O hO W B (hBN.trans hNW) x (hNW hx)
    hdiam (fun a ha b hb hab => hsep a (hBN ha) b (hBN hb) hab) j hj
  intro y hy
  obtain ⟨p, hp⟩ := hwalk y hy
  have hdist := threshold_walk_distance hd N (8 * largestRadius d O) p
  have hcast : (p.length : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp
  have hmul := mul_le_mul_of_nonneg_right hcast (show 0 ≤ 8 * largestRadius d O by positivity)
  nlinarith

lemma growth_constant_gt_one (ε : ℝ) (hε : 0 < ε) : 1 < growthConstant ε := by
  have h1 : 0 < 80 / ε := div_pos (by norm_num) hε
  have h2 : 0 < 80 / ε ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hε)
  dsimp [growthConstant]
  linarith

/- A source-style connected subgraph radius premise, measured using walks inside
that subgraph, satisfies precisely the vertex-count hypothesis of Campbell's theorem. -/
end GrowthAux

open GrowthAux

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → 2 * largestRadius d O < d a b)
    (H : (thresholdGraph d (8 * largestRadius d O) N).Subgraph)
    (hHN : H.verts ⊆ (N : Set (Point n)))
    (x : H.verts) (j : ℕ) (hj : 1 ≤ j)
    (hwalk : ∀ y : H.verts, ∃ p : H.coe.Walk x y, p.length ≤ j) :
    ((Finset.univ.filter (fun y => y ∈ H.verts)).card : ℝ) ≤
      growthConstant (γ - 1) * (j : ℝ) := by
  classical
  apply interaction_walk_radius_growth d hd k hk γ hγ hkn O hO W N
    (Finset.univ.filter (fun y => y ∈ H.verts)) hNW
    (fun y hy => hHN (Finset.mem_filter.mp hy).2) hdiam hsep x.val (hHN x.property) j hj
  intro y hy
  obtain ⟨p, hp⟩ := hwalk ⟨y, (Finset.mem_filter.mp hy).2⟩
  refine ⟨p.map H.hom, ?_⟩
  exact (SimpleGraph.Walk.length_map H.hom p).le.trans hp

