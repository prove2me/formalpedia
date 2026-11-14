-- Prove2me | solution 1 for StableMSR.Recovery.local_cluster_density
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:19:03.552006+00:00
-- url     : https://prove2.me/submissions/3610fe4c-0183-4d43-84cd-cb0cf30652b9

import Theorems.Thm_StableMSR_Recovery_merge_split_inequality
import Theorems.Thm_StableMSR_Recovery_contained_cluster_radii

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery
namespace DensityAux

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

end DensityAux


set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery
namespace DensityAux

lemma many_union_lower {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (T F : Partition n) (hTO : T ⊆ O) (hFO : F ⊆ O)
    (hFT : Disjoint F T) (hTne : T.Nonempty)
    (hTns : ∀ C ∈ T, 2 ≤ C.card) (hsize : T.card + 1 ≤ F.card) :
    (γ - 1) * cost d T < radius d (F.biUnion id) := by
  classical
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  have hUne := nonempty_union hFne (fun C hC => hO.1.2.1 C (hFO hC))
  obtain ⟨z, hz⟩ := exists_center d hUne
  obtain ⟨A, hAF, hzA⟩ := Finset.mem_biUnion.mp hz.1
  obtain ⟨G, hAG, hGF, hGcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.singleton_subset_iff.mpr hAF) (by simp : ({A} : Partition n).card ≤ T.card + 1) hsize
  have hGO : G ⊆ O := hGF.trans hFO
  have hGT : Disjoint G T := hFT.mono_left hGF
  have hTcard : 0 < T.card := Finset.card_pos.mpr hTne
  have hGsize : 2 ≤ G.card := by omega
  have hcount : T.card + 1 = G.card := hGcard.symm
  have hmerge := merge_split_inequality d hd k hk γ hγ O hO G T hGO hTO hGT hGsize hcount hTns
  have hzG : z ∈ G.biUnion id :=
    Finset.mem_biUnion.mpr ⟨A, hAG (Finset.mem_singleton_self A), hzA⟩
  have hrad : radius d (G.biUnion id) ≤ radius d (F.biUnion id) := by
    apply radius_le_center_bound hzG
    intro y hy
    obtain ⟨B, hBG, hyB⟩ := Finset.mem_biUnion.mp hy
    exact distance_le_radius hz (Finset.mem_biUnion.mpr ⟨B, hGF hBG, hyB⟩)
  have hnonneg := cost_nonneg hd G
  linarith

lemma meeting_union_upper {n : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    (F : Partition n) (hF : F.Nonempty) (x : Point n) (u b : ℝ)
    (hmeet : ∀ C ∈ F, (C ∩ ball d x u).Nonempty)
    (hsmall : ∀ C ∈ F, radius d C < b) :
    radius d (F.biUnion id) < 2 * u + 2 * b := by
  classical
  obtain ⟨A, hA⟩ := hF
  obtain ⟨z, hz⟩ := hmeet A hA
  have hzU : z ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨A, hA, (Finset.mem_inter.mp hz).1⟩
  have hUne : (F.biUnion id).Nonempty := ⟨z, hzU⟩
  have hxz : d x z ≤ u := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
  have hzx : d z x ≤ u := by rw [metric_symm hd z x]; exact hxz
  have hbound : ∀ y ∈ F.biUnion id, d z y < 2 * u + 2 * b := by
    intro y hy
    obtain ⟨C, hC, hyC⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨v, hv⟩ := hmeet C hC
    have hvC := (Finset.mem_inter.mp hv).1
    have hxv : d x v ≤ u := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    have hvy := diameter_bound hd hvC hyC
    have h1 := metric_triangle hd z x y
    have h2 := metric_triangle hd x v y
    have hrad := hsmall C hC
    linarith
  have hecc : eccentricity d (F.biUnion id) z < 2 * u + 2 * b := by
    rw [eccentricity, dif_pos hUne]
    simpa only [Finset.sup'_lt_iff] using hbound
  have hle : radius d (F.biUnion id) ≤ eccentricity d (F.biUnion id) z := by
    rw [radius, dif_pos hUne]
    exact Finset.inf'_le _ hzU
  exact hle.trans_lt hecc

lemma lower_cost_of_radius_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (F : Partition n) (b : ℝ) (hbound : ∀ C ∈ F, b ≤ radius d C) :
    (F.card : ℝ) * b ≤ cost d F := by
  classical
  calc
    (F.card : ℝ) * b = ∑ C ∈ F, b := by simp
    _ ≤ cost d F := Finset.sum_le_sum hbound

lemma few_meeting_count {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (T F : Partition n) (hTO : T ⊆ O) (hFO : F ⊆ O)
    (hFT : Disjoint F T) (hTns : ∀ C ∈ T, 2 ≤ C.card)
    (b u : ℝ) (hb : 0 < b) (hu : 0 ≤ u)
    (hTr : ∀ C ∈ T, b ≤ radius d C) (hcard : F.card ≤ T.card)
    (hupper : F.Nonempty → radius d (F.biUnion id) < 2 * u + 2 * b) :
    (F.card : ℝ) ≤ 1 + (2 * u + 2 * b) / ((γ - 1) * b) := by
  classical
  have heps : 0 < γ - 1 := by linarith
  have hden : 0 < (γ - 1) * b := mul_pos heps hb
  by_cases hF2 : 2 ≤ F.card
  · obtain ⟨G, hGT, hGcard⟩ := Finset.exists_subset_card_eq
      (show F.card - 1 ≤ T.card by omega)
    have hcount : G.card + 1 = F.card := by omega
    have hmerge := merge_split_inequality d hd k hk γ hγ O hO F G hFO (hGT.trans hTO)
      (hFT.mono_right hGT) hF2 hcount (fun C hC => hTns C (hGT hC))
    have hcostG := lower_cost_of_radius_bound G b (fun C hC => hTr C (hGT hC))
    have hmul := mul_le_mul_of_nonneg_left hcostG heps.le
    have hnonneg := cost_nonneg hd F
    have hup := hupper (Finset.card_pos.mp (by omega))
    have hcast : (G.card : ℝ) + 1 = (F.card : ℝ) := by exact_mod_cast hcount
    have hcast' : (G.card : ℝ) = (F.card : ℝ) - 1 := by linarith
    rw [hcast'] at hmul
    have hfrac : (F.card : ℝ) - 1 ≤ (2 * u + 2 * b) / ((γ - 1) * b) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  · have hFc : (F.card : ℝ) ≤ 1 := by exact_mod_cast (show F.card ≤ 1 by omega)
    have hfrac : 0 ≤ (2 * u + 2 * b) / ((γ - 1) * b) :=
      div_nonneg (by linarith) hden.le
    linarith

lemma large_meeting_count {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (O : Partition n)
    (hO : Optimal d Finset.univ k O) (T : Partition n) (hTO : T ⊆ O)
    (R b : ℝ) (hR : 0 ≤ R) (hb : 0 < b)
    (hmax : ∀ C ∈ O, radius d C ≤ R) (hTr : ∀ C ∈ T, b ≤ radius d C)
    (x : Point n) (u : ℝ) (hu : 0 ≤ u) :
    ((meeting T (ball d x u)).card : ℝ) ≤ (u + 2 * R) / b := by
  classical
  let F := meeting T (ball d x u)
  have hsub : F ⊆ O.filter (fun C => C ⊆ ball d x (u + 2 * R)) := by
    intro C hCF
    obtain ⟨hCT, hmeet⟩ := Finset.mem_filter.mp hCF
    apply Finset.mem_filter.mpr
    refine ⟨hTO hCT, ?_⟩
    intro y hy
    obtain ⟨v, hv⟩ := hmeet
    have hvC := (Finset.mem_inter.mp hv).1
    have hxv : d x v ≤ u := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    have hvy := diameter_bound hd hvC hy
    have hrad := hmax C (hTO hCT)
    have htri := metric_triangle hd x v y
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by linarith⟩
  have hlower := lower_cost_of_radius_bound F b (fun C hC => hTr C (Finset.mem_filter.mp hC).1)
  have hcost : cost d F ≤ ∑ C ∈ O.filter (fun C => C ⊆ ball d x (u + 2 * R)), radius d C :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => radius_nonneg_all hd C)
  have hupper := contained_cluster_radii d hd k hk O hO x (u + 2 * R) (by linarith)
  apply (le_div_iff₀ hb).2
  exact hlower.trans (hcost.trans hupper)

end DensityAux

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) :
    (∀ F : Partition n, F ⊆ smallClusters d O (γ - 1) →
      (largeClusters d O (γ - 1)).card + 1 ≤ F.card →
      (γ - 1) * largeMass d O (γ - 1) < radius d (F.biUnion id)) ∧
    (∀ x : Point n, ∀ u : ℝ, 0 ≤ u → u ≤ densityScale d O (γ - 1) →
      ((meeting (smallClusters d O (γ - 1)) (ball d x u)).card : ℝ) ≤
        1 + (2 * u + 2 * smallThreshold d O (γ - 1)) /
          ((γ - 1) * smallThreshold d O (γ - 1))) ∧
    (∀ x : Point n, ∀ u : ℝ, 0 ≤ u →
      ((meeting (largeClusters d O (γ - 1)) (ball d x u)).card : ℝ) ≤
        (u + 2 * largestRadius d O) / smallThreshold d O (γ - 1)) := by
  classical
  let ε := γ - 1
  let R := largestRadius d O
  let b := smallThreshold d O ε
  let T := largeClusters d O ε
  let S := smallClusters d O ε
  let M := largeMass d O ε
  have heps : 0 < ε := by dsimp [ε]; linarith [hγ.1]
  have heps1 : ε < 1 := by dsimp [ε]; linarith [hγ.2]
  have hR : 0 < R := DensityAux.largest_pos hd hO.1 hkn
  have hbdef : b = ε * R / 4 := rfl
  have hb : 0 < b := by rw [hbdef]; exact div_pos (mul_pos heps hR) (by norm_num)
  have hbR : b < R := by
    have h := mul_lt_mul_of_pos_right heps1 hR
    rw [hbdef]
    nlinarith
  have hOne : O.Nonempty := Finset.card_pos.mp (by rw [hO.1.1]; omega)
  obtain ⟨Cmax, hCO, hCmax⟩ := DensityAux.exists_largest d hOne
  have hCmaxT : Cmax ∈ T := Finset.mem_filter.mpr ⟨hCO, by change b ≤ radius d Cmax; rw [hCmax]; exact hbR.le⟩
  have hTne : T.Nonempty := ⟨Cmax, hCmaxT⟩
  have hTO : T ⊆ O := Finset.filter_subset _ _
  have hSO : S ⊆ O := Finset.filter_subset _ _
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro C hCS hCT
    exact (not_lt_of_ge (Finset.mem_filter.mp hCT).2) (Finset.mem_filter.mp hCS).2
  have hTr : ∀ C ∈ T, b ≤ radius d C := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  have hTns : ∀ C ∈ T, 2 ≤ C.card := by
    intro C hC
    exact DensityAux.card_two_of_radius_pos hd (hO.1.2.1 C (hTO hC)) (hb.trans_le (hTr C hC))
  have hMR : R ≤ M := by
    change largestRadius d O ≤ cost d T
    rw [← hCmax]
    exact Finset.single_le_sum (fun C _ => DensityAux.radius_nonneg_all hd C) hCmaxT
  have hmany : ∀ F : Partition n, F ⊆ S → T.card + 1 ≤ F.card →
      ε * M < radius d (F.biUnion id) := by
    intro F hFS hsize
    exact DensityAux.many_union_lower d hd k hk γ hγ.1 O hO T F hTO (hFS.trans hSO)
      (hST.mono_left hFS) hTne hTns hsize
  refine ⟨hmany, ?_, ?_⟩
  · intro x u hu hρ
    let F := meeting S (ball d x u)
    have hFS : F ⊆ S := Finset.filter_subset _ _
    have hmeet : ∀ C ∈ F, (C ∩ ball d x u).Nonempty := by
      intro C hC
      exact (Finset.mem_filter.mp hC).2
    have hsmall : ∀ C ∈ F, radius d C < b := by
      intro C hC
      exact (Finset.mem_filter.mp (hFS hC)).2
    have hupper : F.Nonempty → radius d (F.biUnion id) < 2 * u + 2 * b :=
      fun hF => DensityAux.meeting_union_upper hd F hF x u b hmeet hsmall
    have hnumeric : 2 * u + 2 * b ≤ ε * M := by
      change u ≤ ε * M / 4 at hρ
      have hm := mul_le_mul_of_nonneg_left hMR heps.le
      rw [hbdef]
      nlinarith
    have hcard : F.card ≤ T.card := by
      by_contra hn
      have hbig : T.card + 1 ≤ F.card := by omega
      have hlow := hmany F hFS hbig
      have hup := hupper (Finset.card_pos.mp (by omega))
      linarith
    exact DensityAux.few_meeting_count d hd k hk γ hγ.1 O hO T F hTO (hFS.trans hSO)
      (hST.mono_left hFS) hTns b u hb hu hTr hcard hupper
  · intro x u hu
    have hid : Perturbation d γ d := by
      refine ⟨DensityAux.metric_symm hd, ?_⟩
      intro x y
      refine ⟨le_rfl, ?_⟩
      have hnonneg := DensityAux.metric_nonneg hd x y
      nlinarith [hγ.1]
    exact DensityAux.large_meeting_count d hd k hk O (hO.2 d hid).1 T hTO R b hR.le hb
      (fun C hC => DensityAux.radius_le_largest hC) hTr x u hu
