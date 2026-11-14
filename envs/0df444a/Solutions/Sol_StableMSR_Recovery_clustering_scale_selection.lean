-- Prove2me | solution 1 for StableMSR.Recovery.clustering_scale_selection
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:49:27.07867+00:00
-- url     : https://prove2.me/submissions/79c11a17-f771-4314-9e74-42a95ee1c899

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_StableMSR_Recovery_Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Base

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

namespace StableMSR.Recovery

/- The deterministic few-cluster alternative in Lemma A.4. -/
theorem few_bound_of_densityScale_lt (ε R M : ℝ) (t : ℕ)
    (hε : 0 < ε) (hR : 0 < R)
    (ht : (t : ℝ) * (ε * R / 4) ≤ M)
    (hscale : ε * M / 4 < sigma * R) : t ≤ fewBound ε := by
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hm := mul_le_mul_of_nonneg_left ht hε.le
  have htR : R * ((t : ℝ) * ε ^ 2) < R * (16 * sigma) := by
    nlinarith
  have htε : (t : ℝ) * ε ^ 2 < 16 * sigma :=
    (mul_lt_mul_iff_right₀ hR).mp (by simpa [mul_comm] using htR)
  have hreal : (t : ℝ) < 16 * sigma / ε ^ 2 := (lt_div_iff₀ he2).2 htε
  have hceil : (t : ℝ) ≤ (⌈16 * sigma / ε ^ 2⌉₊ : ℝ) :=
    hreal.le.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/- The deterministic dyadic-scale alternative in Lemma A.4. The upper index
is exactly the finite scale list used by Algorithm 1. -/
theorem dyadic_scale_selection (ε R M : ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 0 < R)
    (hM : M ≤ (n : ℝ) * R)
    (hscale : sigma * R ≤ ε * M / 4) :
    ∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * R ≤ (2 : ℝ) ^ j * R ∧
      (2 : ℝ) ^ j * R ≤ ε * M / 4 ∧
      ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) ∧
      M / ((2 : ℝ) ^ j * R) < 8 / ε := by
  have hsig : sigma = 512 := rfl
  have hρ : 0 < ε * M / 4 := by rw [hsig] at hscale; nlinarith
  have hMpos : 0 < M := by
    by_contra h
    have hm0 : ε * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt h)
    linarith
  have hratio : 1 ≤ (ε * M / 4) / R := by
    apply (le_div_iff₀ hR).2
    rw [hsig] at hscale
    nlinarith
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hj9 : 9 ≤ j := by
    by_contra h
    have hjpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ 9 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h512 : (512 : ℝ) ≤ (ε * M / 4) / R := by
      apply (le_div_iff₀ hR).2
      simpa [sigma] using hscale
    norm_num at hjpow
    linarith
  have hL : 0 < (2 : ℝ) ^ j * R := by positivity
  have hjLlo : (2 : ℝ) ^ j * R ≤ ε * M / 4 := (le_div_iff₀ hR).mp hjlo
  have hjLhi : ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) := by
    have hh := (div_lt_iff₀ hR).mp hjhi
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
  have hρn : ε * M / 4 < (n : ℝ) * R := by
    have hp := mul_pos hMpos (sub_pos.mpr hε1)
    nlinarith
  have hjn : (2 : ℝ) ^ j < (n : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    simpa [mul_comm] using hjLlo.trans_lt hρn
  have hjlog : (j : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (show 0 < (2 : ℝ) ^ j by positivity) hjn.le
    simpa [Real.logb_pow] using hh
  have hjceil : j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ := by
    exact_mod_cast hjlog.trans (Nat.le_ceil _)
  refine ⟨j, hj9, hjceil, ?_, hjLlo, hjLhi, ?_⟩
  · have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj9
    norm_num at hpow
    simpa [sigma] using mul_le_mul_of_nonneg_right hpow hR.le
  · apply (div_lt_div_iff₀ hL hε).2
    nlinarith

/- Lemma A.4's deterministic case distinction, independent of the random
partition routine and therefore requiring no probability hypothesis. -/
theorem scale_selection_alternatives (ε R M : ℝ) (n t : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 0 < R)
    (ht : (t : ℝ) * (ε * R / 4) ≤ M)
    (hM : M ≤ (n : ℝ) * R) :
    (ε * M / 4 < sigma * R ∧ t ≤ fewBound ε) ∨
    (∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * R ≤ (2 : ℝ) ^ j * R ∧
      (2 : ℝ) ^ j * R ≤ ε * M / 4 ∧
      ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) ∧
      M / ((2 : ℝ) ^ j * R) < 8 / ε) := by
  rcases lt_or_ge (ε * M / 4) (sigma * R) with h | h
  · exact Or.inl ⟨h, few_bound_of_densityScale_lt ε R M t hε hR ht h⟩
  · exact Or.inr (dyadic_scale_selection ε R M n hε hε1 hR hM h)


/- The mass bounds used by Lemma A.4 follow from feasibility alone. -/
theorem large_mass_bounds {n k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (O : Partition n) (hO : Feasible Finset.univ k O)
    (hkn : k < n) (ε : ℝ) :
    ((largeClusters d O ε).card : ℝ) * (ε * largestRadius d O / 4) ≤
      largeMass d O ε ∧
    largeMass d O ε ≤ (n : ℝ) * largestRadius d O := by
  classical
  let T := largeClusters d O ε
  have hTO : T ⊆ O := Finset.filter_subset _ _
  have hcard : T.card ≤ n := by
    have hh := Finset.card_le_card hTO
    rw [hO.1] at hh
    omega
  have hR : 0 < largestRadius d O := DensityAux.largest_pos hd hO hkn
  constructor
  · change (T.card : ℝ) * (ε * largestRadius d O / 4) ≤ ∑ C ∈ T, radius d C
    calc
      (T.card : ℝ) * (ε * largestRadius d O / 4) =
          ∑ _C ∈ T, ε * largestRadius d O / 4 := by simp
      _ ≤ ∑ C ∈ T, radius d C := by
        apply Finset.sum_le_sum
        intro C hC
        exact (Finset.mem_filter.mp hC).2
  · change (∑ C ∈ T, radius d C) ≤ (n : ℝ) * largestRadius d O
    calc
      (∑ C ∈ T, radius d C) ≤ ∑ _C ∈ T, largestRadius d O := by
        exact Finset.sum_le_sum (fun C hC => DensityAux.radius_le_largest (hTO hC))
      _ = (T.card : ℝ) * largestRadius d O := by simp
      _ ≤ (n : ℝ) * largestRadius d O := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hR.le

/- Lemma A.4, deterministic alternatives, instantiated with the canonical
clustering scales. No stability hypothesis is needed for this numerical step. -/
end StableMSR.Recovery

open StableMSR.Recovery

theorem solution {n k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (O : Partition n) (hO : Feasible Finset.univ k O)
    (hkn : k < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (densityScale d O ε < sigma * largestRadius d O ∧
      (largeClusters d O ε).card ≤ fewBound ε) ∨
    (∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * largestRadius d O ≤ (2 : ℝ) ^ j * largestRadius d O ∧
      (2 : ℝ) ^ j * largestRadius d O ≤ densityScale d O ε ∧
      densityScale d O ε < 2 * ((2 : ℝ) ^ j * largestRadius d O) ∧
      largeMass d O ε / ((2 : ℝ) ^ j * largestRadius d O) < 8 / ε) := by
  obtain ⟨ht, hM⟩ := large_mass_bounds d hd O hO hkn ε
  exact scale_selection_alternatives ε (largestRadius d O) (largeMass d O ε)
    n (largeClusters d O ε).card hε hε1 (DensityAux.largest_pos hd hO hkn) ht hM

