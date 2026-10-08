-- Prove2me | solution 1 for ThomsonProblem.thomson_six
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:57:32.477467+00:00
-- url     : https://prove2.me/submissions/9c243880-332d-43a0-bf64-afdddc10dea0

import Mathlib
import Definitions.Def_ThomsonProblem_defs

set_option maxHeartbeats 1000000

lemma ptwise_6078810e (d : ℝ) (hd : 0 < d) (hd2 : d ≤ 2) :
    Real.sqrt 2 / 2 + Real.sqrt 2 / 4 * (1 - d ^ 2 / 2)
      + (1 / 2 - Real.sqrt 2 / 4) * (1 - d ^ 2 / 2) ^ 2 ≤ 1 / d := by
  set r := Real.sqrt 2 with hrdef
  have hr : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := by positivity
  have hr2 : r < 2 := by nlinarith
  have key : 1 - (r / 2 + r / 4 * (1 - d ^ 2 / 2) + (1 / 2 - r / 4) * (1 - d ^ 2 / 2) ^ 2) * d
      = (d - r) ^ 2 * (2 - d) * ((2 - r) / 16 * d ^ 2 + r / 8 * d + 1 / 4) := by
    linear_combination ((-1/2 : ℝ) + 1/4 * d + 1/4 * d^2 - 3/8 * d^3 + 1/8 * d^4
      - 1/4 * r * d + 1/4 * r * d^2 - 1/16 * r * d^3) * hr
  have hq : 0 ≤ (2 - r) / 16 * d ^ 2 + r / 8 * d + 1 / 4 := by
    have : 0 ≤ (2 - r) / 16 * d ^ 2 := by
      apply mul_nonneg; linarith; positivity
    have : 0 ≤ r / 8 * d := by positivity
    linarith
  have hprod : 0 ≤ (d - r) ^ 2 * (2 - d) * ((2 - r) / 16 * d ^ 2 + r / 8 * d + 1 / 4) := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hq
  rw [le_div_iff₀ hd]
  linarith

lemma pairsum_6078810e (f : Fin 6 → Fin 6 → ℝ) :
    ∑ i : Fin 6, ∑ j ∈ Finset.Ioi i, f i j =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 + f 1 2 + f 1 3 + f 1 4 + f 1 5
      + f 2 3 + f 2 4 + f 2 5 + f 3 4 + f 3 5 + f 4 5 := by
  have h0 : Finset.Ioi (0 : Fin 6) = {1, 2, 3, 4, 5} := by decide
  have h1 : Finset.Ioi (1 : Fin 6) = {2, 3, 4, 5} := by decide
  have h2 : Finset.Ioi (2 : Fin 6) = {3, 4, 5} := by decide
  have h3 : Finset.Ioi (3 : Fin 6) = {4, 5} := by decide
  have h4 : Finset.Ioi (4 : Fin 6) = {5} := by decide
  have h5 : Finset.Ioi (5 : Fin 6) = ∅ := by decide
  simp [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]
  ring

lemma qq_6078810e (P Q R : ℝ) (h : P + Q + R = 6) : 12 ≤ P ^ 2 + Q ^ 2 + R ^ 2 := by
  nlinarith [sq_nonneg (P - Q), sq_nonneg (Q - R), sq_nonneg (P - R)]

lemma gram_id_6078810e (a b c : Fin 6 → ℝ) :
    2 * ((a 0 * a 1 + b 0 * b 1 + c 0 * c 1) ^ 2 + (a 0 * a 2 + b 0 * b 2 + c 0 * c 2) ^ 2
            + (a 0 * a 3 + b 0 * b 3 + c 0 * c 3) ^ 2 + (a 0 * a 4 + b 0 * b 4 + c 0 * c 4) ^ 2
            + (a 0 * a 5 + b 0 * b 5 + c 0 * c 5) ^ 2 + (a 1 * a 2 + b 1 * b 2 + c 1 * c 2) ^ 2
            + (a 1 * a 3 + b 1 * b 3 + c 1 * c 3) ^ 2 + (a 1 * a 4 + b 1 * b 4 + c 1 * c 4) ^ 2
            + (a 1 * a 5 + b 1 * b 5 + c 1 * c 5) ^ 2 + (a 2 * a 3 + b 2 * b 3 + c 2 * c 3) ^ 2
            + (a 2 * a 4 + b 2 * b 4 + c 2 * c 4) ^ 2 + (a 2 * a 5 + b 2 * b 5 + c 2 * c 5) ^ 2
            + (a 3 * a 4 + b 3 * b 4 + c 3 * c 4) ^ 2 + (a 3 * a 5 + b 3 * b 5 + c 3 * c 5) ^ 2
            + (a 4 * a 5 + b 4 * b 5 + c 4 * c 5) ^ 2)
          + ((a 0 ^ 2 + b 0 ^ 2 + c 0 ^ 2) ^ 2 + (a 1 ^ 2 + b 1 ^ 2 + c 1 ^ 2) ^ 2
          + (a 2 ^ 2 + b 2 ^ 2 + c 2 ^ 2) ^ 2 + (a 3 ^ 2 + b 3 ^ 2 + c 3 ^ 2) ^ 2
          + (a 4 ^ 2 + b 4 ^ 2 + c 4 ^ 2) ^ 2 + (a 5 ^ 2 + b 5 ^ 2 + c 5 ^ 2) ^ 2)
          = (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2) ^ 2
            + (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 + b 4 ^ 2 + b 5 ^ 2) ^ 2
            + (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 + c 4 ^ 2 + c 5 ^ 2) ^ 2
            + 2 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4 + a 5 * b 5) ^ 2
            + 2 * (a 0 * c 0 + a 1 * c 1 + a 2 * c 2 + a 3 * c 3 + a 4 * c 4 + a 5 * c 5) ^ 2
            + 2 * (b 0 * c 0 + b 1 * c 1 + b 2 * c 2 + b 3 * c 3 + b 4 * c 4 + b 5 * c 5) ^ 2 := by
  ring

lemma poly_gram_6078810e (a b c : Fin 6 → ℝ) (h : ∀ i, a i ^ 2 + b i ^ 2 + c i ^ 2 = 1)
    (t : Fin 6 → Fin 6 → ℝ) (ht : ∀ i j, t i j = a i * a j + b i * b j + c i * c j) :
    -3 ≤ ∑ i : Fin 6, ∑ j ∈ Finset.Ioi i, t i j ∧
      3 ≤ ∑ i : Fin 6, ∑ j ∈ Finset.Ioi i, (t i j) ^ 2 := by
  rw [pairsum_6078810e, pairsum_6078810e]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [ht]
  constructor
  · have id1 : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5) ^ 2 + (b 0 + b 1 + b 2 + b 3 + b 4 + b 5) ^ 2
        + (c 0 + c 1 + c 2 + c 3 + c 4 + c 5) ^ 2
        = (a 0 ^ 2 + b 0 ^ 2 + c 0 ^ 2) + (a 1 ^ 2 + b 1 ^ 2 + c 1 ^ 2)
          + (a 2 ^ 2 + b 2 ^ 2 + c 2 ^ 2) + (a 3 ^ 2 + b 3 ^ 2 + c 3 ^ 2)
          + (a 4 ^ 2 + b 4 ^ 2 + c 4 ^ 2) + (a 5 ^ 2 + b 5 ^ 2 + c 5 ^ 2)
          + 2 * ((a 0 * a 1 + b 0 * b 1 + c 0 * c 1) + (a 0 * a 2 + b 0 * b 2 + c 0 * c 2)
            + (a 0 * a 3 + b 0 * b 3 + c 0 * c 3) + (a 0 * a 4 + b 0 * b 4 + c 0 * c 4)
            + (a 0 * a 5 + b 0 * b 5 + c 0 * c 5) + (a 1 * a 2 + b 1 * b 2 + c 1 * c 2)
            + (a 1 * a 3 + b 1 * b 3 + c 1 * c 3) + (a 1 * a 4 + b 1 * b 4 + c 1 * c 4)
            + (a 1 * a 5 + b 1 * b 5 + c 1 * c 5) + (a 2 * a 3 + b 2 * b 3 + c 2 * c 3)
            + (a 2 * a 4 + b 2 * b 4 + c 2 * c 4) + (a 2 * a 5 + b 2 * b 5 + c 2 * c 5)
            + (a 3 * a 4 + b 3 * b 4 + c 3 * c 4) + (a 3 * a 5 + b 3 * b 5 + c 3 * c 5)
            + (a 4 * a 5 + b 4 * b 5 + c 4 * c 5)) := by ring
    rw [h0, h1, h2, h3, h4, h5] at id1
    nlinarith [sq_nonneg (a 0 + a 1 + a 2 + a 3 + a 4 + a 5),
      sq_nonneg (b 0 + b 1 + b 2 + b 3 + b 4 + b 5), sq_nonneg (c 0 + c 1 + c 2 + c 3 + c 4 + c 5)]
  · have id2 := gram_id_6078810e a b c
    rw [h0, h1, h2, h3, h4, h5] at id2
    have hPQR := qq_6078810e (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2)
      (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 + b 4 ^ 2 + b 5 ^ 2)
      (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 + c 4 ^ 2 + c 5 ^ 2) (by linarith)
    have hX2 := sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4 + a 5 * b 5)
    have hY2 := sq_nonneg (a 0 * c 0 + a 1 * c 1 + a 2 * c 2 + a 3 * c 3 + a 4 * c 4 + a 5 * c 5)
    have hZ2 := sq_nonneg (b 0 * c 0 + b 1 * c 1 + b 2 * c 2 + b 3 * c 3 + b 4 * c 4 + b 5 * c 5)
    linarith

open ThomsonProblem in
lemma inner_coord_6078810e (u v : Space) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

open ThomsonProblem in
lemma norm_coord_6078810e (u : Space) (h : ‖u‖ = 1) : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
  have h1 := real_inner_self_eq_norm_sq u
  rw [h, inner_coord_6078810e] at h1
  nlinarith [h1]

open ThomsonProblem in
lemma ypt_6078810e (u v : Space) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne : u ≠ v) :
    Real.sqrt 2 / 2 + Real.sqrt 2 / 4 * inner ℝ u v
      + (1 / 2 - Real.sqrt 2 / 4) * (inner ℝ u v) ^ 2 ≤ 1 / dist u v := by
  have hd : 0 < dist u v := dist_pos.mpr hne
  have hd2 : dist u v ≤ 2 := by
    rw [dist_eq_norm]
    calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
      _ = 2 := by rw [hu, hv]; norm_num
  have hsq : dist u v ^ 2 = 2 - 2 * inner ℝ u v := by
    rw [dist_eq_norm, norm_sub_sq_real, hu, hv]; ring
  have ht : inner ℝ u v = 1 - dist u v ^ 2 / 2 := by linarith
  rw [ht]
  exact ptwise_6078810e _ hd hd2

open ThomsonProblem in
lemma oct_energy_6078810e :
    coulombEnergy regularOctahedron = 6 * Real.sqrt 2 + 3 / 2 := by
  rw [ThomsonProblem.coulombEnergy, pairsum_6078810e]
  simp [ThomsonProblem.regularOctahedron, EuclideanSpace.dist_eq, Fin.sum_univ_three, Real.dist_eq]
  have h4 : Real.sqrt (1 + 1) = Real.sqrt 2 := by norm_num
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  rw [h4]
  field_simp
  norm_num
  nlinarith

open ThomsonProblem in
lemma oct_norm_6078810e (i : Fin 6) : ‖regularOctahedron i‖ = 1 := by
  fin_cases i <;> simp [regularOctahedron, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open ThomsonProblem in
theorem solution : IsEnergyMinimizer regularOctahedron := by
  refine ⟨⟨oct_norm_6078810e, ?_⟩, fun y hy => ?_⟩
  · intro i j hij
    have h0 := congrArg (fun v : Space => v 0) hij
    have h1 := congrArg (fun v : Space => v 1) hij
    have h2 := congrArg (fun v : Space => v 2) hij
    fin_cases i <;> fin_cases j <;> simp [regularOctahedron] at h0 h1 h2 ⊢ <;> linarith
  · obtain ⟨hn, hinj⟩ := hy
    rw [oct_energy_6078810e]
    set g : Fin 6 → Fin 6 → ℝ := fun i j => Real.sqrt 2 / 2 + Real.sqrt 2 / 4 * inner ℝ (y i) (y j)
      + (1 / 2 - Real.sqrt 2 / 4) * (inner ℝ (y i) (y j)) ^ 2 with hg
    have hle : ∑ i : Fin 6, ∑ j ∈ Finset.Ioi i, g i j ≤ coulombEnergy y := by
      unfold coulombEnergy
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
      exact ypt_6078810e _ _ (hn i) (hn j) (fun h => hij (hinj h))
    have hgr := poly_gram_6078810e (fun i => y i 0) (fun i => y i 1) (fun i => y i 2)
      (fun i => norm_coord_6078810e _ (hn i)) (fun i j => inner ℝ (y i) (y j))
      (fun i j => inner_coord_6078810e _ _)
    obtain ⟨hS1, hS2⟩ := hgr
    rw [pairsum_6078810e] at hle hS1 hS2
    simp only [hg] at hle
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hp : 0 < Real.sqrt 2 := by positivity
    have hp2 : Real.sqrt 2 < 2 := by nlinarith
    have m1 := mul_le_mul_of_nonneg_left hS1 (le_of_lt hp)
    have m2 := mul_le_mul_of_nonneg_left hS2 (show 0 ≤ 1 / 2 - Real.sqrt 2 / 4 by linarith)
    linarith
