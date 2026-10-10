-- Prove2me | solution 1 for ThomsonProblem.thomson_seven
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-09T23:57:17.952826+00:00
-- url     : https://prove2.me/submissions/cbf1ee56-d8ce-437b-8624-9077bc4d9515

import Definitions.Def_ThomsonProblem_defs
import Theorems.Thm_ThomsonProblem_N7_case_one
import Theorems.Thm_ThomsonProblem_N7_cap
import Theorems.Thm_ThomsonProblem_N7_slab_s99_98
import Theorems.Thm_ThomsonProblem_N7_slab_s98_96
import Theorems.Thm_ThomsonProblem_N7_slab_s96_94
import Theorems.Thm_ThomsonProblem_N7_slab_s94_93
import Theorems.Thm_ThomsonProblem_N7_slab_s93_90

namespace ThomsonProblem.N7Reduction

open ThomsonProblem

/-- With Lean's convention `1 / 0 = 0` the diagonal terms vanish, so the energy is half of the
full double sum. -/
lemma two_mul_coulombEnergy {N : ℕ} (x : Fin N → Space) :
    2 * coulombEnergy x = ∑ i, ∑ j, 1 / dist (x i) (x j) := by
  unfold coulombEnergy
  have key : ∀ i, ∑ j, 1 / dist (x i) (x j)
      = ∑ j ∈ Finset.Ioi i, 1 / dist (x i) (x j) + ∑ j ∈ Finset.Iio i, 1 / dist (x i) (x j) := by
    intro i
    have h1 : (Finset.univ : Finset (Fin N)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [h1, Finset.sum_union, Finset.sum_union]
    · simp
    · simp
    · rw [Finset.disjoint_left]; intro a ha; simp at ha ⊢; omega
  simp_rw [key, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, 1 / dist (x i) (x j)
      = ∑ i, ∑ j ∈ Finset.Ioi i, 1 / dist (x i) (x j) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp at hp ⊢; exact hp
    · intro p hp; simp at hp ⊢; exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [dist_comm]
  rw [hswap]; ring

lemma coulombEnergy_comp_perm {N : ℕ} (x : Fin N → Space) (σ : Equiv.Perm (Fin N)) :
    coulombEnergy (x ∘ σ) = coulombEnergy x := by
  have h1 := two_mul_coulombEnergy (x ∘ σ)
  have h2 := two_mul_coulombEnergy x
  have h3 : ∑ i, ∑ j, 1 / dist ((x ∘ σ) i) ((x ∘ σ) j) = ∑ i, ∑ j, 1 / dist (x i) (x j) := by
    simp only [Function.comp]
    rw [Equiv.sum_comp σ (fun i => ∑ j, 1 / dist (x i) (x (σ j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp σ (fun j => 1 / dist (x i) (x j))
  linarith

lemma isAdmissible_comp_perm {N : ℕ} {x : Fin N → Space} (hx : IsAdmissible x)
    (σ : Equiv.Perm (Fin N)) : IsAdmissible (x ∘ σ) :=
  ⟨fun i => hx.1 (σ i), hx.2.comp σ.injective⟩

/-- A permutation of `Fin 7` sending `0 ↦ i` and `1 ↦ j` for any `i ≠ j`. -/
lemma exists_perm_zero_one {i j : Fin 7} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 7), σ 0 = i ∧ σ 1 = j := by
  have hj'0 : Equiv.swap 0 i j ≠ 0 := by
    intro h
    have h2 := congrArg (Equiv.swap 0 i) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact hij h2.symm
  refine ⟨(Equiv.swap 0 i) * (Equiv.swap 1 (Equiv.swap 0 i j)), ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj'0), Equiv.swap_apply_left]
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Every admissible configuration can be relabelled so that the pair `(0, 1)` realises the
smallest inner product. -/
lemma exists_minimal_pair_relabel (y : Fin 7 → Space) :
    ∃ σ : Equiv.Perm (Fin 7),
      ∀ i j, i ≠ j → inner ℝ ((y ∘ σ) 0) ((y ∘ σ) 1) ≤ inner ℝ ((y ∘ σ) i) ((y ∘ σ) j) := by
  let S : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hS : S.Nonempty := ⟨(0, 1), by simp [S]⟩
  obtain ⟨p, hpS, hpmin⟩ := S.exists_min_image (fun p => inner ℝ (y p.1) (y p.2)) hS
  have hp : p.1 ≠ p.2 := by simpa [S] using hpS
  obtain ⟨σ, h0, h1⟩ := exists_perm_zero_one hp
  refine ⟨σ, fun i j hij => ?_⟩
  simp only [Function.comp, h0, h1]
  exact hpmin (σ i, σ j) (by simpa [S] using σ.injective.ne hij)

lemma pentagonVertex_norm (k : ℕ) : ‖pentagonVertex k‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [pentagonVertex, Real.cos_sq_add_sin_sq]

lemma pentagonVertex_dist_sq (k l : ℕ) :
    ‖pentagonVertex k - pentagonVertex l‖ ^ 2
      = 2 - 2 * Real.cos (2 * Real.pi * k / 5 - 2 * Real.pi * l / 5) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [pentagonVertex, PiLp.sub_apply, Real.norm_eq_abs, sq_abs,
    Real.cos_sub]
  simp
  nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * k / 5),
    Real.cos_sq_add_sin_sq (2 * Real.pi * l / 5)]

lemma pentagonVertex_injOn {k l : ℕ} (hk : k < 5) (hl : l < 5)
    (h : pentagonVertex k = pentagonVertex l) : k = l := by
  have h2 := pentagonVertex_dist_sq k l
  rw [h, sub_self, norm_zero] at h2
  have hc : Real.cos (2 * Real.pi * ((k : ℤ) - l) / 5) = 1 := by
    have : 2 * Real.pi * ((k : ℤ) - l : ℤ) / 5 = 2 * Real.pi * k / 5 - 2 * Real.pi * l / 5 := by
      push_cast; ring
    rw [show ((k : ℤ) - l : ℝ) = (((k : ℤ) - l : ℤ) : ℝ) by push_cast; ring, this]
    linarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) * 5 = (k : ℝ) - l := by
    push_cast at hn
    field_simp at hn
    nlinarith
  have h3 : n * 5 = (k : ℤ) - l := by exact_mod_cast h1
  omega

lemma pentagonVertex_ne_pole (k : ℕ) (c : ℝ) (hc : c ≠ 0) :
    pentagonVertex k ≠ !₂[0, 0, c] := by
  intro h
  have := congrArg (fun v : Space => v 2) h
  simp [pentagonVertex] at this
  exact hc this.symm

lemma pentagonalBipyramid_isAdmissible : IsAdmissible pentagonalBipyramid := by
  constructor
  · intro i
    fin_cases i
    · simp [pentagonalBipyramid, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    · simp [pentagonalBipyramid, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    all_goals exact pentagonVertex_norm _
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [pentagonalBipyramid] at hij ⊢ <;>
      first
        | (norm_num at hij; done)
        | exact absurd hij (pentagonVertex_ne_pole _ _ (by norm_num))
        | exact absurd hij.symm (pentagonVertex_ne_pole _ _ (by norm_num))
        | exact absurd hij (Ne.symm (pentagonVertex_ne_pole _ _ (by norm_num)))
        | exact absurd (pentagonVertex_injOn (by norm_num) (by norm_num) hij) (by norm_num)

end ThomsonProblem.N7Reduction

open ThomsonProblem ThomsonProblem.N7Reduction in
theorem solution : ThomsonProblem.IsEnergyMinimizer ThomsonProblem.pentagonalBipyramid := by
  refine ⟨pentagonalBipyramid_isAdmissible, fun y hy => ?_⟩
  obtain ⟨σ, hmin⟩ := exists_minimal_pair_relabel y
  have hz := isAdmissible_comp_perm hy σ
  rw [← coulombEnergy_comp_perm y σ]
  set z := y ∘ σ
  set m := inner ℝ (z 0) (z 1) with hm
  by_cases h1 : (-9 / 10 : ℝ) ≤ m
  · have := N7.case_one z hz (fun i j hij => h1.trans (hmin i j hij))
    linarith
  by_cases h2 : m ≤ -99 / 100
  · exact N7.cap z hz h2 hmin
  push Not at h1 h2
  by_cases h3 : m ≤ -49 / 50
  · exact (N7.slab_s99_98 z hz h2.le h3 hmin).le
  push Not at h3
  by_cases h4 : m ≤ -24 / 25
  · exact (N7.slab_s98_96 z hz h3.le h4 hmin).le
  push Not at h4
  by_cases h5 : m ≤ -47 / 50
  · exact (N7.slab_s96_94 z hz h4.le h5 hmin).le
  push Not at h5
  by_cases h6 : m ≤ -93 / 100
  · exact (N7.slab_s94_93 z hz h5.le h6 hmin).le
  push Not at h6
  exact (N7.slab_s93_90 z hz h6.le h1.le hmin).le
