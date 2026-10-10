-- Prove2me | solution 1 for ThomsonProblem.N7.cap
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:07:16.34937+00:00
-- url     : https://prove2.me/submissions/8c8f3498-bb0a-4b7f-9fb5-f1711e2a6bf2

import Mathlib
import Definitions.Def_ThomsonProblem_defs
import Definitions.Def_ThomsonN7_core
import Theorems.Thm_ThomsonN7_Final_capspec_cap
import Theorems.Thm_ThomsonN7_Glue_capSpec_sound

open Real

namespace ThomsonN7.PlatformBridge

lemma two_mul_energy {N : ℕ} (x : Fin N → R3) :
    2 * coulombEnergy x = ∑ i, ∑ j, ‖x i - x j‖⁻¹ := by
  unfold coulombEnergy
  have key : ∀ i, ∑ j, ‖x i - x j‖⁻¹
      = ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ + ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹ := by
    intro i
    have h1 : (Finset.univ : Finset (Fin N)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [h1, Finset.sum_union, Finset.sum_union]
    · simp
    · simp
    · rw [Finset.disjoint_left]; intro a ha; simp at ha ⊢; omega
  simp_rw [key, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹
      = ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp at hp ⊢; exact hp
    · intro p hp; simp at hp ⊢; exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [norm_sub_rev]
  rw [hswap]; ring

lemma energy_comp_perm {N : ℕ} (x : Fin N → R3) (σ : Equiv.Perm (Fin N)) :
    coulombEnergy (x ∘ σ) = coulombEnergy x := by
  have h1 := two_mul_energy (x ∘ σ)
  have h2 := two_mul_energy x
  have h3 : ∑ i, ∑ j, ‖(x ∘ σ) i - (x ∘ σ) j‖⁻¹ = ∑ i, ∑ j, ‖x i - x j‖⁻¹ := by
    simp only [Function.comp]
    rw [Equiv.sum_comp σ (fun i => ∑ j, ‖x i - x (σ j)‖⁻¹)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp σ (fun j => ‖x i - x j‖⁻¹)
  linarith

/-- The two Coulomb energies agree. -/
lemma energy_eq {N : ℕ} (y : Fin N → R3) :
    ThomsonProblem.coulombEnergy y = coulombEnergy y := by
  unfold ThomsonProblem.coulombEnergy coulombEnergy
  simp [dist_eq_norm]

lemma admissible_iff {N : ℕ} (y : Fin N → R3) :
    ThomsonProblem.IsAdmissible y ↔ y ∈ SphereConfig N := Iff.rfl

/-- Relabelling of the repository's bipyramid into the platform's ordering. -/
def relabel : Equiv.Perm (Fin 7) where
  toFun := ![5, 6, 0, 1, 2, 3, 4]
  invFun := ![2, 3, 4, 5, 6, 0, 1]
  left_inv := by decide
  right_inv := by decide

lemma pent_eq : ThomsonProblem.pentagonalBipyramid = pentBipyramid ∘ relabel := by
  funext i
  fin_cases i <;>
    simp [ThomsonProblem.pentagonalBipyramid, ThomsonProblem.pentagonVertex, pentBipyramid,
      relabel, cyl]

lemma pent_energy_eq :
    ThomsonProblem.coulombEnergy ThomsonProblem.pentagonalBipyramid
      = coulombEnergy pentBipyramid := by
  rw [energy_eq, pent_eq, energy_comp_perm]

end ThomsonN7.PlatformBridge

open ThomsonProblem in
theorem solution : ∀ y : Fin 7 → Space, IsAdmissible y → inner ℝ (y 0) (y 1) ≤ -99 / 100 →
    (∀ i j, i ≠ j → inner ℝ (y 0) (y 1) ≤ inner ℝ (y i) (y j)) →
    coulombEnergy pentagonalBipyramid ≤ coulombEnergy y := by
  intro y hy hle hmin
  rw [ThomsonN7.PlatformBridge.pent_energy_eq, ThomsonN7.PlatformBridge.energy_eq]
  exact (ThomsonN7.Glue.capSpec_sound ThomsonN7.Final.capspec_cap y hy hle hmin).1
