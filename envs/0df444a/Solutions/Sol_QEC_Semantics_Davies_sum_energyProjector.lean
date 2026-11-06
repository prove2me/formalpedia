-- Prove2me | solution 1 for QEC.Semantics.Davies.sum_energyProjector
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T11:34:45.825425+00:00
-- url     : https://prove2.me/submissions/b8f60241-d71c-4f9b-8d91-8fe53ecb36f5

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma energyProjector_apply_basis (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (E : ℝ) (k : ι) :
    energyProjector b energy E (b k) = if energy k = E then b k else 0 := by
  simp only [energyProjector, LinearMap.sum_apply]
  rw [Finset.sum_eq_single k]
  · by_cases h : energy k = E
    · simp [h, matrixUnit, InnerProductSpace.rankOne_apply, b.inner_eq_ite]
    · simp [h]
  · intro j _ hjk
    by_cases h : energy j = E
    · simp [h, matrixUnit, InnerProductSpace.rankOne_apply, b.inner_eq_ite, hjk]
    · simp [h]
  · simp

private lemma sum_energyProjector_apply_basis (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (k : ι) :
    (∑ E ∈ energyValues energy, energyProjector b energy E) (b k) = b k := by
  simp only [LinearMap.sum_apply, energyProjector_apply_basis]
  have hk : energy k ∈ energyValues energy := (mem_energyValues energy _).mpr ⟨k, rfl⟩
  have : (∑ E ∈ energyValues energy, if energy k = E then b k else (0 : V)) =
      ∑ E ∈ energyValues energy, if E = energy k then b k else 0 := by
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases h : energy k = E
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Finset.sum_ite_eq', if_pos hk]

theorem solution (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) :
    (∑ E ∈ energyValues energy, energyProjector b energy E) = 1 := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_energyProjector_apply_basis]
  rfl
