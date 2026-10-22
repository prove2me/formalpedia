-- Prove2me | solution 1 for SubSuperStoch.SuperSpec.eigenvalue_pow_le_normInf
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:00.223313+00:00
-- url     : https://prove2.me/submissions/6b730d1c-0022-4613-bc5c-c72f38575512

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

set_option autoImplicit false
open scoped Matrix.Norms.Operator

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    ∀ μ ∈ SubSuperStoch.SubSpec.specC A, ‖μ‖ ^ m ≤ SubSuperStoch.SubSpec.normInf (A ^ m) := by
  intro μ hμ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    unfold SubSuperStoch.SubSpec.specC at hμ
    rw [spectrum.mem_iff] at hμ
    exact hμ (isUnit_of_subsingleton _)
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    set Ac : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ) with hAc
    have h1 : μ ^ m ∈ spectrum ℂ (Ac ^ m) := by
      have := spectrum.subset_polynomial_aeval Ac (Polynomial.X ^ m : Polynomial ℂ)
      have h := this ⟨μ, hμ, rfl⟩
      simpa using h
    have h2 : ‖μ ^ m‖ ≤ ‖Ac ^ m‖ := spectrum.norm_le_norm_of_mem h1
    have h3 : Ac ^ m = (A ^ m).map (algebraMap ℝ ℂ) := by
      have := map_pow (algebraMap ℝ ℂ).mapMatrix A m
      simpa [hAc] using this.symm
    rw [norm_pow, h3, Matrix.linfty_opNorm_def] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n)) Finset.univ_nonempty
      (fun i : Fin n => ∑ j : Fin n, ‖((A ^ m).map (algebraMap ℝ ℂ)) i j‖₊)
    rw [hi] at h2
    refine h2.trans ?_
    unfold SubSuperStoch.SubSpec.normInf
    have : ((∑ j : Fin n, ‖((A ^ m).map (algebraMap ℝ ℂ)) i j‖₊ : NNReal) : ℝ) = ∑ j, |(A ^ m) i j| := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Matrix.map_apply]
    rw [this]
    exact le_ciSup (f := fun i : Fin n => ∑ j, |(A ^ m) i j|) (Set.finite_range _).bddAbove i
