-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P10.cloning_classical_environment
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:55:59.864188+00:00
-- url     : https://prove2.me/submissions/20fbe84c-5830-463d-bc06-7aac563564ea

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace Aux_P10_cloning

open QAlgorithms QAlgorithms.Papers.Independent.Intakethird100.P10

theorem repr {m : ℕ} (basis : Matrix.unitaryGroup (Fin m) ℂ) (c : Fin m → ℂ) (σ : Fin m ≃ Fin m) :
    ∑ i, c i • pureDensity (basisColumn basis (σ i))
      = (basis : Matrix (Fin m) (Fin m) ℂ) * Matrix.diagonal (fun k => c (σ.symm k)) *
        (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, pureDensity, basisColumn, Matrix.of_apply,
    PiLp.toLp_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Equiv.symm_apply_apply, Complex.star_def]
  ring

theorem weights (m : ℕ) (hm : 0 < m) :
    ∑ i : Fin m, (((i.val + 1 : ℝ) / cloningNormalization m : ℝ) : ℂ) = 1 := by
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hN : 0 < cloningNormalization m := by
    unfold cloningNormalization
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  rw [← Complex.ofReal_sum, ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) + 1) m, hsum]
  unfold cloningNormalization at hN ⊢
  rw [div_self hN.ne', Complex.ofReal_one]

end Aux_P10_cloning

open QAlgorithms QAlgorithms.Papers.Independent.Intakethird100.P10 in
theorem solution (m : ℕ) (hm : 0 < m)
    (basis : Matrix.unitaryGroup (Fin m) ℂ) :
    IsBinaryCQ (cloningEnvironment m basis) ∧
    Commute (cloningEnvironment m basis false) (cloningEnvironment m basis true) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin m → ℂ, c = fun i => (((i.val + 1 : ℝ) / cloningNormalization m : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hN : 0 < cloningNormalization m := by
    unfold cloningNormalization
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i; rw [hc]
    exact Complex.zero_le_real.mpr (by positivity)
  have hcsum : ∑ i, c i = 1 := by rw [hc]; exact Aux_P10_cloning.weights m hm
  have hUU : (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ * (basis : Matrix (Fin m) (Fin m) ℂ) = 1 := by
    have := Unitary.star_mul_self_of_mem basis.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hW : ∀ x, ∃ σ : Fin m ≃ Fin m,
      cloningEnvironment m basis x = (basis : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal (fun k => c (σ.symm k)) * (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
    intro x
    cases x
    · refine ⟨Equiv.refl _, ?_⟩
      rw [← Aux_P10_cloning.repr basis c (Equiv.refl _)]
      unfold cloningEnvironment
      rw [hc]
      simp
    · refine ⟨Fin.revPerm, ?_⟩
      rw [← Aux_P10_cloning.repr basis c Fin.revPerm]
      unfold cloningEnvironment
      rw [hc]
      simp
  have hdens : ∀ σ : Fin m ≃ Fin m,
      IsDensityMatrix ((basis : Matrix (Fin m) (Fin m) ℂ) * Matrix.diagonal (fun k => c (σ.symm k)) *
        (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ) := by
    intro σ
    refine ⟨(Matrix.posSemidef_diagonal_iff.mpr fun k => hc0 _).mul_mul_conjTranspose_same _, ?_⟩
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal,
      Equiv.sum_comp σ.symm c, hcsum]
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := hW x
    rw [hσ]
    exact hdens σ
  · obtain ⟨σ1, h1⟩ := hW false
    obtain ⟨σ2, h2⟩ := hW true
    rw [h1, h2]
    have hD : Matrix.diagonal (fun k => c (σ1.symm k)) * Matrix.diagonal (fun k => c (σ2.symm k))
        = Matrix.diagonal (fun k => c (σ2.symm k)) * Matrix.diagonal (fun k => c (σ1.symm k)) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      ring
    show _ * _ = _ * _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ (basis : Matrix (Fin m) (Fin m) ℂ),
      hUU, Matrix.one_mul,
      ← Matrix.mul_assoc (basis : Matrix (Fin m) (Fin m) ℂ)ᴴ (basis : Matrix (Fin m) (Fin m) ℂ),
      hUU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal (fun k => c (σ1.symm k))), hD,
      Matrix.mul_assoc]
