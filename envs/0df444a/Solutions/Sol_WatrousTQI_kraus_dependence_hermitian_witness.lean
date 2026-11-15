-- Prove2me | solution 1 for WatrousTQI.kraus_dependence_hermitian_witness
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:06:24.288605+00:00
-- url     : https://prove2.me/submissions/90a001a1-11fb-4d43-8394-a4b5aac0fffa

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace WatrousCriterionAux20261112
lemma hermitian_kernel_vector (m : ℕ)
    (S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ))
    (hs : ∀ C ∈ S, Cᴴ ∈ S) (C : Matrix (Fin m) (Fin m) ℂ) (hC : C ∈ S) (hn : C ≠ 0) :
    ∃ H : Matrix (Fin m) (Fin m) ℂ, H.IsHermitian ∧ H ≠ 0 ∧ H ∈ S := by
  have hr : (realPart C : Matrix (Fin m) (Fin m) ℂ) ∈ S := by
    rw [realPart_apply_coe]
    exact S.smul_of_tower_mem _ (S.add_mem hC (hs C hC))
  have hi : (imaginaryPart C : Matrix (Fin m) (Fin m) ℂ) ∈ S := by
    rw [imaginaryPart_apply_coe]
    exact S.smul_mem _ (S.smul_of_tower_mem _ (S.sub_mem hC (hs C hC)))
  by_cases hR : (realPart C : Matrix (Fin m) (Fin m) ℂ) = 0
  · refine ⟨imaginaryPart C,(imaginaryPart C).property,?_,hi⟩
    intro hI
    apply hn
    have hh := realPart_add_I_smul_imaginaryPart C
    rw [hR,hI,smul_zero,add_zero] at hh
    exact hh.symm
  · exact ⟨realPart C,(realPart C).property,hR,hr⟩
end WatrousCriterionAux20261112


set_option autoImplicit false


theorem solution {dx dy m : ℕ}
    (hdx : 0 < dx) (hdy : 0 < dy) (hm : 0 < m)
    (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ)
    (hdep : ¬ LinearIndependent ℂ (fun ab : Fin m × Fin m => (A ab.2)ᴴ * A ab.1)) :
    ∃ H : Matrix (Fin m) (Fin m) ℂ,
      H.IsHermitian ∧ H ≠ 0 ∧ ∑ a, ∑ b, H a b • ((A b)ᴴ * A a) = 0 := by
  classical
  let L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin dx) (Fin dx) ℂ :=
    { toFun := fun C => ∑ a, ∑ b, C a b • ((A b)ᴴ * A a)
      map_add' := by intro C D; simp [add_smul,Finset.sum_add_distrib]
      map_smul' := by intro c C; simp [Finset.smul_sum,smul_smul] }
  have hs : ∀ C ∈ LinearMap.ker L, Cᴴ ∈ LinearMap.ker L := by
    intro C hC
    change L C = 0 at hC
    have h := congrArg Matrix.conjTranspose hC
    change (∑ a, ∑ b, C a b • ((A b)ᴴ * A a))ᴴ = 0ᴴ at h
    simp only [Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
    change (∑ a, ∑ b, Cᴴ a b • ((A b)ᴴ * A a)) = 0
    rw [Finset.sum_comm] at h
    simpa only [Matrix.conjTranspose_apply,Complex.star_def] using h
  rw [Fintype.linearIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨c,hc,i,hi⟩ := hdep
  let C : Matrix (Fin m) (Fin m) ℂ := fun a b => c (a,b)
  have hC : C ∈ LinearMap.ker L := by
    change (∑ a, ∑ b, c (a,b) • ((A b)ᴴ * A a)) = 0
    simpa only [Fintype.sum_prod_type] using hc
  have hn : C ≠ 0 := by
    intro he
    apply hi
    exact congrFun (congrFun he i.1) i.2
  obtain ⟨H,hH,hnH,hLH⟩ := WatrousCriterionAux20261112.hermitian_kernel_vector m (LinearMap.ker L) hs C hC hn
  exact ⟨H,hH,hnH,hLH⟩
