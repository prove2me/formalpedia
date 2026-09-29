-- Prove2me | solution 1 for RobustLS.Structured.worst_case_residual_sq_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:48:08.980227+00:00
-- url     : https://prove2.me/submissions/87857d84-c7cd-48db-ab0e-d66a003ce396

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

lemma aux_wcrq_eucNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v ^ 2 = v ⬝ᵥ v := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]
  simp [dotProduct, sq]

lemma aux_wcrq_resid_vec {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) :
    structMatrix A0 A δ *ᵥ x - structVector b0 b δ = (A0 *ᵥ x - b0) + Mx A b x *ᵥ δ := by
  unfold structMatrix structVector
  rw [Matrix.add_mulVec, Matrix.sum_mulVec]
  ext k
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply,
    smul_eq_mul, Mx, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [show ∀ a c d e : ℝ, a + c - (d + e) = a - d + (c - e) by intros; ring]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma aux_wcrq_quad {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) :
    oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) =
      structuredResidual A0 A b0 b x δ ^ 2 := by
  unfold structuredResidual
  rw [aux_wcrq_eucNorm_sq, aux_wcrq_resid_vec]
  set r0 := A0 *ᵥ x - b0 with hr0
  set M := Mx A b x with hM
  unfold hgFBlock oneStack
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  have h1 : (Sum.elim (fun _ : Unit => (1:ℝ)) δ ∘ Sum.inl) = fun _ => 1 := rfl
  have h2 : (Sum.elim (fun _ : Unit => (1:ℝ)) δ ∘ Sum.inr) = δ := rfl
  rw [h1, h2]
  have hg : gvec A0 A b0 b x = Mᵀ *ᵥ r0 := rfl
  have hF : Fmat A b x = Mᵀ * M := rfl
  have hh : hval A0 b0 x = r0 ⬝ᵥ r0 := by
    unfold hval; rw [aux_wcrq_eucNorm_sq]
  rw [hF, hh]
  have e1 : (fun _ : Unit => (1:ℝ)) ⬝ᵥ ((Matrix.of fun _ _ => r0 ⬝ᵥ r0 : Matrix Unit Unit ℝ)
      *ᵥ (fun _ => 1) + (Matrix.of fun _ j => gvec A0 A b0 b x j : Matrix Unit (Fin p) ℝ) *ᵥ δ)
      = r0 ⬝ᵥ r0 + gvec A0 A b0 b x ⬝ᵥ δ := by
    simp [dotProduct, Matrix.mulVec]
  have e2 : δ ⬝ᵥ ((Matrix.of fun i _ => gvec A0 A b0 b x i : Matrix (Fin p) Unit ℝ)
      *ᵥ (fun _ => 1) + (Mᵀ * M) *ᵥ δ) = δ ⬝ᵥ gvec A0 A b0 b x + δ ⬝ᵥ ((Mᵀ * M) *ᵥ δ) := by
    rw [dotProduct_add]
    congr 1
    simp [dotProduct, Matrix.mulVec]
  rw [e1, e2, hg]
  have e3 : (Mᵀ *ᵥ r0) ⬝ᵥ δ = r0 ⬝ᵥ (M *ᵥ δ) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have e4 : δ ⬝ᵥ (Mᵀ *ᵥ r0) = r0 ⬝ᵥ (M *ᵥ δ) := by
    rw [dotProduct_comm, e3]
  have e5 : δ ⬝ᵥ ((Mᵀ * M) *ᵥ δ) = (M *ᵥ δ) ⬝ᵥ (M *ᵥ δ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
  rw [e3, e4, e5]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (M *ᵥ δ) r0]

end RobustLS.Structured

open RobustLS.Structured

open Matrix

theorem solution {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 →
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ rS A0 A b0 b 1 x ^ 2) ∧
      ∃ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 ∧
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) = rS A0 A b0 b 1 x ^ 2 := by
  -- the ball
  have hball : ∀ δ : Fin p → ℝ, eucNorm δ ≤ 1 ↔ δ ⬝ᵥ δ ≤ 1 := by
    intro δ
    rw [← aux_wcrq_eucNorm_sq]
    constructor
    · intro h
      have h0 : 0 ≤ eucNorm δ := Real.sqrt_nonneg _
      nlinarith
    · intro h
      have h0 : 0 ≤ eucNorm δ := Real.sqrt_nonneg _
      nlinarith
  set K : Set (Fin p → ℝ) := {δ | δ ⬝ᵥ δ ≤ 1} with hK
  have hKc : IsCompact K := by
    have hsub : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
      intro δ hδ i _
      simp only [hK, Set.mem_ofPred_eq, dotProduct] at hδ
      have hi : δ i * δ i ≤ ∑ j, δ j * δ j :=
        Finset.single_le_sum (f := fun j => δ j * δ j) (fun j _ => mul_self_nonneg (δ j))
          (Finset.mem_univ i)
      constructor <;> nlinarith
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc)) ?_ hsub
    exact isClosed_le (by fun_prop) continuous_const
  have hKne : K.Nonempty := ⟨0, by simp [hK]⟩
  have hcont : Continuous (fun δ => structuredResidual A0 A b0 b x δ) := by
    unfold structuredResidual eucNorm structMatrix structVector
    fun_prop
  obtain ⟨δs, hδsK, hmax⟩ := hKc.exists_isMaxOn hKne hcont.continuousOn
  set S := {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧ r = structuredResidual A0 A b0 b x δ}
    with hS
  have hrS : rS A0 A b0 b 1 x = structuredResidual A0 A b0 b x δs := by
    unfold rS
    rw [← hS]
    apply IsGreatest.csSup_eq
    refine ⟨⟨δs, (hball δs).2 hδsK, rfl⟩, ?_⟩
    rintro r ⟨δ, hδ, rfl⟩
    exact hmax ((hball δ).1 hδ)
  have hnn : ∀ δ, 0 ≤ structuredResidual A0 A b0 b x δ := fun δ => Real.sqrt_nonneg _
  refine ⟨fun δ hδ => ?_, ⟨δs, hδsK, ?_⟩⟩
  · rw [aux_wcrq_quad, hrS]
    have := hmax (show δ ∈ K from hδ)
    exact pow_le_pow_left₀ (hnn δ) this 2
  · rw [aux_wcrq_quad, hrS]
