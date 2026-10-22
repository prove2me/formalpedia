-- Prove2me | solution 1 for RegMCBSDE.Simulation.eq_28_29_least_squares
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:36:17.450497+00:00
-- url     : https://prove2.me/submissions/89ba6447-509b-4dbe-8c55-7821343430a2

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting

set_option autoImplicit false
open RegMCBSDE.Simulation

lemma ls_V_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (v : Fin M → ι → ℝ)
    (d : ι → ℝ) :
    ((1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)).mulVec d
      = (1 / (M : ℝ)) • ∑ s, (v s ⬝ᵥ d) • v s := by
  funext i
  simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

lemma ls_Q {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (v : Fin M → ι → ℝ) (d : ι → ℝ) :
    d ⬝ᵥ (((1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)).mulVec d)
      = (1 / (M : ℝ)) * ∑ s, (d ⬝ᵥ v s) ^ 2 := by
  rw [ls_V_mulVec, dotProduct_smul, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dotProduct_comm (v s) d]; ring

lemma ls_J {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (v : Fin M → ι → ℝ)
    (r : Fin M → ℝ) (d : ι → ℝ) :
    (1 / (M : ℝ)) * ∑ s, (r s - d ⬝ᵥ v s) ^ 2
      = (1 / (M : ℝ)) * ∑ s, r s ^ 2 - 2 * (d ⬝ᵥ ((1 / (M : ℝ)) • ∑ s, r s • v s))
        + d ⬝ᵥ (((1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)).mulVec d) := by
  rw [ls_Q, dotProduct_smul, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  have : ∑ s, (r s - d ⬝ᵥ v s) ^ 2 = ∑ s, r s ^ 2 - 2 * ∑ s, r s * (d ⬝ᵥ v s)
      + ∑ s, (d ⬝ᵥ v s) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [this]
  ring

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : 0 < M)
    (v : Fin M → ι → ℝ)
    (hV : ((1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)).PosDef) :
    let V : Matrix ι ι ℝ := (1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)
    let empSq : (Fin M → ℝ) → ℝ := fun y => (1 / (M : ℝ)) * ∑ s, y s ^ 2
    let θ : (Fin M → ℝ) → (ι → ℝ) := fun x => V⁻¹.mulVec ((1 / (M : ℝ)) • ∑ s, x s • v s)
    (∀ x : Fin M → ℝ, ∀ θ' : ι → ℝ, θ' ≠ θ x →
        empSq (fun s => x s - θ x ⬝ᵥ v s) < empSq (fun s => x s - θ' ⬝ᵥ v s)) ∧
    (∀ (a b : ℝ) (x y : Fin M → ℝ), θ (a • x + b • y) = a • θ x + b • θ y) ∧
    (∀ (c : ℝ), (∀ y : ι → ℝ, c * sqn y ≤ y ⬝ᵥ V.mulVec y) → ∀ x : Fin M → ℝ,
        c * sqn (θ x) ≤ empSq (fun s => θ x ⬝ᵥ v s) ∧ empSq (fun s => θ x ⬝ᵥ v s) ≤ empSq x) := by
  intro V empSq θ
  have hU : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hVθ : ∀ x, V.mulVec (θ x) = (1 / (M : ℝ)) • ∑ s, x s • v s := by
    intro x
    simp only [θ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hU, Matrix.one_mulVec]
  have hres : ∀ x, (1 / (M : ℝ)) • ∑ s, (x s - θ x ⬝ᵥ v s) • v s = 0 := by
    intro x
    have h1 : V.mulVec (θ x) = (1 / (M : ℝ)) • ∑ s, (v s ⬝ᵥ θ x) • v s := ls_V_mulVec M v (θ x)
    have h2 : (1 / (M : ℝ)) • ∑ s, (x s - θ x ⬝ᵥ v s) • v s
        = (1 / (M : ℝ)) • ∑ s, x s • v s - (1 / (M : ℝ)) • ∑ s, (v s ⬝ᵥ θ x) • v s := by
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sub_smul, dotProduct_comm (θ x) (v s)]
    rw [h2, ← h1, hVθ x, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · intro x θ' hne
    have hd : θ' - θ x ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < (θ' - θ x) ⬝ᵥ (V.mulVec (θ' - θ x)) := by
      have := hV.dotProduct_mulVec_pos hd
      rw [star_trivial] at this
      exact this
    have hJ := ls_J M v (fun s => x s - θ x ⬝ᵥ v s) (θ' - θ x)
    rw [hres x] at hJ
    have hx : ∀ s, x s - θ' ⬝ᵥ v s = (x s - θ x ⬝ᵥ v s) - (θ' - θ x) ⬝ᵥ v s := by
      intro s; rw [sub_dotProduct]; ring
    have key : empSq (fun s => x s - θ' ⬝ᵥ v s)
        = empSq (fun s => x s - θ x ⬝ᵥ v s) + (θ' - θ x) ⬝ᵥ (V.mulVec (θ' - θ x)) := by
      show (1 / (M : ℝ)) * ∑ s, (x s - θ' ⬝ᵥ v s) ^ 2 = _ + _
      simp_rw [hx]
      rw [hJ]
      simp only [dotProduct_zero]
      show _ = (1 / (M : ℝ)) * ∑ s, (x s - θ x ⬝ᵥ v s) ^ 2 + _
      ring
    rw [key]
    linarith
  · intro a b x y
    simp only [θ]
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
    congr 1
    funext i
    simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul, mul_assoc, mul_left_comm]
  · intro c hc x
    have hQ : empSq (fun s => θ x ⬝ᵥ v s) = θ x ⬝ᵥ (V.mulVec (θ x)) := (ls_Q M v (θ x)).symm
    refine ⟨by rw [hQ]; exact hc (θ x), ?_⟩
    have hJ := ls_J M v (fun s => x s - θ x ⬝ᵥ v s) (-θ x)
    rw [hres x] at hJ
    have hx : ∀ s, x s = (x s - θ x ⬝ᵥ v s) - (-θ x) ⬝ᵥ v s := by
      intro s; rw [neg_dotProduct]; ring
    have key : empSq x = empSq (fun s => x s - θ x ⬝ᵥ v s) + θ x ⬝ᵥ (V.mulVec (θ x)) := by
      show (1 / (M : ℝ)) * ∑ s, x s ^ 2 = _ + _
      have e : ∑ s, x s ^ 2 = ∑ s, ((x s - θ x ⬝ᵥ v s) - (-θ x) ⬝ᵥ v s) ^ 2 :=
        Finset.sum_congr rfl fun s _ => by rw [← hx s]
      rw [e, hJ]
      simp only [dotProduct_zero, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
      show _ = (1 / (M : ℝ)) * ∑ s, (x s - θ x ⬝ᵥ v s) ^ 2 + _
      ring
    have hnn : 0 ≤ empSq (fun s => x s - θ x ⬝ᵥ v s) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hQ, key]
    linarith
