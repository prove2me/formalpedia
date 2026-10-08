-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.pbe_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:48:26.010981+00:00
-- url     : https://prove2.me/submissions/596e2752-7528-4efb-a5a5-fee720d3fe08

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace PBEgrad0002

lemma muNormSq_eq {S : Type} [Fintype S] [DecidableEq S] (μ : S → ℝ) (v : S → ℝ) :
    SuttonBartoRL.OffPolicy.muNormSq μ v = v ⬝ᵥ (SuttonBartoRL.OffPolicy.Dmat μ *ᵥ v) := by
  unfold SuttonBartoRL.OffPolicy.muNormSq SuttonBartoRL.OffPolicy.Dmat
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma core {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (μ : S → ℝ)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * diagonal μ * X).det) (δ : S → ℝ) :
    ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ δ) ⬝ᵥ
        (diagonal μ *ᵥ ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ δ))
      = (Xᵀ *ᵥ (diagonal μ *ᵥ δ)) ⬝ᵥ ((Xᵀ * diagonal μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (diagonal μ *ᵥ δ))) := by
  set G := Xᵀ * diagonal μ * X with hGdef
  set u := Xᵀ *ᵥ (diagonal μ *ᵥ δ) with hu
  set y := G⁻¹ *ᵥ u with hy
  have hPi : (X * G⁻¹ * Xᵀ * diagonal μ) *ᵥ δ = X *ᵥ y := by
    simp only [hy, hu, mulVec_mulVec, Matrix.mul_assoc]
  have hGy : G *ᵥ y = u := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hX, one_mulVec]
  rw [hPi]
  have : (X *ᵥ y) ⬝ᵥ (diagonal μ *ᵥ (X *ᵥ y)) = y ⬝ᵥ (G *ᵥ y) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    simp only [hGdef, mulVec_mulVec, Matrix.mul_assoc]
  rw [this, hGy, dotProduct_comm]

open SuttonBartoRL.OffPolicy in
lemma bellmanOp_affine {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (v : S → ℝ) :
    bellmanOp M π γ v = bellmanOp M π γ 0 + γ • (policyTrans M π *ᵥ v) := by
  funext s
  simp only [bellmanOp, policyTrans, MDP.trans, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mulVec, dotProduct, Pi.zero_apply, mul_zero, add_zero, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

open SuttonBartoRL.OffPolicy in
lemma bellmanError_affine {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ)
    (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) :
    bellmanError M π γ X w = bellmanOp M π γ 0 + (γ • (policyTrans M π * X) - X) *ᵥ w := by
  unfold bellmanError vw
  rw [bellmanOp_affine, sub_mulVec, smul_mulVec, ← mulVec_mulVec]
  abel

/-- derivative of a quadratic form of an affine map -/
lemma quad_hasFDerivAt {d : ℕ} (k : Fin d → ℝ) (K N : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun w => (k + K *ᵥ w) ⬝ᵥ (N *ᵥ (k + K *ᵥ w))) L w ∧
      ∀ u, L u = (K *ᵥ u) ⬝ᵥ (N *ᵥ (k + K *ᵥ w)) + (k + K *ᵥ w) ⬝ᵥ (N *ᵥ (K *ᵥ u)) := by
  let Kc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' K)
  let Hc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' (N * K))
  have hKc : ∀ u, Kc u = K *ᵥ u := fun u => by simp [Kc]
  have hHc : ∀ u, Hc u = (N * K) *ᵥ u := fun u => by simp [Hc]
  have hg : HasFDerivAt (fun w => k + K *ᵥ w) Kc w := by
    have := (Kc.hasFDerivAt (x := w)).const_add k
    simpa [hKc] using this
  have hh : HasFDerivAt (fun w => N *ᵥ (k + K *ᵥ w)) Hc w := by
    have := (Hc.hasFDerivAt (x := w)).const_add (N *ᵥ k)
    have e : (fun w => N *ᵥ (k + K *ᵥ w)) = fun x => N *ᵥ k + Hc x := by
      funext v
      simp [hHc, mulVec_add, mulVec_mulVec]
    rw [e]
    exact this
  have hsum : HasFDerivAt (fun w => ∑ i, (k + K *ᵥ w) i * (N *ᵥ (k + K *ᵥ w)) i)
      (∑ i, ((k + K *ᵥ w) i • (ContinuousLinearMap.proj i).comp Hc
        + (N *ᵥ (k + K *ᵥ w)) i • (ContinuousLinearMap.proj i).comp Kc)) w := by
    apply HasFDerivAt.fun_sum
    intro i _
    have h1 := (hasFDerivAt_apply i (k + K *ᵥ w)).comp w hg
    have h2 := (hasFDerivAt_apply i (N *ᵥ (k + K *ᵥ w))).comp w hh
    exact h1.mul h2
  refine ⟨_, hsum, fun u => ?_⟩
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, hKc, hHc, ← mulVec_mulVec]
  simp only [dotProduct, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

end PBEgrad0002

open SuttonBartoRL.OffPolicy Matrix in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (w : Fin d → ℝ) :
    PBE M π γ μ X w
        = (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w)) ⬝ᵥ
            ((Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) ∧
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasFDerivAt (PBE M π γ μ X) L w ∧
      ∀ u : Fin d → ℝ,
        L u = ((2 : ℝ) • ((γ • (policyTrans M π * X) - X)ᵀ * Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹)
                *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) ⬝ᵥ u := by
  have hval : ∀ v, PBE M π γ μ X v
      = (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X v)) ⬝ᵥ
          ((Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X v))) := by
    intro v
    have h := PBEgrad0002.core μ X hX (bellmanError M π γ X v)
    unfold PBE projMatrix
    rw [PBEgrad0002.muNormSq_eq]
    simpa only [Dmat] using h
  refine ⟨hval w, ?_⟩
  set Bm := γ • (policyTrans M π * X) - X with hBm
  set G := Xᵀ * Dmat μ * X with hG
  set c := bellmanOp M π γ 0 with hc
  set k := Xᵀ *ᵥ (Dmat μ *ᵥ c) with hk
  set K := Xᵀ * Dmat μ * Bm with hK
  have hf : ∀ v, Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X v) = k + K *ᵥ v := by
    intro v
    rw [PBEgrad0002.bellmanError_affine]
    simp only [hk, hK, hc, hBm, mulVec_mulVec, mulVec_add, Matrix.mul_assoc]
  have hfun : PBE M π γ μ X = fun v => (k + K *ᵥ v) ⬝ᵥ (G⁻¹ *ᵥ (k + K *ᵥ v)) := by
    funext v
    rw [hval v, hf v]
  obtain ⟨L, hL, hLu⟩ := PBEgrad0002.quad_hasFDerivAt k K G⁻¹ w
  refine ⟨L, hfun ▸ hL, fun u => ?_⟩
  rw [hLu u, hf w]
  have hDT : (Dmat μ)ᵀ = Dmat μ := by simp [Dmat]
  have hGT : Gᵀ = G := by
    simp only [hG, transpose_mul, transpose_transpose, hDT, Matrix.mul_assoc]
  have hGiT : (G⁻¹)ᵀ = G⁻¹ := by rw [transpose_nonsing_inv, hGT]
  set y := k + K *ᵥ w
  -- both terms equal u ⬝ᵥ (Kᵀ *ᵥ (G⁻¹ *ᵥ y))
  have e1 : (K *ᵥ u) ⬝ᵥ (G⁻¹ *ᵥ y) = (Kᵀ *ᵥ (G⁻¹ *ᵥ y)) ⬝ᵥ u := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have e2 : y ⬝ᵥ (G⁻¹ *ᵥ (K *ᵥ u)) = (Kᵀ *ᵥ (G⁻¹ *ᵥ y)) ⬝ᵥ u := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hGiT, dotProduct_mulVec, ← mulVec_transpose]
  rw [e1, e2, ← add_dotProduct]
  congr 1
  rw [two_smul]
  congr 1 <;>
  · rw [hK, transpose_mul, transpose_mul, hDT, mulVec_mulVec]
    simp only [Matrix.mul_assoc, transpose_transpose]
