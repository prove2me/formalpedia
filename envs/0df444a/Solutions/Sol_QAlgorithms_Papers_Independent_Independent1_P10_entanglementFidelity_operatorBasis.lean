-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.entanglementFidelity_operatorBasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:38:03.804978+00:00
-- url     : https://prove2.me/submissions/949fee7c-5c0f-4765-b251-e6ce5f9a5e0c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P10
/-- Nielsen, PDF p.2, Eq. (16): entanglement fidelity in any orthogonal unitary
operator basis. Real parts transcribe the real-valued fidelity. -/
theorem gp_ef_complete (d : ℕ) (hd : 0 < d) (B : OrthogonalUnitaryOperatorBasis d)
    (a b e c : Fin d) :
    ∑ j, B.basis j a b * star (B.basis j e c) = if a = e ∧ b = c then (d : ℂ) else 0 := by
  let σ : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  let W : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := Matrix.of fun r s => B.basis (σ r) s.1 s.2
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : ((d : ℂ)⁻¹ • W.map star) * Wᵀ = 1 := by
    ext r r'
    have := B.orthogonal (σ r) (σ r')
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply] at this
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum, Matrix.transpose_apply, W, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    rw [Finset.sum_comm, this]
    simp only [σ, EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp [hd']
  have h1' : Wᵀ * ((d : ℂ)⁻¹ • W.map star) = 1 := mul_eq_one_comm.mp h1
  have h2 := congrFun (congrFun h1' (a, b)) (e, c)
  simp only [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, W, Matrix.of_apply, Matrix.one_apply, smul_eq_mul] at h2
  have h2' : (d : ℂ)⁻¹ * ∑ j, B.basis j a b * star (B.basis j e c) =
      if (a, b) = (e, c) then 1 else 0 := by
    rw [← h2, Finset.mul_sum, ← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ j, B.basis j a b * star (B.basis j e c) =
      (d : ℂ) * ((d : ℂ)⁻¹ * ∑ j, B.basis j a b * star (B.basis j e c)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hd', one_mul]
  rw [h3, h2']
  simp only [Prod.mk.injEq]
  split_ifs <;> simp

theorem gp_ef_linmap {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ, ∀ X, E X = L X := by
  obtain ⟨m, K, -, hK⟩ := hE
  refine ⟨∑ i, (LinearMap.mulLeft ℂ (K i)).comp (LinearMap.mulRight ℂ (K i)ᴴ), fun X => ?_⟩
  rw [hK]
  simp [krausApply, LinearMap.sum_apply, mul_assoc]

theorem gp_ef_lin {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    E X = ∑ a, ∑ b, X a b • E (Matrix.single a b 1) := by
  obtain ⟨L, hL⟩ := gp_ef_linmap E hE
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [hL, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem gp_ef_swap {ι α β γ δ : Type*} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : ι → α → β → γ → δ → ℂ) :
    ∑ j, ∑ c, ∑ e, ∑ a, ∑ b, f j c e a b = ∑ c, ∑ e, ∑ a, ∑ b, ∑ j, f j c e a b := by
  rw [Finset.sum_comm]; congr 1; ext c
  rw [Finset.sum_comm]; congr 1; ext e
  rw [Finset.sum_comm]; congr 1; ext a
  rw [Finset.sum_comm]

theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (B : OrthogonalUnitaryOperatorBasis d) :
    QuditFidelity.entanglementFidelity d hd E =
      (∑ j, (star (B.basis j)*E (B.basis j)).trace.re)/(d : ℝ)^3 := by
  set S : ℂ := ∑ a, ∑ b, E (Matrix.single a b 1) a b with hSdef
  have hR : ∑ j, (star (B.basis j) * E (B.basis j)).trace = (d : ℂ) * S := by
    have step : ∀ j, (star (B.basis j) * E (B.basis j)).trace =
        ∑ c, ∑ e, ∑ a, ∑ b, (B.basis j a b * star (B.basis j e c)) * E (Matrix.single a b 1) e c := by
      intro j
      rw [gp_ef_lin E hE (B.basis j)]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [step]
    rw [gp_ef_swap]
    simp only [← Finset.sum_mul, gp_ef_complete d hd B]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', hSdef, Finset.mul_sum]
    exact Finset.sum_comm
  have hRre : (∑ j, (star (B.basis j) * E (B.basis j)).trace.re) = (d : ℝ) * S.re := by
    rw [← Complex.re_sum, hR]; simp
  rw [hRre]
  unfold QuditFidelity.entanglementFidelity effectProb
  simp only [pureDensity, finiteMaxEntangled, idTensorSuperop, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fintype.card_fin]
  obtain ⟨L, hL⟩ := gp_ef_linmap E hE
  have hsm : ∀ (c : ℂ) X, E (c • X) = c • E X := fun c X => by rw [hL, hL, map_smul]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr : ((Real.sqrt d : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) ((Real.sqrt d : ℝ) : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  have hmat : ∀ x x2 : Fin d, (Matrix.of fun i i' =>
      (if x2 = i then ((Real.sqrt d : ℝ) : ℂ)⁻¹ else 0) *
        (starRingEnd ℂ) (if x = i' then ((Real.sqrt d : ℝ) : ℂ)⁻¹ else 0)) =
      (d : ℂ)⁻¹ • Matrix.single x2 x 1 := by
    intro x x2
    ext i i'
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp only [hmat, hsm]
  simp only [Matrix.smul_apply, smul_eq_mul, apply_ite (starRingEnd ℂ), map_zero, ite_mul,
    mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hr]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]
  rw [hSdef, Finset.sum_comm (f := fun a b => E (Matrix.single a b 1) a b)]
  rw [show ((d : ℂ))⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

