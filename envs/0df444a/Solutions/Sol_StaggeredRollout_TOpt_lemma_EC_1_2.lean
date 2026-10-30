-- Prove2me | solution 1 for StaggeredRollout.TOpt.lemma_EC_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:04:31.418698+00:00
-- url     : https://prove2.me/submissions/3b23edb9-3e12-4a29-be23-8c320d5d7361

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting
import Definitions.Def_StaggeredRollout_TOpt_Quadratic

open Matrix StaggeredRollout.TOpt

namespace EC12Aux

/-- `1 + UᵀU` is positive definite. -/
lemma M_posDef {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) :
    (1 + Uᵀ * U : Matrix (Fin du) (Fin du) ℝ).PosDef := by
  have h2 := posSemidef_conjTranspose_mul_self U
  rw [conjTranspose_eq_transpose_of_trivial] at h2
  exact PosDef.one.add_posSemidef h2

lemma M_det {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) :
    IsUnit (1 + Uᵀ * U : Matrix (Fin du) (Fin du) ℝ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (M_posDef U).isUnit

/-- Woodbury: `Ψ⁻¹ = σ⁻² (I − U (I + UᵀU)⁻¹ Uᵀ)` when `Σ_v = σ² I`. -/
lemma psi_inv {N du : ℕ} (sig2 : ℝ) (hsig : 0 < sig2) (U : Matrix (Fin N) (Fin du) ℝ) :
    (Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹
      = sig2⁻¹ • (1 - U * (1 + Uᵀ * U)⁻¹ * Uᵀ) := by
  apply Matrix.inv_eq_right_inv
  unfold Psi
  have hM := mul_nonsing_inv (1 + Uᵀ * U) (M_det U)
  have hs : sig2 ≠ 0 := hsig.ne'
  have e1 : U * (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)) * Uᵀ + sig2 • (1 : Matrix (Fin N) (Fin N) ℝ)
      = sig2 • (U * Uᵀ + 1) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_add]
  rw [e1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have e2 : (U * Uᵀ + 1) * (1 - U * (1 + Uᵀ * U)⁻¹ * Uᵀ)
      = U * Uᵀ + 1 - U * ((1 + Uᵀ * U) * (1 + Uᵀ * U)⁻¹) * Uᵀ := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  rw [e2, hM, Matrix.mul_one]
  abel


/-- `Ψ` is positive definite. -/
lemma psi_posDef {N du : ℕ} (sig2 : ℝ) (hsig : 0 < sig2) (U : Matrix (Fin N) (Fin du) ℝ) :
    (Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ))).PosDef := by
  unfold Psi
  have h1 : (sig2 • (1 : Matrix (Fin N) (Fin N) ℝ)).PosDef := by
    have := (PosDef.one (n := Fin N) (R := ℝ)).smul hsig
    exact this
  have h2 : (U * (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)) * Uᵀ).PosSemidef := by
    have h3 : (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)).PosSemidef := h0.posSemidef
    have := h3.mul_mul_conjTranspose_same U
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact h1.posSemidef_add h2
where h0 : (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)).PosDef := (PosDef.one (n := Fin du) (R := ℝ)).smul hsig

lemma q_nonneg {N du : ℕ} (sig2 : ℝ) (hsig : 0 < sig2) (U : Matrix (Fin N) (Fin du) ℝ)
    (x : Fin N → ℝ) :
    0 ≤ x ⬝ᵥ ((Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ *ᵥ x) := by
  have := (psi_posDef sig2 hsig U).inv.posSemidef.dotProduct_mulVec_nonneg x
  simpa using this

noncomputable def BB {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  U * (1 + Uᵀ * U)⁻¹ * Uᵀ

lemma q_formula {N du : ℕ} (sig2 : ℝ) (hsig : 0 < sig2) (U : Matrix (Fin N) (Fin du) ℝ)
    (x : Fin N → ℝ) :
    x ⬝ᵥ ((Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ *ᵥ x)
      = sig2⁻¹ * (x ⬝ᵥ x - x ⬝ᵥ (BB U *ᵥ x)) := by
  rw [psi_inv sig2 hsig U, smul_mulVec, sub_mulVec, one_mulVec, dotProduct_smul, dotProduct_sub,
    smul_eq_mul]
  rfl

lemma BB_apply {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) (x : Fin N → ℝ) :
    BB U *ᵥ x = U *ᵥ ((1 + Uᵀ * U)⁻¹ *ᵥ (Uᵀ *ᵥ x)) := by
  unfold BB; rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

lemma dot_U {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) (y : Fin N → ℝ) (w : Fin du → ℝ) :
    y ⬝ᵥ (U *ᵥ w) = (Uᵀ *ᵥ y) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma BB_kill {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) (x y : Fin N → ℝ)
    (hy : Uᵀ *ᵥ y = 0) : (x + y) ⬝ᵥ (BB U *ᵥ (x + y)) = x ⬝ᵥ (BB U *ᵥ x) := by
  rw [BB_apply, BB_apply, mulVec_add, hy, add_zero, add_dotProduct, dot_U U y, hy, zero_dotProduct,
    add_zero]

/-- Normal equations of least squares are solvable. -/
lemma normal_eq {N dx : ℕ} (X : Matrix (Fin N) (Fin dx) ℝ) (v : Fin N → ℝ) :
    ∃ c : Fin dx → ℝ, Xᵀ *ᵥ (v - X *ᵥ c) = 0 := by
  have hle : LinearMap.range (Xᵀ * X).mulVecLin ≤ LinearMap.range Xᵀ.mulVecLin := by
    rintro _ ⟨c, rfl⟩
    exact ⟨X *ᵥ c, by simp [mulVec_mulVec]⟩
  have hrank : Module.finrank ℝ (LinearMap.range (Xᵀ * X).mulVecLin)
      = Module.finrank ℝ (LinearMap.range Xᵀ.mulVecLin) := by
    have h1 := rank_transpose_mul_self X
    have h2 := rank_transpose X
    unfold Matrix.rank at h1 h2
    rw [h1, h2]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : Xᵀ *ᵥ v ∈ LinearMap.range (Xᵀ * X).mulVecLin := by
    rw [heq]; exact ⟨v, rfl⟩
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  simp only [mulVecLin_apply] at hc
  rw [mulVec_sub, mulVec_mulVec, hc, sub_self]

lemma ls_inf {N dx : ℕ} (X : Matrix (Fin N) (Fin dx) ℝ) (v : Fin N → ℝ) (c0 : Fin dx → ℝ)
    (hc0 : Xᵀ *ᵥ (v - X *ᵥ c0) = 0) :
    (⨅ c : Fin dx → ℝ, (v - X *ᵥ c) ⬝ᵥ (v - X *ᵥ c)) = (v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0) := by
  have key : ∀ c, (v - X *ᵥ c) ⬝ᵥ (v - X *ᵥ c)
      = (v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0) + (X *ᵥ (c0 - c)) ⬝ᵥ (X *ᵥ (c0 - c)) := by
    intro c
    have e : v - X *ᵥ c = (v - X *ᵥ c0) + X *ᵥ (c0 - c) := by
      rw [mulVec_sub]; abel
    rw [e, add_dotProduct, dotProduct_add, dotProduct_add]
    have h0 : (v - X *ᵥ c0) ⬝ᵥ (X *ᵥ (c0 - c)) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hc0, zero_dotProduct]
    rw [h0, dotProduct_comm (X *ᵥ (c0 - c)) (v - X *ᵥ c0), h0]
    ring
  have hnn : ∀ c, (v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0) ≤ (v - X *ᵥ c) ⬝ᵥ (v - X *ᵥ c) := by
    intro c; rw [key c]
    have : 0 ≤ (X *ᵥ (c0 - c)) ⬝ᵥ (X *ᵥ (c0 - c)) := by
      simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    linarith
  apply le_antisymm
  · exact ciInf_le ⟨(v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0), by rintro _ ⟨c, rfl⟩; exact hnn c⟩ c0
  · exact le_ciInf hnn


lemma per_s {N dx du : ℕ} (hN : 0 < N) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (v : Fin N → ℝ) (c0 : Fin dx → ℝ) (hc0 : Xᵀ *ᵥ (v - X *ᵥ c0) = 0) (β : ℝ) (θ : Fin dx → ℝ) :
    (v - (fun _ => β) - X *ᵥ θ) ⬝ᵥ
        ((Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ *ᵥ (v - (fun _ => β) - X *ᵥ θ))
      = sig2⁻¹ * ((v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0) - (∑ i, v i) ^ 2 / N - v ⬝ᵥ (BB U *ᵥ v)
          + ((fun _ => (∑ i, v i) / N - β) + X *ᵥ (c0 - θ)) ⬝ᵥ ((fun _ => (∑ i, v i) / N - β) + X *ᵥ (c0 - θ))) := by
  set one : Fin N → ℝ := fun _ => 1 with hone
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set bs : ℝ := (∑ i, v i) / N with hbs
  have hX1 : Xᵀ *ᵥ one = 0 := by
    funext k; simp [mulVec, dotProduct, one, hXc k]
  have hU1 : Uᵀ *ᵥ one = 0 := by
    funext k; simp [mulVec, dotProduct, one, hUc k]
  have hUX : ∀ c, Uᵀ *ᵥ (X *ᵥ c) = 0 := by
    intro c
    have : Uᵀ * X = 0 := by
      have := congrArg Matrix.transpose hXU
      simpa [Matrix.transpose_mul] using this
    rw [mulVec_mulVec, this, zero_mulVec]
  have hconst : ∀ a : ℝ, (fun _ : Fin N => a) = a • one := by
    intro a; funext i; simp [one]
  set vp := v - bs • one - X *ᵥ c0 with hvp
  set y := (fun _ : Fin N => bs - β) + X *ᵥ (c0 - θ) with hy
  have hsplit : v - (fun _ => β) - X *ᵥ θ = vp + y := by
    simp only [hvp, hy, hconst, mulVec_sub]
    funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one]; ring
  have hone_dot : ∀ w : Fin N → ℝ, one ⬝ᵥ w = ∑ i, w i := by
    intro w; simp [dotProduct, one]
  have hdot_one : ∀ w : Fin N → ℝ, w ⬝ᵥ one = ∑ i, w i := by
    intro w; rw [dotProduct_comm]; exact hone_dot w
  have hsum_vp : vp ⬝ᵥ one = 0 := by
    have h1 : (X *ᵥ c0) ⬝ᵥ one = 0 := by
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hX1, zero_dotProduct]
    rw [hvp, sub_dotProduct, sub_dotProduct, h1, smul_dotProduct, hdot_one, hdot_one]
    simp only [one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_eq_mul, hbs]
    field_simp
    ring
  have hXvp : Xᵀ *ᵥ vp = 0 := by
    have : vp = (v - X *ᵥ c0) - bs • one := by rw [hvp]; abel
    rw [this, mulVec_sub, mulVec_smul, hc0, hX1, smul_zero, sub_zero]
  have hUy : Uᵀ *ᵥ y = 0 := by
    rw [hy, hconst, mulVec_add, mulVec_smul, hU1, hUX, smul_zero, add_zero]
  have hvpy : vp ⬝ᵥ y = 0 := by
    rw [hy, hconst, dotProduct_add, dotProduct_smul, hsum_vp, smul_zero, zero_add,
      dotProduct_mulVec, ← mulVec_transpose, hXvp, zero_dotProduct]
  have hB1 : (vp + y) ⬝ᵥ (BB U *ᵥ (vp + y)) = v ⬝ᵥ (BB U *ᵥ v) := by
    rw [BB_kill U vp y hUy]
    have hv : v = vp + (bs • one + X *ᵥ c0) := by rw [hvp]; abel
    have hUz : Uᵀ *ᵥ (bs • one + X *ᵥ c0) = 0 := by
      rw [mulVec_add, mulVec_smul, hU1, hUX, smul_zero, add_zero]
    conv_rhs => rw [hv]
    rw [BB_kill U vp _ hUz]
  have hnorm : (v - X *ᵥ c0) ⬝ᵥ (v - X *ᵥ c0) = vp ⬝ᵥ vp + (∑ i, v i) ^ 2 / N := by
    have hv : v - X *ᵥ c0 = vp + bs • one := by rw [hvp]; abel
    rw [hv, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul, smul_dotProduct,
      smul_dotProduct, dotProduct_smul, hsum_vp, dotProduct_comm one vp, hsum_vp]
    simp only [smul_eq_mul, hone_dot, one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hbs]
    field_simp
    ring
  rw [hsplit, q_formula sig2 hsig U, hB1, hnorm]
  clear_value vp y
  rw [add_dotProduct, dotProduct_add, dotProduct_add, hvpy, dotProduct_comm y vp, hvpy]
  ring


lemma quad_sum {N n : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (x : Fin n → Fin N → ℝ) :
    ∑ s, x s ⬝ᵥ (W *ᵥ x s) = ∑ i, ∑ i', W i i' * ∑ s, x s i * x s i' := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma center_id {N n : ℕ} (hn : 0 < n) (W : Matrix (Fin N) (Fin N) ℝ) (x : Fin n → Fin N → ℝ) :
    ∑ s, x s ⬝ᵥ (W *ᵥ x s)
      = ∑ s, (x s - (n : ℝ)⁻¹ • ∑ s', x s') ⬝ᵥ (W *ᵥ (x s - (n : ℝ)⁻¹ • ∑ s', x s'))
        + (n : ℝ) * ((n : ℝ)⁻¹ • ∑ s', x s') ⬝ᵥ (W *ᵥ ((n : ℝ)⁻¹ • ∑ s', x s')) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [quad_sum, quad_sum]
  have hc : ∀ s', ((n : ℝ)⁻¹ • ∑ s, x s) s' = (n : ℝ)⁻¹ * ∑ s, x s s' := by
    intro s'; simp [Finset.sum_apply]
  simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [Pi.sub_apply, hc]
  have e : ∑ s, (x s i - (n : ℝ)⁻¹ * ∑ s, x s i) * (x s i' - (n : ℝ)⁻¹ * ∑ s, x s i')
      = ∑ s, x s i * x s i' - (n : ℝ)⁻¹ * (∑ s, x s i) * (∑ s, x s i') := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [← Finset.mul_sum, ← Finset.mul_sum, e]
  field_simp
  ring


/-- Centring of a family of vectors over the window index. -/
noncomputable def cen {N n : ℕ} (Z : Fin n → Fin N → ℝ) (s : Fin n) : Fin N → ℝ :=
  fun i => Z s i - (n : ℝ)⁻¹ * ∑ s', Z s' i

lemma cen_sum {N n : ℕ} (hn : 0 < n) (Z : Fin n → Fin N → ℝ) (i : Fin N) :
    ∑ s, cen Z s i = 0 := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [cen, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

lemma window_inf {N n dx du : ℕ} (hN : 0 < N) (hn : 0 < n) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (Z : Fin n → Fin N → ℝ) :
    (⨅ γ : (Fin N → ℝ) × (Fin n → ℝ) × (Fin n → Fin dx → ℝ),
      ∑ s, (fun i => Z s i - (γ.1 i + γ.2.1 s + ∑ k, X i k * γ.2.2 s k)) ⬝ᵥ
        ((Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ *ᵥ
          (fun i => Z s i - (γ.1 i + γ.2.1 s + ∑ k, X i k * γ.2.2 s k))))
    = ∑ s, sig2⁻¹ * ((⨅ c : Fin dx → ℝ, (cen Z s - X *ᵥ c) ⬝ᵥ (cen Z s - X *ᵥ c))
        - (∑ i, cen Z s i) ^ 2 / N - cen Z s ⬝ᵥ (BB U *ᵥ cen Z s)) := by
  set W := (Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ with hW
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hex : ∀ s, ∃ c : Fin dx → ℝ, Xᵀ *ᵥ (cen Z s - X *ᵥ c) = 0 := fun s => normal_eq X _
  choose c hc using hex
  have hrhs : ∀ s, (⨅ c' : Fin dx → ℝ, (cen Z s - X *ᵥ c') ⬝ᵥ (cen Z s - X *ᵥ c'))
      = (cen Z s - X *ᵥ c s) ⬝ᵥ (cen Z s - X *ᵥ c s) := fun s => ls_inf X _ _ (hc s)
  simp only [hrhs]
  set V := ∑ s, sig2⁻¹ * ((cen Z s - X *ᵥ c s) ⬝ᵥ (cen Z s - X *ᵥ c s)
        - (∑ i, cen Z s i) ^ 2 / N - cen Z s ⬝ᵥ (BB U *ᵥ cen Z s)) with hV
  set obj : (Fin N → ℝ) × (Fin n → ℝ) × (Fin n → Fin dx → ℝ) → ℝ := fun γ =>
      ∑ s, (fun i => Z s i - (γ.1 i + γ.2.1 s + ∑ k, X i k * γ.2.2 s k)) ⬝ᵥ
        (W *ᵥ (fun i => Z s i - (γ.1 i + γ.2.1 s + ∑ k, X i k * γ.2.2 s k))) with hobj
  have hsig' : 0 ≤ sig2⁻¹ := inv_nonneg.mpr hsig.le
  have hdotnn : ∀ y : Fin N → ℝ, 0 ≤ y ⬝ᵥ y := by
    intro y; simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  -- lower bound
  have hlow : ∀ γ, V ≤ obj γ := by
    intro γ
    obtain ⟨α, β, θ⟩ := γ
    set x : Fin n → Fin N → ℝ := fun s i => Z s i - (α i + β s + ∑ k, X i k * θ s k) with hx
    have h1 := center_id hn W x
    have hq0 := q_nonneg sig2 hsig U ((n : ℝ)⁻¹ • ∑ s', x s')
    have hge : ∑ s, (x s - (n : ℝ)⁻¹ • ∑ s', x s') ⬝ᵥ (W *ᵥ (x s - (n : ℝ)⁻¹ • ∑ s', x s'))
        ≤ obj (α, β, θ) := by
      change _ ≤ ∑ s, x s ⬝ᵥ (W *ᵥ x s)
      rw [h1]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    refine le_trans ?_ hge
    apply Finset.sum_le_sum
    intro s _
    set βb := (n : ℝ)⁻¹ * ∑ s', β s' with hβb
    set θb := (n : ℝ)⁻¹ • ∑ s', θ s' with hθb
    have hxs : x s - (n : ℝ)⁻¹ • ∑ s', x s' = cen Z s - (fun _ => β s - βb) - X *ᵥ (θ s - θb) := by
      funext i
      have A1 : (∑ s', x s') i = ∑ s', Z s' i - n * α i - ∑ s', β s'
          - ∑ k, X i k * ∑ s', θ s' k := by
        simp only [Finset.sum_apply, hx, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun x k => X i k * θ x k)]
        ring
      have A2 : (X *ᵥ (θ s - θb)) i = ∑ k, X i k * θ s k - (n : ℝ)⁻¹ * ∑ k, X i k * ∑ s', θ s' k := by
        simp only [mulVec, dotProduct, hθb, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
          smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s' _ => by ring
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, A1, A2, cen, hβb]
      simp only [hx]
      field_simp
      ring
    rw [hxs, per_s hN sig2 hsig X U hXc hUc hXU _ (c s) (hc s)]
    apply mul_le_mul_of_nonneg_left _ hsig'
    linarith [hdotnn ((fun _ => (∑ i, cen Z s i) / N - (β s - βb)) + X *ᵥ (c s - (θ s - θb)))]
  -- attained
  set βs : Fin n → ℝ := fun s => (∑ i, cen Z s i) / N with hβs
  set αs : Fin N → ℝ := fun i => (n : ℝ)⁻¹ * ∑ s, Z s i - (n : ℝ)⁻¹ * ∑ s, (βs s + (X *ᵥ c s) i)
    with hαs
  set y : Fin n → Fin N → ℝ := fun s => cen Z s - (fun _ => βs s) - X *ᵥ c s with hy
  have hup : obj (αs, βs, c) ≤ V := by
    have hxy : ∀ s, (fun i => Z s i - (αs i + βs s + ∑ k, X i k * c s k))
        = y s - (n : ℝ)⁻¹ • ∑ s', y s' := by
      intro s
      funext i
      have hcs := cen_sum hn Z i
      have A1 : (∑ s', y s') i = ∑ s', cen Z s' i - ∑ s', (βs s' + (X *ᵥ c s') i) := by
        simp only [Finset.sum_apply, hy, Pi.sub_apply, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
        ring
      rw [Pi.sub_apply, Pi.smul_apply, A1, hcs]
      simp only [hy, hαs, cen, mulVec, dotProduct, Pi.sub_apply, smul_eq_mul]
      ring
    have h1 := center_id hn W y
    have hq0 := q_nonneg sig2 hsig U ((n : ℝ)⁻¹ • ∑ s', y s')
    have hle : obj (αs, βs, c) ≤ ∑ s, y s ⬝ᵥ (W *ᵥ y s) := by
      change ∑ s, (fun i => Z s i - (αs i + βs s + ∑ k, X i k * c s k)) ⬝ᵥ
        (W *ᵥ (fun i => Z s i - (αs i + βs s + ∑ k, X i k * c s k))) ≤ _
      simp only [hxy]
      rw [h1]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    refine le_trans hle (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro s _
    rw [hy]
    simp only
    rw [per_s hN sig2 hsig X U hXc hUc hXU _ (c s) (hc s)]
    simp [hβs]
  have hbdd : BddBelow (Set.range obj) := ⟨V, by rintro _ ⟨γ, rfl⟩; exact hlow γ⟩
  apply le_antisymm
  · exact le_trans (ciInf_le hbdd (αs, βs, c)) hup
  · exact le_ciInf hlow


lemma stag_shape {N T : ℕ} (ℓ : ℕ) (A : Fin N → WithTop (Fin T)) (i : Fin N) (j : Fin (ℓ + 1)) :
    ∃ k ≤ T - ℓ, ∀ s : Fin (T - ℓ), z A i (win ℓ j s) = if k ≤ s.val then 1 else -1 := by
  cases h : A i with
  | top =>
    refine ⟨T - ℓ, le_rfl, fun s => ?_⟩
    have hs := s.isLt
    unfold z; rw [h]
    simp only [top_le_iff, WithTop.coe_ne_top, if_false]
    rw [if_neg (by omega)]
  | coe a =>
    refine ⟨min (a.val - j.val) (T - ℓ), min_le_right _ _, fun s => ?_⟩
    have hs := s.isLt
    unfold z; rw [h]
    simp only [WithTop.coe_le_coe, Fin.le_def, win]
    by_cases h1 : a.val ≤ j.val + s.val
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

lemma src_cast (m : ℕ) : ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma stag_sum (n k : ℕ) (hk : k ≤ n) (hn : 0 < n) :
    ∑ s : Fin n, (if k ≤ s.val then (1 : ℝ) else -1) ^ 2
      - (n : ℝ)⁻¹ * (∑ s : Fin n, (if k ≤ s.val then (1 : ℝ) else -1)) ^ 2
      = -2 * ∑ s : Fin n, ((n : ℝ) + 1 - 2 * ((s.val : ℝ) + 1)) / n * (if k ≤ s.val then (1 : ℝ) else -1) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : ∀ s : Fin n, (if k ≤ s.val then (1 : ℝ) else -1) ^ 2 = 1 := by
    intro s; split_ifs <;> norm_num
  simp only [e1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun s => if k ≤ s then (1 : ℝ) else -1) n,
    Fin.sum_univ_eq_sum_range (fun s => ((n : ℝ) + 1 - 2 * ((s : ℝ) + 1)) / n * (if k ≤ s then (1 : ℝ) else -1)) n]
  have hsplit : n = k + (n - k) := by omega
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
  have a1 : ∑ x ∈ Finset.range k, (if k ≤ x then (1 : ℝ) else -1) = -k := by
    rw [Finset.sum_congr rfl (fun x hx => if_neg (by rw [Finset.mem_range] at hx; omega))]; simp
  have a2 : ∑ x ∈ Finset.range (n - k), (if k ≤ k + x then (1 : ℝ) else -1) = ((n - k : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl (fun x _ => if_pos (by omega))]; simp
  have b1 : ∑ x ∈ Finset.range k, ((((k + (n - k) : ℕ) : ℝ) + 1 - 2 * ((x : ℝ) + 1)) / ((k + (n - k) : ℕ) : ℝ)
      * (if k ≤ x then (1 : ℝ) else -1))
      = -∑ x ∈ Finset.range k, ((((k + (n - k) : ℕ) : ℝ) + 1 - 2 * ((x : ℝ) + 1)) / ((k + (n - k) : ℕ) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx; rw [if_neg (by omega)]; ring
  have b2 : ∑ x ∈ Finset.range (n - k), ((((k + (n - k) : ℕ) : ℝ) + 1 - 2 * (((k + x : ℕ) : ℝ) + 1)) / ((k + (n - k) : ℕ) : ℝ)
      * (if k ≤ k + x then (1 : ℝ) else -1))
      = ∑ x ∈ Finset.range (n - k), ((((k + (n - k) : ℕ) : ℝ) + 1 - 2 * (((k + x : ℕ) : ℝ) + 1)) / ((k + (n - k) : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [if_pos (by omega)]; ring
  rw [a1, a2, b1, b2]
  rw [← hsplit]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, src_cast]
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, src_cast]
  rw [Nat.cast_sub hk]
  field_simp
  ring

lemma pone_bilin (n : ℕ) (x y : Fin n → ℝ) :
    ∑ s, ∑ s', Pone n s s' * (x s * y s')
      = ∑ r, (x r - (n : ℝ)⁻¹ * ∑ s, x s) * (y r - (n : ℝ)⁻¹ * ∑ s, y s) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : ∀ s s' : Fin n, Pone n s s' = (if s = s' then 1 else 0) - (n : ℝ)⁻¹ := by
    intro s s'; simp [Pone, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  have lhs : ∑ s, ∑ s', Pone n s s' * (x s * y s')
      = ∑ s, x s * y s - (n : ℝ)⁻¹ * ((∑ s, x s) * (∑ s, y s)) := by
    simp only [hP, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
  rw [lhs]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma quad_center (n N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ) (a : Fin n → Fin N → ℝ) :
    ∑ s, ∑ s', Pone n s s' * (a s ⬝ᵥ (B *ᵥ a s'))
      = ∑ r, (fun i => a r i - (n : ℝ)⁻¹ * ∑ s, a s i) ⬝ᵥ
          (B *ᵥ fun i => a r i - (n : ℝ)⁻¹ * ∑ s, a s i) := by
  have key : ∀ i i', ∑ s, ∑ s', Pone n s s' * (a s i * a s' i')
      = ∑ r, (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i') :=
    fun i i' => pone_bilin n (fun s => a s i) (fun s => a s i')
  simp only [dotProduct, mulVec, Finset.mul_sum]
  calc ∑ s, ∑ s', ∑ i, ∑ i', Pone n s s' * (a s i * (B i i' * a s' i'))
      = ∑ s, ∑ i, ∑ s', ∑ i', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ s', ∑ i', Pone n s s' * (a s i * (B i i' * a s' i')) := Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ i', ∑ s', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ i', ∑ s, ∑ s', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ i', B i i' * ∑ s, ∑ s', Pone n s s' * (a s i * a s' i') := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ = ∑ i, ∑ i', ∑ r, (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ i, ∑ r, ∑ i', (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ i', (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

lemma pone_mulVec (n : ℕ) (x : Fin n → ℝ) :
    Pone n *ᵥ x = fun s => x s - (n : ℝ)⁻¹ * ∑ s', x s' := by
  funext s
  simp only [Pone, mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]

lemma f1j_formula (ℓ T : ℕ) (ω : Fin T → ℝ) (j : Fin (ℓ + 1)) :
    f1j ℓ T ω j = ∑ s, ω (win ℓ j s) ^ 2 - ((T - ℓ : ℕ) : ℝ)⁻¹ * (∑ s, ω (win ℓ j s)) ^ 2
      + 2 * ∑ s, bl ℓ T s * ω (win ℓ j s) := by
  unfold f1j
  rw [pone_mulVec]
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  ring


lemma var_id {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∑ s, (a s - (n : ℝ)⁻¹ * ∑ s', a s') * (a s - (n : ℝ)⁻¹ * ∑ s', a s')
      = ∑ s, a s ^ 2 - (n : ℝ)⁻¹ * (∑ s', a s') ^ 2 := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e2 : ∀ s, (a s - (n : ℝ)⁻¹ * ∑ s', a s') * (a s - (n : ℝ)⁻¹ * ∑ s', a s')
      = a s ^ 2 - 2 * ((n : ℝ)⁻¹ * ∑ s', a s') * a s + ((n : ℝ)⁻¹ * ∑ s', a s') ^ 2 := by
    intro s; ring
  rw [Finset.sum_congr rfl (fun s _ => e2 s)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma K1 {N T : ℕ} (ℓ : ℕ) (hN : 0 < N) (hn : 0 < T - ℓ) (A : Fin N → WithTop (Fin T))
    (j : Fin (ℓ + 1)) :
    (N : ℝ) * f1j ℓ T (omegaBar (z A)) j
      = ∑ s, (∑ i, cen (fun s i => z A i (win ℓ j s)) s i) ^ 2 / N
        - ∑ s, cen (fun s i => z A i (win ℓ j s)) s ⬝ᵥ cen (fun s i => z A i (win ℓ j s)) s := by
  set n := T - ℓ with hndef
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set Z : Fin n → Fin N → ℝ := fun s i => z A i (win ℓ j s) with hZ
  set ω : Fin n → ℝ := fun s => (N : ℝ)⁻¹ * ∑ i, Z s i with hω
  have hωe : ∀ s, omegaBar (z A) (win ℓ j s) = ω s := fun s => rfl
  rw [f1j_formula]
  simp only [hωe]
  -- the sum of the centred columns
  have hcs : ∀ s, ∑ i, cen Z s i = N * (ω s - (n : ℝ)⁻¹ * ∑ s', ω s') := by
    intro s
    simp only [cen, Finset.sum_sub_distrib, ← Finset.mul_sum, hω]
    rw [Finset.sum_comm]
    field_simp
  -- the staggered identity for each unit
  have hst : ∀ i, ∑ s, Z s i ^ 2 - (n : ℝ)⁻¹ * (∑ s, Z s i) ^ 2 = -2 * ∑ s, bl ℓ T s * Z s i := by
    intro i
    obtain ⟨k, hk, hks⟩ := stag_shape ℓ A i j
    have e : ∀ s, Z s i = if k ≤ s.val then 1 else -1 := fun s => hks s
    simp only [e]
    exact stag_sum n k hk hn
  have hcc : ∑ s, cen Z s ⬝ᵥ cen Z s = -2 * N * ∑ s, bl ℓ T s * ω s := by
    have : ∑ s, cen Z s ⬝ᵥ cen Z s = ∑ i, (∑ s, Z s i ^ 2 - (n : ℝ)⁻¹ * (∑ s, Z s i) ^ 2) := by
      simp only [dotProduct, cen]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact var_id hn (fun s => Z s i)
    rw [this]
    simp only [hst, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hcc]
  simp only [hcs]
  have hsq : ∑ s, ((N : ℝ) * (ω s - (n : ℝ)⁻¹ * ∑ s', ω s')) ^ 2 / N
      = N * (∑ s, ω s ^ 2 - (n : ℝ)⁻¹ * (∑ s, ω s) ^ 2) := by
    simp only [mul_pow, sub_sq, Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Finset.sum_div]
    field_simp
    ring
  rw [hsq]
  ring

end EC12Aux

open EC12Aux

theorem solution (N T ℓ dx du : ℕ) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (Sv : Matrix (Fin du) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (hSv : Sv = sig2 • (1 : Matrix (Fin du) (Fin du) ℝ))
    (A : Fin N → WithTop (Fin T)) :
    traceT ℓ sig2 X U Sv A
      = -((N : ℝ) / sig2) * ∑ j : Fin (ℓ + 1),
          (f1j ℓ T (omegaBar (z A)) j + fXj ℓ X (z A) j + fUj ℓ U (z A) j) := by
  subst hSv
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [traceT, dotProduct]
  rcases Nat.eq_zero_or_pos (T - ℓ) with hn | hn
  · haveI : IsEmpty (Fin (T - ℓ)) := by rw [hn]; infer_instance
    simp [traceT, f1j, fXj, fUj, dotProduct, Finset.univ_eq_empty]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsr : sig2 ≠ 0 := hsig.ne'
  have hTl : ℓ < T := by omega
  -- per-window identity
  have hwin : ∀ j : Fin (ℓ + 1),
      ∑ s, sig2⁻¹ * ((⨅ c : Fin dx → ℝ, (cen (fun s i => z A i (win ℓ j s)) s - X *ᵥ c) ⬝ᵥ
          (cen (fun s i => z A i (win ℓ j s)) s - X *ᵥ c))
        - (∑ i, cen (fun s i => z A i (win ℓ j s)) s i) ^ 2 / N
        - cen (fun s i => z A i (win ℓ j s)) s ⬝ᵥ (BB U *ᵥ cen (fun s i => z A i (win ℓ j s)) s))
      = -((N : ℝ) / sig2) *
          (f1j ℓ T (omegaBar (z A)) j + fXj ℓ X (z A) j + fUj ℓ U (z A) j) := by
    intro j
    set Z : Fin (T - ℓ) → Fin N → ℝ := fun s i => z A i (win ℓ j s) with hZ
    have hK := K1 ℓ hN hn A j
    have hfX : fXj ℓ X (z A) j = (N : ℝ)⁻¹ * (∑ s, cen Z s ⬝ᵥ cen Z s
        - ∑ s, (⨅ c : Fin dx → ℝ, (cen Z s - X *ᵥ c) ⬝ᵥ (cen Z s - X *ᵥ c))) := by
      rw [← Finset.sum_sub_distrib]; rfl
    have hfU : fUj ℓ U (z A) j = (N : ℝ)⁻¹ * ∑ s, cen Z s ⬝ᵥ (BB U *ᵥ cen Z s) := by
      unfold fUj
      rw [quad_center (T - ℓ) N (U * (1 + Uᵀ * U)⁻¹ * Uᵀ) Z]
      rfl
    rw [hfX, hfU]
    have hf1 : f1j ℓ T (omegaBar (z A)) j = (N : ℝ)⁻¹ * (∑ s, (∑ i, cen Z s i) ^ 2 / N
        - ∑ s, cen Z s ⬝ᵥ cen Z s) := by
      rw [← hK]; field_simp
    rw [hf1, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    field_simp
    ring
  unfold traceT
  calc ∑ j : Fin (ℓ + 1),
        ⨅ γ : (Fin N → ℝ) × (Fin (T - ℓ) → ℝ) × (Fin (T - ℓ) → Fin dx → ℝ),
          ∑ s : Fin (T - ℓ),
            (fun i => lagCol ℓ A j s i - nuisanceFit ℓ X γ s i) ⬝ᵥ
              ((Psi sig2 U (sig2 • (1 : Matrix (Fin du) (Fin du) ℝ)))⁻¹ *ᵥ
                (fun i => lagCol ℓ A j s i - nuisanceFit ℓ X γ s i))
      = ∑ j : Fin (ℓ + 1), ∑ s, sig2⁻¹ * ((⨅ c : Fin dx → ℝ,
          (cen (fun s i => lagCol ℓ A j s i) s - X *ᵥ c) ⬝ᵥ (cen (fun s i => lagCol ℓ A j s i) s - X *ᵥ c))
          - (∑ i, cen (fun s i => lagCol ℓ A j s i) s i) ^ 2 / N
          - cen (fun s i => lagCol ℓ A j s i) s ⬝ᵥ (BB U *ᵥ cen (fun s i => lagCol ℓ A j s i) s)) :=
        Finset.sum_congr rfl (fun j _ =>
          window_inf hN hn sig2 hsig X U hXc hUc hXU (fun s i => lagCol ℓ A j s i))
    _ = ∑ j : Fin (ℓ + 1), ∑ s, sig2⁻¹ * ((⨅ c : Fin dx → ℝ,
          (cen (fun s i => z A i (win ℓ j s)) s - X *ᵥ c) ⬝ᵥ (cen (fun s i => z A i (win ℓ j s)) s - X *ᵥ c))
          - (∑ i, cen (fun s i => z A i (win ℓ j s)) s i) ^ 2 / N
          - cen (fun s i => z A i (win ℓ j s)) s ⬝ᵥ (BB U *ᵥ cen (fun s i => z A i (win ℓ j s)) s)) := by
        rw [← Equiv.sum_comp Fin.revPerm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hL : (fun s i => lagCol ℓ A (Fin.revPerm j) s i) = (fun s i => z A i (win ℓ j s)) := by
          funext s i
          unfold lagCol win
          congr 1
          ext
          simp only [Fin.revPerm_apply, Fin.val_rev]
          have := j.isLt
          omega
        rw [hL]
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => hwin j)
