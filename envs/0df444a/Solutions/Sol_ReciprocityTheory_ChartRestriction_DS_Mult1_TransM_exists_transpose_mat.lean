-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.TransM.exists_transpose_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:41.701339+00:00
-- url     : https://prove2.me/submissions/62fe9fe0-36d1-485a-9954-a49892799adc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JTransMA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
open scoped InnerProductSpace ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Mult1
namespace TransM
variable {S : Type} [Fintype S] [DecidableEq S]
private theorem unitary_exists_unit_scalar_isUnit_det_one_add (m : Matrix S S ℂ) (hm : mᴴ * m = 1) :
    ∃ ζ : ℂ, starRingEnd ℂ ζ * ζ = 1 ∧ IsUnit (1 + ζ • m).det := by
  have hH : (m + mᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := ((Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).diff
    (Finset.univ.image fun j => -hH.eigenvalues j / 2).finite_toSet).nonempty
  obtain ⟨s, hs2⟩ : ∃ s : ℝ, s ^ 2 = 1 - r ^ 2 := ⟨Real.sqrt (1 - r ^ 2), Real.sq_sqrt (by nlinarith)⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = (r : ℂ) + (s : ℂ) * Complex.I := ⟨_, rfl⟩
  have hζ1 : starRingEnd ℂ ζ * ζ = 1 := by
    subst hζ
    apply Complex.ext <;> simp <;> nlinarith [hs2]
  have hζ2 : ζ + starRingEnd ℂ ζ = 2 * (r : ℂ) := by
    subst hζ
    apply Complex.ext <;> simp <;> ring
  refine ⟨ζ, hζ1, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have ha : m *ᵥ v = (-starRingEnd ℂ ζ) • v := by
    funext i
    have h1 := congrFun hv i
    have hsm : (ζ • m) *ᵥ v = ζ • (m *ᵥ v) := by
      first
        | exact Matrix.smul_mulVec ζ m v
        | exact Matrix.smul_mulVec_assoc ζ m v
        | (funext k; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, hsm, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (starRingEnd ℂ ζ) * h1 - (m *ᵥ v) i * hζ1
  have hb : mᴴ *ᵥ v = (-ζ) • v := by
    have h2 : mᴴ *ᵥ (m *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at h2
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at h3 ⊢
    linear_combination (-ζ) * h3 - (mᴴ *ᵥ v) i * hζ1
  have hsum : (m + mᴴ) *ᵥ v = ((-2 * r : ℝ) : ℂ) • v := by
    funext i
    rw [Matrix.add_mulVec, Pi.add_apply, ha, hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-(v i)) * hζ2
  obtain ⟨W, hW⟩ : ∃ W : Matrix S S ℂ, W = (hH.eigenvectorUnitary : Matrix S S ℂ) := ⟨_, rfl⟩
  have hW1 : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hW2 : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hsp : m + mᴴ = W * Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) * Wᴴ := by
    rw [hW]
    conv_lhs => rw [hH.spectral_theorem]
    first
      | rfl
      | simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  obtain ⟨y, hy⟩ : ∃ y : S → ℂ, y = Wᴴ *ᵥ v := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := by
    intro h
    apply hv0
    rw [← Matrix.one_mulVec v, ← hW2, ← Matrix.mulVec_mulVec, ← hy, h, Matrix.mulVec_zero]
  have h4 : Wᴴ *ᵥ ((m + mᴴ) *ᵥ v) = Wᴴ *ᵥ (((-2 * r : ℝ) : ℂ) • v) := by rw [hsum]
  rw [Matrix.mulVec_smul, ← hy, Matrix.mulVec_mulVec, hsp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW1,
    Matrix.one_mul, ← Matrix.mulVec_mulVec, ← hy] at h4
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have h5 := congrFun h4 j
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h5
  have h6 : (hH.eigenvalues j : ℂ) = ((-2 * r : ℝ) : ℂ) := mul_right_cancel₀ hj h5
  have h7 : hH.eigenvalues j = -2 * r := by exact_mod_cast h6
  exact hr (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [h7]; ring⟩))
private theorem unitary_exists_diagonalization (m : Matrix S S ℂ) (hm : mᴴ * m = 1) :
    ∃ V : Matrix S S ℂ, ∃ d : S → ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      (∀ i, starRingEnd ℂ (d i) * d i = 1) ∧ m = V * Matrix.diagonal d * Vᴴ := by
  obtain ⟨ζ, hζ1, hQ⟩ := unitary_exists_unit_scalar_isUnit_det_one_add m hm
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have hζ0' : starRingEnd ℂ ζ ≠ 0 := by rintro h; rw [h, zero_mul] at hζ1; exact zero_ne_one hζ1
  obtain ⟨u, hu⟩ : ∃ u : Matrix S S ℂ, u = ζ • m := ⟨_, rfl⟩
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, smul_smul]
    show (starRingEnd ℂ ζ * ζ) • (1 : Matrix S S ℂ) = 1
    rw [hζ1, one_smul]
  obtain ⟨Q, hQd⟩ : ∃ Q : Matrix S S ℂ, Q = 1 + u := ⟨_, rfl⟩
  rw [← hu, ← hQd] at hQ
  obtain ⟨X, hX⟩ : ∃ X : Matrix S S ℂ, X = (1 - u) * Q⁻¹ := ⟨_, rfl⟩
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  have hXQ : X * Q = 1 - u := by rw [hX, Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have key : u * (1 + X) = 1 - X := by
    have h2 : u * (1 + X) * Q = (1 - X) * Q := by
      rw [Matrix.mul_assoc, add_mul, sub_mul, Matrix.one_mul, hXQ, hQd]
      noncomm_ring
    calc u * (1 + X) = u * (1 + X) * Q * Q⁻¹ := by rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_one]
      _ = (1 - X) * Q * Q⁻¹ := by rw [h2]
      _ = 1 - X := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hQH : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  have canc : ∀ Y : Matrix S S ℂ, Y = (Q⁻¹)ᴴ * (Qᴴ * Y * Q) * Q⁻¹ := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hQQ, Matrix.mul_one, ← Matrix.mul_assoc, hQH, Matrix.one_mul]
  have e : Qᴴ * Xᴴ * Q = Qᴴ * (-X) * Q := by
    rw [← Matrix.conjTranspose_mul, hXQ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hXQ, hQd,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    simp only [add_mul, sub_mul, mul_add, mul_sub, Matrix.one_mul, Matrix.mul_one, hu1]
    abel
  have hXs : Xᴴ = -X := by rw [canc Xᴴ, e, ← canc]
  have hH : (Complex.I • X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hXs, smul_neg, ← neg_smul]
    congr 1
    show -(starRingEnd ℂ Complex.I) = Complex.I
    rw [Complex.conj_I, neg_neg]
  obtain ⟨W, hW⟩ : ∃ W : Matrix S S ℂ, W = (hH.eigenvectorUnitary : Matrix S S ℂ) := ⟨_, rfl⟩
  have hW1 : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hW2 : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  obtain ⟨ev, hev⟩ : ∃ ev : S → ℝ, ev = hH.eigenvalues := ⟨_, rfl⟩
  have hsp : Complex.I • X = W * Matrix.diagonal (fun j => (ev j : ℂ)) * Wᴴ := by
    rw [hW, hev]
    conv_lhs => rw [hH.spectral_theorem]
    first
      | rfl
      | simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hY : Wᴴ * X * W = Matrix.diagonal (fun j => -Complex.I * (ev j : ℂ)) := by
    have h := congrArg (fun M => Wᴴ * M * W) hsp
    try simp only at h
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    rw [show Wᴴ * (W * Matrix.diagonal (fun j => (ev j : ℂ)) * Wᴴ) * W =
        Matrix.diagonal (fun j => (ev j : ℂ)) by
      simp only [Matrix.mul_assoc]
      rw [hW1, Matrix.mul_one, ← Matrix.mul_assoc, hW1, Matrix.one_mul]] at h
    ext i j
    have h8 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply] at h8 ⊢
    split_ifs at h8 ⊢ with hij
    · linear_combination (-Complex.I) * h8 + (Wᴴ * X * W) i j * Complex.I_sq
    · linear_combination (-Complex.I) * h8 + (Wᴴ * X * W) i j * Complex.I_sq
  have eL : Wᴴ * (u * (1 + X)) * W = (Wᴴ * u * W) * (1 + Wᴴ * X * W) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W Wᴴ, hW2, Matrix.one_mul]
  have eR : Wᴴ * (1 - X) * W = 1 - Wᴴ * X * W := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [hW1]
  have h := congrArg (fun M => Wᴴ * M * W) key
  try simp only at h
  rw [eL, eR, hY, hu, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul] at h
  have hent : ∀ i j, ζ * (Wᴴ * m * W) i j * (1 - Complex.I * (ev j : ℂ)) =
      if i = j then 1 + Complex.I * (ev i : ℂ) else 0 := by
    intro i j
    have h9 := congrFun (congrFun h i) j
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul] at h9
    split_ifs at h9 ⊢ with hij
    · subst hij; linear_combination h9
    · linear_combination h9
  have hc : ∀ i, (1 - Complex.I * (ev i : ℂ)) ≠ 0 := by
    intro i h0
    have := congrArg Complex.re h0
    simp at this
  have hc' : ∀ i, (1 + Complex.I * (ev i : ℂ)) ≠ 0 := by
    intro i h0
    have := congrArg Complex.re h0
    simp at this
  refine ⟨W, fun i => (1 + Complex.I * (ev i : ℂ)) / (ζ * (1 - Complex.I * (ev i : ℂ))), hW1, hW2,
    fun i => ?_, ?_⟩
  · have ha : starRingEnd ℂ (1 + Complex.I * (ev i : ℂ)) = 1 - Complex.I * (ev i : ℂ) := by
      simp [Complex.conj_ofReal] <;> ring
    have hb : starRingEnd ℂ (1 - Complex.I * (ev i : ℂ)) = 1 + Complex.I * (ev i : ℂ) := by
      simp [Complex.conj_ofReal] <;> ring
    simp only [map_div₀, map_mul, ha, hb]
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hζ0' (hc' i)) (mul_ne_zero hζ0 (hc i)))]
    linear_combination (-((1 - Complex.I * (ev i : ℂ)) * (1 + Complex.I * (ev i : ℂ)))) * hζ1
  · have hm' : Wᴴ * m * W = Matrix.diagonal
        (fun i => (1 + Complex.I * (ev i : ℂ)) / (ζ * (1 - Complex.I * (ev i : ℂ)))) := by
      ext i j
      rw [Matrix.diagonal_apply]
      split_ifs with hij
      · subst hij
        have h10 := hent i i
        rw [if_pos rfl] at h10
        rw [eq_div_iff (mul_ne_zero hζ0 (hc i))]
        linear_combination h10
      · have h10 := hent i j
        rw [if_neg hij] at h10
        simpa [hζ0, hc j] using h10
    calc m = W * Wᴴ * m * (W * Wᴴ) := by rw [hW2, Matrix.one_mul, Matrix.mul_one]
      _ = W * (Wᴴ * m * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hm']
end TransM
end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1
open ReciprocityTheory.ChartRestriction.DS.Mult1.TransM
variable {S : Type} [Fintype S] [DecidableEq S]
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TransM
theorem _root_.solution (m : Matrix S S ℂ) (hm : mᴴ * m = 1) (w : S → ℂ) (hw : ∀ s, conj (w s) = w s) :
    ∃ U : Matrix S S ℂ, Uᴴ * U = 1 ∧ U *ᵥ w = w ∧ m.map (starRingEnd ℂ) * U * m = U := by
  obtain ⟨V, d, hV1, hV2, hd, rfl⟩ := unitary_exists_diagonalization m hm
  obtain ⟨x, hx⟩ : ∃ x : S → ℂ, x = Vᴴ *ᵥ w := ⟨_, rfl⟩
  obtain ⟨p, hp, hpx⟩ : ∃ p : S → ℂ, (∀ i, starRingEnd ℂ (p i) * p i = 1) ∧
      ∀ i, p i * (‖x i‖ : ℂ) = x i := by
    refine ⟨fun i => Complex.exp (Complex.arg (x i) * Complex.I), fun i => ?_, fun i => ?_⟩
    · rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    · rw [mul_comm]
      first
        | exact Complex.norm_mul_exp_arg_mul_I (x i)
        | exact Complex.abs_mul_exp_arg_mul_I (x i)
  obtain ⟨e, he⟩ : ∃ e : S → ℂ, ∀ i, e i = starRingEnd ℂ (p i) ^ 2 := ⟨_, fun _ => rfl⟩
  have he1 : ∀ i, e i * x i = starRingEnd ℂ (x i) := by
    intro i
    have hcx : starRingEnd ℂ (x i) = starRingEnd ℂ (p i) * (‖x i‖ : ℂ) := by
      conv_lhs => rw [← hpx i]
      rw [map_mul, Complex.conj_ofReal]
    rw [hcx, he i]
    linear_combination (-(starRingEnd ℂ (p i)) ^ 2) * hpx i + (starRingEnd ℂ (p i) * (‖x i‖ : ℂ)) * hp i
  have he2 : ∀ i, starRingEnd ℂ (e i) * e i = 1 := by
    intro i
    rw [he i]
    simp only [map_pow, starRingEnd_self_apply]
    linear_combination (starRingEnd ℂ (p i) * p i + 1) * hp i
  have hVT : Vᴴ.map (starRingEnd ℂ) = Vᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hcVH : (V.map (starRingEnd ℂ))ᴴ = Vᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hcV : Vᵀ * V.map (starRingEnd ℂ) = 1 := by
    have h : (Vᴴ * V).map (starRingEnd ℂ) = 1 := by
      rw [hV1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [Matrix.map_mul, hVT] at h
  have hEE : (Matrix.diagonal e)ᴴ * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact he2 i
  have hVx : V *ᵥ x = w := by rw [hx, Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
  have hEx : Matrix.diagonal e *ᵥ x = fun i => starRingEnd ℂ (x i) := by
    funext i
    rw [Matrix.mulVec_diagonal]
    exact he1 i
  have hmv : ∀ (M : Matrix S S ℂ) (v : S → ℂ),
      M.map (starRingEnd ℂ) *ᵥ (fun i => starRingEnd ℂ (v i)) = fun i => starRingEnd ℂ ((M *ᵥ v) i) := by
    intro M v
    funext i
    first
      | simp [Matrix.mulVec, dotProduct, map_sum]
      | simp [Matrix.mulVec, Matrix.dotProduct, map_sum]
  refine ⟨V.map (starRingEnd ℂ) * Matrix.diagonal e * Vᴴ, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hcVH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hcV, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal e)ᴴ, hEE,
      Matrix.one_mul, hV2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx, hEx, hmv, hVx]
    funext i
    exact hw i
  · rw [Matrix.map_mul, Matrix.map_mul, hVT, Matrix.diagonal_map (map_zero _)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hcV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hV1, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal e) (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have hde : ∀ i, starRingEnd ℂ (d i) * (e i * d i) = e i := fun i => by linear_combination e i * hd i
    simp only [hde]
end ReciprocityTheory.ChartRestriction.DS.Mult1.TransM
