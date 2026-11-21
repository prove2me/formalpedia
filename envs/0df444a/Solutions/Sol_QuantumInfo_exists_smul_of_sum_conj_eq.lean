-- Prove2me | solution 1 for QuantumInfo.exists_smul_of_sum_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:44.746432+00:00
-- url     : https://prove2.me/submissions/26fc7502-c0e6-4786-9848-74ea45bfff89

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_exists_smul_of_forall_smul
public import Theorems.Thm_QuantumInfo_Channel_id_apply
attribute [local simp] QuantumInfo.Channel.id_apply



set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
omit [Fintype ι] [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution {κ : Type*} [Fintype κ] (hP : IsCodeProjector P)
    (A : κ → Matrix n n ℂ) (lam : ℂ) (hA : ∀ k, A k * P = A k)
    (h : ∀ X : Matrix n n ℂ, ∑ k, A k * X * (A k)ᴴ = lam • (P * X * P)) (k : κ) :
    ∃ μ : ℂ, A k = μ • P := by
  refine exists_smul_of_forall_smul (hA k) fun w => ?_
  set v := P *ᵥ w with hv
  set a : κ → n → ℂ := fun k' => A k' *ᵥ w with ha
  have hav : ∀ k', A k' *ᵥ v = a k' := fun k' => by
    rw [hv, mulVec_mulVec, hA k']
  have hPv : P *ᵥ v = v := by rw [hv, mulVec_mulVec, hP.mul_self]
  -- the identity on the rank-one state `v vᴴ`
  have hX := h (vecMulVec v (star v))
  have hL : ∀ k', A k' * vecMulVec v (star v) * (A k')ᴴ = vecMulVec (a k') (star (a k')) := by
    intro k'
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hav]
  have hR : P * vecMulVec v (star v) * P = vecMulVec v (star v) := by
    rw [mul_vecMulVec, vecMulVec_mul, hPv]
    congr 1
    conv_lhs => rw [← hP.conjTranspose_eq]
    rw [← star_mulVec, hPv]
  simp only [hL, hR] at hX
  -- the sandwiched scalar identity
  have h2 : ∀ u x : n → ℂ, (star u ⬝ᵥ x) * (star x ⬝ᵥ u)
      = ((Complex.normSq (star u ⬝ᵥ x) : ℝ) : ℂ) := by
    intro u x
    rw [star_dotProduct (v := x) (w := u), Complex.star_def, Complex.mul_conj]
  have hq : ∀ u : n → ℂ, ∑ k', ((Complex.normSq (star u ⬝ᵥ a k') : ℝ) : ℂ)
      = lam * ((Complex.normSq (star u ⬝ᵥ v) : ℝ) : ℂ) := by
    intro u
    have h1 := congrArg (fun M : Matrix n n ℂ => star u ⬝ᵥ (M *ᵥ u)) hX
    simp only [dotProduct_mulVec, Matrix.vecMul_sum, sum_dotProduct, Matrix.vecMul_smul,
      vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, h2] at h1
    exact h1
  by_cases hv0 : v = 0
  · refine ⟨0, ?_⟩
    have hw : A k *ᵥ w = A k *ᵥ v := by rw [hv, mulVec_mulVec, hA k]
    rw [hw, hv0, mulVec_zero, zero_smul]
  have hvv : star v ⬝ᵥ v ≠ 0 := fun h0 => hv0 (dotProduct_star_self_eq_zero.mp h0)
  set α : ℂ := (star v ⬝ᵥ a k) / (star v ⬝ᵥ v) with hα
  set u : n → ℂ := a k - α • v with hu
  have huv : star u ⬝ᵥ v = 0 := by
    rw [hu, star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, hα,
      star_div₀, star_dotProduct (v := a k) (w := v), ← star_dotProduct (v := v) (w := v),
      div_mul_cancel₀ _ hvv, sub_self]
  have hsum := hq u
  rw [huv, Complex.normSq_zero, Complex.ofReal_zero, mul_zero, ← Complex.ofReal_sum,
    Complex.ofReal_eq_zero] at hsum
  have hk : Complex.normSq (star u ⬝ᵥ a k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k' _ => Complex.normSq_nonneg _).mp hsum k
      (Finset.mem_univ k)
  rw [Complex.normSq_eq_zero] at hk
  have huu : star u ⬝ᵥ u = 0 := by
    have h3 : star u ⬝ᵥ u = star u ⬝ᵥ (a k - α • v) := by rw [hu]
    rw [h3, dotProduct_sub, dotProduct_smul, hk, huv, smul_zero, sub_zero]
  have hu0 : u = 0 := dotProduct_star_self_eq_zero.mp huu
  refine ⟨α, ?_⟩
  rw [hu] at hu0
  exact sub_eq_zero.mp hu0
end QuantumInfo
