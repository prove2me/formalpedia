-- Prove2me | solution 1 for SVD.mul_approximationNumber_le_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:20:35.441933+00:00
-- url     : https://prove2.me/submissions/a56b739c-5658-4956-b28d-df1e3d7d6e62

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
public import Theorems.Thm_SVD_svd_sigma_eq_approx
public import Theorems.Thm_SVD_svd_sigma_le_mul_of_factorization
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable {H₃ : Type u}
variable [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃] [CompleteSpace H₃]
namespace SVD
theorem _root_.solution {T : H₁ →L[𝕜] H₃}
    (hT : IsCompactOperator T) {T₁ : H₁ →L[𝕜] H₂} {T₂ : H₂ →L[𝕜] H₃}
    (hfact : T = T₂.comp T₁) {a b : ℝ}
    (ha : ∀ u : ℕ → H₁, OrthonormalOrZero 𝕜 u → ∀ s : Finset ℕ,
      ∑ k ∈ s, ‖T₁ (u k)‖ ^ 2 ≤ a ^ 2)
    (hb : ∀ v : ℕ → H₃, OrthonormalOrZero 𝕜 v → ∀ s : Finset ℕ,
      ∑ k ∈ s, ‖ContinuousLinearMap.adjoint T₂ (v k)‖ ^ 2 ≤ b ^ 2)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (n : ℕ) :
    ((n : ℝ) + 1) * SNumbers.approximationNumber T n ≤ b * a := by
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, hσlim, hsum⟩ := IsCompactOperator.SVD hT
  have hσeq : σ n = SNumbers.approximationNumber T n :=
    svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n
  -- Cauchy–Schwarz over `k ≤ n`, then the two Hilbert–Schmidt bounds.
  have hcs : ∑ k ∈ Finset.range (n + 1), σ k ≤ b * a :=
    calc ∑ k ∈ Finset.range (n + 1), σ k
        ≤ ∑ k ∈ Finset.range (n + 1),
            ‖ContinuousLinearMap.adjoint T₂ (v k)‖ * ‖T₁ (u k)‖ :=
          Finset.sum_le_sum fun k _ =>
            svd_sigma_le_mul_of_factorization hfact hu hv hut hvt hsum k
      _ ≤ Real.sqrt (∑ k ∈ Finset.range (n + 1),
              ‖ContinuousLinearMap.adjoint T₂ (v k)‖ ^ 2)
            * Real.sqrt (∑ k ∈ Finset.range (n + 1), ‖T₁ (u k)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (b ^ 2) * Real.sqrt (a ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt (hb v hv _)) (Real.sqrt_le_sqrt (ha u hu _))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = b * a := by rw [Real.sqrt_sq hb0, Real.sqrt_sq ha0]
  -- `(n+1)·σₙ ≤ ∑_{k ≤ n} σₖ` since `σ` is antitone.
  have hcard : ((n : ℝ) + 1) * σ n ≤ ∑ k ∈ Finset.range (n + 1), σ k := by
    have h := Finset.card_nsmul_le_sum (Finset.range (n + 1)) σ (σ n) fun k hk =>
      hσanti (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simpa [Finset.card_range, nsmul_eq_mul] using h
  rw [← hσeq]
  exact hcard.trans hcs
end SVD
