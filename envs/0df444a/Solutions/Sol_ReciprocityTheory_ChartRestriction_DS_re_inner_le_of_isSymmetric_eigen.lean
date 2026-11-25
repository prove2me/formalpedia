-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.re_inner_le_of_isSymmetric_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:14.411791+00:00
-- url     : https://prove2.me/submissions/6b2617ac-4b00-44a5-a505-c2e55511152b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section KUnitB
private theorem re_inner_basis_lemma {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (T : E →ₗ[ℂ] E)
    (hb : ∀ i, T (b i) = (lam i : ℂ) • b i) (C : ℝ) (hC : ∀ i, lam i ≤ C) (x : E) :
    RCLike.re (inner ℂ (T x) x) ≤ C * ‖x‖ ^ 2 := by
  have hx : x = ∑ i, (inner ℂ (b i) x) • b i := (b.sum_repr' x).symm
  have hTx : T x = ∑ i, (inner ℂ (b i) x * (lam i : ℂ)) • b i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, smul_smul]
  have h1 : inner ℂ (T x) x =
      ∑ i, (starRingEnd ℂ) (inner ℂ (b i) x * (lam i : ℂ)) * inner ℂ (b i) x := by
    have e : inner ℂ (T x) x = inner ℂ (∑ i, (inner ℂ (b i) x * (lam i : ℂ)) • b i)
        (∑ i, (inner ℂ (b i) x) • b i) := by
      rw [← hTx, ← hx]
    rw [e]
    exact b.orthonormal.inner_sum _ _ _
  have h2 : inner ℂ x x = ∑ i, (starRingEnd ℂ) (inner ℂ (b i) x) * inner ℂ (b i) x := by
    have e : inner ℂ x x = inner ℂ (∑ i, (inner ℂ (b i) x) • b i)
        (∑ i, (inner ℂ (b i) x) • b i) := by
      rw [← hx]
    rw [e]
    exact b.orthonormal.inner_sum _ _ _
  have hself : RCLike.re (inner ℂ x x) = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hn : ‖x‖ ^ 2 = ∑ i, Complex.normSq (inner ℂ (b i) x) := by
    rw [← hself, RCLike.re_to_complex, h2, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [h1, hn, Finset.mul_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have e3 : (starRingEnd ℂ) (inner ℂ (b i) x * (lam i : ℂ)) * inner ℂ (b i) x =
      ((lam i * Complex.normSq (inner ℂ (b i) x) : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [e3, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hC i) (Complex.normSq_nonneg _)
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
end KUnitB
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (C : ℝ)
    (h : ∀ v : E, v ≠ 0 → ∀ θ : ℝ, T v = (θ : ℂ) • v → θ ≤ C) (x : E) :
    RCLike.re (inner ℂ (T x) x) ≤ C * ‖x‖ ^ 2 := by
  exact re_inner_basis_lemma (hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl)
    (hT.eigenvalues (n := Module.finrank ℂ E) rfl) T
    (fun i => hT.apply_eigenvectorBasis rfl i) C
    (fun i => h _ ((hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl).orthonormal.ne_zero i) _
      (hT.apply_eigenvectorBasis rfl i)) x
end ReciprocityTheory.ChartRestriction.DS
