-- Prove2me | solution 1 for PositivityTheory.KReal.pos_of_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:53.188799+00:00
-- url     : https://prove2.me/submissions/997d1534-8490-41f1-8052-3dd7ffddffb1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (h : ∀ t : ℝ, t ≤ 0 → ∀ x, S x = (t : ℂ) • x → x = 0) (x : E) :
    0 ≤ (⟪x, S x⟫_ℂ).re ∧ ((⟪x, S x⟫_ℂ).re = 0 → x = 0) := by
  let b := hS.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let ev := hS.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (ev i : ℂ) • b i := fun i => hS.apply_eigenvectorBasis rfl i
  have hev : ∀ i, 0 < ev i := by
    intro i
    by_contra hc
    exact b.orthonormal.ne_zero i (h _ (not_lt.1 hc) _ (hb i))
  have key : (⟪x, S x⟫_ℂ).re = ∑ i, ev i * Complex.normSq ⟪b i, x⟫_ℂ := by
    rw [← b.sum_inner_mul_inner x (S x), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS (b i) x, hb, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b i), mul_left_comm,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ev i * Complex.normSq ⟪b i, x⟫_ℂ :=
    fun i _ => mul_nonneg (hev i).le (Complex.normSq_nonneg _)
  rw [key]
  refine ⟨Finset.sum_nonneg hnn, fun h0 => ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  have hz : ∀ i, ⟪b i, x⟫_ℂ = 0 := fun i =>
    Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hev i).ne')
  rw [← b.sum_repr' x]
  simp [hz]
end PositivityTheory.KReal
