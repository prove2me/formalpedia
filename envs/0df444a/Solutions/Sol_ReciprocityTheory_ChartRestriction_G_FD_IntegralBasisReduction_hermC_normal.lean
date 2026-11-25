-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.hermC_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:11.561619+00:00
-- url     : https://prove2.me/submissions/0c0dfa47-874b-4c0f-8cbe-5ab51c05d7b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum4_lemma {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
private lemma hermC_mulVec_lemma_2 {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    hermC τ G (Y *ᵥ u) (Y *ᵥ v) = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
  calc hermC τ G (Y *ᵥ u) (Y *ᵥ v)
      = ∑ a, ∑ b, ∑ i, ∑ j, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := by
        simp only [hermC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
    _ = ∑ i, ∑ j, ∑ a, ∑ b, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := sum4_lemma _
    _ = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gram, hermC, col, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end IntegralBasisReduction
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
theorem _root_.solution {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ X.Gm Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ X.Gm p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have key := hermC_mulVec_lemma_2 τ X.Gm Y (Y⁻¹ *ᵥ p) (Y⁻¹ *ᵥ q)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec, hg] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h
end ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
