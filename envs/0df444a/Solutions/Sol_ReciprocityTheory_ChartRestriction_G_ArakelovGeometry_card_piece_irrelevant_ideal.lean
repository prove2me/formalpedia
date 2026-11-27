-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_irrelevant_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:40.681018+00:00
-- url     : https://prove2.me/submissions/66353efd-d7f8-4e2b-a736-0451a68f2e8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_multidegree_piece_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_iff_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 1 ≤ a k) : Nat.card (mPiece q a) = 1 := by
  have key : ∀ y ∈ mPiece q a, y = 0 := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
    rw [Ideal.Quotient.eq_zero_iff_mem, h.as_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hmk : i2bdeg m k = a k :=
      congrFun ((isMultiHomog_iff_coeff h a).1 hh m (mem_support_iff.1 hm)) k
    have : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h0 : i2bdeg m k = 0 := show ∑ i, m ⟨k, i⟩ = 0 from Finset.sum_eq_zero fun i _ => hne i
      rw [h0] at hmk
      rw [← hmk] at ha
      exact absurd ha (by norm_num)
    obtain ⟨i, hi⟩ := this
    have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have e : monomial m (coeff m h) =
        X ⟨k, i⟩ * monomial (m - Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) (coeff m h) := by
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [e]
    exact Ideal.mul_mem_right _ _ (hk i)
  haveI : Subsingleton (mPiece q a) :=
    ⟨fun x y => Subtype.ext ((key _ x.2).trans (key _ y.2).symm)⟩
  exact Nat.card_of_subsingleton (0 : mPiece q a)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
