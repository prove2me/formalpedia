-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.hermC_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:15.183795+00:00
-- url     : https://prove2.me/submissions/a450ed30-de58-4b9e-9a99-bcb373207ff4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  have hcc : ∀ x : E, τ (cc x) = conj (τ x) := fun x =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ x
  have hL : ∀ a b, ((P.map τ) *ᵥ u) a * τ (X.Gm a b) * conj (((P.map τ) *ᵥ w) b) =
      ∑ k, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum, Finset.sum_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  have hR : ∀ k l, u k * conj (w l) *
      τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) = ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro k l
    simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, map_sum, map_mul, hcc,
      Finset.mul_sum]
    rfl
  simp only [hermC, hL, hR]
  calc _ = ∑ a, ∑ k, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_congr rfl fun k _ => Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
