-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_quot_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:04.398409+00:00
-- url     : https://prove2.me/submissions/218f72ef-a246-4575-bf11-90c1921b6d2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL

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
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (B.map A.mkQ)
  have e1 : Nat.card ((V ⧸ A) ⧸ B.map A.mkQ) = Nat.card (V ⧸ B) :=
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient A B h).toEquiv
  let φ : B →ₗ[R] V ⧸ A := A.mkQ ∘ₗ B.subtype
  have hr : LinearMap.range φ = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker φ = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e2 : Nat.card (B.map A.mkQ) = Nat.card (B ⧸ A.comap B.subtype) := by
    rw [← hr, ← hk]
    exact Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv.symm
  rw [h1, e1, e2]
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
