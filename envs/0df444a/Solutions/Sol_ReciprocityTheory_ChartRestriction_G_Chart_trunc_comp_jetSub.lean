-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.trunc_comp_jetSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:51.063265+00:00
-- url     : https://prove2.me/submissions/ec6ece80-f298-4f24-8c1e-772eff1dc611

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_zR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
private theorem jet_ext_lemma_2 {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A]
    {f g : JetR R κ m →ₐ[R] A} (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j
private theorem trunc_zR_lemma_3 {κ : Type} (m : ℕ) (j : κ) :
    jetTruncR R κ m (zR (m + 1) j) = zR m j := rfl
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetTruncR R (Fin a) m).comp (jetSub T (m + 1)) = (jetSub T m).comp (jetTruncR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k
  simp only [AlgHom.comp_apply, jetSub_zR, trunc_zR_lemma_3, map_sum, map_smul]
end ReciprocityTheory.ChartRestriction.G.Chart
