-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_jetSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:40.323163+00:00
-- url     : https://prove2.me/submissions/19125243-905f-4d60-b6b7-c9858b30787d

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
    (jetAug R (Fin a) m).comp (jetSub T m) = jetAug R (Fin b) m := by
  apply jet_ext_lemma_2
  intro k
  rw [AlgHom.comp_apply, jetSub_zR, jetAug_zR_lemma]
  exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)
end ReciprocityTheory.ChartRestriction.G.Chart
