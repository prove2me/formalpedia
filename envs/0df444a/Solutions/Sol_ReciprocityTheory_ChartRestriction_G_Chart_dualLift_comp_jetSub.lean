-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualLift_comp_jetSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:49.325774+00:00
-- url     : https://prove2.me/submissions/9ec1ce00-5be5-481e-a42a-6b018449f10f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_sum_single
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
private theorem sum_inr_lemma_5 {I : Type} (s : Finset I) (f : I → R) :
    ∑ i ∈ s, (TrivSqZeroExt.inr (f i) : DualNumber R) = TrivSqZeroExt.inr (∑ i ∈ s, f i) := by
  first
  | exact (map_sum (TrivSqZeroExt.inrHom R R) f s).symm
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, TrivSqZeroExt.inr_add])
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
theorem _root_.solution {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (c : Fin a → R) :
    (dualLift c).comp (jetSub T 1) = dualLift (T c) := by
  apply jet_ext_lemma_2
  intro k
  simp only [AlgHom.comp_apply, jetSub_zR, map_sum, map_smul, dualLift_zR]
  simp_rw [← TrivSqZeroExt.inr_smul, sum_inr_lemma_5]
  congr 1
  conv_rhs => rw [← sum_single c]
  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]
end ReciprocityTheory.ChartRestriction.G.Chart
