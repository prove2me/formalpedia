-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_epsMul_zero_jetTan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:14.237496+00:00
-- url     : https://prove2.me/submissions/979c29e3-fc0b-4331-a3a4-01e4028e3514

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_fst_jetTan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (ℓ : Fin 1 × Fin g) :
    spMap (epsMul (0 : ℂ)) ≫ spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
  have h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp
      ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · simp [epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
