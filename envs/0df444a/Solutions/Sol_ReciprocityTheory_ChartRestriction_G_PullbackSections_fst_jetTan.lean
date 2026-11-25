-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.fst_jetTan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:09.651863+00:00
-- url     : https://prove2.me/submissions/fe9d971e-3df1-4504-83d3-2f04549f4c42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX

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
theorem _root_.solution (ℓ : Fin 1 × Fin g) (a : Jet ℂ (Fin 1 × Fin g) (0 + 1)) :
    ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) a).fst =
      (jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [jetTan, jetAug, liftJet]
  try simp only [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  induction p using MvPolynomial.induction_on with
  | C r => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = ℓ <;> simp [hj, hp]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
