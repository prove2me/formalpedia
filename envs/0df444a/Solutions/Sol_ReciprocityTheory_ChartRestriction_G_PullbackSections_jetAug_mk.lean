-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:56.132213+00:00
-- url     : https://prove2.me/submissions/f32535ee-4d84-4ddf-a503-6a3cec6411bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD

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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {K : Type} [Field K] {ι : Type} {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (p : MvPolynomial ι K) :
    (jetAug : Jet K ι m →ₐ[K] K) (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p := by
  show (MvPolynomial.aeval fun _ : ι => (0 : K)) p = MvPolynomial.constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
