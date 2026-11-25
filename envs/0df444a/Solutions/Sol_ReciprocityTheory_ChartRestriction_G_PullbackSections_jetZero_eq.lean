-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:55.525806+00:00
-- url     : https://prove2.me/submissions/5b1a09b5-0cdd-44cf-8df6-c69280911239

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE

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
variable {g : ℕ} {Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) :
    jetZero m a = algebraMap ℂ _ ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) a) := by
  have h : (jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) =
      (Algebra.ofId ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp jetAug := by
    apply Ideal.Quotient.algHom_ext
    simp only [jetZero, jetMap, jetAug, liftJet, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [h]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
