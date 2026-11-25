-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:45.617776+00:00
-- url     : https://prove2.me/submissions/1daab838-7ebf-4e96-87b8-0456de77eddd

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
theorem _root_.solution {ι' : Type} (φ φ' : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι')
    (hφ' : ∀ i, φ' i ∈ orig K ι')
    (h : ∀ i, Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ i) = Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ' i))
    (a : Jet K ι m) : jetMap φ hφ a = jetMap φ' hφ' a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hext : (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ) =
      (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ') := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using h i
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ' p)
  exact DFunLike.congr_fun hext p
end ReciprocityTheory.ChartRestriction.G.PullbackSections
