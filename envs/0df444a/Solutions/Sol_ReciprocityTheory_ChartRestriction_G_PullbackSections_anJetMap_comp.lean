-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anJetMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:20.013597+00:00
-- url     : https://prove2.me/submissions/e7003b4f-1e6e-4d53-8d5a-0a78fc42ed80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo

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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {K : Type} [Field K] {Ia Ib Ic : Type} {m : ℕ} (φ : Ia → MvPolynomial Ib K)
    (hφ : ∀ i, φ i ∈ orig K Ib) (ψ : Ib → MvPolynomial Ic K) (hψ : ∀ i, ψ i ∈ orig K Ic)
    (ch : Ia → MvPolynomial Ic K) (hch : ∀ i, ch i ∈ orig K Ic) (h : ∀ i, MvPolynomial.aeval ψ (φ i) = ch i)
    (a : Jet K Ia m) : jetMap ψ hψ (jetMap φ hφ a) = jetMap ch hch a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval ψ (MvPolynomial.aeval φ p)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval ch p)
  congr 1
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, h i]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
