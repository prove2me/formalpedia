-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_jetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:08.75787+00:00
-- url     : https://prove2.me/submissions/bd340e0f-0bed-4da6-97e5-613d45e52744

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_of_mem_orig

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
theorem _root_.solution {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') (a : Jet K ι m) :
    (jetAug : Jet K ι' m →ₐ[K] K) (jetMap φ hφ a) = (jetAug : Jet K ι m →ₐ[K] K) a := by
  have hcc : ∀ {ι' : Type} (φ : ι → MvPolynomial ι' K), (∀ i, φ i ∈ orig K ι') →
      ∀ q : MvPolynomial ι K, MvPolynomial.constantCoeff (MvPolynomial.aeval φ q) = MvPolynomial.constantCoeff q := by
    intro ι' φ hφ q
    induction q using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.aeval_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, hp, MvPolynomial.constantCoeff_X, mul_zero,
        constantCoeff_of_mem_orig (hφ i)]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hmap : jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl
  rw [hmap, jetAug_mk, jetAug_mk, hcc φ hφ p]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
