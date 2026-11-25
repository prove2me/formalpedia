-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:17.822785+00:00
-- url     : https://prove2.me/submissions/3d300a96-4df0-4439-a41c-4c3424bc1be6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) (i : V)
    (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (MvPolynomial.map φ P) =
      MvPolynomial.map φ (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) := by
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [MvPolynomial.support_map_of_injective _ hφ, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.coeff_map]
end ReciprocityTheory.ChartRestriction.G.T0
