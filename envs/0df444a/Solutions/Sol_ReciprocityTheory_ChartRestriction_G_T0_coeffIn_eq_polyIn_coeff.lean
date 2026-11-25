-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_eq_polyIn_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:29.278991+00:00
-- url     : https://prove2.me/submissions/7ba89ca1-807d-4618-9ebd-b6e52e20fd35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_add_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_polyIn_monomial

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
theorem _root_.solution (i : V) (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k P = (asPolyInVar i P).coeff k := by
  classical
  refine MvPolynomial.induction_on' P (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [coeffIn_eq_sum i k _ {u} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, polyIn_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases h : u i = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rw [coeffIn_add_alt, map_add, Polynomial.coeff_add, hp, hq]
end ReciprocityTheory.ChartRestriction.G.T0
