-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.polyIn_monomial_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:25.392502+00:00
-- url     : https://prove2.me/submissions/5f457032-ee9d-47f0-a67e-c7cf31bbde07

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
theorem _root_.solution (i : V) (t : V →₀ ℕ) (ht : t i = 0) (a : R) :
    asPolyInVar i (MvPolynomial.monomial t a) = Polynomial.C (MvPolynomial.monomial t a) := by
  rw [asPolyInVar, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Polynomial.C_mul,
    Finsupp.prod, Finsupp.prod, map_prod, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvi : v ≠ i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hv) ht
  rw [if_neg hvi, map_pow]
end ReciprocityTheory.ChartRestriction.G.T0
