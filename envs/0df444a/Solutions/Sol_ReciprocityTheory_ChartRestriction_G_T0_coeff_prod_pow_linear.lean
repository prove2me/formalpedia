-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeff_prod_pow_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:15.787175+00:00
-- url     : https://prove2.me/submissions/abb95e5c-318c-4277-aa57-1b0e2811ec3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
import Theorems.Thm_GlobalTheory_ProductDegreeCoefficient_natDegree_le_and_coeff_prod_pow


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
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {B : Type*} [CommRing B] {T : Type*} (s : Finset T) (p : T → Polynomial B)
    (e : T → ℕ) (hp : ∀ t, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  first | exact GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow .. | (apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> first | assumption | infer_instance)
end ReciprocityTheory.ChartRestriction.G.T0
