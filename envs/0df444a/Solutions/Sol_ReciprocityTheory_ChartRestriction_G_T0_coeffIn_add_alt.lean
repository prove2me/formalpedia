-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeffIn_add_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:09.661807+00:00
-- url     : https://prove2.me/submissions/67f79179-45ad-4816-924e-7ca355e1c672

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_eq_sum

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
theorem _root_.solution (i : V) (k : ℕ) (p q : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (p + q) = ReciprocityTheory.MultiplicativeHeights.coeffIn i k p + ReciprocityTheory.MultiplicativeHeights.coeffIn i k q := by
  classical
  rw [coeffIn_eq_sum i k _ _ MvPolynomial.support_add,
    coeffIn_eq_sum i k p (p.support ∪ q.support) Finset.subset_union_left,
    coeffIn_eq_sum i k q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [MvPolynomial.coeff_add, map_add]
end ReciprocityTheory.ChartRestriction.G.T0
