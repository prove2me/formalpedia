-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.exists_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:34.178797+00:00
-- url     : https://prove2.me/submissions/f56310f3-97ba-4f5f-b28d-ca14c8cabb05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_addv_eq_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F)
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
theorem _root_.solution (n : AddValuation L (WithTop ℤ) → ℤ) :
    ∃ g : L, g ≠ 0 ∧ ∀ w ∈ PlacesOver O L, w g = n w := by
  classical
  obtain ⟨_, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F L
  haveI : IsPrincipalIdealRing (integralClosure O L) := IsPrincipalIdealRing.of_finite_maximals hmax
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O L) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  letI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  let π : HeightOneSpectrum (integralClosure O L) → integralClosure O L := fun v =>
    Submodule.IsPrincipal.generator v.asIdeal
  have hπ : ∀ v, v.asIdeal = Ideal.span {π v} := fun v =>
    (Ideal.span_singleton_generator v.asIdeal).symm
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => v.ne_bot (by rw [hπ v, Ideal.span_singleton_eq_bot.mpr h])
  have hπL : ∀ v, algebraMap (integralClosure O L) L (π v) ≠ 0 := fun v =>
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).mpr (hπ0 v)
  have hval : ∀ v v' : HeightOneSpectrum (integralClosure O L),
      v'.valuation L (algebraMap _ L (π v)) = if v' = v then exp (-1 : ℤ) else 1 := by
    intro v v'
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    split_ifs with h
    · subst h
      exact HeightOneSpectrum.intValuation_singleton _ (hπ0 v') (hπ v')
    · apply le_antisymm (v'.intValuation_le_one _)
      rw [← not_lt, v'.intValuation_lt_one_iff_mem]
      intro hmem
      apply h
      have hle : v.asIdeal ≤ v'.asIdeal := by
        rw [hπ v, Ideal.span_singleton_le_iff_mem]
        exact hmem
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm
  let g : L := ∏ v, (algebraMap _ L (π v)) ^ (n (addv L v))
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hπL v)
  have hgv : ∀ v' : HeightOneSpectrum (integralClosure O L), v'.valuation L g = exp (-(n (addv L v'))) := by
    intro v'
    simp only [g, map_prod, map_zpow₀, hval]
    rw [Finset.prod_eq_single v']
    · rw [if_pos rfl, ← exp_zsmul, smul_eq_mul, mul_neg_one]
    · intro v _ hv
      rw [if_neg (Ne.symm hv), one_zpow]
    · simp
  refine ⟨g, hg0, fun w hw => ?_⟩
  obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
  rw [addv_apply v hg0, hgv, log_exp, neg_neg]
end ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
