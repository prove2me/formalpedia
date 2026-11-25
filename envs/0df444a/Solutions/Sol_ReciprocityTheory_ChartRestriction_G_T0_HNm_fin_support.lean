-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HNm.fin_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:00.048153+00:00
-- url     : https://prove2.me/submissions/b874ffb3-f768-46c6-b757-526d52dab5cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_nonneg_of_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_wt_add_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_wt_add_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_heightOne_principal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm
open IsDedekindDomain IsLocalRing
variable {R F L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]
namespace ReciprocityTheory.ChartRestriction.G.T0.HNm
theorem _root_.solution [FiniteDimensional F L] (y : L) (hy : y ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ ∃ w ∈ OverR R F L p, w y ≠ 0}.Finite := by
  classical
  letI : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  haveI : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ z : L, IsAlgebraic R z := fun z =>
    (IsFractionRing.isAlgebraic_iff R F L).mpr (Algebra.IsIntegral.isIntegral (R := F) z).isAlgebraic
  obtain ⟨d, hd0, hd⟩ := (halg y).exists_integral_multiple
  obtain ⟨e, he0, he⟩ := (halg y⁻¹).exists_integral_multiple
  have hD0 : d * e ≠ 0 := mul_ne_zero hd0 he0

  have key : ∀ p : Ideal R, (∃ w ∈ OverR R F L p, w y ≠ 0) → d * e ∈ p := by
    rintro p ⟨w, hw, hwy⟩
    simp only [OverR, Set.mem_setOf_eq] at hw
    by_contra hde
    have hdp : d ∉ p := fun h => hde (p.mul_mem_right e h)
    have hep : e ∉ p := fun h => hde (p.mul_mem_left d h)
    have h0 : ∀ r : R, 0 ≤ w (algebraMap R L r) := fun r => (hw.2 r).1
    have hwd : w (algebraMap R L d) = 0 :=
      le_antisymm (not_lt.mp fun h => hdp ((hw.2 d).2.mp h)) (hw.2 d).1
    have hwe : w (algebraMap R L e) = 0 :=
      le_antisymm (not_lt.mp fun h => hep ((hw.2 e).2.mp h)) (hw.2 e).1
    have h1 : 0 ≤ w (d • y) := nonneg_of_isIntegral w h0 hd
    have h2 : 0 ≤ w (e • y⁻¹) := nonneg_of_isIntegral w h0 he
    rw [Algebra.smul_def, AddValuation.map_mul, hwd, zero_add] at h1
    rw [Algebra.smul_def, AddValuation.map_mul, hwe, zero_add] at h2
    have h3 : w y + w y⁻¹ = 0 := by
      rw [← AddValuation.map_mul w y y⁻¹, mul_inv_cancel₀ hy, AddValuation.map_one]
    exact hwy (wt_add_eq_zero h1 h2 h3)
  have hsub : {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ ∃ w ∈ OverR R F L p, w y ≠ 0} ⊆
      (fun q : R => Ideal.span {q}) '' {q | q ∈ UniqueFactorizationMonoid.factors (d * e)} := by
    rintro p ⟨hp, hh, hw⟩
    haveI := hp
    obtain ⟨g, hg, rfl⟩ := ValUFD.heightOne_principal p hh
    have hdvd : g ∣ d * e := Ideal.mem_span_singleton.mp (key _ hw)
    obtain ⟨q, hq, hgq⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hD0 hg.irreducible hdvd
    exact ⟨q, hq, Ideal.span_singleton_eq_span_singleton.mpr hgq.symm⟩
  exact ((Multiset.finite_toSet _).image _).subset hsub
end ReciprocityTheory.ChartRestriction.G.T0.HNm
