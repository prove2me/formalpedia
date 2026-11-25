-- Prove2me | solution 1 for PI.HtPlacesSumWork.mem_range_plOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:02.341507+00:00
-- url     : https://prove2.me/submissions/b0443633-6aeb-4e6f-a635-4a8041e44868

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_mem_vRing
import Theorems.Thm_PI_HtPlacesSumWork_valPl_max_iff
import Theorems.Thm_PI_HtPlacesSumWork_eq_addv
import Theorems.Thm_PI_HtPlacesSumWork_plOf_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
namespace PI.HtPlacesSumWork
theorem _root_.solution {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ Q, plOf O L Q = w := by
  let f : integralClosure O L →+* vRing w := (algebraMap (integralClosure O L) L).codRestrict (vRing w)
    (fun b => (valPl_mem_vRing w _).2 (plOf_nonneg hw b))
  let Q : Ideal (integralClosure O L) := (maximalIdeal (vRing w)).comap f
  have hQmem : ∀ b : integralClosure O L, b ∈ Q ↔ 0 < w (algebraMap (integralClosure O L) L b) :=
    fun b => Ideal.mem_comap.trans (valPl_max_iff (vRing w) w (valPl_mem_vRing w) (f b))
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  have hQne : Q ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field O)
    intro hb
    have hm : algebraMap O (integralClosure O L) a ∈ Q := by
      rw [hQmem, ← IsScalarTower.algebraMap_apply]
      exact ((hw.2 a).2).2 ha
    rw [hb, Ideal.mem_bot] at hm
    exact ha0 (hinj (by rw [hm, map_zero]))
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
  refine ⟨⟨Q, hmax⟩, ?_⟩
  symm
  exact eq_addv _ w hw.1 (fun b => plOf_nonneg hw b) (fun b => (hQmem b).symm)
end PI.HtPlacesSumWork
