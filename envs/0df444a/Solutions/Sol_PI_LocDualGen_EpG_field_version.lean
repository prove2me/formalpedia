-- Prove2me | solution 1 for PI.LocDualGen.EpG.field_version
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:34.149352+00:00
-- url     : https://prove2.me/submissions/158539ea-4a4b-4445-9fd6-ce013fc8ad44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualCase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDual
import Theorems.Thm_PI_LocDualGen_EpF_selfDual_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpG
namespace PI.LocDualGen.EpG
theorem _root_.solution (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] (hr : finrank K L = 2)
    (O : Subring L) (hO : ∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x)
    (hU : ∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)})
    (x : L) : (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  have hOC : ∀ z : L, z ∈ O ↔ z ∈ integralClosure 𝒪[K] L := fun z => (hO z).trans Iff.rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm : 𝓂[K] = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hcoe : ∀ c : integralClosure 𝒪[K] L,
      ((c * algebraMap 𝒪[K] (integralClosure 𝒪[K] L) ϖ : integralClosure 𝒪[K] L) : L) =
        (c : L) * algebraMap K L (ϖ : K) := by
    intro c
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[K] K L]
    rfl
  have hmem : ∀ z : integralClosure 𝒪[K] L,
      z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] ↔
        (z : L) ∈ Submodule.span O {algebraMap K L (ϖ : K)} := by
    intro z
    rw [hm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨c, (hOC c).2 c.2⟩, ?_⟩
      rw [← hc, hcoe]
      rfl
    · rintro ⟨a, ha⟩
      refine ⟨⟨a, (hOC a).1 a.2⟩, Subtype.ext ?_⟩
      rw [hcoe, ← ha]
      rfl
  have hU' : ∀ z : integralClosure 𝒪[K] L,
      z * z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] →
        z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] := by
    intro z hz
    rw [hmem] at hz ⊢
    exact hU ϖ hϖ z ((hOC z).2 z.2) hz
  have key := PI.LocDualGen.EpF.selfDual_field K L hU' x
  simpa only [hOC] using key
end PI.LocDualGen.EpG
