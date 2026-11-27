-- Prove2me | solution 1 for PI.VolStabSW.idxAA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:44.301505+00:00
-- url     : https://prove2.me/submissions/5568a4f2-9a2c-4243-adc6-c0b51a4d390c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
import Theorems.Thm_PI_VolStabSW_measure_eq_relIndex_mul
import Theorems.Thm_PI_VolStabSW_smul_mem_hermO
import Theorems.Thm_PI_VolStabSW_LatFactsW_isOpen_hermO
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_latFacts_holds
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_mem_smulSub
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv
import Theorems.Thm_PI_VolStabSW_unifV_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
namespace PI.VolStabSW
theorem _root_.solution (hL : IdxL) (hH : IdxH) : IdxAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv
  intro μ ν hμ hν
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨l1, -, -, l4, l5, -, -⟩ := latFacts_holds F E σ d b a M v
  have hq : Nat.card (𝓞 F ⧸ v.asIdeal) ≠ 0 := by
    have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    exact Nat.card_pos.ne'
  have hLi := hL F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b v
  refine ⟨?_, ?_⟩
  · have e := measure_eq_relIndex_mul μ (lamF b v a M 0) (latSub b v a M) l4
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet (l1 0).measurableSet
      (by rw [hLi]; exact pow_ne_zero _ hq)
    rw [hLi, Nat.cast_pow] at e
    exact e
  · have e := measure_eq_relIndex_mul ν (hF b v σ a 0) (hermO b v σ a)
      (by intro x hx
          simp only [hF, mem_smulSub] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact smul_mem_hermO b v σ a (pow_mem (unifV_spec v).2.2 _) hp)
      (LatFactsW.isOpen_hermO b v σ a).measurableSet (l5 0).measurableSet
      (by rw [hv]; exact pow_ne_zero _ hq)
    rw [hv, Nat.cast_pow] at e
    exact e
end PI.VolStabSW
