-- Prove2me | solution 1 for PI.VolStabSW.latFacts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:35.280666+00:00
-- url     : https://prove2.me/submissions/0eb64fae-7b75-4284-91d5-058a2b5d0363

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
import Theorems.Thm_PI_VolStabSW_LatFactsW_smul_mem_latSub
import Theorems.Thm_PI_VolStabSW_LatFactsW_isOpen_hermO
import Theorems.Thm_PI_VolStabSW_LatFactsW_isCompact_hermO
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabSW_coe_smulSub
import Theorems.Thm_PI_VolStabSW_eventually_smul_sub
import Theorems.Thm_PI_VolStabSW_isCompact_smulSub
import Theorems.Thm_PI_VolStabSW_isOpen_smulSub
import Theorems.Thm_PI_VolStabSW_mem_smulSub
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
open NumberField IsDedekindDomain Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW LatFactsW
namespace PI.VolStabSW
theorem _root_.solution : LatFacts := by
  intro F E _ _ _ _ _ σ d b a M v
  obtain ⟨h0, hπ, hint⟩ := unifV_spec v
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (PositiveNearLattice.isClopen_latV b v a M).isOpen
  · exact isCompact_smulSub _ _ (PositiveNearLattice.isCompact_latV b v a M)
  · intro m n hmn x hx
    simp only [lamF, mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨unifV v ^ (n - m) • p, smul_mem_latSub b v (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  · intro x hx
    simp only [lamF, mem_smulSub] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact smul_mem_latSub b v (pow_mem hint _) hp
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (isOpen_hermO b v σ a)
  · exact isCompact_smulSub _ _ (isCompact_hermO b v σ a)
  · intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (hermO b v σ a : Set (HermR (Fv F v) σ a))
      (isCompact_hermO b v σ a) (fun k => unifV v ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN
    refine ⟨k, ?_⟩
    simp only [hF, coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp
end PI.VolStabSW
