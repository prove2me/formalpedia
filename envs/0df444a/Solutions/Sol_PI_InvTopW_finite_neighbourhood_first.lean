-- Prove2me | solution 1 for PI.InvTopW.finite_neighbourhood_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:08.538507+00:00
-- url     : https://prove2.me/submissions/d9e0d72e-ea9a-4249-9349-be2d51e7afbf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Theorems.Thm_PI_InvTopW_isOpen_intAd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Topology Filter
namespace PI.InvTopW
theorem _root_.solution : FinNhdA := by
  intro F _ _ N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have : (N : FiniteAdeleRing (𝓞 F) F) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F) := by
      simp
    rw [this]
    exact (IsUnit.mk0 _ hNF).map _
  obtain ⟨u, hu⟩ := hu
  have hcont : Continuous (fun a : FiniteAdeleRing (𝓞 F) F => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) * a) := continuous_const.mul continuous_id
  refine Filter.mem_of_superset (((isOpen_intAd F).preimage hcont).mem_nhds ?_) ?_
  · simp only [Set.mem_preimage, mul_zero, SetLike.mem_coe]
    exact zero_mem _
  · intro a ha
    refine ⟨_, ha, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
end PI.InvTopW
