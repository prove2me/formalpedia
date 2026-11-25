-- Prove2me | solution 1 for PI.VolStabW.VolAAW.ev_pow_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:44.631108+00:00
-- url     : https://prove2.me/submissions/93efe303-cfcb-4948-96e2-09dc8b51f5f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_VolStabW_unifV_spec
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isCompact_integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabW.VolAAW
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {W : Set (Fv F v)} (hW : W ∈ 𝓝 (0 : Fv F v)) :
    ∃ n : ℕ, ∀ s ∈ v.adicCompletionIntegers F, unifV v ^ n * s ∈ W := by
  have hK : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  have hP : ∀ s ∈ (v.adicCompletionIntegers F : Set (Fv F v)),
      ∀ᶠ z : Fv F v × Fv F v in 𝓝 ((0 : Fv F v), s), z.1 * z.2 ∈ W := by
    intro s _
    have hc : Continuous (fun z : Fv F v × Fv F v => z.1 * z.2) := continuous_fst.mul continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : Fv F v)) (P := fun e s => e * s ∈ W) hP
  obtain ⟨n, hn⟩ := ((unifV_spec v).2.1.eventually h).exists
  exact ⟨n, hn⟩
end PI.VolStabW.VolAAW
