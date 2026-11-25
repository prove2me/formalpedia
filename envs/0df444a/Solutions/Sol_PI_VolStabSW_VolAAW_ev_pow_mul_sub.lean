-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.ev_pow_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:32.301399+00:00
-- url     : https://prove2.me/submissions/c6d2c932-30ab-44a5-a64b-42ae0dc9239d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_VolStabSW_HasDens_le
import Theorems.Thm_PI_VolStabSW_unifV_spec
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
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {W : Set (Fv F v)} (hW : W ∈ 𝓝 (0 : Fv F v)) :
    ∃ n : ℕ, ∀ s ∈ v.adicCompletionIntegers F, unifV v ^ n * s ∈ W := by
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation W).mp hW
  obtain ⟨n, hn⟩ := ((unifV_spec v).2.1.eventually
    ((Valued.is_topological_valuation _).mpr ⟨γ, subset_rfl⟩)).exists
  refine ⟨n, fun s hs => hγ ?_⟩
  have hs' : Valued.v s ≤ 1 := hs
  have hs'' : Valued.v.restrict s ≤ 1 := by
    first
      | simpa using hs'
      | exact_mod_cast hs'
      | (rw [← map_one Valued.v.restrict]; simpa [Valuation.restrict_le_iff] using hs')
  show Valued.v.restrict (unifV v ^ n * s) < _
  rw [map_mul]
  have h1 : Valued.v.restrict (unifV v ^ n) * Valued.v.restrict s ≤ Valued.v.restrict (unifV v ^ n) := by
    first
      | exact mul_le_of_le_one_right' hs''
      | exact (mul_le_mul' le_rfl hs'').trans (mul_one _).le
      | exact mul_le_of_le_one_right (zero_le _) hs''
  exact lt_of_le_of_lt h1 hn
end PI.VolStabSW.VolAAW
