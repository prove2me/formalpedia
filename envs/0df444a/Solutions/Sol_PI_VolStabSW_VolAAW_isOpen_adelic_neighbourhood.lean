-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.isOpen_adelic_neighbourhood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:01.162609+00:00
-- url     : https://prove2.me/submissions/7c8c48e3-fd83-4445-af0b-f5b944a09414

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
theorem _root_.solution (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsOpen (U0 I n : Set (Af F)) := by
  have hO : ∀ w : HeightOneSpectrum (𝓞 F), IsOpen (w.adicCompletionIntegers F : Set (Fv F w)) := by
    intro w
    first
      | exact Valued.isOpen_valuationSubring _
      | exact Valued.valuationSubring_isOpen _
      | exact (w.adicCompletionIntegers F).isOpen
  have hev : ∀ w : HeightOneSpectrum (𝓞 F), Continuous fun y : Af F => y w := by
    intro w
    first
      | exact RestrictedProduct.continuous_eval w
      | exact RestrictedProduct.continuous_apply w
  have h1 : IsOpen {y : Af F | ∀ w, y w ∈ w.adicCompletionIntegers F} := by
    first
      | exact RestrictedProduct.isOpen_forall_mem hO
      | exact RestrictedProduct.isOpen_forall_mem (fun w => hO w)
  have h2 : IsOpen {y : Af F | ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} := by
    have e : {y : Af F | ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} =
        ⋂ w ∈ I, {y : Af F | (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} := by
      ext y
      simp
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hO w).preimage (continuous_const.mul (hev w))
  exact h1.inter h2
end PI.VolStabSW.VolAAW
