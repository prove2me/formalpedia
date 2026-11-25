-- Prove2me | solution 1 for PI.VolStabW.exists_unif_Fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:07.271819+00:00
-- url     : https://prove2.me/submissions/baa84bee-cf90-465d-bdef-6600cbde330f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallySmulSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDxSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExistsUnifFv
import Theorems.Thm_PI_VolStabW_HasDens_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le
end PI.VolStabW
