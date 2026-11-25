-- Prove2me | solution 1 for PI.VolSemiDirect.W.SR.stable_rank_one_pi_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:23.147548+00:00
-- url     : https://prove2.me/submissions/9fbf4538-7e59-42d1-8406-5d5509d9faea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HasStableRangeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.SR
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct
namespace PI.VolSemiDirect.W.SR
theorem _root_.solution {ι : Type} {K : ι → Type} [∀ i, Field (K i)] : Cj.HasStableRangeOne (∀ i, K i) := by
  classical
  intro a b x y h
  refine ⟨fun i => if a i = 0 then 1 else 0, Pi.isUnit_iff.2 fun i => ?_⟩
  have hi : a i * x i + b i * y i = 1 := by simpa using congrFun h i
  by_cases ha : a i = 0
  · have hb : b i ≠ 0 := by
      rintro hb
      simp [ha, hb] at hi
    simp [ha, hb]
  · simp [ha]
end PI.VolSemiDirect.W.SR
