-- Prove2me | solution 1 for PI.VolSemiDirect.W.SR.sr1_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:17.304446+00:00
-- url     : https://prove2.me/submissions/ab8c607b-0b92-4950-bf9b-f870e136cecd

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
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (hA : Cj.HasStableRangeOne A) (hB : Cj.HasStableRangeOne B) :
    Cj.HasStableRangeOne (A × B) := by
  intro a b x y h
  obtain ⟨t1, ht1⟩ := hA a.1 b.1 x.1 y.1 (by simpa using congrArg Prod.fst h)
  obtain ⟨t2, ht2⟩ := hB a.2 b.2 x.2 y.2 (by simpa using congrArg Prod.snd h)
  exact ⟨(t1, t2), Prod.isUnit_iff.2 ⟨ht1, ht2⟩⟩
end PI.VolSemiDirect.W.SR
