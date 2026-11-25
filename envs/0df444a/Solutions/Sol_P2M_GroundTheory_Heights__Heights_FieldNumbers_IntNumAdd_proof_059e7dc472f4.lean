-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumAdd_proof_059e7dc472f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:47.681168+00:00
-- url     : https://prove2.me/submissions/488f3f97-e0e6-4bf4-8d1b-5729ed05ae93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace IntNumAdd
theorem _root_.solution (h1 : MixedDiffConst.Statement.{u}) : IntNumAdd.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs i b b'
  have e := fun x : K → ℤ => (h1 F K ι I hI hrel n hn).1 (Function.update bs i x)
  have e' := (tendsto_sub_const_atTop b).eventually (e b')
  obtain ⟨m, h0, hb, hb'⟩ := ((e (b + b')).and ((e b).and e')).exists
  rw [← h0, ← hb, ← hb']
  exact mixedDiff_update_add bs i b b' _ m
end IntNumAdd
end GroundTheory.Heights₂.Heights.FieldNumbers
