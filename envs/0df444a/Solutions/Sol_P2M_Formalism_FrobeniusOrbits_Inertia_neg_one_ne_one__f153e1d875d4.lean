-- Prove2me | solution 1 for P2M_Formalism_FrobeniusOrbits_Inertia_neg_one_ne_one__f153e1d875d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:12.704928+00:00
-- url     : https://prove2.me/submissions/ae42983a-6125-4b17-bf3b-32724ff314cd

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  simp at h'
end Formalism.FrobeniusOrbits.Inertia
