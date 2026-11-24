-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:46.342784+00:00
-- url     : https://prove2.me/submissions/ab8e86fd-5db6-4674-a9a6-79dc3fafad6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) :
    (Ideal.span {(q : 𝓞 L)} : Ideal (𝓞 L)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hq.ne_zero
end GroundTheory.Heights₂.Heights.NineStatements
