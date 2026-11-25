-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_parVar_injective_284065df29b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:10.879813+00:00
-- url     : https://prove2.me/submissions/e5de41d9-0af1-492e-aaf0-84f5ca300d14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
theorem _root_.solution : Function.Injective (parVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parVar]
end GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
