-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:43.725662+00:00
-- url     : https://prove2.me/submissions/cd7fb641-b821-432a-bff4-407ae1a5cf58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩
end GroundTheory.Heights₂.Heights
