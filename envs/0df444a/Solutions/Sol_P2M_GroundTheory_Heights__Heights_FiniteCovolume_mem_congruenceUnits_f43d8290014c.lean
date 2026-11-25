-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:06.891281+00:00
-- url     : https://prove2.me/submissions/09536868-5bf8-4e8b-b829-750539bb5d5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable (E : Type*) [Field E] [NumberField E]
omit [NumberField E]
variable {E}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]
end GroundTheory.Heights₂.Heights.FiniteCovolume
