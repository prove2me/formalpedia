-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:14.967309+00:00
-- url     : https://prove2.me/submissions/91591369-e783-4f49-8d54-f7453d050ad3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection

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
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v g = 0 := by
  simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
end GroundTheory.Heights₂.Heights
