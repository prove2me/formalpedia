-- Prove2me | solution 1 for PI.WAU.Cpt.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:37.771287+00:00
-- url     : https://prove2.me/submissions/99807814-596f-4ab2-ab13-7e6037e5b1c9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_PI_WAU_Cpt_mulVec_mem_Lf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (N : ℕ) (p : Cset I N) : psi I N p ∈ I.Kset := by
  intro y
  have h1 := mulVec_mem_Lf I _ p.2.2.2.2.2.1
  have h2 := mulVec_mem_Lf I _ p.2.2.2.2.2.2
  show y ∈ I.Lf ↔ matOf I p.1.1 *ᵥ y ∈ I.Lf
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, p.2.2.2.1, Matrix.one_mulVec] at this
end PI.WAU.Cpt
