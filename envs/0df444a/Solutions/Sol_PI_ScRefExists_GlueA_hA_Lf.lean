-- Prove2me | solution 1 for PI.ScRefExists.GlueA.hA_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:17:49.023864+00:00
-- url     : https://prove2.me/submissions/c4b28dde-c919-4a18-80f7-3aabf1c26e52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_mem
import Theorems.Thm_PI_ScRefExists_GlueA_sigA_mem
import Theorems.Thm_PI_ScRefExists_GlueA_hA_add_left
import Theorems.Thm_PI_ScRefExists_GlueA_hA_add_right
import Theorems.Thm_PI_ScRefExists_GlueA_hA_smul_left
import Theorems.Thm_PI_ScRefExists_GlueA_hA_smul_right
import Theorems.Thm_PI_ScRefExists_GlueA_hA_zero_left
import Theorems.Thm_PI_ScRefExists_GlueA_hA_zero_right
import Theorems.Thm_PI_ScRefExists_GlueA_hA_incl
import Theorems.Thm_PI_ScRefExists_GlueA_hG_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ I.Lf) : hA I x y ∈ IntAf I.F I.E := by
  have key : ∀ a ∈ I.L, ∀ w ∈ I.Lf, hA I (incl I a) w ∈ IntAf I.F I.E := by
    intro a ha w hw
    change w ∈ Submodule.span (IntAf I.F I.E) _ at hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨b, hb⟩, rfl⟩ := hz
        show hA I (incl I a) (incl I b) ∈ IntAf I.F I.E
        rw [hA_incl]
        exact inclE_mem I (hG_int I ha hb)
    | zero => rw [hA_zero_right]; exact zero_mem _
    | add u v _ _ hu hv => rw [hA_add_right]; exact add_mem hu hv
    | smul c u _ hu =>
        show hA I (incl I a) ((c : I.E ⊗[I.F] Af I.F) • u) ∈ IntAf I.F I.E
        rw [hA_smul_right]
        exact mul_mem c.2 hu
  change x ∈ Submodule.span (IntAf I.F I.E) _ at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨a, ha⟩, rfl⟩ := hz
      exact key a ha y hy
  | zero => rw [hA_zero_left]; exact zero_mem _
  | add u v _ _ hu hv => rw [hA_add_left]; exact add_mem hu hv
  | smul c u _ hu =>
      show hA I ((c : I.E ⊗[I.F] Af I.F) • u) y ∈ IntAf I.F I.E
      rw [hA_smul_left]
      exact mul_mem (sigA_mem I c.2) hu
end PI.ScRefExists.GlueA
