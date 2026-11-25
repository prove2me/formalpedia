-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DualI.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:03.286495+00:00
-- url     : https://prove2.me/submissions/0254cec4-c3d9-412a-b041-6612dd103bb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_hform_smul_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_hform_add_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_hform_zero_right
import Theorems.Thm_Formalism_UG_P_csDual_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DualI
open Formalism.UG Formalism.UG.P
namespace PI.UnitaryGroupMassFormula.LCG.DualI
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) (hw : w ∈ I.L)
    (x : Fin I.n → AA I) (hx : x ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L) :
    hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) (fun i => iA I (w i)) x ∈ SS I := by
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, hl, rfl⟩ := h
    exact csDual_span I.cm.sig I.J I.L l ((I.L_dual l).mp hl) (fun i => iA I (w i))
      (Submodule.subset_span ⟨w, hw, rfl⟩)
  | zero =>
    rw [hform_zero_right]
    exact (SS I).zero_mem
  | add x y _ _ hx hy =>
    rw [hform_add_right]
    exact (SS I).add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, hform_smul_right]
    exact (SS I).mul_mem a.2 hx
end PI.UnitaryGroupMassFormula.LCG.DualI
