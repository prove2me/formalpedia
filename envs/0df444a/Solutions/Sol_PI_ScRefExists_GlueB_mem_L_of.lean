-- Prove2me | solution 1 for PI.ScRefExists.GlueB.mem_L_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:58.952891+00:00
-- url     : https://prove2.me/submissions/864476f4-5eaf-4843-90e0-bf8a02d0691f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueB
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)
namespace PI.ScRefExists.GlueB
theorem _root_.solution (h3 : LocGlob) {x : Fin I.n → I.E} (hx : incl I x ∈ I.Lf) : x ∈ I.L := by
  refine (I.L_dual x).mpr fun y hy => ?_
  let H : VA I → I.E ⊗[I.F] Af I.F := fun v =>
    ∑ i, ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E (y i) * I.J i j) * v j
  have hinc : ∀ z : Fin I.n → I.E, H (incl I z) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J y z) := by
    intro z
    simp only [H, incl, Formalism.UG.hform, map_sum, map_mul]
  have key : ∀ v ∈ I.Lf, H v ∈ IntAf I.F I.E := by
    intro v hv
    change v ∈ Submodule.span _ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      change H (incl I (z : Fin I.n → I.E)) ∈ IntAf I.F I.E
      obtain ⟨s, hs⟩ := (I.L_dual z).mp z.2 y hy
      rw [hinc, ← hs]
      exact inclE_mem' I s
    | zero => simp [H]
    | add a b _ _ ha hb =>
      have e : H (a + b) = H a + H b := by
        simp only [H, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem ha hb
    | smul a v _ hv =>
      have e : H (a • v) = (a : I.E ⊗[I.F] Af I.F) * H v := by
        simp only [H, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      exact mul_mem a.2 hv
  have hm := key _ hx
  rw [hinc x] at hm
  obtain ⟨s, hs⟩ := h3 I _ hm
  exact ⟨s, hs⟩
end PI.ScRefExists.GlueB
