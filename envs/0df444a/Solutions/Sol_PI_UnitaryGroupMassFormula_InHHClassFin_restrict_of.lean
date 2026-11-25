-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.restrict_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:41.769333+00:00
-- url     : https://prove2.me/submissions/a0532f47-b31f-4316-a0d1-b67cb4fc9d56

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (hE : FrameExists) (hIso : FrameIso) (hG : FrameGram) (hRat : FrameRat)
    (hLev : LevelStep) (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (hS : DefiniteCompl I S) :
    Restrict I S := by
  obtain ⟨fr⟩ := hE I S hS
  obtain ⟨Φ, hΦ⟩ := hIso I S fr
  obtain ⟨hH, hU, hD⟩ := hG I S fr hS
  refine ⟨fr.k, fr.J', Φ, hH, hU, hD, hRat I S fr Φ hΦ, ?_⟩
  intro g hg
  obtain ⟨N, hNL, hNi, hNK⟩ := hLev I fr.m fr.k fr.B fr.Bi fr.mul_inv fr.inv_mul fr.J' g hg
  have hle : N ≤ stdLevel I fr.J' ⊓ (congS I S g).map Φ.toMonoidHom := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hNL hy, Subgroup.mem_map.mpr ⟨Φ.symm y, ?_, by simp⟩⟩
    exact Subgroup.subset_closure (hNK y hy _ (hΦ y))
  exact fun h0 => hNi (Subgroup.relIndex_eq_zero_of_le_left hle h0)
end PI.UnitaryGroupMassFormula.InHHClassFin
