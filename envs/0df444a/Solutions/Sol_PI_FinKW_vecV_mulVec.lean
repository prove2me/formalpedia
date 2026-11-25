-- Prove2me | solution 1 for PI.FinKW.vecV_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:29.375049+00:00
-- url     : https://prove2.me/submissions/2ca4e3c5-5807-4af6-8bcd-a4b7efdfc5bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
import Theorems.Thm_PI_FinKW_psiV_tauF
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge
namespace PI.FinKW
theorem _root_.solution (I : AutInst) (h : HAd I) (v : HeightOneSpectrum (𝓞 I.F))
    (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    vecV I v (ofHAFin I h *ᵥ x) =
      ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ vecV I v x := by
  funext i
  simp only [vecV]
  have := RingHom.map_mulVec (psiV I v).toRingHom (ofHAFin I h) x i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext a b
  simp [ofHAFin, Formalism.L2.SG.Sub.compV, Formalism.UG.bc, psiV_tauF]
end PI.FinKW
