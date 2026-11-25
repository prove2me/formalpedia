-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.adaptedProjection_psiV_mem_integers_of_mem_intAf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:08:26.422818+00:00
-- url     : https://prove2.me/submissions/9a933475-541f-46db-b9d6-4482a70175dc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_gp_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_alg_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_sig_alg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_conj_intOE
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_psiV_inclE
import Theorems.Thm_PI_FinKW_LocTo_psiV_tmul
import Theorems.Thm_PI_FinKW_psiV_tmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_inclE
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sigV_inclV
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (t : I.E ⊗[I.F] Af I.F) (ht : t ∈ IntAf I.F I.E) :
    p1 (PI.FinKW.psiV I v t) ∈ OV I v ∧ p1 (sigV I v (PI.FinKW.psiV I v t)) ∈ OV I v := by
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have e1 : PI.FinKW.psiV I v ((y : I.E) ⊗ₜ[I.F] (1 : Af I.F)) = inclV I v (y : I.E) :=
        psiV_inclE I v (y : I.E)
      rw [e1, spl_sigV_inclV]
      exact ⟨gp_int I v ε p1 hp _ y.2, gp_int I v ε p1 hp _ (conj_intOE I _ y.2)⟩
    · have e1 : PI.FinKW.psiV I v ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) =
          algebraMap (KV I v) (RV I v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (y : Af I.F)) := by
        rw [PI.FinKW.LocTo.psiV_tmul, alg_eq]
      have hy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (y : Af I.F) ∈ OV I v := y.2 v
      rw [e1, sig_alg, hp.1]
      exact ⟨hy, hy⟩
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => simp only [map_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  | neg a _ ha => simp only [map_neg]; exact ⟨neg_mem ha.1, neg_mem ha.2⟩
  | mul a b _ _ ha hb => simp only [map_mul]; exact ⟨mul_mem ha.1 hb.1, mul_mem ha.2 hb.2⟩
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
