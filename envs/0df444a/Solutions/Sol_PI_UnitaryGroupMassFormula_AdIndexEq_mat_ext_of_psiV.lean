-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.mat_ext_of_psiV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:42.05784+00:00
-- url     : https://prove2.me/submissions/cc4a29d9-bb3c-431b-8c4b-c4698e10e1d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
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


section
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
private theorem eq_of_forall_evalV_eq {F : Type} [Field F] [NumberField F] (a b : Af F)
    (h : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b) : a = b :=
  Subtype.ext (funext fun v => h v)
private theorem tensorBasis_repr_psiV_eq_evalV_repr_comm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : I.E ⊗[I.F] Af I.F) (i : Module.Free.ChooseBasisIndex I.F I.E) :
    (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Free.chooseBasis I.F I.E)).repr
        (PI.FinKW.psiV I v z) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        ((Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr
          (Algebra.TensorProduct.comm I.F I.E (Af I.F) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [PI.FinKW.psiV, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (h : ∀ v, M.map (PI.FinKW.psiV I v).toRingHom = N.map (PI.FinKW.psiV I v).toRingHom) :
    M = N := by
  ext i j
  have hij : ∀ v, PI.FinKW.psiV I v (M i j) = PI.FinKW.psiV I v (N i j) := fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa [Matrix.map_apply] using this
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  apply (Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr.injective
  refine Finsupp.ext fun k => ?_
  apply eq_of_forall_evalV_eq
  intro v
  rw [← tensorBasis_repr_psiV_eq_evalV_repr_comm, ← tensorBasis_repr_psiV_eq_evalV_repr_comm, hij v]
end PI.UnitaryGroupMassFormula.AdIndexEq
