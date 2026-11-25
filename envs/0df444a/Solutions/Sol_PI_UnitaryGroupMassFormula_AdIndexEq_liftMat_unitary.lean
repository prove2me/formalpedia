-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.liftMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:31.916524+00:00
-- url     : https://prove2.me/submissions/beb5fa91-7866-487f-8671-cc2c6be3fde2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
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
private theorem psiV_sigR_eq_sigV_psiV (I : AutInst) (w : HeightOneSpectrum (𝓞 I.F))
    (x : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I w (Formalism.UG.sigR I.cm.sig (Af I.F) x) = sigV I w (PI.FinKW.psiV I w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [Formalism.UG.sigR, sigV, PI.FinKW.psiV, AlgEquiv.coe_algHom, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
private theorem psiV_inclE' (I : AutInst) (w : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I w (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I w e := by
  simp [Formalism.UG.inclE, inclV, PI.FinKW.psiV, AlgEquiv.coe_algHom, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.map_tmul]
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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) (hg : g ∈ Uv I v) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (liftMat I v g.val) *
              I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * liftMat I v g.val =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hJ : ∀ w, (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I w).toRingHom =
      I.J.map (inclV I w) := by
    intro w
    ext a b
    simp [psiV_inclE']
  have hC : ∀ w, ∀ M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F),
      (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M).map (PI.FinKW.psiV I w).toRingHom =
        Formalism.UG.cT (sigV I w) (M.map (PI.FinKW.psiV I w).toRingHom) := by
    intro w M
    ext a b
    simp [Formalism.UG.cT, psiV_sigR_eq_sigV_psiV]
  have hmap : ∀ w, (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (liftMat I v g.val) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * liftMat I v g.val).map
          (PI.FinKW.psiV I w).toRingHom =
      (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I w).toRingHom := by
    intro w
    rw [Matrix.map_mul, Matrix.map_mul, hC, hJ]
    by_cases hw : w = v
    · subst hw
      rw [liftMat_map_same]
      first
      | exact hg
      | simpa [Uv, Formalism.UG.UJ] using hg
    · rw [liftMat_map_ne I hw, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  apply eq_of_forall_psiV_eq I
  intro w
  have h1 := congrFun (congrFun (hmap w) i) j
  simpa using h1
end PI.UnitaryGroupMassFormula.AdIndexEq
