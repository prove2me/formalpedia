-- Prove2me | solution 1 for PIW.AdelClassFin.dictTop_hhat_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:17.028667+00:00
-- url     : https://prove2.me/submissions/4157ce2e-311a-42fa-b375-297f836fc6ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
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
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
private theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
private theorem hform_mulVec_mulVec_eq_hform_cT_mul_mul {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J M : Matrix (Fin k) (Fin k) A) (a b : Fin k → A) :
    Formalism.UG.hform σ J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) a b := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  show _ = (fun i => σ (a i)) ⬝ᵥ (((M.map σ)ᵀ * J * M) *ᵥ b)
  have e : (fun i => σ ((M *ᵥ a) i)) = M.map σ *ᵥ (fun i => σ (a i)) := by
    funext i
    exact RingHom.map_mulVec σ M a i
  rw [e, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose (M.map σ) (fun i => σ (a i)),
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (I : AutInst) (x : I.Gf) (a b : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (I.fmat x *ᵥ a) (I.fmat x *ᵥ b) = hhat I a b := by
  have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hhat
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hx]
end PIW.AdelClassFin
