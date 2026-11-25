-- Prove2me | solution 1 for PIW.AdelClassFin.lattice_m_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:38.01917+00:00
-- url     : https://prove2.me/submissions/cecbce34-716f-4832-93a3-845090b68b86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop
import Theorems.Thm_PIW_AdelClassFin_dictTop_fmat_mul
import Theorems.Thm_PIW_AdelClassFin_dictTop_map_mulVec
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
private theorem sigR_inclE' (I : AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) :=
  Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) e 1
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : MEquiv := by
  intro I γ hγ
  have hmem : Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ ∈
      Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    have hg : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
        (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map
          (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact sigR_inclE' I _
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let c : I.Gf := ⟨_, hmem⟩
  have hfc : I.fmat c =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  refine ⟨c, ⟨γ, hγ, rfl⟩, rfl, fun x v => ?_⟩
  have K : ∀ z, I.fmat (c * x)⁻¹ *ᵥ (I.fmat c *ᵥ z) = I.fmat x⁻¹ *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← dictTop_fmat_mul, mul_inv_rev, inv_mul_cancel_right]
  constructor
  · intro hv
    refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, ?_, ?_⟩
    · show I.fmat x⁻¹ *ᵥ iv I (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v) ∈ I.Lf
      rw [← K, hfc, dictTop_map_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨w, hw, rfl⟩
    show I.fmat (c * x)⁻¹ *ᵥ iv I ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w) ∈ I.Lf
    rw [← dictTop_map_mulVec, ← hfc, K]
    exact hw
end PIW.AdelClassFin
