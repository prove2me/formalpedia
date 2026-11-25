-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:40.626878+00:00
-- url     : https://prove2.me/submissions/20f2a303-57bc-4f60-9f46-6c74b4251f38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_factor
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_uMat_mul_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_Jm_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_coordV
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LCG_ap_hP__62d51219ff0c
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_AQ
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_QJQ
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_star
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_ker
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ)
    (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ z : Fin I.n → ℂ, (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ *ᵥ z = 0 → amat I x y v δ *ᵥ z = 0 := by
  intro z hz
  obtain ⟨X, hX⟩ := ap_factor δ (hM I b') (ap_ker I δ k u b' hu hsp hb hperp)
  set Φ : Matrix (Fin I.n) (Fin k) ℂ := Matrix.of fun j a => I.φ v (b' a j) with hΦ
  have hC : colM I y v b' = qM I y v * Φ := by
    ext j a
    simp only [colM, Matrix.of_apply]
    rw [ap_coordV]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ, phv]
  have hH : (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * qM I y v = (hM I b').map (I.φ v) := by
    rw [hC, Matrix.conjTranspose_mul, ap_Jm_herm, Matrix.conjTranspose_mul]
    calc Φᴴ * (qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v
        = Φᴴ * ((qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v) := by simp only [Matrix.mul_assoc]
      _ = Φᴴ * I.J.map (I.φ v) := by rw [ap_QJQ]
      _ = (hM I b').map (I.φ v) := by
          rw [hM, Matrix.map_mul]
          congr 1
          ext a j
          simp [hΦ, ap_star]
  have hinv : qM I y v * (I.P v * Formalism.MainNotions.S.uMat (y.1 v)) = 1 := by
    unfold qM
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v)⁻¹, ap_hP', Matrix.one_mul]
    have := ap_uMat_mul_inv (y.1 v)⁻¹
    rwa [inv_inv] at this
  set z' := (I.P v * Formalism.MainNotions.S.uMat (y.1 v)) *ᵥ z with hz'
  have hzz : z = qM I y v *ᵥ z' := by
    rw [hz', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hM0 : (hM I b').map (I.φ v) *ᵥ z' = 0 := by
    rw [← hH, ← Matrix.mulVec_mulVec, ← hzz]
    exact hz
  have hd0 : δ.map (I.φ v) *ᵥ z' = 0 := by
    rw [hX, Matrix.map_mul, ← Matrix.mulVec_mulVec, hM0, Matrix.mulVec_zero]
  rw [hzz, Matrix.mulVec_mulVec, ap_AQ, ← Matrix.mulVec_mulVec, hd0, Matrix.mulVec_zero]
end PI.UnitaryGroupMassFormula.LCG
