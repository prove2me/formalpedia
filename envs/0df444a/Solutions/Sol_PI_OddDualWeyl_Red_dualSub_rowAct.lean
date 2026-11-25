-- Prove2me | solution 1 for PI.OddDualWeyl.Red.dualSub_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:33.591365+00:00
-- url     : https://prove2.me/submissions/227793b8-2e67-4c78-ad4e-43f17e1a70f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_sbs
import Theorems.Thm_PI_OddDualWeyl_Red_genM_map
import Theorems.Thm_PI_OddDualWeyl_Red_cM_map
import Theorems.Thm_PI_OddDualWeyl_Red_map_mul_sbs
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_det
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_eq
import Theorems.Thm_PI_OddDualWeyl_Red_dualSub_eq
import Theorems.Thm_PI_OddDualWeyl_Red_aeval_mul_homog
import Theorems.Thm_PI_OddDualWeyl_Red_det_inv_eq
import Theorems.Thm_PI_OddDualWeyl_Red_det_cM
import Theorems.Thm_PI_OddDualWeyl_Red_key_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
variable {K : Type*} [Field K] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0)
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D) :
    dualSub K k (rowAct K gᵀ p') =
      C g.det ^ D * ((C (g.det)⁻¹ * (genM K k).det) ^ M * rowAct K g⁻¹ p) := by
  have hrel' : PI.OddDualWeyl.dualSub K k p' = (PI.OddDualWeyl.genM K k).det ^ M * p := hrel
  have hB : sbs (cM g⁻¹ * PI.OddDualWeyl.genM K k) (PI.OddDualWeyl.genM K k).det =
      C (g.det)⁻¹ * (PI.OddDualWeyl.genM K k).det := by
    rw [sbs_det, Matrix.det_mul, det_cM, det_inv_eq]
  have hsmul : ∀ (c : MvPolynomial (Fin k × Fin k) K)
      (E : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) K)),
      sbs (c • E) p' = c ^ D * sbs E p' := by
    intro c E
    have h := aeval_mul_homog (R := K) (fun v : Fin k × Fin k => E v.1 v.2) c hp'
    unfold sbs
    simpa only [Matrix.smul_apply, smul_eq_mul] using h
  have e1 : PI.OddDualWeyl.dualSub K k (PI.OddDualWeyl.rowAct K gᵀ p') =
      sbs (cM gᵀ * PI.OddDualWeyl.dualM K k) p' := by
    rw [dualSub_eq, rowAct_eq, sbs_sbs, map_mul_sbs,
      cM_map, genM_map]
  have e2 : sbs ((PI.OddDualWeyl.dualM K k).map (sbs (cM g⁻¹ * PI.OddDualWeyl.genM K k))) p' =
      (C (g.det)⁻¹ * (PI.OddDualWeyl.genM K k).det) ^ M * PI.OddDualWeyl.rowAct K g⁻¹ p := by
    rw [← sbs_sbs, ← dualSub_eq, hrel', _root_.map_mul, _root_.map_pow, hB,
      ← rowAct_eq]
  rw [e1, key_mat g hd, hsmul, e2]
end PI.OddDualWeyl.Red
