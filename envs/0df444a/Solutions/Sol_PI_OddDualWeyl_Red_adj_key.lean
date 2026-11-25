-- Prove2me | solution 1 for PI.OddDualWeyl.Red.adj_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:19.407906+00:00
-- url     : https://prove2.me/submissions/84874a98-b83f-48ce-9882-38339b8485ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_adj_inv
import Theorems.Thm_PI_OddDualWeyl_Red_cM_smul

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
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) :
    (genM K k).adjugate * cM g = (C g.det : MvPolynomial (Fin k × Fin k) K) • (cM g⁻¹ * genM K k).adjugate := by
  have hc : (cM g⁻¹).adjugate = (C (g.det)⁻¹ : MvPolynomial (Fin k × Fin k) K) • cM g := by
    have h := RingHom.map_adjugate (C : K →+* MvPolynomial (Fin k × Fin k) K) g⁻¹
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, adj_inv g hd] at h
    rw [← cM_smul]
    exact h.symm
  rw [Matrix.adjugate_mul_distrib, hc, Matrix.mul_smul, smul_smul, ← MvPolynomial.C_mul, mul_inv_cancel₀ hd,
    MvPolynomial.C_1, one_smul]
end PI.OddDualWeyl.Red
