-- Prove2me | solution 1 for PI.OddDualWeyl.Red.relK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:18.794531+00:00
-- url     : https://prove2.me/submissions/66b5017f-d2fb-46bc-815e-4adccc536d09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_dualSub_rowAct

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
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D)
    (c c' : K) (hc : c' * g.det ^ D * (g.det)⁻¹ ^ M = c) :
    dualSub K k (c' • rowAct K gᵀ p') = (genM K k).det ^ M * (c • rowAct K g⁻¹ p) := by
  have hs : PI.OddDualWeyl.dualSub K k (c' • PI.OddDualWeyl.rowAct K gᵀ p') = c' • PI.OddDualWeyl.dualSub K k (PI.OddDualWeyl.rowAct K gᵀ p') := by
    first | exact _root_.map_smul _ _ _ | exact AlgHom.map_smul_of_tower _ _ _ | simp
  rw [hs, dualSub_rowAct g hd hrel hp', ← hc]
  simp only [MvPolynomial.smul_eq_C_mul, _root_.map_mul, _root_.map_pow, mul_pow]
  ring
end PI.OddDualWeyl.Red
