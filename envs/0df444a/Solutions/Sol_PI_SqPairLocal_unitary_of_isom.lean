-- Prove2me | solution 1 for PI.SqPairLocal.unitary_of_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:11.286801+00:00
-- url     : https://prove2.me/submissions/7f40cd09-63e6-4e51-abee-275168c4c285

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_PI_UG_W_hStd_apply
import Theorems.Thm_PI_UG_W_hStd_eStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {N : ℕ} {g : (Fin N → E) ≃ₗ[E] (Fin N → E)} (hg : g ∈ isom (hStd E N)) :
    (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *
      LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  ext i j
  have h1 : hStd E N (g (PI.UG.W.eStd E N i)) (g (PI.UG.W.eStd E N j)) = if i = j then 1 else 0 :=
    (hg _ _).trans (PI.UG.W.hStd_eStd E N i j)
  rw [PI.UG.W.hStd_apply] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  simp only [conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, PI.UG.W.eStd]
end PI.SqPairLocal
