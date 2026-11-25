-- Prove2me | solution 1 for PI.WGL.lm_isWH_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:02.789816+00:00
-- url     : https://prove2.me/submissions/5b5f0b43-b218-4116-91f9-3e25c9368b2d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {σ M : Type*} [AddCommMonoid M] (w : σ → M) (f : MvPolynomial σ ℤ) (d : M)
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w (map (Int.castRingHom ℂ) f) d := by
  intro m hm
  apply hf
  rw [coeff_map] at hm
  intro h0
  apply hm
  rw [h0, map_zero]
end PI.WGL
