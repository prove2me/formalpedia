-- Prove2me | solution 1 for PI.CompDegEF.normCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:54.226801+00:00
-- url     : https://prove2.me/submissions/440a2557-eefd-4d27-ae02-059776900cfe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_SpanLIsMaximal
import Theorems.Thm_PI_CompDegEF_span_l_isMaximal
import Theorems.Thm_PI_CompDegEF_liesOver_of_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution : NormCard := by
  intro l _ E _ _ v hv
  have := liesOver_of_mem hv
  have hmax := span_l_isMaximal l
  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h1 : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Ideal.absNorm (v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, map_pow, Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal
    (Ideal.span {((l : ℕ) : ℤ)}) hmax.isPrime (by simp [(Fact.out : l.Prime).ne_zero]),
    Ideal.absNorm_span_natCast, Module.finrank_self, pow_one,
    Ideal.inertiaDeg'_eq_inertiaDeg, Formalism.MainNotions.N.locDeg, ← pow_mul, mul_comm]
end PI.CompDegEF
