-- Prove2me | solution 1 for PI.AlgValsFin.W.valued_atFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:03.023965+00:00
-- url     : https://prove2.me/submissions/5133ba9d-a9f1-4b43-8d7f-6826492634ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-ordF v k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)]
  simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  first
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := L) v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := L) v (k : L)
  | exact Valued.extension_extends _
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
end PI.AlgValsFin.W
