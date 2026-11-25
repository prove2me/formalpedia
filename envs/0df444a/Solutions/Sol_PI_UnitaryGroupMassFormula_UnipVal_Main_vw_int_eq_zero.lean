-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.vw_int_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:03.194221+00:00
-- url     : https://prove2.me/submissions/0c18442f-d711-4480-be44-6025b3f86653

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0)
    (hxw : x ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K x) = 0 := by
  have hJ : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  have h0 : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {x})).factors = 0 := by
    by_contra hne
    exact hxw ((Ideal.span_singleton_le_iff_mem _).mp
      (Ideal.le_of_dvd ((Associates.count_ne_zero_iff_dvd hJ w.irreducible).mp hne)))
  simp only [vw]
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  exact_mod_cast h0
end PI.UnitaryGroupMassFormula.UnipVal.Main
