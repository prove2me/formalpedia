-- Prove2me | solution 1 for P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:39.658747+00:00
-- url     : https://prove2.me/submissions/e917b61d-1f0b-4d62-83ad-0ee6e49dd4bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) (n : ℕ) :
    ordAt L w (a ^ n) = n * ordAt L w a := by
  unfold ordAt
  have h : ((a ^ n : Ideles L) : AdeleRing (𝓞 L) L).2 w = ((a : AdeleRing (𝓞 L) L).2 w) ^ n := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  rw [h, map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
end PI.AlgValsFin.W
