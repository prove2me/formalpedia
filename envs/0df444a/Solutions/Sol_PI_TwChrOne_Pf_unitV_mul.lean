-- Prove2me | solution 1 for PI.TwChrOne.Pf.unitV_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:59.705916+00:00
-- url     : https://prove2.me/submissions/8764ebb7-fac6-4dfc-9f6c-6e15393ab7ca

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

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
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
variable {K : Type} [Field K]
namespace PI.TwChrOne.Pf
theorem _root_.solution (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b d : E} (ha : IsUnit (redP P a)) (hb : IsUnit (redP P b))
    (hd : redP P d = redP P a * redP P b) :
    LocE.unitV ξ d = LocE.unitV ξ a * LocE.unitV ξ b := by
  have hd' : IsUnit (redP P d) := hd ▸ ha.mul hb
  unfold LocE.unitV
  rw [dif_pos hd', dif_pos ha, dif_pos hb]
  have hu : hd'.unit = ha.unit * hb.unit := Units.ext (by simp [hd])
  rw [hu, map_mul, Units.val_mul]
end PI.TwChrOne.Pf
