-- Prove2me | solution 1 for PI.TwChrOne.Pf.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:58.952846+00:00
-- url     : https://prove2.me/submissions/5a0427ad-9beb-4f26-81e1-9e6952c78a25

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
namespace PI.TwChrOne.Pf
theorem _root_.solution (f : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) (i : Fin n) :
    f v i = ∑ m, v m * f (Loc.eN E n m.1) i := by
  have hv : v = ∑ m : Fin n, v m • Loc.eN E n m.1 := by
    funext j
    simp [Loc.eN, Finset.sum_apply, Fin.val_inj]
  conv_lhs => rw [hv]
  simp [map_sum, Finset.sum_apply]
end PI.TwChrOne.Pf
