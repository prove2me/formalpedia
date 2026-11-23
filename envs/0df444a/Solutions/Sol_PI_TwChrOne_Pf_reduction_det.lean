-- Prove2me | solution 1 for PI.TwChrOne.Pf.reduction_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:42.971082+00:00
-- url     : https://prove2.me/submissions/5db48a76-1a62-4ff6-953b-8681ddf42579

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
namespace PI.TwChrOne.Pf
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by
  have h1 : M.det = (intS P).subtype (Matrix.of fun s t => (⟨M s t, hM s t⟩ : intS P)).det := by
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact RingHom.map_det (redH P) _
end PI.TwChrOne.Pf
