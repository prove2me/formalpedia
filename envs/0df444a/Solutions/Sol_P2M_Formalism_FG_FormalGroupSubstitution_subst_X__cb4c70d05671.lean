-- Prove2me | solution 1 for P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:53.204359+00:00
-- url     : https://prove2.me/submissions/d89ad8ff-224f-4bcc-9773-9eeb78e938a6

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries
namespace Formalism.FG.FormalGroupSubstitution
theorem _root_.solution {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p : σ) :
    subst a (X p : MvPowerSeries σ R) = a p :=
  subst_X (hasSubst_of_constantCoeff_zero h) p
end Formalism.FG.FormalGroupSubstitution
