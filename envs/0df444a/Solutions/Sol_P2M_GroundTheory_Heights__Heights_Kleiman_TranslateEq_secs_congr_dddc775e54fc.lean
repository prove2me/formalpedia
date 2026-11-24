-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:57.792352+00:00
-- url     : https://prove2.me/submissions/59644d2e-7cff-46e3-bdaf-63493d20232f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution {F F' : Fin (N + 1) → Submodule S Ω} (h : ∀ i, x i ≠ 0 → F i = F' i) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x F = IndefiniteRowSideFullHecke.Kleiman.secs S x F' := by
  unfold IndefiniteRowSideFullHecke.Kleiman.secs
  exact iInf_congr fun i => iInf_congr fun hi => h i hi
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
