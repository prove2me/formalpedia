-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:39.465963+00:00
-- url     : https://prove2.me/submissions/da6483c1-1bf8-466c-9cb0-fb675fa6d949

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}
namespace GroundTheory.Heights₂.Heights.logCardLength
theorem _root_.solution (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) [hm : m.IsMaximal] :
    term R N m = ((Module.length (Localization.AtPrime m)
      (LocalizedModule m.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (R ⧸ m)) := by
  classical
  rw [term, finsum_eq_if, if_pos hm, locLen, dif_pos hm.isPrime]
end GroundTheory.Heights₂.Heights.logCardLength
