-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:06.712346+00:00
-- url     : https://prove2.me/submissions/72665b09-7380-410c-a80d-6846e347162d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution [IsNoetherianRing S] (hF : FiniteSections.Statement.{w, w}) (hx' : x' ≠ 0) :
    (Subalgebra.toSubmodule (domSub (S := S) x' hi)).FG := by
  have := isNoetherianRing_chartRing (S := S) hi
  have h := (hF (chartRing S x (singleChart hi)) Ω N' x' (twistBundle _ x' 0) hx').1
  rw [Module.Finite.iff_fg] at h
  have heq : Subalgebra.toSubmodule (domSub (S := S) x' hi) = (twistBundle _ x' 0).secs := by
    ext z
    rw [Subalgebra.mem_toSubmodule, mem_secs_twistBundle_zero_iff, domSub, Algebra.mem_iInf]
  rw [heq]
  exact h
end GroundTheory.Heights₂.Heights.Kleiman.Domination
