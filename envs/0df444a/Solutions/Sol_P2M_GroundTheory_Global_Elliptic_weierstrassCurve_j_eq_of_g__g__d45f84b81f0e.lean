-- Prove2me | solution 1 for P2M_GroundTheory_Global_Elliptic_weierstrassCurve_j_eq_of_g__g__d45f84b81f0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:43.748091+00:00
-- url     : https://prove2.me/submissions/34965117-09d7-424a-b9c4-86a5c11241c7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_discr_of_g__g__3aa54b399eb9
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCurve_j


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (h₂ : L'.g₂ = t ^ 4 * L.g₂) (h₃ : L'.g₃ = t ^ 6 * L.g₃) :
    (weierstrassCurve L).j = (weierstrassCurve L').j := by
  rw [weierstrassCurve_j, weierstrassCurve_j, discr_of_g₂_g₃ h₂ h₃, h₂,
    show 1728 * (t ^ 4 * L.g₂) ^ 3 = t ^ 12 * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ ht)]
end GroundTheory.Global.Elliptic
