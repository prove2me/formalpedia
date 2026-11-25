-- Prove2me | solution 1 for P2M_GroundTheory_Global_Elliptic_G_eq_of_g__g__73f0116ddc71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:55.577079+00:00
-- url     : https://prove2.me/submissions/3407bec8-960a-408b-b08c-25aa6f37dd1f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_scale
import Theorems.Thm_GroundTheory_Global_Elliptic_G_eq_weierstrassCoeff_div

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
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L' : PeriodPair} {t : ℂ} (h₂ : L'.g₂ = t ^ 4 * L.g₂)
    (h₃ : L'.g₃ = t ^ 6 * L.g₃) {k : ℕ} (hk : 2 ≤ k) :
    L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, G_eq_weierstrassCoeff_div hn,
    G_eq_weierstrassCoeff_div hn, h₂, h₃, weierstrassCoeff_scale]
  ring
end GroundTheory.Global.Elliptic
