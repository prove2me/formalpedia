-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_pow__7258d14ed956
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:10.183629+00:00
-- url     : https://prove2.me/submissions/df9c4429-bc69-4342-9283-7cc963410022

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {σ : Type}
namespace Formalism.GM.M
theorem _root_.solution {F : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (k : ℕ) : F ^ k ∈ IntPol p σ := by
  obtain ⟨F₀, rfl⟩ := (intPol_iff' F).mp hF
  exact (intPol_iff' _).mpr ⟨F₀ ^ k, map_pow _ _ _⟩
end Formalism.GM.M
