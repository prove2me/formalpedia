-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_rename__d2058bf01e91
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.903552+00:00
-- url     : https://prove2.me/submissions/065937f0-b008-4db3-b7ee-42db46cf148d

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
theorem _root_.solution {τ : Type} (e : τ → σ) {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    rename e y ∈ IntPol p σ := by
  obtain ⟨y₀, rfl⟩ := (intPol_iff' y).mp hy
  exact (intPol_iff' _).mpr ⟨rename e y₀, map_rename _ _ _⟩
end Formalism.GM.M
