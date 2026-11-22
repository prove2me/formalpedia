-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:49.781261+00:00
-- url     : https://prove2.me/submissions/63afeef9-a33d-4bd4-ba42-9c4bdd4fd23a

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
theorem _root_.solution {F G : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (hG : G ∈ IntPol p σ) :
    F * G ∈ IntPol p σ := by
  obtain ⟨F₀, rfl⟩ := (intPol_iff' F).mp hF
  obtain ⟨G₀, rfl⟩ := (intPol_iff' G).mp hG
  exact (intPol_iff' _).mpr ⟨F₀ * G₀, map_mul _ _ _⟩
end Formalism.GM.M
