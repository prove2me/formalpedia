-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_iff__d65ab3cebd50
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:04.389852+00:00
-- url     : https://prove2.me/submissions/42b05432-522d-4464-8537-a17d4d1da974

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

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
theorem _root_.solution (F : MvPolynomial σ ℚ_[p]) :
    F ∈ IntPol p σ ↔ ∃ F₀ : MvPolynomial σ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by
  simp [IntPol, LinearMap.mem_range, MvPolynomial.mapAlgHom_apply, Algebra.ofId_apply]
end Formalism.GM.M
