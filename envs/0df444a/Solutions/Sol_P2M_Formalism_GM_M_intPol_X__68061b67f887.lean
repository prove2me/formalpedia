-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_X__68061b67f887
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:54.095613+00:00
-- url     : https://prove2.me/submissions/885383be-89f1-41b4-8b17-650c54350202

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
theorem _root_.solution (x : σ) : (X x : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ :=
  (intPol_iff' _).mpr ⟨X x, map_X _ _⟩
end Formalism.GM.M
