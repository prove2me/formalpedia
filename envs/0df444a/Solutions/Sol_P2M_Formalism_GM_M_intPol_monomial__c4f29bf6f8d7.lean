-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:38.213685+00:00
-- url     : https://prove2.me/submissions/a71b4f8e-980a-4816-8adc-273fafd01d56

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
theorem _root_.solution (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ :=
  (intPol_iff' _).mpr ⟨monomial m 1, by rw [map_monomial, map_one]⟩
end Formalism.GM.M
