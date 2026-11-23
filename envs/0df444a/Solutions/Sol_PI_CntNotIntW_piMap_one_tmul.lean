-- Prove2me | solution 1 for PI.CntNotIntW.piMap_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:10.075087+00:00
-- url     : https://prove2.me/submissions/60d88f4a-f64c-429b-8dbd-284458247fec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
namespace PI.CntNotIntW
theorem _root_.solution (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp]
    (ι : K →+* Fp) (y : K) : piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := by
  simp [piMap]
end PI.CntNotIntW
