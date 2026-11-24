-- Prove2me | solution 1 for PI.KLW.Rp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:58:05.668879+00:00
-- url     : https://prove2.me/submissions/0b972937-bf91-4975-9004-b54635d61705

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_mem_range_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact hsx.mul hty
end PI.KLW
