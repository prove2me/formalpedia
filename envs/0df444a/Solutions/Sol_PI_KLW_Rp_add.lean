-- Prove2me | solution 1 for PI.KLW.Rp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:58:03.96283+00:00
-- url     : https://prove2.me/submissions/f063243d-6e0c-491c-806d-6f894f47b353

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
theorem _root_.solution {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x + y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  have ht' : IsIntegral ℤ (t : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (t : ℤ)))
  have hs' : IsIntegral ℤ (s : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (s : ℤ)))
  exact (ht'.mul hsx).add (hs'.mul hty)
end PI.KLW
