-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:10.516949+00:00
-- url     : https://prove2.me/submissions/9edf4026-597c-493a-a432-c61eb40cb482

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ArithmeticCylinders

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ArithmeticCylinders
theorem _root_.solution :
    ∀ {L : Type} [inst : Field L] {d : Type} [inst_1 : Fintype d] [inst_2 : DecidableEq d]
    (M : Matrix d d L) (n : ℕ), M ^ n = (1 : Matrix d d L) → ∀ (μ : L), M.charpoly.IsRoot μ → μ ^ n = (1 : L) := by
  intro L _ d _ _ M n hM μ hμ
  have h1 : μ ∈ spectrum L M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ
  have h2 : μ ^ n ∈ spectrum L (M ^ n) := spectrum.pow_mem_pow M n h1
  rw [hM, spectrum.mem_iff] at h2
  by_contra hne
  apply h2
  have hu : IsUnit (μ ^ n - 1) := (sub_ne_zero.mpr hne).isUnit
  have h3 := hu.map (algebraMap L (Matrix d d L))
  rwa [map_sub, map_one] at h3
end UpperTheory.Reformulated.B.ArithmeticCylinders
