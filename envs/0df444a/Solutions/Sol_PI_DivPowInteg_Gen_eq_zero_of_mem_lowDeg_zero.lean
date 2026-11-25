-- Prove2me | solution 1 for PI.DivPowInteg.Gen.eq_zero_of_mem_lowDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:21.409682+00:00
-- url     : https://prove2.me/submissions/b5e62c3d-203c-436c-801b-1b27c6aede6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
import Theorems.Thm_PI_DivPowInteg_Gen_mem_lowDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.DivPowInteg.Gen
theorem _root_.solution {f : ι → σ} {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f 0) : R = 0 := by
  rw [mem_lowDeg] at h
  by_contra hR
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hR)
  exact absurd (h m hm) (Nat.not_lt_zero _)
end PI.DivPowInteg.Gen
