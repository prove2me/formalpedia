-- Prove2me | solution 1 for PI.WittUnramWork.psi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:20.597194+00:00
-- url     : https://prove2.me/submissions/f5a238df-c1f8-4aa7-ab6a-952886f10627

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]
namespace PI.WittUnramWork
theorem _root_.solution (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 ?_
  intro x hx
  by_contra hne
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hirr
  obtain ⟨u, hu⟩ := hn
  have h2 : ψ ((p : W) ^ n) = 0 := by rw [← hu, map_mul, hx, zero_mul]
  rw [map_pow, map_natCast] at h2
  exact pow_ne_zero n (WittVector.p_nonzero p k) h2
end PI.WittUnramWork
