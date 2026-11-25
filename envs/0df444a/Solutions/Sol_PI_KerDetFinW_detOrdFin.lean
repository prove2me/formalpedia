-- Prove2me | solution 1 for PI.KerDetFinW.detOrdFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:23.229372+00:00
-- url     : https://prove2.me/submissions/50a2af07-5eb9-4536-a02d-8f11e0010bf7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
import Theorems.Thm_PI_KerDetFinW_exists_denom_forward
import Theorems.Thm_PI_KerDetFinW_exists_denom_backward
import Theorems.Thm_PI_KerDetFinW_ordK_detRel_eq_zero


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
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution : DetOrdFin := by
  intro K E _ _ _ _ _ n _ I hI S pp gp g₀ hpp hgp
  obtain ⟨N₁, h1pos, h1⟩ := exists_denom_forward (K := K) I g₀
  obtain ⟨N₂, h2pos, h2⟩ := exists_denom_backward I hI g₀
  have hg₀ : ∀ p, p.Prime → ¬ p ∣ N₁ * N₂ → AtP {x : E | x ∈ I} g₀ p := by
    intro p hp hdvd
    have hcop : Nat.Coprime (N₁ * N₂) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd).symm
    exact ⟨fun x hx => ⟨N₁, Nat.Coprime.coprime_dvd_left (dvd_mul_right N₁ N₂) hcop, h1 x hx⟩,
      fun v hv => ⟨N₂, Nat.Coprime.coprime_dvd_left (dvd_mul_left N₂ N₁) hcop, h2 v hv⟩⟩
  refine (Nat.divisors (N₁ * N₂)).finite_toSet.subset ?_
  rintro p ⟨hp, hS, hne⟩
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, (Nat.mul_pos h1pos h2pos).ne'⟩
  by_contra hdvd
  exact hne (ordK_detRel_eq_zero (pp p) (hpp p hp hS) (hg₀ p hp hdvd) (hgp p hp hS))
end PI.KerDetFinW
