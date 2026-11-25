-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.chArg_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:50.7531+00:00
-- url     : https://prove2.me/submissions/6919ddb7-53d4-45d6-8cbc-5d60c45923a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_map
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_add
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_eN_ne
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_smul
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_eN_apply
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_mem_Ufl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
private theorem atN_zero {N : ℕ} (i : ℕ) : PI.UnfoldEquiv.Loc.atN (0 : Fin N → k) i = 0 := by
  have h := atN_smul (0 : k) (0 : Fin N → k) i
  rwa [zero_smul, zero_mul] at h
private theorem eN_eq_zero_of_le {N i : ℕ} (h : N ≤ i) : PI.UnfoldEquiv.Loc.eN k N i = 0 := by
  funext l
  have hl := l.2
  rw [eN_apply, Pi.zero_apply, if_neg (by omega)]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by
  have key : ∀ i ∈ Finset.range c,
      PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) =
        PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1))) (n + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hic : i + 1 < c
    · have hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) :=
        h.2.2 (i + 1) (by omega) hic
      have hcoord := atN_map hr hi hu
      have hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) =
          (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) :=
        (sub_add_cancel _ _).symm
      rw [hx, map_add, atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]
    · have hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) := by
        rw [mem_Ufl]
        intro l hl
        exfalso
        have := l.2
        omega
      rw [atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero,
        atN_zero, add_zero]
  simp only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero,
      atN_zero, add_zero]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
