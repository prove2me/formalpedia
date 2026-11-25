-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:24.606807+00:00
-- url     : https://prove2.me/submissions/89962c75-ef36-471c-856a-7dda13c25097

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_add
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_eN
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_atN_of_mem
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
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by
  have hlt : n + i < n + c := by omega
  have hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i := by
    rw [mem_Ufl] at hw ⊢
    intro l hl
    rw [Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    by_cases hl' : l.1 = n + i
    · rw [if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dif_pos hlt]
      have hle : l = ⟨n + i, hlt⟩ := Fin.ext hl'
      rw [hle, sub_self]
    · rw [if_neg hl', mul_zero, sub_zero]
      exact hw l (by omega)
  have hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1 := by
    have h1 := atN_of_mem (hr.2.2 i)
    have h2 := atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)
    rw [sub_add_cancel] at h2
    rw [h2, h1, atN_eN hlt, zero_add]
  have hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
    rw [map_sub, map_smul, sub_add_cancel]
  rw [hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
