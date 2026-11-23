-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.star_dotProduct_Hpk_mulVec_eq_sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:09.98521+00:00
-- url     : https://prove2.me/submissions/dcb92ce7-57b3-4ae5-8e93-0503c741c706

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mulVec_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_not_inW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution (v w : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, ¬ inW k r i → v i = 0) :
    star w ⬝ᵥ (Hpk k r *ᵥ v) =
      (∑ i ∈ Wp k r, star (w i) * v i) - star (w (lI k r)) * v (lI k r) := by
  have hterm : ∀ i, star (w i) * (Hpk k r *ᵥ v) i =
      (if r ≤ i.val ∧ i.val < r + k then star (w i) * v i else 0) -
        (if lI k r = i then star (w (lI k r)) * v (lI k r) else 0) := by
    intro i
    rw [Hpk_mulVec_apply]
    have hi := i.isLt
    by_cases hW : inW k r i
    · have hp : piI k r i = i := by
        have hW' := hW
        unfold inW at hW'
        unfold piI
        rw [if_pos hW']
      rw [hp]
      unfold inW at hW
      by_cases hl : i.val = r + k
      · have h1 : lI k r = i := Fin.ext hl.symm
        rw [if_neg (by omega), if_pos h1, h1]
        unfold epsI; rw [if_pos hl]; ring
      · have h1 : lI k r ≠ i := fun h => hl (by rw [← h]; rfl)
        rw [if_pos ⟨hW.1, by omega⟩, if_neg h1]
        unfold epsI; rw [if_neg hl]; ring
    · have h0 : v (piI k r i) = 0 := hv _ (piI_not_inW hW)
      have h1 : lI k r ≠ i := fun h => hW (by rw [← h]; unfold inW lI; simp)
      unfold inW at hW
      rw [h0, if_neg (by omega), if_neg h1]; ring
  simp only [dotProduct, Pi.star_apply, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Wp, Finset.sum_filter]
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
