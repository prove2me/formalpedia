-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.Dl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:21.378442+00:00
-- url     : https://prove2.me/submissions/25e8fc58-42c5-4b83-ab7e-0af397af85de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_entry_le_gN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_herm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_hermForm_phi_le_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
theorem _root_.solution (k r : ℕ) (l : Fin (r + 1)) (h : Mat k r) :
    ‖Dl k r l h‖ ≤ (l.val + 1).factorial * (K0 k r * gN h) ^ (l.val + 1) := by
  have hx : ∀ i j, NormedField.toAbsoluteValue ℂ ((Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) (h *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a))) i j)
        ≤ K0 k r * gN h := by
    intro i j
    show ‖herm (Hpk k r) (h *ᵥ phiV' k r _) (phiV' k r _)‖ ≤ _
    exact (herm_le _ _ _ _).trans (mul_le_mul_of_nonneg_right (hermForm_phi_le_bound _ _ _ _)
      (le_trans (norm_nonneg _) (entry_le_gN h 0 0)))
  have := Matrix.det_le hx
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  exact this
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
