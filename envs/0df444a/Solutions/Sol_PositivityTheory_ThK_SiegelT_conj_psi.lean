-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.conj_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:05.213793+00:00
-- url     : https://prove2.me/submissions/681d72f4-a9fe-4568-ba76-713b3899de84

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {k : Type} [AddCommGroup k] {ψ : AddChar k ℂ} (h : ∀ x, ‖ψ x‖ = 1) (x : k) : star (ψ x) = ψ (-x) := by
  have h0 : ψ x ≠ 0 := fun e => by simpa [e] using h x
  refine mul_left_cancel₀ h0 ?_
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h x]
  simp
end PositivityTheory.ThK.SiegelT
