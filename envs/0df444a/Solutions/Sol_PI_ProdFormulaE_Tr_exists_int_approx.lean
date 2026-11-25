-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.exists_int_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:00.84782+00:00
-- url     : https://prove2.me/submissions/09a11802-c06f-43c3-bc12-828f11388d29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
namespace PI.ProdFormulaE.Tr
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1 := by
  obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (⟨c, hc⟩ : ℤ_[ℓ])
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at hn
  obtain ⟨y, hy⟩ := hn
  refine ⟨n, ?_⟩
  have hy' : c - (n : ℚ_[ℓ]) = ℓ * (y : ℚ_[ℓ]) := by
    have := congrArg (fun w : ℤ_[ℓ] => (w : ℚ_[ℓ])) hy
    push_cast at this
    exact this
  have hℓ : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  rw [show ((n : ℤ) : ℚ_[ℓ]) = (n : ℚ_[ℓ]) by push_cast; rfl, hy', mul_div_cancel_left₀ _ hℓ]
  exact y.norm_le_one
end PI.ProdFormulaE.Tr
