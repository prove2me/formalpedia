-- Prove2me | solution 1 for PIW.AdelClassFin.spDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:50.22893+00:00
-- url     : https://prove2.me/submissions/9c9c26a6-8ebd-4b02-bf78-a20747e4731d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpDen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
namespace PIW.AdelClassFin
theorem _root_.solution : SpDen := by
  intro E _ _ k X
  have h : ∀ p : Fin k × Fin k, ∃ D : ℕ, 1 ≤ D ∧ (D : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range := by
    intro p
    obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (X p.1 p.2)))
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    have hmem : (y : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range :=
      ⟨⟨(y : E) * X p.1 p.2, by rw [mem_integralClosure_iff]; simpa [zsmul_eq_mul] using hint⟩, rfl⟩
    have h2 : (y.natAbs : ℤ) = y ∨ (y.natAbs : ℤ) = -y := by
      rcases Int.natAbs_eq y with h | h
      · exact Or.inl h.symm
      · right; linarith
    rw [← Int.cast_natCast]
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hmem
    · rw [Int.cast_neg, neg_mul]; exact neg_mem hmem
  choose Dp hDp1 hDp using h
  refine ⟨∏ p, Dp p, Finset.one_le_prod' fun p _ => hDp1 p, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Dp (Finset.mem_univ (i, j))
  rw [hc, Nat.cast_mul, mul_comm (Dp (i, j) : E), mul_assoc]
  exact Subring.mul_mem _ ⟨c, by simp⟩ (hDp (i, j))
end PIW.AdelClassFin
