-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.exists_rat_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:17.519321+00:00
-- url     : https://prove2.me/submissions/c4d49319-baea-4b67-ac8f-6ebc450015cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_ExistsRatCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E)
    (hK : Module.finrank ℚ K = 2) (d : ℕ) (hd : d ≠ 0) (b : K)
    (hb : b ^ 2 = ((-(d : ℤ) : ℤ) : K)) (w : K) :
    ∃ x y : ℚ, w = (x : K) + (y : K) * b := by
  let v : Fin 2 → K := ![1, b]
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.smul_def, mul_one] at hg
    have h1 : g 1 = 0 := by
      by_contra h1
      have hg1 : ((g 1 : ℚ) : K) ≠ 0 := by exact_mod_cast h1
      have hmul : ((g 1 : ℚ) : K) * b = -((g 0 : ℚ) : K) := by linear_combination hg
      have hbq : b = ((-(g 0 / g 1) : ℚ) : K) := by
        rw [(eq_inv_mul_iff_mul_eq₀ hg1).mpr hmul]
        push_cast
        ring
      have hsq : (((-(g 0 / g 1)) ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
        rw [Rat.cast_pow, ← hbq, hb]
        push_cast
        ring
      have hq := Rat.cast_injective hsq
      have hd' : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      nlinarith [sq_nonneg (-(g 0 / g 1))]
    have h0 : g 0 = 0 := by
      rw [h1] at hg
      have : ((g 0 : ℚ) : K) = 0 := by simpa using hg
      exact_mod_cast this
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by simp [hK]
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr w
  rw [hB, Fin.sum_univ_two] at hsum
  refine ⟨B.repr w 0, B.repr w 1, hsum.symm.trans ?_⟩
  simp [v, Rat.smul_def]
end PI.UnitaryGroupMassFormula.ProdUnitInert
