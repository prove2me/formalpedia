-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.mat_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:08.783719+00:00
-- url     : https://prove2.me/submissions/30479304-f079-496d-a213-0121c4e243f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_int_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {M : ℕ} (A : Matrix (Fin M) (Fin M) E) : ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : E) * A i j) := by
  have hex : ∀ a : E, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
    intro a
    have halg : IsAlgebraic ℤ a := by
      first
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff (R := ℤ) (K := ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact Algebra.IsAlgebraic.isAlgebraic a
    obtain ⟨y, hy0, hy⟩ : ∃ y ≠ (0 : ℤ), IsIntegral ℤ (y • a) := by
      first
      | exact halg.exists_integral_multiple
      | exact exists_integral_multiple halg
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
    have hcast : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
    rcases (show ((y.natAbs : ℕ) : ℤ) = y ∨ ((y.natAbs : ℕ) : ℤ) = -y by omega) with h | h
    · rw [hcast, h, ← zsmul_eq_mul]
      exact hy
    · rw [hcast, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  choose d hd0 hd using fun p : Fin M × Fin M => hex (A p.1 p.2)
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd0 p, fun i j => ?_⟩
  have hsplit : (∏ p, d p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), d p) * d (i, j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  rw [hsplit, Nat.cast_mul, mul_assoc]
  exact (int_nat _).mul (hd (i, j))
end PI.UnitaryGroupMassFormula.UJClassFin
