-- Prove2me | solution 1 for PI.QnCovHat2W.sum_sgnL_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:34.680817+00:00
-- url     : https://prove2.me/submissions/21b8430a-e85e-4deb-b53f-62ea5f25d4f4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (F : (Fin r → α) → M)
    (hF : ∀ (x : Fin r → α) (π : Equiv.Perm (Fin r)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x) :
    ∑ x, sgnL x e • F x = (r.factorial : ℂ) • F e := by
  rw [sum_sgnL]
  have h1 : ∀ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • F (e ∘ π) = F e := by
    intro π
    rw [hF, smul_smul]
    have h2 : ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign π : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, one_smul]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]
end PI.QnCovHat2W
