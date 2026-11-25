-- Prove2me | solution 1 for PI.QnCovHat2W.sum_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:16.384006+00:00
-- url     : https://prove2.me/submissions/538c4541-6865-4a3d-ba6c-9c93ea6f109f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL_alt
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL_succ

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
theorem _root_.solution {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (m + 2) → α) (F : (Fin m → α) → M)
    (hF : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : α → ℂ) :
    ∑ c : Fin (m + 2) → α, sgnL c e • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β (e j) * β' (e (j.succAbove j'))) * (m.factorial : ℂ)) •
          F (fun k => e (j.succAbove (j'.succAbove k))) := by
  refine (sum_sgnL_succ e (fun c => (β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := sum_sgnL_succ (e ∘ j.succAbove)
    (fun y : Fin (m + 1) → α => (β (e j) * β' (y 0)) • F (fun k => y k.succ))
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Function.comp_apply] at h2 ⊢
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h3 : ∑ z : Fin m → α, sgnL z ((e ∘ j.succAbove) ∘ j'.succAbove) •
      ((β (e j) * β' (e (j.succAbove j'))) • F z) =
      (β (e j) * β' (e (j.succAbove j'))) • ((m.factorial : ℂ) • F ((e ∘ j.succAbove) ∘ j'.succAbove)) := by
    simp_rw [smul_comm (sgnL _ _) (β (e j) * β' (e (j.succAbove j')))]
    rw [← Finset.smul_sum, sum_sgnL_alt _ F hF]
  rw [h3, smul_smul, smul_smul, smul_smul, pow_add]
  congr 1
end PI.QnCovHat2W
