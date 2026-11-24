-- Prove2me | solution 1 for PI.FockOneDegW.minus2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:01.356253+00:00
-- url     : https://prove2.me/submissions/36ae0217-b151-43f2-9b29-e1cf1704e383

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Theorems.Thm_FockRL_Lop_apply
import Theorems.Thm_FockRL_Lop_shift
import Theorems.Thm_FockRL_Rop_raise
import Theorems.Thm_FockRL_fockAct2_eq
import Theorems.Thm_FockRL_omAct_eq_Rop_add_Lop
import Theorems.Thm_FockRaiseLowGrade_raisingLoweringSplit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution {p q r s : ℕ} (Z : Mat r s) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Z) P = -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P := by
  classical

  have hside : ∀ (a : Ix p q) (c d : Ix r s), ¬ sameBlock c d →
      linePos ((a, d) : Ln p q r s) = true → linePos ((a, c) : Ln p q r s) = false := by
    intro a c d hcd hd
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [sameBlock, linePos]
  have hOpp : FockRL.OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z) := by
    rintro ⟨a, c⟩ ⟨b, d⟩ hne
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at hne
    split_ifs at hne with hab
    · subst hab
      have hcd : ¬ sameBlock c d := fun h => hne (by rw [hZ c d h, mul_zero])
      intro hEq
      rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
        simp_all [sameBlock, linePos]
    · simp at hne
  rw [FockRL.fockAct2_eq, FockRL.omAct_eq_Rop_add_Lop _ hOpp,
    (FockRaiseLowGrade.raisingLoweringSplit _ _ _ (fun d P hP => FockRL.Rop_raise _ d P hP)
      (fun e P => FockRL.Lop_shift _ e P) P).2, FockRL.Lop_apply]

  have hL : ∀ (a : Ix p q) (c : Ix r s),
      (∑ l' : Ln p q r s, if linePos ((a, c) : Ln p q r s) = false ∧ linePos l' = true then
        Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z (a, c) l' •
          (-(pderiv ((a, c) : Ln p q r s) (pderiv l' P))) else 0) =
      ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    intro a c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
      by_cases hZcd : Z c d = 0
      · simp [hZcd]
      · have hcd : ¬ sameBlock c d := fun h => hZcd (hZ c d h)
        by_cases hd : linePos ((a, d) : Ln p q r s) = true
        · simp [hd, hside a c d hcd hd]
        · simp [hd]
    · intro b _ hba
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hba)]
    · simp
  have hR : -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P =
      ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [lowOp, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [Fintype.sum_prod_type]
  simp only [hL]
  rw [Finset.sum_comm, hR]
end PI.FockOneDegW
