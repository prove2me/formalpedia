-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.arith_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:32.590298+00:00
-- url     : https://prove2.me/submissions/97650e5e-00b7-413d-b89a-76784b09b3a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_gauss
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_l_succ
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_exp_product_square_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eJ
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eU
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_eL
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_card_uidx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
open Real
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) (A : Fin (r + 1) → ℝ) (hA : ∀ i, 0 < A i) (G m : ℝ) (hG : 0 < G) :
    m ^ ((r + 1) * (r + 1)) * G ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((A i * A j) ^ 2)⁻¹) *
        ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          A i ^ 2) * G⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * G ^ 2 * (A q.1.1 / A q.1.2) ^ 4)) *
        ∏ l : Fin (r + 1), (m * G ^ 3 * (A l ^ 4)⁻¹) := by
  obtain ⟨γ, rfl⟩ : ∃ γ, G = exp γ := ⟨log G, (exp_log hG).symm⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin (r + 1) → ℝ, A = fun i => exp (a i) :=
    ⟨fun i => log (A i), funext fun i => (exp_log (hA i)).symm⟩
  have hU : ∏ q : UIdx r, (m ^ 2 * exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      (m ^ 2) ^ Fintype.card (UIdx r) * ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hL : ∏ l : Fin (r + 1), (m * exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      m ^ (r + 1) * ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  simp only at hU hL ⊢
  rw [hU, hL, exp_product_square_inv, eJ, eU, eL]
  have hK := card_uidx r
  have hN : 2 * Fintype.card (UIdx r) + (r + 1) = (r + 1) * (r + 1) := by
    have : ((2 * Fintype.card (UIdx r) + (r + 1) : ℕ) : ℝ) = (((r + 1) * (r + 1) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hm : (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) = m ^ ((r + 1) * (r + 1)) := by
    rw [← pow_mul, ← pow_add, hN]
  have hS := gauss r
  have hS' := sum_l_succ r
  have h1 : ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i + ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j =
      (r : ℝ) * ∑ i, a i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hE : exp γ ^ (3 * ((r + 1) * (r + 1))) *
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) *
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    linear_combination (-4 * γ) * hS' + (-2 * γ) * hS + (-γ) * hK + 4 * h1
  rw [← hm]
  calc (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))
      = (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * (exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))) := by
        ring
    _ = _ := by rw [hE]; ring
end PI.UnitaryGroupMassFormula.LocJacTyp
