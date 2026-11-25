-- Prove2me | solution 1 for PI.LocJacOrd.W.Ar.arith_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:05.470471+00:00
-- url     : https://prove2.me/submissions/7f39810c-1273-4bc7-ad85-0d38fd354073

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Theorems.Thm_PI_LocJacOrd_W_Ar_jac_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
namespace PI.LocJacOrd.W.Ar
theorem _root_.solution (r : ℕ) (m : ℝ) (a : Fin (r + 1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    m ^ ((r + 1) * (r + 1)) * (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹) *
        ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          a i ^ 2) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4)) * ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) := by
  have hm : m ^ ((r + 1) * (r + 1)) = ∏ _p : Fin (r + 1) × Fin (r + 1), m := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hP : ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹ =
      ∏ p : Fin (r + 1) × Fin (r + 1), ((a p.1 * a p.2) ^ 2)⁻¹ :=
    (Fintype.prod_prod_type (fun p : Fin (r + 1) × Fin (r + 1) => ((a p.1 * a p.2) ^ 2)⁻¹)).symm
  have hJ : ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
      a i ^ 2) ^ 2) ^ 2 =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1) := by
    rw [← jac_count r (fun i => a i ^ 8)]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hU : ∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype _ (fun p : Fin (r + 1) × Fin (r + 1) => by simp)
      (fun p : Fin (r + 1) × Fin (r + 1) => m ^ 2 * (a p.1 / a p.2) ^ 4)).symm
  have hD : ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_ite_eq]
    simp
  have hL : ∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) := by
    refine Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm (a p.2)]
  have hsplit : ∏ p : Fin (r + 1) × Fin (r + 1), (m * ((a p.1 * a p.2) ^ 2)⁻¹) =
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_pos h, h]
      ring
    · simp [h, h.ne', not_lt.2 h.le]
  have key : (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1)) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    split_ifs with h
    · have h1 := ha p.1
      have h2 := ha p.2
      field_simp
    · simp
  rw [hm, hP, ← Finset.prod_mul_distrib, hsplit, hL, hJ, hU, hD, ← key]
  ring
end PI.LocJacOrd.W.Ar
