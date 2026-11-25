-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TotalIdentity_proof_bb35e2091cf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:49.168728+00:00
-- url     : https://prove2.me/submissions/dbbddb9f-9b61-41d0-9aa5-e97fcb78b4de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PTotalIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_one_eq_factorial_7ef4a563eab9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_two_eq_factorial_051e3b0dba3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace TotalIdentity
theorem _root_.solution (h1 : FrobeniusDimensionFormula.Statement)
    (h2 : CombVandermondeSucc.Statement) : TotalIdentity.Statement := by
  intro r a hr _
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  set lam : Fin (n + 1) → ℕ := fun i => a + if (i : ℕ) = 0 then 1 else 0 with hlam
  have hanti : Antitone lam := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [lam]
    split_ifs <;> omega
  have hrect : Antitone (rectangle (n + 1) a) := fun _ _ _ => le_rfl
  have e1 := h1 (n + 1) lam hanti
  have e2 := h1 (n + 1) (rectangle (n + 1) a) hrect
  rw [h2] at e1 e2
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, lam, rectangle, Fin.val_zero, Fin.val_succ,
    Nat.add_one_ne_zero, if_true, if_false, add_zero, Nat.add_sub_cancel, Nat.sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at e1 e2
  set V := vandermondeOf fun j : Fin n => ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ) with hV
  set D := ∏ x : Fin n, (((a + (n - ((x : ℕ) + 1))).factorial : ℕ) : ℚ) with hD
  have hP1 : ∏ j : Fin n, (((a + n : ℕ) : ℚ) - ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ)) =
      (n.factorial : ℚ) := by
    rw [← prod_fin_add_one_eq_factorial]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h' : (j : ℕ) + 1 ≤ n := j.isLt
    push_cast [Nat.cast_sub h']
    ring
  have hP2 : ∏ j : Fin n, (((a + 1 + n : ℕ) : ℚ) - ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ)) =
      ((n + 1).factorial : ℚ) := by
    rw [← prod_fin_add_two_eq_factorial]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h' : (j : ℕ) + 1 ≤ n := j.isLt
    push_cast [Nat.cast_sub h']
    ring
  rw [hP2, show a + 1 + n * a = (n + 1) * a + 1 by ring, show a + 1 + n = a + n + 1 by ring,
    Nat.factorial_succ ((n + 1) * a), Nat.factorial_succ (a + n)] at e1
  rw [hP1] at e2
  rw [Nat.factorial_succ n] at e1
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => by positivity
  have hf0 : ((a + n).factorial : ℚ) ≠ 0 := by positivity
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [e1, e2]
  push_cast
  field_simp
  ring
end TotalIdentity
end GroundTheory.Heights₂.Heights.RestTerms
