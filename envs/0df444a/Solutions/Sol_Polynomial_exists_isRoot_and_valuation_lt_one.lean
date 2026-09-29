-- Prove2me | solution 1 for Polynomial.exists_isRoot_and_valuation_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/dfee2fdc-1c4f-5254-b868-44e6c8607ac5

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_isRoot_and_valuation_lt_one

open Polynomial

namespace M3dS11

theorem valuation_coeff_prod_X_sub_C_le {K : Type*} [Field K] (A : ValuationSubring K)
    (s : Multiset K) (hs : ∀ r ∈ s, 1 ≤ A.valuation r) :
    A.valuation ((s.map (X - C ·)).prod.coeff 0) = (s.map A.valuation).prod ∧
      ∀ m, A.valuation ((s.map (X - C ·)).prod.coeff m) ≤ (s.map A.valuation).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨by simp, fun m => ?_⟩
    rcases m with _ | m
    · simp
    · simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Nat.succ_ne_zero, if_false,
        map_zero]
      exact zero_le'
  | cons a s ih =>
    obtain ⟨ih0, ihm⟩ := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    have ha : 1 ≤ A.valuation a := hs a (Multiset.mem_cons_self a s)
    set P : Polynomial K := (s.map (X - C ·)).prod with hP
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    have hexp : (X - C a) * P = X * P - C a * P := by ring
    have hc0 : ((X - C a) * P).coeff 0 = -(a * P.coeff 0) := by
      rw [hexp, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
    have hcs : ∀ m, ((X - C a) * P).coeff (m + 1) = P.coeff m - a * P.coeff (m + 1) := by
      intro m
      rw [hexp, coeff_sub, coeff_X_mul, coeff_C_mul]
    have hPle : (s.map A.valuation).prod ≤ A.valuation a * (s.map A.valuation).prod :=
      le_mul_of_one_le_left zero_le' ha
    refine ⟨?_, fun m => ?_⟩
    · rw [hc0, Valuation.map_neg, map_mul, ih0]
    · rcases m with _ | m
      · rw [hc0, Valuation.map_neg, map_mul, ih0]
      · rw [hcs m]
        refine le_trans (A.valuation.map_sub _ _) (max_le ((ihm m).trans hPle) ?_)
        rw [map_mul]
        gcongr
        exact ihm (m + 1)

end M3dS11

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) {f : Polynomial K} (h0 : A.valuation (f.coeff 0) < 1) {n : ℕ} (hn : A.valuation (f.coeff n) = 1) : ∃ r : K, f.IsRoot r ∧ A.valuation r < 1 := by
  by_contra hno
  push Not at hno
  have hf0 : f ≠ 0 := fun h => by simp [h] at hn
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hfac := hsplit.eq_prod_roots
  have hroots : ∀ r ∈ f.roots, 1 ≤ A.valuation r := fun r hr => hno r ((mem_roots hf0).mp hr)
  obtain ⟨hP0, hPm⟩ := M3dS11.valuation_coeff_prod_X_sub_C_le A f.roots hroots
  have hcn : A.valuation (f.coeff n) ≤ A.valuation (f.coeff 0) := by
    conv_lhs => rw [hfac]
    conv_rhs => rw [hfac]
    rw [coeff_C_mul, coeff_C_mul, map_mul, map_mul, hP0]
    gcongr
    exact hPm n
  rw [hn] at hcn
  exact absurd (lt_of_le_of_lt hcn h0) (lt_irrefl 1)

end S_Polynomial_exists_isRoot_and_valuation_lt_one
end P2MW
export P2MW.S_Polynomial_exists_isRoot_and_valuation_lt_one (solution)
