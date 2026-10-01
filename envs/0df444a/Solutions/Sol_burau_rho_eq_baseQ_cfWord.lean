-- Prove2me | solution 1 for burau_rho_eq_baseQ_cfWord
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T23:54:24.929428+00:00
-- url     : https://prove2.me/submissions/d6af297e-d8a5-4f05-b4ca-0b4813b87b8c

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

open Matrix

namespace BurauNC

theorem cfWord_cons_ (e : ℤ) (l : List ℤ) :
    cfWord (e :: l) = cfWord l * (liftS⁻¹ * liftT ^ e) := rfl

theorem cfEnd_eq_ (M : M2) (h : M 0 0 = 0) : cfEnd M = M := by
  rw [cfEnd.eq_def]
  exact dif_pos h

theorem cfEnd_cons_ (M : M2) (h : M 0 0 ≠ 0) :
    cfEnd M = cfEnd ((M * Tm (-(M 0 1 / M 0 0))) * Sm) := by
  rw [cfEnd.eq_def]
  exact dif_neg h

theorem rhoIter_eq_rhoIter_ (j : ℕ) (M : M2) (hk : (M 0 0).natAbs ≤ j) :
    rhoIter j M = rhoIter ((M 0 0).natAbs) M := by
  revert M
  refine Nat.strong_induction_on j ?_
  intro j ih M hk
  match j with
  | 0 =>
      have h0 : M 0 0 = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp only [h0, Int.natAbs_zero]
  | k + 1 =>
      by_cases h0 : M 0 0 = 0
      · simp only [rhoIter, h0, Int.natAbs_zero, ↓reduceIte]
      · have hdec : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs < (M 0 0).natAbs :=
          euclid_decrease M h0
        have hle2 : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs ≤ (M 0 0).natAbs - 1 := by
          omega
        have hlt : (M 0 0).natAbs - 1 < k + 1 := by omega
        have hN : (M 0 0).natAbs = ((M 0 0).natAbs - 1) + 1 := by omega
        simp only [rhoIter, if_neg h0]
        rw [hN]
        simp only [rhoIter, if_neg h0]
        congr 1
        rw [ih k (by omega) (M * Tm (-(M 0 1 / M 0 0)) * Sm) (by omega),
          ih ((M 0 0).natAbs - 1) hlt (M * Tm (-(M 0 1 / M 0 0)) * Sm) hle2]

theorem rhoIter_eq_rho_ (k : ℕ) (M : M2) (hk : (M 0 0).natAbs ≤ k) :
    rhoIter k M = rho M := by
  rw [rhoIter_eq_rhoIter_ k M hk]
  rfl

end BurauNC

theorem solution (M : BurauNC.M2) :
    BurauNC.rho M = BurauNC.baseQ (BurauNC.cfEnd M) * BurauNC.cfWord (BurauNC.cfList M) := by
  have main : ∀ k : ℕ, ∀ M : BurauNC.M2, (M 0 0).natAbs ≤ k →
      BurauNC.rho M = BurauNC.baseQ (BurauNC.cfEnd M) * BurauNC.cfWord (BurauNC.cfList M) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro M hk
      by_cases h : M 0 0 = 0
      · rw [BurauNC.cfEnd_eq_ M h, BurauNC.cfList_eq_nil M h, BurauNC.rho]
        simp only [h, Int.natAbs_zero, BurauNC.rhoIter, BurauNC.cfWord]
        simp
      · have hbud : (((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 0).natAbs
            ≤ (M 0 0).natAbs - 1 := by
          have := BurauNC.euclid_decrease M h
          omega
        have hlt : (M 0 0).natAbs - 1 < k := by omega
        have hN : (M 0 0).natAbs = ((M 0 0).natAbs - 1) + 1 := by omega
        rw [BurauNC.cfEnd_cons_ M h, BurauNC.cfList_cons M h, BurauNC.cfWord_cons_,
          BurauNC.rho, hN]
        simp only [BurauNC.rhoIter, if_neg h]
        rw [BurauNC.rhoIter_eq_rho_ _ _ hbud]
        rw [ih ((M 0 0).natAbs - 1) hlt ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) hbud]
        group
  exact main (M 0 0).natAbs M le_rfl
