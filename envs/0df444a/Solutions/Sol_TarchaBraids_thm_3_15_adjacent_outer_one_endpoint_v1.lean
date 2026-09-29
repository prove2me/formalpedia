-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_outer_one_endpoint_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:34:19.957608+00:00
-- url     : https://prove2.me/submissions/898f0710-6902-4165-b792-90cfd5278504

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma outerRotateFun_one_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (hi2 : (i : ℕ) + 2 < n) :
    outerRotateFun n i 1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  funext k
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · have hkfin : k = strandIdx i := by
      apply Fin.ext
      simpa [strandIdx] using hk0
    subst k
    rw [Function.comp_apply, Equiv.swap_apply_left]
    simp [outerRotateFun, twistPoint, strandIdx, strandIdxSucc, hji, baseOrdered]
    push_cast
    ring
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · have hkfin : k = strandIdxSucc i := by
        apply Fin.ext
        simpa [strandIdxSucc] using hk1
      subst k
      have hleft : strandIdxSucc i ≠ strandIdx i := by
        intro h
        have hv := congrArg Fin.val h
        simp [strandIdx, strandIdxSucc] at hv
      have hright : strandIdxSucc i ≠ strandIdxSucc j := by
        intro h
        have hv := congrArg Fin.val h
        simp [strandIdxSucc, hji] at hv
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hleft hright]
      simp [outerRotateFun, twistPoint, strandIdx, strandIdxSucc, hji, baseOrdered]
      push_cast
      ring
    · by_cases hk2 : (k : ℕ) = (i : ℕ) + 2
      · have hkfin : k = strandIdxSucc j := by
          apply Fin.ext
          simpa [strandIdxSucc, hji] using hk2
        subst k
        rw [Function.comp_apply, Equiv.swap_apply_right]
        have hv : (strandIdxSucc j : ℕ) = (i : ℕ) + 2 := by
          simp [strandIdxSucc, hji]
        have h0 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) := by omega
        have h1 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) + 1 := by omega
        rw [show outerRotateFun n i 1 (strandIdxSucc j) =
            twistPoint ((i : ℕ) + 2) 2 1 by
          simp [outerRotateFun, h0, h1, hv]]
        simp [twistPoint, baseOrdered, strandIdx]
        push_cast
        ring
      · have hk_ne_left : k ≠ strandIdx i := by
          intro hk
          exact hk0 (by simpa [strandIdx] using congrArg Fin.val hk)
        have hk_ne_right : k ≠ strandIdxSucc j := by
          intro hk
          exact hk2 (by simpa [strandIdxSucc, hji] using congrArg Fin.val hk)
        rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk_ne_left hk_ne_right]
        simp [outerRotateFun, hk0, hk1, hk2, baseOrdered]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (hi2 : (i : ℕ) + 2 < n),
      outerRotateFun n i 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  exact fun i j hji hi2 => outerRotateFun_one_endpoint i j hji hi2
