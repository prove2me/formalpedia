-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_8d3b99047953
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:30.798267+00:00
-- url     : https://prove2.me/submissions/6718a345-1dc8-4a65-b7e7-47500d1e2cf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m)
    (x e : K → ℤ) :
    f (fun _ => x) - f (fun _ => x - e) - ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons e fun _ : Fin d => x) =
      -∑ s ∈ Finset.univ.filter (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
        f (s.piecewise (fun _ => x) (fun _ => -e)) := by
  have hadd : f (fun _ => x - e) = ∑ s : Finset (Fin (d + 1)), f (s.piecewise (fun _ => x) (fun _ => -e)) := by
    rw [← MultilinearMap.map_add_univ]
    congr 1

  have hone : ∀ s : Finset (Fin (d + 1)), s.card = d →
      f (s.piecewise (fun _ => x) (fun _ => -e)) = -f (Matrix.vecCons e fun _ : Fin d => x) := by
    intro s hs
    obtain ⟨j, hj⟩ : ∃ j, j ∉ s := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have : s = Finset.univ := Finset.eq_univ_of_forall hne
      rw [this, Finset.card_univ, Fintype.card_fin] at hs
      omega
    have hsj : s = Finset.univ.erase j := by
      refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
      · exact Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hi), Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hs]
        omega
    have hpw : s.piecewise (fun _ => x) (fun _ => -e) =
        (Matrix.vecCons (-e) fun _ : Fin d => x) ∘ (Equiv.swap 0 j) := by
      funext i
      simp only [Function.comp]
      by_cases hij : i = j
      · subst hij
        rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Equiv.swap_apply_right]
        simp
      · have hi : i ∈ s := by rw [hsj]; exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
        rw [Finset.piecewise_eq_of_mem _ _ _ hi]
        refine (vecCons_const_of_ne_zero _ _ _ ?_).symm
        intro h0
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
        exact hij h0
    rw [hpw, hsym]
    have hupd : (Matrix.vecCons (-e) fun _ : Fin d => x) =
        Function.update (Matrix.vecCons e fun _ : Fin d => x) 0 (-e) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp
    rw [hupd, MultilinearMap.map_update_neg]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hadd, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1)
      (fun s => s.card = d + 1)]
  have hA : ((Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1).filter
      fun s => s.card = d + 1) = {Finset.univ} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Finset.eq_univ_of_card s (by rw [h, Fintype.card_fin])
    · rintro rfl
      simp
  have hB : ((Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1).filter
      fun s => ¬ s.card = d + 1) = Finset.powersetCard d Finset.univ := by
    ext s
    have hle : s.card ≤ d + 1 := by simpa using Finset.card_le_univ s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    omega
  rw [hA, hB, Finset.sum_singleton, Finset.piecewise_univ,
    Finset.sum_congr rfl (fun s hs => hone s (Finset.mem_powersetCard.mp hs).2), Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_succ_self_right]
  simp only [nsmul_eq_mul]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
