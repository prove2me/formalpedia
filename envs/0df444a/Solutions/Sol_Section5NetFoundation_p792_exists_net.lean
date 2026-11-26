-- Prove2me | solution 1 for Section5NetFoundation.p792_exists_net
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:36.064907+00:00
-- url     : https://prove2.me/submissions/0ff30e3d-8b1d-44fe-92fb-945fb4365278

import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Mathlib
import Theorems.Thm_Section5NetFoundation_p792_pack_bound
set_option autoImplicit false
namespace Section5NetFoundation
end Section5NetFoundation
open Section5NetFoundation
open MeasureTheory HighDimProb.RandomMatrices in

theorem solution (n : ℕ) (ε : ℝ) (hε : 0 < ε) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : K ⊆ Metric.closedBall 0 1) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)), IsEpsNet K (↑N : Set _) ε ∧
      (N.card : ℝ) ≤ (2 / ε + 1) ^ n := by
  classical
  let P : ℕ → Prop := fun m => ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    (↑C : Set _) ⊆ K ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧ C.card = m
  let B : ℕ := ⌊(2 / ε + 1) ^ n⌋₊
  have hbound : ∀ m, P m → m ≤ B := by
    rintro m ⟨C, hCK, hsep, rfl⟩
    exact Nat.le_floor (Section5NetFoundation.p792_pack_bound n ε hε C (hCK.trans hK) hsep)
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  have hk : P (Nat.findGreatest P B) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨C, hCK, hsep, hcard⟩ := hk
  refine ⟨C, ⟨hCK, fun x hx => ?_⟩, Section5NetFoundation.p792_pack_bound n ε hε C (hCK.trans hK) hsep⟩
  by_contra hno
  push Not at hno
  have hxC : x ∉ C := by
    intro hxC
    have := hno x (Finset.mem_coe.2 hxC)
    rw [dist_self] at this
    linarith
  have hP1 : P (Nat.findGreatest P B + 1) := by
    refine ⟨insert x C, ?_, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hCK
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hno b (Finset.mem_coe.2 hb)
      · rw [dist_comm]; exact hno a (Finset.mem_coe.2 ha)
      · exact hsep a ha b hb hab
    · rw [Finset.card_insert_of_notMem hxC, hcard]
  have := Nat.le_findGreatest (hbound _ hP1) hP1
  omega
