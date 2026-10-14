-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_sign_count_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T09:57:22.247614+00:00
-- url     : https://prove2.me/submissions/66a180a9-2f43-4e92-ac55-d912fda42b4d

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Theorems.Thm_TaoFivePrimes_rh_high_height_normalized_function
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHHighHeightBridgeProof
open RHHighHeight Set
lemma root_of_sign_change {l r : ℝ} (hlr : l ≤ r)
    (hsign : normalized l*normalized r < 0) :
    ∃ t ∈ Ioo l r, riemannZeta (critical t) = 0 := by
  have hc := TaoFivePrimes.rh_high_height_normalized_function.2.1
  have hs : (normalized l < 0 ∧ 0 < normalized r) ∨
      (normalized r < 0 ∧ 0 < normalized l) := by
    rcases mul_neg_iff.mp hsign with h | h
    · exact Or.inr ⟨h.2,h.1⟩
    · exact Or.inl h
  have hex : 0 ∈ normalized '' Ioo l r := by
    rcases hs with h | h
    · exact intermediate_value_Ioo hlr hc.continuousOn h
    · exact intermediate_value_Ioo' hlr hc.continuousOn h
  rcases hex with ⟨t,ht,hzero⟩
  exact ⟨t,ht,(TaoFivePrimes.rh_high_height_normalized_function.2.2 t).mp hzero⟩
lemma critical_injective : Function.Injective critical := by
  intro x y h
  have hi:= congrArg Complex.im h
  simpa [critical] using hi
end RHHighHeightBridgeProof

theorem solution {m : ℕ} {a b : ℝ} (l r : Fin m → ℝ)
    (hbounds : ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j)))
    (hsign : ∀ i, RHHighHeight.normalized (l i)*RHHighHeight.normalized (r i) < 0)
    (hfinite : (RHHighHeight.windowZeros a b).Finite)
    (hcount : (RHHighHeight.windowZeros a b).ncard ≤ m) :
    ∀ s ∈ RHHighHeight.windowZeros a b, s.re = 1/2 := by
  classical
  choose t ht hz using fun i  => RHHighHeightBridgeProof.root_of_sign_change
    (hbounds i).2.1.le (hsign i)
  have hti : Function.Injective t := by
    intro i j hij
    by_contra hne
    have hd := Set.disjoint_left.mp (hdisjoint i j hne)
    exact hd (ht i) (hij ▸ ht j)
  let z : Fin m → ℂ := fun i  => RHHighHeight.critical (t i)
  have hzi : Function.Injective z := RHHighHeightBridgeProof.critical_injective.comp hti
  have hsub : Set.range z ⊆ RHHighHeight.windowZeros a b := by
    rintro s ⟨i,rfl⟩
    refine ⟨hz i,?_,?_,?_,?_⟩
    · norm_num [z,RHHighHeight.critical]
    · norm_num [z,RHHighHeight.critical]
    · simpa [z,RHHighHeight.critical] using (hbounds i).1.trans (ht i).1.le
    · simpa [z,RHHighHeight.critical] using (ht i).2.le.trans (hbounds i).2.2
  have hcard : (Set.range z).ncard = m := by
    rw [Set.ncard_range_of_injective hzi]
    simp
  have heq : Set.range z = RHHighHeight.windowZeros a b := Set.eq_of_subset_of_ncard_le hsub (by simpa [hcard] using hcount) hfinite
  intro s hs
  rw [←heq] at hs
  rcases hs with ⟨i,rfl⟩
  norm_num [z,RHHighHeight.critical]
