-- Prove2me | solution 1 for RetailVariety.Fashion.wPrime_majorized
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:53:07.982935+00:00
-- url     : https://prove2.me/submissions/a750b72d-b146-4e21-82ee-943dd930413b

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_RetailVariety_Fashion_ProofObjects
open RetailVariety.Fashion RetailVariety.Statics
private lemma prefix_cast {n r k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (f : Fin n → ℝ) :
    (∑ j ∈ A r k, f (Fin.castLE hr j)) = ∑ j ∈ A n k, f j := by
  classical
  apply Finset.sum_bij (fun j _ => Fin.castLE hr j)
  · intro j hj
    simpa [A, RetailVariety.Structure.popularSet] using hj
  · intro i hi j hj he
    exact Fin.castLE_injective hr he
  · intro j hj
    have h : j.val < k := by simpa [A, RetailVariety.Structure.popularSet] using hj
    refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
    · simp [A, RetailVariety.Structure.popularSet, h]
    · rfl
  · intro j hj
    rfl

private lemma wp_sum {n r t : ℕ} (hr : r ≤ n) (ht : t < r) (w : Fin n → ℝ) (θ : ℝ) :
    (∑ j : Fin r, wPrime w r t θ hr j) =
      ∑ j ∈ A n t, w j + θ * w ⟨t, by omega⟩ := by
  classical
  unfold wPrime
  rw [Finset.sum_ite]
  have hs : (∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬j.val < t),
      if j.val = t then θ * w (Fin.castLE hr j) else 0) = θ * w ⟨t, by omega⟩ := by
    rw [Finset.sum_eq_single (⟨t,ht⟩ : Fin r)]
    · simp
    · intro j hj hjt
      have hne : j.val ≠ t := by simpa [Fin.ext_iff] using hjt
      simp [hne]
    · simp
  rw [hs]
  rw [show Finset.univ.filter (fun j : Fin r => j.val < t) = A r t by rfl,
    prefix_cast hr (by omega)]

theorem solution {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∑ j : Fin r, wPrime w r t θ hr j = ∑ j : Fin r, v (Fin.castLE hr j) ∧
      Majorized (fun j : Fin r => v (Fin.castLE hr j)) (wPrime w r t θ hr) := by
  classical
  have hsum := wp_sum hr ht w θ
  have hvsum : (∑ j : Fin r, v (Fin.castLE hr j)) = ∑ j ∈ A n r, v j := by
    simpa [A, RetailVariety.Structure.popularSet] using prefix_cast hr (le_refl r) v
  have he : (∑ j : Fin r, wPrime w r t θ hr j) = ∑ j : Fin r, v (Fin.castLE hr j) :=
    hsum.trans (heq.trans hvsum.symm)
  refine ⟨he, Equiv.refl _, Equiv.refl _, ?_, ?_, he.symm, ?_⟩
  · intro i j hij
    exact hva (show Fin.castLE hr i ≤ Fin.castLE hr j from hij)
  · intro i j hij
    dsimp [Function.comp, wPrime]
    have hij' : i.val ≤ j.val := hij
    have hwi := hw (Fin.castLE hr i)
    have hwj := hw (Fin.castLE hr j)
    have hwij := hwa (show Fin.castLE hr i ≤ Fin.castLE hr j from hij)
    split_ifs <;> try omega
    all_goals try (have heij : i = j := Fin.ext (by omega); simp [heij])
    all_goals nlinarith
  · intro k hk hkr
    obtain ⟨σv,σw,hvσ,hwσ,heall,hpart⟩ := hvw
    have hvEq : v ∘ σv = v := by
      simpa using Tuple.unique_antitone (σ := σv) (τ := Equiv.refl _) hvσ hva
    have hwEq : w ∘ σw = w := by
      simpa using Tuple.unique_antitone (σ := σw) (τ := Equiv.refl _) hwσ hwa
    have hev (i : Fin n) : v (σv i) = v i := congrFun hvEq i
    have hew (i : Fin n) : w (σw i) = w i := congrFun hwEq i
    simp_rw [hev, hew] at hpart
    change (∑ j ∈ A r k, v (Fin.castLE hr j)) ≤ ∑ j ∈ A r k, wPrime w r t θ hr j
    by_cases hkt : k ≤ t
    · rw [prefix_cast hr (by omega)]
      have hwpre : (∑ j ∈ A r k, wPrime w r t θ hr j) = ∑ j ∈ A n k, w j := by
        rw [← prefix_cast hr (by omega) w]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j.val < k := by simpa [A, RetailVariety.Structure.popularSet] using hj
        simp [wPrime, show j.val < t by omega]
      rw [hwpre]
      exact hpart k hk (by omega)
    · have hwpre : (∑ j ∈ A r k, wPrime w r t θ hr j) = ∑ j : Fin r, wPrime w r t θ hr j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j hj hjk
        have hjk' : k ≤ j.val := by
          simpa [A, RetailVariety.Structure.popularSet] using hjk
        simp [wPrime, show ¬j.val < t by omega, show j.val ≠ t by omega]
      rw [hwpre, he]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => hv _)
#print axioms solution
