-- Prove2me | solution 1 for RetailVariety.Fashion.eq_12_sides
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:55:55.210794+00:00
-- url     : https://prove2.me/submissions/51e441aa-21e6-43e3-96f8-9c55c3e306b9

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Lemma1Functions
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

private lemma wp_map_sum {n r t : ℕ} (hr : r ≤ n) (ht : t < r) (w : Fin n → ℝ)
    (θ : ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (∑ j : Fin r, g (wPrime w r t θ hr j)) =
      ∑ j ∈ A n t, g (w j) + g (θ * w ⟨t, by omega⟩) := by
  classical
  have he (j : Fin r) : g (wPrime w r t θ hr j) =
      if j.val < t then g (w (Fin.castLE hr j))
      else if j.val = t then g (θ * w (Fin.castLE hr j)) else 0 := by
    unfold wPrime
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.sum_ite]
  have hs : (∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬j.val < t),
      if j.val = t then g (θ * w (Fin.castLE hr j)) else 0) = g (θ * w ⟨t, by omega⟩) := by
    rw [Finset.sum_eq_single (⟨t,ht⟩ : Fin r)]
    · simp
    · intro j hj hjt
      have hne : j.val ≠ t := by simpa [Fin.ext_iff] using hjt
      simp [hne]
    · simp
  rw [hs]
  rw [show Finset.univ.filter (fun j : Fin r => j.val < t) = A r t by rfl,
    prefix_cast hr (by omega) (fun j => g (w j))]

private lemma sum_g {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (p c lam σ β L : ℝ) :
    (∑ j ∈ S, gFun p c lam σ β L (v j)) =
      (p-c)*lam/L*(∑ j ∈ S, v j) - safetyCoeff p c lam σ β / L^β * (∑ j ∈ S, v j^β) := by
  simp [gFun, Finset.sum_sub_distrib, Finset.mul_sum]

theorem solution {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) = ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ∧
      profitT p c lam v v0 (RetailVariety.Statics.A n r) = ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ∧
      (0 < β → ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) =
        hI p c lam σ β w v0 (RetailVariety.Statics.A n t) (θ * w ⟨t, by omega⟩)) ∧
      ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) =
        hT p c lam w v0 (RetailVariety.Statics.A n t) (θ * w ⟨t, by omega⟩) := by
  classical
  have hLp : 0 < L := by
    rw [hL]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => hv j) hv0
  have hD : RetailVariety.Structure.fDen w v0 (A n t) (θ * w ⟨t,by omega⟩) = L := by
    unfold RetailVariety.Structure.fDen
    rw [heq, hL]
  have hprefix (f : Fin n → ℝ) :
      (∑ j : Fin r, f (Fin.castLE hr j)) = ∑ j ∈ A n r, f j := by
    simpa [A, RetailVariety.Structure.popularSet] using prefix_cast hr (le_refl r) f
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprefix (fun j => gFun p c lam σ β L (v j))]
    unfold profitI RetailVariety.Structure.share
    rw [← hL]
    simp_rw [Real.div_rpow (hv _) hLp.le]
    rw [← Finset.sum_div, ← Finset.sum_div, sum_g]
    ring
  · rw [hprefix (fun j => gFunT p c lam L (v j))]
    unfold profitT RetailVariety.Structure.share
    rw [← hL]
    apply Finset.sum_congr rfl
    intro j hj
    have he : p * (v j / L) - c = (p*v j-c*L)/L := by field_simp
    rw [he]
    have hm : max ((p*v j-c*L)/L) 0 = max (p*v j-c*L) 0 / L := by
      simpa using max_div_div_right hLp.le (p*v j-c*L) 0
    rw [hm]
    unfold gFunT
    ring
  · intro hb
    rw [wp_map_sum hr ht w θ _ (by simp [gFun, Real.zero_rpow hb.ne'])]
    rw [sum_g]
    unfold gFun hI gNumI
    rw [hD, Real.rpow_sub hLp, Real.rpow_one]
    field_simp
    ring
  · have hzero : gFunT p c lam L 0 = 0 := by
      simp [gFunT, max_eq_right (show -(c*L) ≤ 0 by nlinarith)]
    rw [wp_map_sum hr ht w θ _ hzero]
    unfold gFunT hT gNumT
    rw [hD, ← Finset.mul_sum]
    ring
#print axioms solution
