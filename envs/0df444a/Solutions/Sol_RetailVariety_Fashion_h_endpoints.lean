-- Prove2me | solution 1 for RetailVariety.Fashion.h_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:30:42.808891+00:00
-- url     : https://prove2.me/submissions/d194ea39-b507-433a-9030-4e4a2486fbb2

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Lemma1Functions
namespace LocalProof
open RetailVariety.Structure

private lemma den_pos {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 ≤ v j)
    (hv0 : 0 < v0) (S : Finset (Fin n)) : 0 < ∑ j ∈ S, v j + v0 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (hv j)) hv0

private lemma independent {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 ≤ v j)
    (hv0 : 0 < v0) (p c lam σ β : ℝ) (S : Finset (Fin n)) :
    profitI p c lam σ β v v0 S =
      ((p-c)*lam*(∑ j ∈ S, v j) -
        (p*σ*lam^β*Real.exp (-(criticalFractile p c)^2/2)/Real.sqrt (2*Real.pi))*
        (∑ j ∈ S, v j^β)*(∑ j ∈ S, v j+v0)^(1-β)) / (∑ j ∈ S, v j+v0) := by
  have hD := den_pos v v0 hv hv0 S
  have hp : (∑ j ∈ S, v j+v0)^(1-β) / (∑ j ∈ S, v j+v0) =
      1 / (∑ j ∈ S, v j+v0)^β := by
    rw [Real.rpow_sub hD, Real.rpow_one]
    field_simp
  unfold profitI share
  simp_rw [Real.div_rpow (hv _) hD.le]
  rw [← Finset.sum_div, ← Finset.sum_div, sub_div]
  simp only [mul_div_assoc]
  rw [hp]
  ring

private lemma trend {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 ≤ v j)
    (hv0 : 0 < v0) (p c lam : ℝ) (S : Finset (Fin n)) :
    profitT p c lam v v0 S =
      lam * (∑ j ∈ S, max (p*v j-c*(∑ i ∈ S, v i+v0)) 0) / (∑ i ∈ S, v i+v0) := by
  have hD := den_pos v v0 hv hv0 S
  unfold profitT share
  have he (j : Fin n) : p * (v j / (∑ i ∈ S, v i+v0)) - c =
      (p*v j-c*(∑ i ∈ S, v i+v0))/(∑ i ∈ S, v i+v0) := by field_simp
  have hm (z : ℝ) : max (z / (∑ i ∈ S, v i+v0)) 0 =
      max z 0 / (∑ i ∈ S, v i+v0) := by
    simpa using (max_div_div_right hD.le z 0)
  simp_rw [he, hm]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  ring

private theorem endpoints {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 ≤ v j) (hv0 : 0 < v0)
    (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (S : Finset (Fin n)) :
    (∀ j, j ∉ S → hI p c lam σ β v v0 S (v j) = profitI p c lam σ β v v0 (insert j S)) ∧
      (∀ j, j ∉ S → hT p c lam v v0 S (v j) = profitT p c lam v v0 (insert j S)) ∧
      hT p c lam v v0 S 0 = profitT p c lam v v0 S ∧
      (0 < β → hI p c lam σ β v v0 S 0 = profitI p c lam σ β v v0 S) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [independent v v0 hv hv0]
    simp [hI, gI, fDen, Finset.sum_insert, hj, add_comm]
  · intro j hj
    rw [trend v v0 hv hv0]
    simp [hT, gT, fDen, Finset.sum_insert, hj, add_comm]
  · rw [trend v v0 hv hv0]
    have hD := den_pos v v0 hv hv0 S
    have hm : max (-(c*(∑ j ∈ S, v j+v0))) 0 = 0 := max_eq_right (by nlinarith)
    simp [hT, gT, fDen, hm]
  · intro hb
    rw [independent v v0 hv hv0]
    simp [hI, gI, fDen, Real.zero_rpow hb.ne']

end LocalProof

open RetailVariety.Fashion

/-- p. 1503, after Lemma 1: `h(0) = π(S, v)` and `h(v_j) = π(S ∪ {j}, v)` for `j ∉ S`, for both
profit functions. The independent-model identities need `0 < β` (with `β = 0`, `0^β = 1`). -/
theorem solution {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    hI p c lam σ β v v0 S 0 = profitI p c lam σ β v v0 S ∧
      hI p c lam σ β v v0 S (v j) = profitI p c lam σ β v v0 (insert j S) ∧
      hT p c lam v v0 S 0 = profitT p c lam v v0 S ∧
      hT p c lam v v0 S (v j) = profitT p c lam v v0 (insert j S) := by


  have h := LocalProof.endpoints v v0 hv hv0 p c lam σ β hc hcp hlam hσ hβ0.le hβ1 S
  exact ⟨h.2.2.2 hβ0, h.1 j hj, h.2.2.1, h.2.1 j hj⟩
#print axioms solution

