-- Prove2me | solution 1 for TractableDRO.Unified.pi_le_piOf
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:53:53.406976+00:00
-- url     : https://prove2.me/submissions/8fd63e98-6660-4a04-8346-3520bef72946

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model
open MeasureTheory ProbabilityTheory Matrix
namespace TractableDRO.Unified
theorem psi_zero_le {d : ℕ} (W : Set (Fin d → ℝ)) (sf sb : Fin d → ℝ) :
    psi W sf sb 0 0 ≤ 0 := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hz' : 0 < z := by exact_mod_cast hz
  unfold psi
  apply iInf_le_of_le (z * Real.exp 1)
  apply iInf_le_of_le (mul_pos hz' (Real.exp_pos 1))
  apply iSup_le
  intro zh
  apply iSup_le
  intro _
  have he : z * Real.exp 1 / Real.exp 1 = z := mul_div_cancel_right₀ z (Real.exp_ne_zero 1)
  simp [uvec, he]

theorem piOf_zero_le {n N d : ℕ} (D : Data n N d) (s : Fin 3) :
    piOf D s 0 0 ≤ 0 := by
  fin_cases s
  · unfold piOf pi1
    apply iInf_le_of_le 0
    have h1 : (⨆ zh ∈ D.Vhat, (( (0 : Fin n → ℝ) ⬝ᵥ zh : ℝ) : EReal)) ≤ 0 := by
      apply iSup_le; intro zh; apply iSup_le; intro _; simp
    have h2 : (⨆ z ∈ D.V, ((max (0 + (0 : Fin n → ℝ) ⬝ᵥ z - (0 : Fin n → ℝ) ⬝ᵥ z)
        (-((0 : Fin n → ℝ) ⬝ᵥ z)) : ℝ) : EReal)) ≤ 0 := by
      apply iSup_le; intro zh; apply iSup_le; intro _; simp
    simpa using add_le_add h1 h2
  · unfold piOf TractableDRO.MeanCov.pi2
    apply iInf_le_of_le 0
    apply iInf_le_of_le (show D.Fᵀ *ᵥ (0 : Fin N → ℝ) = 0 by simp)
    apply iSup_le; intro zh; apply iSup_le; intro _
    simp
  · unfold piOf pi3
    apply iInf_le_of_le 0
    apply iInf_le_of_le 0
    apply iInf_le_of_le 0
    apply iInf_le_of_le 0
    apply iInf_le_of_le (show (0:ℝ) + (0 : Fin d → ℝ) ⬝ᵥ D.gσ = 0 by simp)
    apply iInf_le_of_le (show D.Fσᵀ *ᵥ (0 : Fin d → ℝ) = 0 by simp)
    have h1 : (⨆ zh ∈ D.Vhat, ((( (0 : Fin n → ℝ) - D.Fσᵀ *ᵥ 0) ⬝ᵥ zh : ℝ) : EReal)) ≤ 0 := by
      apply iSup_le; intro zh; apply iSup_le; intro _; simp
    have hp := psi_zero_le D.Wσhat D.σf D.σb
    simpa using add_le_add (add_le_add (add_le_add (le_refl (0 : EReal)) h1) hp) hp


/-- Theorem 4, p. 911, (26) (right inequality): `π(r⁰, r) ≤ π^s(r⁰, r)` for every `s ∈ S`. -/
theorem pi_le_piOf {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3)) (r0 : ℝ)
    (r : Fin n → ℝ) : ∀ s ∈ S, piU D S r0 r ≤ piOf D s r0 r := by
  classical
  intro s hs
  let r0s : Fin 3 → ℝ := fun t => if t = s then r0 else 0
  let rs : Fin 3 → Fin n → ℝ := fun t => if t = s then r else 0
  unfold piU
  apply iInf_le_of_le r0s
  apply iInf_le_of_le rs
  apply iInf_le_of_le (show r0 = ∑ t ∈ S, r0s t by simp [r0s, hs])
  apply iInf_le_of_le (show r = ∑ t ∈ S, rs t by simp [rs, hs])
  calc
    ∑ t ∈ S, piOf D t (r0s t) (rs t) ≤
      ∑ t ∈ S, (if t = s then piOf D s r0 r else 0) := by
        apply Finset.sum_le_sum
        intro t _
        by_cases ht : t = s
        · subst t; simp [r0s, rs]
        · simpa [r0s, rs, ht] using piOf_zero_le D t
    _ = piOf D s r0 r := by simp [hs]


end TractableDRO.Unified

theorem solution {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ)
    (S : Finset (Fin 3)) (r0 : ℝ) (r : Fin n → ℝ) :
    ∀ s ∈ S, TractableDRO.Unified.piU D S r0 r ≤ TractableDRO.Unified.piOf D s r0 r :=
  TractableDRO.Unified.pi_le_piOf D S r0 r
#print axioms solution
