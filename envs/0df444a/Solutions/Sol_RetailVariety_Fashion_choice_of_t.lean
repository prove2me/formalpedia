-- Prove2me | solution 1 for RetailVariety.Fashion.choice_of_t
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:34:43.877974+00:00
-- url     : https://prove2.me/submissions/227e6331-e814-4587-be78-d4bb45f05e01

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
open RetailVariety.Fashion
open RetailVariety.Statics

private lemma prefix_succ {n k : ℕ} (hk : k < n) :
    A n (k+1) = insert ⟨k,hk⟩ (A n k) := by
  ext j
  simp only [A, RetailVariety.Structure.popularSet, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

private lemma fractional_prefix {n : ℕ} (w : Fin n → ℝ) (q : ℝ) (hq : 0 < q) :
    ∀ r, r ≤ n → q ≤ ∑ j ∈ A n r, w j →
      ∃ t : Fin n, t.val < r ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
        ∑ j ∈ A n t.val, w j + θ * w t = q := by
  intro r
  induction r with
  | zero =>
    intro hr hh
    simp [A, RetailVariety.Structure.popularSet] at hh
    linarith
  | succ r ih =>
    intro hr hh
    by_cases hq' : q ≤ ∑ j ∈ A n r, w j
    · obtain ⟨t,ht,θ,hθ,hθ1,he⟩ := ih (by omega) hq'
      exact ⟨t,by omega,θ,hθ,hθ1,he⟩
    · have hrn : r < n := by omega
      let t : Fin n := ⟨r,hrn⟩
      have ht : t ∉ A n r := by simp [t, A, RetailVariety.Structure.popularSet]
      rw [prefix_succ hrn, Finset.sum_insert ht] at hh
      have hw : 0 < w t := by dsimp [t] at *; linarith
      refine ⟨t,by dsimp [t]; omega,(q-∑ j ∈ A n r, w j)/w t,
        div_pos (by linarith) hw, (div_le_one hw).mpr (by linarith), ?_⟩
      dsimp [t]
      rw [div_mul_cancel₀ _ hw.ne']
      ring

open RetailVariety.Fashion

/-- p. 1506: if `v ≺ w` (both sorted decreasingly, nonnegative) and `∑_{j=1}^r v_j > 0`, there is
a `t ≤ r` and `0 < δ ≤ 1` with `∑_{j=1}^{t−1} w_j + δ w_t = ∑_{j=1}^r v_j`. In Lean, `t : Fin n`
is the paper's `t − 1` (so `t.val < r`, `A n t` is `{1, …, t − 1}` and `w t` is `w_t`), and `θ`
is the paper's `δ`. -/
theorem solution {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (hpos : 0 < ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∃ t : Fin n, t.val < r ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∑ j ∈ RetailVariety.Statics.A n t.val, w j + θ * w t = ∑ j ∈ RetailVariety.Statics.A n r, v j := by


  classical
  obtain ⟨σv,σw,hvσ,hwσ,he,hpart⟩ := hvw
  have hvEq : v ∘ σv = v := by
    simpa using (Tuple.unique_antitone (σ := σv) (τ := Equiv.refl _) hvσ hva)
  have hwEq : w ∘ σw = w := by
    simpa using (Tuple.unique_antitone (σ := σw) (τ := Equiv.refl _) hwσ hwa)
  have hev (i : Fin n) : v (σv i) = v i := congrFun hvEq i
  have hew (i : Fin n) : w (σw i) = w i := congrFun hwEq i
  simp_rw [hev,hew] at he hpart
  have hh : ∑ j ∈ A n r, v j ≤ ∑ j ∈ A n r, w j := by
    by_cases hrn : r = n
    · subst r
      simpa [A, RetailVariety.Structure.popularSet] using he.le
    · by_cases hr0 : r = 0
      · subst r
        simp [A, RetailVariety.Structure.popularSet]
      · exact hpart r (by omega) (by omega)
  exact fractional_prefix w _ hpos r hr hh
#print axioms solution

