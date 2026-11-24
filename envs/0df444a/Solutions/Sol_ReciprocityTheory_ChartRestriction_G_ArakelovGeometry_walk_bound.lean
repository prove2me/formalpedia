-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.walk_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:52.899085+00:00
-- url     : https://prove2.me/submissions/83ce9051-2edb-4e98-90ab-51197e0f89a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pow_tdeg_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution [DecidableEq K] (Δ : (K → ℕ) → ℝ) (a₁ m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ B * m * ((tdeg a : ℝ) + 1) ^ (m - 1)) :
    ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) →
      |Δ a| ≤ |Δ (fun _ => a₁)| + B * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  have hnn : ∀ a : K → ℕ, 0 ≤ B * m * (tdeg a : ℝ) * ((tdeg a : ℝ) + 1) ^ (m - 1) := fun a =>
    mul_nonneg (mul_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pow_nonneg (by positivity) _)
  have hconst : ∀ a : K → ℕ, (∀ k, a k ≤ a₁) → (∀ k, a₁ ≤ a k) →
      |Δ a| ≤ |Δ (fun _ => a₁)| + B * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a h1 h2
    have hc : a = fun _ => a₁ := funext fun k => le_antisymm (h1 k) (h2 k)
    subst hc
    linarith [hnn (fun _ => a₁)]
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n, tdeg a = n := ⟨_, rfl⟩
  induction n generalizing a with
  | zero =>
    apply hconst a _ ha
    intro k
    have hk : a k ≤ tdeg a := by
      unfold tdeg
      exact Finset.single_le_sum (f := a) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
    have := ha k
    omega
  | succ n ih =>
    by_cases hex : ∃ b, a₁ < a b
    · obtain ⟨b, hb⟩ := hex
      obtain ⟨a', ha'⟩ : ∃ a' : K → ℕ, a' = a - Pi.single b 1 := ⟨_, rfl⟩
      have ha'k : ∀ k, a' k + (Pi.single b 1 : K → ℕ) k = a k := by
        intro k
        rw [ha', Pi.sub_apply]
        apply Nat.sub_add_cancel
        by_cases hk : k = b
        · subst hk; simp; omega
        · simp [Pi.single_eq_of_ne hk]
      have ha'1 : ∀ k, a₁ ≤ a' k := by
        intro k
        have e := ha'k k
        by_cases hk : k = b
        · subst hk; simp at e; omega
        · simp [Pi.single_eq_of_ne hk] at e; rw [e]; exact ha k
      have htd : tdeg a' + 1 = tdeg a := by
        have h1 : ∑ k, (Pi.single b 1 : K → ℕ) k = 1 := by simp
        calc tdeg a' + 1 = ∑ k, a' k + ∑ k, (Pi.single b 1 : K → ℕ) k := by rw [h1]; rfl
          _ = ∑ k, a k := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => ha'k k
          _ = tdeg a := rfl
      have IH := ih a' ha'1 (by omega)
      have hs := hstep a b ha hb
      rw [← ha'] at hs
      have hmono : ((tdeg a' : ℝ) + 1) ^ (m - 1) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) :=
        pow_tdeg_mono (by omega) _
      have hT : (tdeg a : ℝ) = tdeg a' + 1 := by rw [← htd]; push_cast; ring
      have hBm : 0 ≤ B * m * (tdeg a' : ℝ) :=
        mul_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have key := mul_le_mul_of_nonneg_left hmono hBm
      generalize ((tdeg a : ℝ) + 1) ^ (m - 1) = P at hs key ⊢
      generalize ((tdeg a' : ℝ) + 1) ^ (m - 1) = P' at IH key
      have tri := abs_sub_abs_le_abs_sub (Δ a) (Δ a')
      rw [hT]
      nlinarith
    · push_neg at hex
      exact hconst a hex ha
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
