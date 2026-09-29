-- Prove2me | solution 1 for WeightedHilbert_cotangent_bound_of_real
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T16:41:54.35928+00:00
-- url     : https://prove2.me/submissions/669336da-80bb-456a-9243-7d1f491c70c8

import Theorems.Thm_WeightedHilbert_cauchy_translation_average_tendsto
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

open Filter
open scoped Topology ComplexConjugate

set_option autoImplicit false
open scoped BigOperators
namespace WeightedHilbert

/-- Integer translates preserve circularly admissible gaps. The bound by one
is needed for distinct copies of the same phase. -/
theorem translated_gap {ι : Type} (θ δ : ι → ℝ)
    (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|)
    (n : ℕ) (r s : ι × Fin n) (hrs : r ≠ s) :
    δ r.1 ≤ |(θ r.1 + (r.2 : ℕ)) - (θ s.1 + (s.2 : ℕ))| := by
  rcases r with ⟨r, k⟩
  rcases s with ⟨s, l⟩
  dsimp only
  by_cases he : r = s
  · subst s
    have hkl : (k : ℕ) ≠ (l : ℕ) := by
      intro h
      exact hrs (by cases Fin.ext h; rfl)
    have hz : ((k : ℕ) : ℤ) ≠ ((l : ℕ) : ℤ) := by exact_mod_cast hkl
    have hreal : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by
      exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hz))
    calc
      δ r ≤ 1 := hunit r
      _ ≤ |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := hreal
      _ = |(θ r + (k : ℕ)) - (θ r + (l : ℕ))| := by congr 1 <;> ring
  · have h := hgap r s he (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))
    convert h using 1 <;> push_cast <;> congr 1 <;> ring

theorem translated_injective {ι : Type} (θ δ : ι → ℝ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|)
    (n : ℕ) : Function.Injective (fun r : ι × Fin n => θ r.1 + (r.2 : ℕ)) := by
  intro r s he
  dsimp only at he
  by_contra hn
  have h := translated_gap θ δ hunit hgap n r s hn
  rw [he, sub_self, abs_zero] at h
  exact (not_le_of_gt (hpos r.1)) h

/-- Same-phase interactions cancel, including the diagonal under total inverse. -/
theorem same_phase_kernel_sum (n : ℕ) :
    (∑ k : Fin n, ∑ l : Fin n, (((k : ℕ) : ℂ) - ((l : ℕ) : ℂ))⁻¹) = 0 := by
  let S : ℂ := ∑ k : Fin n, ∑ l : Fin n,
    (((k : ℕ) : ℂ) - ((l : ℕ) : ℂ))⁻¹
  have h : S = -S := by
    dsimp [S]
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    calc
      _ = (-(((k : ℕ) : ℂ) - ((l : ℕ) : ℂ)))⁻¹ := by rw [neg_sub]
      _ = _ := inv_neg
  change S = 0
  have htwo : (2 : ℂ) * S = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end WeightedHilbert


namespace WeightedHilbert
open scoped ComplexConjugate

theorem translation_form {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    (∑ r : ι × Fin n, ∑ s : ι × Fin n,
      if r = s then (0 : ℂ) else
        v r.1 * conj (v s.1) /
          (((θ r.1 + (r.2 : ℕ)) - (θ s.1 + (s.2 : ℕ)) : ℝ) : ℂ)) =
    ∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
      v r * conj (v s) *
        ∑ k : Fin n, ∑ l : Fin n,
          (((θ r - θ s : ℝ) : ℂ) + (k : ℕ) - (l : ℕ))⁻¹ := by
  have hc (r s : ι × Fin n) :
      (if r = s then (0 : ℂ) else
        v r.1 * conj (v s.1) /
          (((θ r.1 + (r.2 : ℕ)) - (θ s.1 + (s.2 : ℕ)) : ℝ) : ℂ)) =
      v r.1 * conj (v s.1) /
          (((θ r.1 + (r.2 : ℕ)) - (θ s.1 + (s.2 : ℕ)) : ℝ) : ℂ) := by
    by_cases h : r = s
    · subst s; simp
    · simp only [if_neg h]
  simp only [hc, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases he : r = s
  · subst s
    simp only [if_pos rfl]
    have hd (k l : Fin n) :
        (((θ r + (k : ℕ)) - (θ r + (l : ℕ)) : ℝ) : ℂ) =
          ((k : ℕ) : ℂ) - ((l : ℕ) : ℂ) := by push_cast; ring
    simp only [hd, div_eq_mul_inv, ← Finset.mul_sum, same_phase_kernel_sum, mul_zero,
      ite_true]
  · simp only [if_neg he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    push_cast
    ring

end WeightedHilbert


namespace WeightedHilbert
open scoped ComplexConjugate

theorem translated_form_bound (C : ℝ)
    (hH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (freq δ : κ → ℝ) (v : κ → ℂ),
      Function.Injective freq → (∀ r, 0 < δ r) →
      (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / ((freq r - freq s : ℝ) : ℂ)‖ ≤
          C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) (n : ℕ) :
    ‖∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
      v r * conj (v s) * ∑ k : Fin n, ∑ l : Fin n,
        (((θ r - θ s : ℝ) : ℂ) + (k : ℕ) - (l : ℕ))⁻¹‖ ≤
      C * (n : ℝ) * ∑ r, ‖v r‖ ^ 2 / δ r := by
  have h := hH (ι × Fin n) (fun r => θ r.1 + (r.2 : ℕ))
    (fun r => δ r.1) (fun r => v r.1)
    (translated_injective θ δ hpos hunit hgap n)
    (fun r => hpos r.1) (translated_gap θ δ hunit hgap n)
  rw [translation_form] at h
  convert h using 1
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Transfer the real weighted Hilbert bound to the pi-cotangent kernel by
finite integer translations. No circle-kernel estimate is an assumption. -/
theorem cotangent_bound_of_real (C : ℝ)
    (hH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (freq δ : κ → ℝ) (v : κ → ℂ),
      Function.Injective freq → (∀ r, 0 < δ r) →
      (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / ((freq r - freq s : ℝ) : ℂ)‖ ≤
          C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / δ r := by
  have hnot (r s : ι) (hrs : r ≠ s) :
      ((θ r - θ s : ℝ) : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨m, hm⟩
    have hm' : (m : ℝ) = θ r - θ s := by exact_mod_cast hm
    have h := hgap r s hrs (-m)
    rw [← hm', Int.cast_neg, add_neg_cancel, abs_zero] at h
    exact (not_le_of_gt (hpos r)) h
  let F (n : ℕ) : ℂ := ∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
    v r * conj (v s) * ∑ k : Fin n, ∑ l : Fin n,
      (((θ r - θ s : ℝ) : ℂ) + (k : ℕ) - (l : ℕ))⁻¹
  have hlim : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • F n) atTop
      (𝓝 (∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
        v r * conj (v s) * ((Real.pi : ℂ) *
          Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))))) := by
    simp only [F, Finset.smul_sum, smul_ite, smul_zero]
    apply tendsto_finsetSum
    intro r hr
    apply tendsto_finsetSum
    intro s hs
    by_cases he : r = s
    · simp only [if_pos he]
      exact tendsto_const_nhds
    · simp only [if_neg he]
      have ht := WeightedHilbert_cauchy_translation_average_tendsto
        ((θ r - θ s : ℝ) : ℂ) (hnot r s he)
      simp only [Finset.sum_range] at ht
      simpa only [mul_smul_comm] using
        (tendsto_const_nhds (x := v r * conj (v s))).mul ht
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hb := translated_form_bound C hH θ δ v hpos hunit hgap n
  change ‖(n⁻¹ : ℝ) • F n‖ ≤ _
  calc
    ‖(n⁻¹ : ℝ) • F n‖ = (n : ℝ)⁻¹ * ‖F n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn'.le)]
    _ ≤ (n : ℝ)⁻¹ * (C * n * ∑ r, ‖v r‖ ^ 2 / δ r) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn'.le)
    _ = C * ∑ r, ‖v r‖ ^ 2 / δ r := by field_simp

end WeightedHilbert


theorem solution (C : ℝ)
    (hH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (freq δ : κ → ℝ) (v : κ → ℂ),
      Function.Injective freq → (∀ r, 0 < δ r) →
      (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / ((freq r - freq s : ℝ) : ℂ)‖ ≤
          C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / δ r :=
  WeightedHilbert.cotangent_bound_of_real C hH θ δ v hpos hunit hgap

#print axioms solution
