-- Prove2me | solution 1 for PochetWolsey.Mixing.extended_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T02:38:30.224212+00:00
-- url     : https://prove2.me/submissions/5e615cb3-e505-4213-a8b5-9f8994b7975a

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model
import Definitions.Def_PochetWolsey_Mixing_Extended

set_option autoImplicit false

namespace PWMixAux

/-- If `X` is closed under translation by `d`, then its convex hull is closed under
translation by any nonnegative real multiple of `d`. -/
lemma shift_mem {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E) (d : E)
    (hX : ∀ x ∈ X, x + d ∈ X) {x : E} (hx : x ∈ convexHull ℝ X) {t : ℝ} (ht : 0 ≤ t) :
    x + t • d ∈ convexHull ℝ X := by
  have hn : ∀ n : ℕ, ∀ x ∈ X, x + (n : ℝ) • d ∈ X := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have h := hX _ (ih x hx)
      have e : x + ((n + 1 : ℕ) : ℝ) • d = x + (n : ℝ) • d + d := by
        push_cast; module
      rw [e]; exact h
  let S : Set E := {x | ∀ t : ℝ, 0 ≤ t → x + t • d ∈ convexHull ℝ X}
  have hXS : X ⊆ S := by
    intro x hx t ht
    have h1 : x + ((⌊t⌋₊ : ℕ) : ℝ) • d ∈ convexHull ℝ X :=
      subset_convexHull ℝ X (hn _ x hx)
    have h2 : x + ((⌊t⌋₊ + 1 : ℕ) : ℝ) • d ∈ convexHull ℝ X :=
      subset_convexHull ℝ X (hn _ x hx)
    have hθ0 : 0 ≤ t - (⌊t⌋₊ : ℝ) := by have := Nat.floor_le ht; linarith
    have hθ1 : t - (⌊t⌋₊ : ℝ) ≤ 1 := by have := Nat.lt_floor_add_one t; linarith
    have h := convex_convexHull ℝ X h1 h2 (by linarith : (0:ℝ) ≤ 1 - (t - (⌊t⌋₊ : ℝ))) hθ0
      (by ring)
    convert h using 1
    push_cast
    module
  have hS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab t ht
    have h := convex_convexHull ℝ X (hx t ht) (hy t ht) ha hb hab
    convert h using 1
    obtain rfl : b = 1 - a := by linarith
    module
  exact convexHull_min hXS hS hx t ht

end PWMixAux

theorem solution {K : ℕ} (hK : 0 < K) (b : Fin K → ℝ) :
    let f : Option (Fin K) → ℝ := fun j =>
      match j with
      | none => 0
      | some k => b k - (⌊b k⌋ : ℝ)
    convexHull ℝ
      {p : ℝ × (Fin K → ℝ) | 0 ≤ p.1 ∧
        (∀ k, ∃ z : ℤ, p.2 k = (z : ℝ)) ∧ ∀ k, b k ≤ p.1 + p.2 k} =
      {p : ℝ × (Fin K → ℝ) | ∃ δ : Option (Fin K) → ℝ, ∃ μ : ℝ,
        (∀ j, 0 ≤ δ j) ∧ 0 ≤ μ ∧ (∑ j, δ j) = 1 ∧
        p.1 = (∑ j, f j * δ j) + μ ∧
        ∀ k, (∑ j, (⌈b k - f j⌉ : ℝ) * δ j) - μ ≤ p.2 k} := by
  intro f
  have hfn : f none = 0 := rfl
  have hfs : ∀ k, f (some k) = b k - (⌊b k⌋ : ℝ) := fun k => rfl
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j; cases j with
    | none => rw [hfn]
    | some k => rw [hfs]; linarith [Int.floor_le (b k)]
  have hf1 : ∀ j, f j < 1 := by
    intro j; cases j with
    | none => rw [hfn]; norm_num
    | some k => rw [hfs]; linarith [Int.lt_floor_add_one (b k)]
  set X : Set (ℝ × (Fin K → ℝ)) := {p : ℝ × (Fin K → ℝ) | 0 ≤ p.1 ∧
        (∀ k, ∃ z : ℤ, p.2 k = (z : ℝ)) ∧ ∀ k, b k ≤ p.1 + p.2 k} with hXdef
  apply Set.Subset.antisymm
  · apply convexHull_min
    · -- X ⊆ Q
      rintro ⟨s, y⟩ ⟨hs, hy, hb⟩
      simp only at hs hy hb
      set φ : ℝ := s - (⌊s⌋ : ℝ) with hφ
      have hφ0 : 0 ≤ φ := by linarith [Int.floor_le s]
      have hφ1 : φ < 1 := by linarith [Int.lt_floor_add_one s]
      have hflo : (0:ℝ) ≤ (⌊s⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hs
      have hne : (Finset.univ.filter (fun j => f j ≤ φ)).Nonempty :=
        ⟨none, by simp [hfn, hφ0]⟩
      obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _ f hne
      have hjφ : f j ≤ φ := (Finset.mem_filter.mp hj).2
      refine ⟨fun i => if i = j then 1 else 0, s - f j, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; dsimp only; split_ifs <;> norm_num
      · linarith
      · simp
      · simp
      · intro k
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        obtain ⟨z, hz⟩ := hy k
        have hbk := hb k
        rw [hz] at hbk ⊢
        -- Z = z + ⌊s⌋ is an integer with Z ≥ b k - φ
        have hZ : b k - f j ≤ ((z + ⌊s⌋ : ℤ) : ℝ) := by
          push_cast
          by_cases hk : f (some k) ≤ φ
          · have hle : f (some k) ≤ f j :=
              hjmax (some k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
            rw [hfs] at hle hk
            have h1 : ((⌊b k⌋ : ℤ) : ℝ) - 1 < ((z + ⌊s⌋ : ℤ) : ℝ) := by
              push_cast; linarith [Int.floor_le (b k)]
            have h2 : (⌊b k⌋ : ℤ) - 1 < z + ⌊s⌋ := by exact_mod_cast h1
            have h3 : (⌊b k⌋ : ℤ) ≤ z + ⌊s⌋ := by omega
            have h4 : ((⌊b k⌋ : ℤ) : ℝ) ≤ ((z + ⌊s⌋ : ℤ) : ℝ) := by exact_mod_cast h3
            push_cast at h4
            linarith
          · push Not at hk
            rw [hfs] at hk
            have h1 : ((⌊b k⌋ : ℤ) : ℝ) < ((z + ⌊s⌋ : ℤ) : ℝ) := by
              push_cast; linarith
            have h2 : (⌊b k⌋ : ℤ) < z + ⌊s⌋ := by exact_mod_cast h1
            have h3 : (⌊b k⌋ : ℤ) + 1 ≤ z + ⌊s⌋ := by omega
            have h4 : ((⌊b k⌋ : ℤ) : ℝ) + 1 ≤ ((z + ⌊s⌋ : ℤ) : ℝ) := by exact_mod_cast h3
            push_cast at h4
            linarith [Int.lt_floor_add_one (b k), hf0 j]
        have hc : ⌈b k - f j⌉ ≤ z + ⌊s⌋ := Int.ceil_le.mpr hZ
        have hc' : ((⌈b k - f j⌉ : ℤ) : ℝ) ≤ ((z + ⌊s⌋ : ℤ) : ℝ) := by exact_mod_cast hc
        push_cast at hc'
        linarith
    · -- Q convex
      rintro p ⟨δ, μ, hδ, hμ, hsum, h1, h2⟩ p' ⟨δ', μ', hδ', hμ', hsum', h1', h2'⟩ a c ha hc hac
      refine ⟨fun j => a * δ j + c * δ' j, a * μ + c * μ', ?_, ?_, ?_, ?_, ?_⟩
      · intro j; have := hδ j; have := hδ' j; positivity
      · positivity
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, hsum']
        linarith
      · have e : (∑ j, f j * (a * δ j + c * δ' j)) =
            a * (∑ j, f j * δ j) + c * (∑ j, f j * δ' j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [e, h1, h1']; ring
      · intro k
        have e : (∑ j, (⌈b k - f j⌉ : ℝ) * (a * δ j + c * δ' j)) =
            a * (∑ j, (⌈b k - f j⌉ : ℝ) * δ j) + c * (∑ j, (⌈b k - f j⌉ : ℝ) * δ' j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [e]
        have := mul_le_mul_of_nonneg_left (h2 k) ha
        have := mul_le_mul_of_nonneg_left (h2' k) hc
        nlinarith
  · -- Q ⊆ conv X
    rintro p ⟨δ, μ, hδ, hμ, hsum, h1, h2⟩
    let v : Option (Fin K) → ℝ × (Fin K → ℝ) := fun j => (f j, fun k => ((⌈b k - f j⌉ : ℤ) : ℝ))
    have hv : ∀ j, v j ∈ X := by
      intro j
      refine ⟨hf0 j, fun k => ⟨⌈b k - f j⌉, rfl⟩, fun k => ?_⟩
      show b k ≤ f j + ((⌈b k - f j⌉ : ℤ) : ℝ)
      linarith [Int.le_ceil (b k - f j)]
    have hx0 : (∑ j, δ j • v j) ∈ convexHull ℝ X :=
      (convex_convexHull ℝ X).sum_mem (fun j _ => hδ j) hsum
        (fun j _ => subset_convexHull ℝ X (hv j))
    let d0 : ℝ × (Fin K → ℝ) := ((1 : ℝ), fun _ => (-1 : ℝ))
    have hd0 : ∀ x ∈ X, x + d0 ∈ X := by
      rintro ⟨s, y⟩ ⟨hs, hy, hb⟩
      refine ⟨?_, fun k => ?_, fun k => ?_⟩
      · show 0 ≤ s + 1; simp only at hs; linarith
      · obtain ⟨z, hz⟩ := hy k
        exact ⟨z - 1, by show y k + -1 = _; simp only at hz; rw [hz]; push_cast; ring⟩
      · show b k ≤ (s + 1) + (y k + -1); have := hb k; simp only at this; linarith
    have hx1 : (∑ j, δ j • v j) + μ • d0 ∈ convexHull ℝ X := PWMixAux.shift_mem X d0 hd0 hx0 hμ
    let e : Fin K → ℝ × (Fin K → ℝ) := fun k => (0, Pi.single k 1)
    have he : ∀ k, ∀ x ∈ X, x + e k ∈ X := by
      intro k
      rintro ⟨s, y⟩ ⟨hs, hy, hb⟩
      simp only at hs hy hb
      refine ⟨?_, fun k' => ?_, fun k' => ?_⟩
      · show 0 ≤ s + 0; linarith
      · obtain ⟨z, hz⟩ := hy k'
        refine ⟨z + (if k' = k then 1 else 0), ?_⟩
        show y k' + (Pi.single k (1:ℝ) : Fin K → ℝ) k' = _
        rw [hz, Pi.single_apply]; split_ifs <;> push_cast <;> ring
      · show b k' ≤ (s + 0) + (y k' + (Pi.single k (1:ℝ) : Fin K → ℝ) k')
        have := hb k'
        have : (0:ℝ) ≤ (Pi.single k (1:ℝ) : Fin K → ℝ) k' := by
          rw [Pi.single_apply]; split_ifs <;> norm_num
        linarith
    set σ : Fin K → ℝ := fun k => p.2 k - ((∑ j, (⌈b k - f j⌉ : ℝ) * δ j) - μ) with hσ
    have hσ0 : ∀ k, 0 ≤ σ k := fun k => by simp only [hσ]; linarith [h2 k]
    have hslack : ∀ T : Finset (Fin K), ∀ x ∈ convexHull ℝ X,
        x + ∑ k ∈ T, σ k • e k ∈ convexHull ℝ X := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro x hx; simpa using hx
      | insert a T haT ih =>
        intro x hx
        rw [Finset.sum_insert haT]
        have := PWMixAux.shift_mem X (e a) (he a) (ih x hx) (hσ0 a)
        convert this using 1
        abel
    have hfin := hslack Finset.univ _ hx1
    convert hfin using 1
    ext
    · simp [v, d0, e, Prod.fst_sum, h1, mul_comm]
    · rename_i k
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Pi.add_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, v, d0, e, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, hσ]
      have : (∑ j, δ j * ((⌈b k - f j⌉ : ℤ) : ℝ)) = ∑ j, ((⌈b k - f j⌉ : ℤ) : ℝ) * δ j :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [this]; ring
