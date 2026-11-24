-- Prove2me | solution 1 for TrigPolyMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:27:02.322741+00:00
-- url     : https://prove2.me/submissions/e81506d1-eaaa-4bb0-b52e-d1f2cbab081d

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyMul

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m l : ℕ} {S T : ℝ → ℝ} (hS : TrigPolyLe m S)
    (hT : TrigPolyLe l T) :
    TrigPolyLe (m + l) (fun t => S t * T t) := by
  obtain ⟨a, b, hS'⟩ := hS
  obtain ⟨c, d, hT'⟩ := hT
  have htr : ∀ f g : ℝ → ℝ, TrigPolyLe (m + l) f → (∀ t, g t = f t) →
      TrigPolyLe (m + l) g := by
    intro f g hf hg
    obtain ⟨p, q, hp⟩ := hf
    exact ⟨p, q, fun t => (hg t).trans (hp t)⟩
  have hlc : ∀ f g : ℝ → ℝ, TrigPolyLe (m + l) f → TrigPolyLe (m + l) g →
      ∀ u v : ℝ, TrigPolyLe (m + l) (fun t => u * f t + v * g t) := by
    intro f g hf hg u v
    obtain ⟨a₁, b₁, h₁⟩ := hf
    obtain ⟨a₂, b₂, h₂⟩ := hg
    refine ⟨fun k => u * a₁ k + v * a₂ k, fun k => u * b₁ k + v * b₂ k, fun t => ?_⟩
    simp only [h₁ t, h₂ t, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hcosg : ∀ r : ℕ, r ≤ m + l →
      TrigPolyLe (m + l) (fun t => Real.cos ((r : ℝ) * t)) := by
    intro r hr
    refine ⟨fun k => if k = r then (1 : ℝ) else 0, fun _ => 0, fun t => ?_⟩
    rw [Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr (by omega))
      (fun k _ hk => by simp [hk])]
    simp
  have hsing : ∀ r : ℕ, r ≤ m + l →
      TrigPolyLe (m + l) (fun t => Real.sin ((r : ℝ) * t)) := by
    intro r hr
    refine ⟨fun _ => 0, fun k => if k = r then (1 : ℝ) else 0, fun t => ?_⟩
    rw [Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr (by omega))
      (fun k _ hk => by simp [hk])]
    simp
  have hzero : TrigPolyLe (m + l) (fun _ => (0 : ℝ)) :=
    ⟨fun _ => 0, fun _ => 0, by simp⟩
  have hsum : ∀ {ι : Type} (s : Finset ι) (F : ι → ℝ → ℝ),
      (∀ i ∈ s, TrigPolyLe (m + l) (F i)) →
      TrigPolyLe (m + l) (fun t => ∑ i ∈ s, F i t) := by
    intro ι s
    classical
    induction s using Finset.induction_on with
    | empty => intro F _; exact htr _ _ hzero (by simp)
    | insert i s hi ih =>
      intro F hF
      refine htr _ _ (hlc _ _ (hF i (Finset.mem_insert_self i s))
        (ih F fun j hj => hF j (Finset.mem_insert_of_mem hj)) 1 1) (fun t => ?_)
      rw [Finset.sum_insert hi]
      ring
  have hcc : ∀ A B : ℝ,
      Real.cos A * Real.cos B = (Real.cos (A + B) + Real.cos (A - B)) / 2 := by
    intro A B
    have h1 := Real.cos_add A B
    have h2 := Real.cos_sub A B
    linarith
  have hss : ∀ A B : ℝ,
      Real.sin A * Real.sin B = (Real.cos (A - B) - Real.cos (A + B)) / 2 := by
    intro A B
    have h1 := Real.cos_add A B
    have h2 := Real.cos_sub A B
    linarith
  have hsc : ∀ A B : ℝ,
      Real.sin A * Real.cos B = (Real.sin (A + B) + Real.sin (A - B)) / 2 := by
    intro A B
    have h1 := Real.sin_add A B
    have h2 := Real.sin_sub A B
    linarith
  have hcs : ∀ A B : ℝ,
      Real.cos A * Real.sin B = (Real.sin (A + B) - Real.sin (A - B)) / 2 := by
    intro A B
    have h1 := Real.sin_add A B
    have h2 := Real.sin_sub A B
    linarith
  have hterm : ∀ k : ℕ, k ≤ m → ∀ j : ℕ, j ≤ l →
      TrigPolyLe (m + l) (fun t =>
        (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t)) *
        (c j * Real.cos ((j : ℝ) * t) + d j * Real.sin ((j : ℝ) * t))) := by
    intro k hk j hj
    have hr : k + j ≤ m + l := by omega
    have hG1 := hcosg (k + j) hr
    have hG3 := hsing (k + j) hr
    have esum : ∀ t : ℝ, (k : ℝ) * t + (j : ℝ) * t = ((k + j : ℕ) : ℝ) * t := by
      intro t
      push_cast
      ring
    rcases le_total j k with hle | hle
    · have hs : k - j ≤ m + l := by omega
      have ediff : ∀ t : ℝ, (k : ℝ) * t - (j : ℝ) * t = ((k - j : ℕ) : ℝ) * t := by
        intro t
        have hcast : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        ring
      refine htr _ _ (hlc _ _
        (hlc _ _ hG1 (hcosg (k - j) hs) ((a k * c j - b k * d j) / 2)
          ((a k * c j + b k * d j) / 2))
        (hlc _ _ hG3 (hsing (k - j) hs) ((a k * d j + b k * c j) / 2)
          ((b k * c j - a k * d j) / 2)) 1 1) (fun t => ?_)
      have P1 := hcc ((k : ℝ) * t) ((j : ℝ) * t)
      have P2 := hcs ((k : ℝ) * t) ((j : ℝ) * t)
      have P3 := hsc ((k : ℝ) * t) ((j : ℝ) * t)
      have P4 := hss ((k : ℝ) * t) ((j : ℝ) * t)
      simp only [esum t, ediff t] at P1 P2 P3 P4
      linear_combination (a k * c j) * P1 + (a k * d j) * P2 + (b k * c j) * P3 +
        (b k * d j) * P4
    · have hs : j - k ≤ m + l := by omega
      have ediff : ∀ t : ℝ, (k : ℝ) * t - (j : ℝ) * t = -(((j - k : ℕ) : ℝ) * t) := by
        intro t
        have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        ring
      refine htr _ _ (hlc _ _
        (hlc _ _ hG1 (hcosg (j - k) hs) ((a k * c j - b k * d j) / 2)
          ((a k * c j + b k * d j) / 2))
        (hlc _ _ hG3 (hsing (j - k) hs) ((a k * d j + b k * c j) / 2)
          ((a k * d j - b k * c j) / 2)) 1 1) (fun t => ?_)
      have P1 := hcc ((k : ℝ) * t) ((j : ℝ) * t)
      have P2 := hcs ((k : ℝ) * t) ((j : ℝ) * t)
      have P3 := hsc ((k : ℝ) * t) ((j : ℝ) * t)
      have P4 := hss ((k : ℝ) * t) ((j : ℝ) * t)
      simp only [esum t, ediff t, Real.cos_neg, Real.sin_neg] at P1 P2 P3 P4
      linear_combination (a k * c j) * P1 + (a k * d j) * P2 + (b k * c j) * P3 +
        (b k * d j) * P4
  refine htr _ _ (hsum (Finset.range (m + 1))
    (fun k t => ∑ j ∈ Finset.range (l + 1),
      (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t)) *
      (c j * Real.cos ((j : ℝ) * t) + d j * Real.sin ((j : ℝ) * t)))
    (fun k hk => hsum (Finset.range (l + 1))
      (fun j t => (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t)) *
        (c j * Real.cos ((j : ℝ) * t) + d j * Real.sin ((j : ℝ) * t)))
      (fun j hj => hterm k (by have := Finset.mem_range.mp hk; omega) j
        (by have := Finset.mem_range.mp hj; omega)))) (fun t => ?_)
  rw [hS' t, hT' t, Finset.sum_mul_sum]
