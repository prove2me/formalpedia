-- Prove2me | solution 1 for PochetWolsey.Mixing.mixing_cuts_valid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:19:17.143223+00:00
-- url     : https://prove2.me/submissions/1c9bae47-ec19-466b-8a94-335363f0927a

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Cuts

open PochetWolsey.Mixing

theorem mix_aux_chain (t : ℕ) (g : ℕ → ℝ) (hmono : ∀ j < t, g j ≤ g (j + 1)) :
    ∀ j ≤ t, g j ≤ g t := by
  have key : ∀ j m, j + m ≤ t → g j ≤ g (j + m) := by
    intro j m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro h
      have := hmono (j + m) (by omega)
      have := ih (by omega)
      rw [← add_assoc]; linarith
  intro j hj
  have := key j (t - j) (by omega)
  rwa [show j + (t - j) = t by omega] at this

theorem mix_aux (g : ℕ → ℝ) (z : ℕ → ℤ) (hg0 : 0 ≤ g 0) (ζ : ℤ) :
    ∀ t : ℕ, (∀ j < t, g j ≤ g (j + 1)) → (∀ j ≤ t, z j ≤ ζ) →
    (g 0 * ((z 0 : ℝ) + 1) + ∑ j ∈ Finset.range t, (g (j + 1) - g j) * ((z (j + 1) : ℝ) + 1)
        ≤ ζ * g t ∨
      ∃ j ≤ t, z j = ζ ∧
        g 0 * ((z 0 : ℝ) + 1) + ∑ j ∈ Finset.range t, (g (j + 1) - g j) * ((z (j + 1) : ℝ) + 1)
          ≤ ζ * g t + g j) := by
  intro t
  induction t with
  | zero =>
    intro _ hz
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    rcases eq_or_lt_of_le (hz 0 le_rfl) with h | h
    · right; refine ⟨0, le_rfl, h, ?_⟩; rw [h]; nlinarith
    · left
      have : (z 0 : ℝ) + 1 ≤ ζ := by exact_mod_cast h
      nlinarith
  | succ t ih =>
    intro hmono hz
    have hgt : g t ≤ g (t + 1) := hmono t (by omega)
    have hch := mix_aux_chain t g (fun j hj => hmono j (by omega))
    have hgt0 : 0 ≤ g t := le_trans hg0 (hch 0 (by omega))
    rw [Finset.sum_range_succ]
    set A := g 0 * ((z 0 : ℝ) + 1) + ∑ j ∈ Finset.range t, (g (j + 1) - g j) * ((z (j + 1) : ℝ) + 1)
    have ih' := ih (fun j hj => hmono j (by omega)) (fun j hj => hz j (by omega))
    have hd : 0 ≤ g (t + 1) - g t := by linarith
    rcases eq_or_lt_of_le (hz (t + 1) le_rfl) with h | h
    · right
      refine ⟨t + 1, le_rfl, h, ?_⟩
      rw [h]
      rcases ih' with h1 | ⟨j, hj, _, h1⟩
      · nlinarith
      · have := hch j hj; nlinarith
    · have h' : (z (t + 1) : ℝ) + 1 ≤ ζ := by exact_mod_cast h
      have hb : (g (t + 1) - g t) * ((z (t + 1) : ℝ) + 1) ≤ (g (t + 1) - g t) * ζ :=
        mul_le_mul_of_nonneg_left h' hd
      rcases ih' with h1 | ⟨j, hj, hj2, h1⟩
      · left; nlinarith
      · right; exact ⟨j, by omega, hj2, by nlinarith⟩

theorem solution {K t : ℕ} (b : Fin K → ℝ)
    (i : Fin (t + 1) → Fin K) (hi : Function.Injective i)
    (horder : Monotone (fun j => frac (b (i j)))) :
    ∀ p ∈ mixingSet b, cutRhs b i p.2 ≤ p.1 ∧ wrapCutRhs b i p.2 ≤ p.1 := by
  rintro ⟨s, y⟩ ⟨hs, hint, hcov⟩
  simp only at hs hint hcov ⊢
  choose w hw using hint
  let idx : ℕ → Fin (t + 1) := fun n => ⟨min n t, by omega⟩
  let g : ℕ → ℝ := fun n => frac (b (i (idx n)))
  let z : ℕ → ℤ := fun n => ⌊b (i (idx n))⌋ - w (i (idx n))
  have hfrac0 : ∀ a : ℝ, 0 ≤ frac a := fun a => by unfold frac; linarith [Int.floor_le a]
  have hfrac1 : ∀ a : ℝ, frac a < 1 := fun a => by unfold frac; linarith [Int.lt_floor_add_one a]
  have hzr : ∀ n, ((z n : ℤ) : ℝ) = (⌊b (i (idx n))⌋ : ℝ) - y (i (idx n)) := by
    intro n; simp only [z]; push_cast; rw [hw]
  have hsz : ∀ n, g n + z n ≤ s := by
    intro n
    rw [hzr]
    have := hcov (i (idx n))
    simp only [g, frac]; linarith
  have hg0 : 0 ≤ g 0 := hfrac0 _
  have hgt1 : g t < 1 := hfrac1 _
  have hmono : ∀ j < t, g j ≤ g (j + 1) := by
    intro j hj
    apply horder
    rw [Fin.le_def]; simp only [idx]; omega
  have hidx0 : idx 0 = 0 := by ext; simp [idx]
  have hidxt : idx t = Fin.last t := by ext; simp [idx]
  have hcut : cutRhs b i y = g 0 * ((z 0 : ℝ) + 1) +
      ∑ j ∈ Finset.range t, (g (j + 1) - g j) * ((z (j + 1) : ℝ) + 1) := by
    unfold cutRhs
    rw [← Fin.sum_univ_eq_sum_range (fun j => (g (j + 1) - g j) * ((z (j + 1) : ℝ) + 1)) t]
    congr 1
    · rw [hzr]; simp only [g]; rw [hidx0]; ring
    · apply Finset.sum_congr rfl
      intro j _
      have e1 : idx (j + 1) = j.succ := by ext; simp [idx]
      have e2 : idx j = j.castSucc := by ext; simp [idx]
      rw [hzr]; simp only [g]; rw [e1, e2]; ring
  have hwrap : wrapCutRhs b i y = cutRhs b i y + (1 - g t) * (z 0 : ℝ) := by
    unfold wrapCutRhs
    rw [hzr]; simp only [g]; rw [hidx0, hidxt]
  rw [hwrap, hcut]
  have hch := mix_aux_chain t g hmono
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.range (t + 1)) z ⟨0, by simp⟩
  rw [Finset.mem_range] at hj0
  have hz0le : (z 0 : ℝ) ≤ z j0 := by exact_mod_cast hmax 0 (by simp)
  by_cases hpos : 0 ≤ z j0
  · have H := mix_aux g z hg0 (z j0) t hmono (fun j hj => hmax j (by simp; omega))
    have hs0 := hsz j0
    have hzp : (0 : ℝ) ≤ z j0 := by exact_mod_cast hpos
    have hgt0 : 0 ≤ g t := le_trans hg0 (hch 0 (by omega))
    rcases H with h1 | ⟨j, hj, hj2, h1⟩
    · have := hg0; have := hfrac0 (b (i (idx j0)))
      constructor <;> nlinarith
    · have := hsz j
      rw [hj2] at this
      constructor <;> nlinarith
  · push Not at hpos
    have hneg : z j0 ≤ -1 := by omega
    have H := mix_aux g z hg0 (-1) t hmono (fun j hj => le_trans (hmax j (by simp; omega)) hneg)
    have hz0' : (z 0 : ℝ) ≤ -1 := by
      have : z 0 ≤ -1 := le_trans (hmax 0 (by simp)) hneg
      exact_mod_cast this
    have hgt0 : 0 ≤ g t := le_trans hg0 (hch 0 (by omega))
    push_cast at H
    rcases H with h1 | ⟨j, hj, _, h1⟩
    · constructor <;> nlinarith
    · have := hch j hj
      constructor <;> nlinarith
