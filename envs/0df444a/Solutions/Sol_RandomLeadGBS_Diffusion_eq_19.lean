-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:10:53.439808+00:00
-- url     : https://prove2.me/submissions/d84b76f2-8bc2-4f88-9239-e4d667be9a7d

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

open RandomLeadGBS.Diffusion

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hr : 0 < r)
    (p : ℤ → ℝ) (hp : IsArtStationary P r p) :
    Summable (fun j : ℤ => p j * (artZ P r j : ℝ)) ∧
    P.β * ∑' j : ℤ, p j * (artZ P r j : ℝ) = r := by
  obtain ⟨hβ, -, -, -, -⟩ := hP
  obtain ⟨_hnn, hsum, hone, hsumx, hbal⟩ := hp
  set Z : ℤ → ℝ := fun j => (artZ P r j : ℝ) with hZ
  -- a j : up-flux, b j : down-flux
  set a : ℤ → ℝ := fun j => p j * (P.β * Z j) with ha
  set b : ℤ → ℝ := fun j => p j * r with hb
  have hsa : Summable a := by
    have : a = fun j => p j * artExitRate P r j - p j * r := by
      funext j; simp only [ha, artExitRate, hZ]; ring
    rw [this]; exact hsumx.sub (hsum.mul_right r)
  have hsZ : Summable (fun j : ℤ => p j * Z j) := by
    have : (fun j : ℤ => p j * Z j) = fun j => a j / P.β := by
      funext j; simp only [ha]; field_simp
    rw [this]; exact hsa.div_const _
  -- balance equation in flux form
  have hbal' : ∀ j' : ℤ, b (j' + 1) + a (j' - 1) = b j' + a j' := by
    intro j'
    have h := hbal j'
    have hfun : (fun j => p j * artRate P r j j') =
        fun j => (if j = j' + 1 then b (j' + 1) else 0) + (if j = j' - 1 then a (j' - 1) else 0) := by
      funext j
      simp only [artRate, mul_add]
      congr 1
      · by_cases h1 : j = j' + 1
        · subst h1; simp [hb]
        · have : ¬ j' = j - 1 := by omega
          simp [h1, this]
      · by_cases h1 : j = j' - 1
        · subst h1; simp [ha, hZ]
        · have : ¬ j' = j + 1 := by omega
          simp [h1, this]
    rw [hfun, Summable.tsum_add (summable_of_ne_finset_zero (s := {j' + 1}) (by intro j hj; simp_all))
      (summable_of_ne_finset_zero (s := {j' - 1}) (by intro j hj; simp_all)),
      tsum_ite_eq, tsum_ite_eq] at h
    rw [h]; simp only [ha, hb, artExitRate, hZ]; ring
  -- φ j = a j - b (j+1) is constant
  set φ : ℤ → ℝ := fun j => a j - b (j + 1) with hφ
  have hstep : ∀ j : ℤ, φ j = φ (j - 1) := by
    intro j
    have := hbal' j
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ j : ℤ, φ j = φ 0 := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hsb1 : Summable (fun j : ℤ => b (j + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsum.mul_right r)
  have hsφ : Summable φ := hsa.sub hsb1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ j, a j = b (j + 1) := by
    intro j; have := hconst j; rw [hφ0] at this; simp only [hφ] at this; linarith
  refine ⟨hsZ, ?_⟩
  rw [← tsum_mul_left]
  have : (fun j => P.β * (p j * Z j)) = fun j => b (j + 1) := by
    funext j; rw [← hab j]; simp only [ha]; ring
  rw [this]
  have h1 : ∑' j : ℤ, b (j + 1) = ∑' j : ℤ, b j :=
    (Equiv.addRight (1 : ℤ)).tsum_eq b
  rw [h1]; simp only [hb]; rw [tsum_mul_right, hone, one_mul]
