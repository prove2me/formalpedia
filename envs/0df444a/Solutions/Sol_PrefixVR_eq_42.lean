-- Prove2me | solution 1 for PrefixVR.eq_42
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:10:19.078012+00:00
-- url     : https://prove2.me/submissions/54687731-c0ee-4b2c-82e0-79d1dacf7c35

import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped InnerProductSpace

private lemma scalar_remainder (g g' : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (g' t) t)
    (hbound : ∀ t, 0 ≤ t → |g' t - g' 0| ≤ L * t) :
    |g 1 - g 0 - g' 0| ≤ L / 2 := by
  let u : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 - L / 2 * t ^ 2
  let l : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 + L / 2 * t ^ 2
  have hu (t : ℝ) : HasDerivAt u (g' t - g' 0 - L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [u, id]) <;> ring
  have hl (t : ℝ) : HasDerivAt l (g' t - g' 0 + L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).add
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [l, id]) <;> ring
  have hanti : AntitoneOn u (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hu t).continuousAt.continuousWithinAt)
      (fun t _ => (hu t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hu t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).2
    linarith
  have hmono : MonotoneOn l (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hl t).continuousAt.continuousWithinAt)
      (fun t _ => (hl t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hl t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).1
    linarith
  have hu01 := hanti (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  have hl01 := hmono (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  dsimp [u, l] at hu01 hl01
  apply abs_le.mpr
  constructor <;> linarith

private lemma smooth_upper {d : ℕ}
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (gradh : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hh : ConvexOptAlg.SmoothGD.IsBetaSmooth h gradh L)
    (x s : EuclideanSpace ℝ (Fin d)) : h s - h x - ⟪gradh x, s - x⟫_ℝ ≤ L / 2 * ‖s - x‖ ^ 2 := by
  let d := s - x
  let f : ℝ → ℝ := fun t => h (x + t • d)
  let f' : ℝ → ℝ := fun t => ⟪gradh (x + t • d), d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    have hp : HasDerivAt (fun r : ℝ => x + r • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hc := (hh.2.1 (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp
    convert! hc using 1
  have hb (t : ℝ) (ht : 0 ≤ t) : |f' t - f' 0| ≤ (L * ‖d‖ ^ 2) * t := by
    have hg := hh.2.2 (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hg
    dsimp [f']
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left]
    calc
      _ ≤ ‖gradh (x + t • d) - gradh x‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * (t * ‖d‖)) * ‖d‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ = (L * ‖d‖ ^ 2) * t := by ring
  have hr := (abs_le.mp (scalar_remainder f f' (L * ‖d‖ ^ 2) hd hb)).2
  simpa [f, f', d, mul_div_assoc, div_mul_eq_mul_div] using hr


theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f G Lf) (x v : EuclideanSpace ℝ (Fin d)) (η : ℝ) :
    f (x - η • v) ≤ f x - η / 2 * ‖G x‖ ^ 2 - η / 2 * (1 - Lf * η) * ‖v‖ ^ 2
      + η / 2 * ‖v - G x‖ ^ 2 := by
  have hu := smooth_upper f G Lf hf x (x - η • v)
  have hinner : ⟪G x, x - η • v - x⟫_ℝ = -η * ⟪G x,v⟫_ℝ := by
    have he : x - η • v - x = -η • v := by module
    rw [he, real_inner_smul_right]
  have hn : ‖x - η • v - x‖^2 = η^2 * ‖v‖^2 := by
    have he : x - η • v - x = -η • v := by module
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  rw [hinner, hn] at hu
  have hp : ‖v-G x‖^2 = ‖G x‖^2+‖v‖^2-2*⟪G x,v⟫_ℝ := by
    rw [norm_sub_sq_real, real_inner_comm v (G x)]
    ring
  rw [hp]
  nlinarith

#print axioms solution