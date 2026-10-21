-- Prove2me | solution 1 for RawBlending.UB.lemma_3_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:54:04.183683+00:00
-- url     : https://prove2.me/submissions/8bbc979d-b52e-4965-8554-c1ed8e95f4d8

import Mathlib
import Definitions.Def_RawBlending_UB_Model

open Filter

namespace RawBlending.UB

/-- Shape is preserved by adding a linear function. -/
theorem shape_add_linear (k1 k2 : ℝ) (f : Vec → ℝ) (hf : Shape f) :
    Shape (fun w : Vec => k1 * w.1 + k2 * w.2 + f w) := by
  obtain ⟨hc, hcont, hsm⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · have hconv : Convex ℝ orthant := convex_Ici (0 : Vec)
    have hlin : ConvexOn ℝ orthant (fun w : Vec => k1 * w.1 + k2 * w.2) := by
      refine ⟨hconv, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      ring
    exact hlin.add hc
  · have : Continuous (fun w : Vec => k1 * w.1 + k2 * w.2) := by fun_prop
    exact this.continuousOn.add hcont
  · intro x hx y hy
    have h := hsm hx hy
    have e1 : (x ⊔ y).1 + (x ⊓ y).1 = x.1 + y.1 := by
      simp only [Prod.fst_sup, Prod.fst_inf]; exact max_add_min x.1 y.1
    have e2 : (x ⊔ y).2 + (x ⊓ y).2 = x.2 + y.2 := by
      simp only [Prod.snd_sup, Prod.snd_inf]; exact max_add_min x.2 y.2
    beta_reduce
    linear_combination h - k1 * e1 - k2 * e2

end RawBlending.UB

open RawBlending.UB in
theorem solution (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) : IsJClass (J d t) := by
  obtain ⟨_, ha1, ha12, hper, _⟩ := hd
  obtain ⟨hσ, he, hh1, hh2, _⟩ := hper t ht htT
  obtain ⟨hshape, hg1, hg2⟩ := hH
  have hp : 0 < p d t := by unfold p; linarith
  set k1 := d.a1 * p d t + d.h1 t - d.c1 (t+1) with hk1
  set k2 := d.a2 * p d t + d.h2 t - d.c2 (t+1) with hk2
  have hJ : J d t = fun w : Vec => k1 * w.1 + k2 * w.2 + V d (t+1) w := by
    funext w; simp [J, Jstep, hk1, hk2]
  rw [hJ]
  refine ⟨shape_add_linear k1 k2 _ hshape, ?_, ?_⟩
  · intro v hv
    have hε : 0 < d.a1 * p d t / 2 := by positivity
    have hev := hg1 _ hε v hv
    have hlim : Tendsto (fun s : ℝ => d.a1 * p d t / 2 * s + k2 * v) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hε tendsto_id)
    refine tendsto_atTop_mono' _ ?_ hlim
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with s hs hs0
    rw [le_div_iff₀ hs0] at hs
    nlinarith
  · intro v hv
    have hε : 0 < d.a2 * p d t / 2 := by
      have : 0 < d.a2 := by linarith
      positivity
    have hev := hg2 _ hε v hv
    have hlim : Tendsto (fun s : ℝ => d.a2 * p d t / 2 * s + k1 * v) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hε tendsto_id)
    refine tendsto_atTop_mono' _ ?_ hlim
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with s hs hs0
    rw [le_div_iff₀ hs0] at hs
    nlinarith
