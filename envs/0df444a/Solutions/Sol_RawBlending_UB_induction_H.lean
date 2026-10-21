-- Prove2me | solution 1 for RawBlending.UB.induction_H
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:54:58.197002+00:00
-- url     : https://prove2.me/submissions/f7c22225-4070-4244-95c6-0068169211f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RawBlending_UB_Model
import Theorems.Thm_RawBlending_UB_lemma_3_d

open Filter

namespace RawBlending.UB

theorem H_terminal (d : Data) (hd : d.Standing) : H d d.T := by
  obtain ⟨_, _, _, _, hc⟩ := hd
  obtain ⟨hc1, hc2⟩ := hc (d.T + 1) (by omega) le_rfl
  have hV : V d (d.T + 1) = fun w : Vec => d.c1 (d.T+1) * w.1 + d.c2 (d.T+1) * w.2 := by
    funext w; simp [V, Vtg, boundary]
  rw [H, hV]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨convex_Ici (0 : Vec), fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  · exact (by fun_prop : Continuous (fun w : Vec => d.c1 (d.T+1) * w.1 + d.c2 (d.T+1) * w.2)).continuousOn
  · intro x _ y _
    have e1 : (x ⊔ y).1 + (x ⊓ y).1 = x.1 + y.1 := by
      simp only [Prod.fst_sup, Prod.fst_inf]; exact max_add_min x.1 y.1
    have e2 : (x ⊔ y).2 + (x ⊓ y).2 = x.2 + y.2 := by
      simp only [Prod.snd_sup, Prod.snd_inf]; exact max_add_min x.2 y.2
    linear_combination (-(d.c1 (d.T+1))) * e1 - d.c2 (d.T+1) * e2
  · intro ε hε v hv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [le_div_iff₀ hs]
    nlinarith [mul_nonneg hc2 hv]
  · intro ε hε v hv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [le_div_iff₀ hs]
    nlinarith [mul_nonneg hc1 hv]

end RawBlending.UB

open RawBlending.UB in
theorem solution (d : Data) (hd : d.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ d.T → H d t := by
  have key : ∀ k : ℕ, k < d.T → H d (d.T - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using H_terminal d hd
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := lemma_3_d d hd (d.T - k) (by omega) (by omega) h1
      have e : d.T - k - 1 = d.T - (k + 1) := by omega
      rwa [e] at h2
  intro t ht htT
  have := key (d.T - t) (by omega)
  have e : d.T - (d.T - t) = t := by omega
  rwa [e] at this
