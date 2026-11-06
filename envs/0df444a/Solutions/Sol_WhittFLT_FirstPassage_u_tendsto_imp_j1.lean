-- Prove2me | solution 1 for WhittFLT.FirstPassage.u_tendsto_imp_j1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:38:23.015787+00:00
-- url     : https://prove2.me/submissions/af65d0bb-fcd5-4ce0-8f8b-744f09eca3ab

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD



open Set Filter Topology

theorem solution (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, WhittFLT.Composition.IsCadlagOn (Ici 0) (xs n)) (hx : WhittFLT.Composition.IsCadlagOn (Ici 0) x)
    (h : WhittFLT.Composition.UTendsto (Ici 0) xs x) : WhittFLT.Composition.J1Tendsto (Ici 0) xs x := by
  refine ⟨hxs, hx, fun a b _ hab _ _ => ?_⟩
  have hid : WhittFLT.Composition.IsTimeChange a b id :=
    ⟨strictMono_id.strictMonoOn _, continuousOn_id, image_id _⟩
  have h0 : WhittFLT.Composition.supDist a b (id : ℝ → ℝ) id = 0 := by
    simp [WhittFLT.Composition.supDist]
  have hle : ∀ n, WhittFLT.Composition.j1Dist a b (xs n) x ≤
      WhittFLT.Composition.supDist a b (xs n) x := by
    intro n
    refine (iInf₂_le (id : ℝ → ℝ) hid).trans ?_
    rw [h0]
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h a b hab)
    (fun n => zero_le) hle

