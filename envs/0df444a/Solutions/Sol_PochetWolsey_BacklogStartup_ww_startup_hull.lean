-- Prove2me | solution 1 for PochetWolsey.BacklogStartup.ww_startup_hull
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:01:44.207351+00:00
-- url     : https://prove2.me/submissions/06b417b1-3796-4517-8909-ed9d2814c1fb

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel
open PochetWolsey.BacklogStartup

theorem solution : ¬ (∀ {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t),
    convexHull ℝ (WWStartup y0 d) = PrintedStartupHull y0 d) := by
  intro h
  have e := h (n := 1) 1 (Or.inr rfl) one_pos (fun _ => 0) (fun _ => le_rfl)
  let p : StartupPoint 1 := (fun _ => 0, fun _ => 0, fun _ => -1)
  have hmem : p ∈ PrintedStartupHull (1:ℝ) (fun _ : Fin 1 => (0:ℝ)) := by
    refine ⟨fun _ => le_rfl, fun _ => ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_Icc] at ht
      obtain rfl : t = 1 := by omega
      simp [p, period, setupState]
    · intro k hk l hl
      simp [startupStockRHS, period, stock, p]
  rw [← e] at hmem
  have hconv : convexHull ℝ (WWStartup (1:ℝ) (fun _ : Fin 1 => (0:ℝ))) ⊆
      {q : StartupPoint 1 | ∀ t, 0 ≤ q.2.2 t} := by
    apply convexHull_min
    · intro q hq t; rcases hq.2.2.1 t with h | h <;> simp [h]
    · intro a ha b hb μ ν hμ hν _ t
      simp only [Set.mem_setOf_eq, Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at *
      have := ha t; have := hb t; positivity
  have := hconv hmem 0
  simp only [p] at this
  norm_num at this
