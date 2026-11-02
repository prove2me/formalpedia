-- Prove2me | solution 1 for SpatialDemandEq.Optimal.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:36:45.798238+00:00
-- url     : https://prove2.me/submissions/221d2848-81f7-4650-af4a-196001a96968

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Theorems.Thm_SpatialDemandEq_Optimal_lemma_1_part_2

open MeasureTheory
open SpatialDemandEq.Optimal

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hcap : lam < ∑ k, μ k) (w w' : Fin K → ℝ)
    (hw : IsEqWeight ν S (distFn dst xs) c lam μ w)
    (hw' : IsEqWeight ν S (distFn dst xs) c lam μ w') : w = w' := by
  have := hS.prob
  have : Nonempty (Fin K) := ⟨⟨0, hS.K_pos⟩⟩
  have key : ∀ u v : Fin K → ℝ, IsEqWeight ν S (distFn dst xs) c lam μ u →
      IsEqWeight ν S (distFn dst xs) c lam μ v → ∀ j, u j ≤ v j := by
    intro u v hu hv
    obtain ⟨k, hk⟩ := Finite.exists_max (fun i => u i - v i)
    have hmono := lemma_1_part_2 S ν (distFn dst xs) u v k hk
    have harea : area ν (cell S (distFn dst xs) u k) ≤ area ν (cell S (distFn dst xs) v k) :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmono
    obtain ⟨hu1, hu2⟩ := hu k
    obtain ⟨hv1, hv2⟩ := hv k
    have hle : u k ≤ v k := by
      rw [hu2, hv2]
      apply div_le_div_of_nonneg_left hS.c_pos.le (by linarith)
      nlinarith [hS.lam_pos]
    intro j
    have := hk j

    linarith
  funext j
  exact le_antisymm (key w w' hw hw' j) (key w' w hw' hw j)
