-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_deterministic_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:04:20.028774+00:00
-- url     : https://prove2.me/submissions/7a4a0776-7ab3-4183-9dc1-62f502a538fa

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_segment_nonzero
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_specialization
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_partial_boundary_values
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 3 ≤ d) : ∀ q : ℕ, 2 ≤ q → ∀ (V : Type) [Fintype V]
    (G : SimpleGraph V), (∀ v, G.degree v ≤ d) → ∀ β : ℂ,
    ‖β - 1‖ < 0.35 / (d : ℝ) → pottsZ q G β ≠ 0 := by
  classical
  intro q hq V _ G hG β hβ
  let W := fun (_ : Sym2 V) (i j : Fin q) => if i=j then β else 1
  have hW : ∀ e i j, W e i j = W e j i := by intro e i j; simp [W,eq_comm]
  have hseg : ∀ e ∈ G.edgeFinset, ∀ i j, ∃ t : ℝ, t ∈ Icc 0 1 ∧ W e i j = 1+(t:ℂ)*(β-1) := by
    intro e he i j
    by_cases hij : i=j
    · refine ⟨1,by norm_num,?_⟩
      simp [W,hij]
    · refine ⟨0,by norm_num,?_⟩
      simp [W,hij]
  let τ : V → Fin q := fun _ => ⟨0,by omega⟩
  have hh := potts_weighted_segment_nonzero d q hd hq V G hG β hβ W hW hseg ∅ τ
  have hs := potts_weighted_specialization q G β ∅ τ
  have hb := (potts_partial_boundary_values q G β τ).1
  rw [hs,hb] at hh
  exact hh
