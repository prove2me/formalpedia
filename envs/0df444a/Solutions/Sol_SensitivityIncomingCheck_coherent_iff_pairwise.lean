-- Prove2me | solution 1 for SensitivityIncomingCheck.coherent_iff_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @jennyuxi
-- created : 2026-11-12T23:38:58.333467+00:00
-- url     : https://prove2.me/submissions/d093131c-de02-4bc1-baf1-d51f55498499

import Lean
set_option autoImplicit false

/-- Eliminating color enumeration from a finite coherence check. -/
theorem solution {V : Type} (vertices : List V)
    (adj : V → V → Bool) (label : V → V → Fin 2) :
    (vertices.all fun j => vertices.all fun i => vertices.all fun k =>
      decide (adj i j = true → adj k j = true → label i j = label k j)) = true ↔
    ∃ colors : V → Fin 2,
      ∀ i, i ∈ vertices → ∀ j, j ∈ vertices →
        adj i j = true → label i j = colors j := by
  classical
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    let colors : V → Fin 2 := fun j =>
      if hj : ∃ i, i ∈ vertices ∧ adj i j = true then
        label (Classical.choose hj) j
      else 0
    refine ⟨colors, ?_⟩
    intro i hi j hj hij
    have he : ∃ k, k ∈ vertices ∧ adj k j = true := ⟨i, hi, hij⟩
    dsimp [colors]
    rw [dif_pos he]
    exact h j hj i hi (Classical.choose he) (Classical.choose_spec he).1
      hij (Classical.choose_spec he).2
  · rintro ⟨colors, hc⟩ j hj i hi k hk hij hkj
    exact (hc i hi j hj hij).trans (hc k hk j hj hkj).symm
