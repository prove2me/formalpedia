-- Prove2me | solution 1 for UnphysicalHilbert.prop20_domain_not_complete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:46:15.268488+00:00
-- url     : https://prove2.me/submissions/c0c21bf8-9c16-4712-86d5-05cffc006dcb

import Mathlib

namespace UHAux

lemma bounded_of_complete
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed) (hc : CompleteSpace X.domain) :
    ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖ := by
  set f : X.domain →ₗ[ℂ] Y := X.toFun
  have hg : (f.graph : Set (X.domain × Y)) =
      (fun p : X.domain × Y => ((p.1 : H), p.2)) ⁻¹' (X.graph : Set (H × Y)) := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage]
    rw [LinearPMap.mem_graph_iff]
    constructor
    · intro h; exact ⟨p.1, rfl, h.symm⟩
    · rintro ⟨y, hy, h⟩
      have : y = p.1 := Subtype.ext hy
      subst this; exact h.symm
  have hcl : IsClosed (f.graph : Set (X.domain × Y)) := by
    rw [hg]
    exact hX.preimage (by fun_prop)
  have hcont := f.continuous_of_isClosed_graph hcl
  set F : X.domain →L[ℂ] Y := ⟨f, hcont⟩
  refine ⟨‖F‖, fun x => ?_⟩
  have := F.le_opNorm x
  exact this

end UHAux

open UHAux in
theorem solution
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed)
    (hunb : ¬ ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖) :
    ¬ CompleteSpace X.domain := fun hc => hunb (bounded_of_complete X hX hc)
