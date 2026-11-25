-- Prove2me | solution 1 for PlankProblem.ne_of_mem_interior_of_subset_halfspace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:26.617926+00:00
-- url     : https://prove2.me/submissions/6a7bd462-b1e4-4412-a937-644218af6f40

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution {A : Set Rn} {f : Rn →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ}
    (hA : A ⊆ {x | c ≤ f x}) {x : Rn} (hx : x ∈ interior A) : f x ≠ c := by
  intro hfx
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  have hnhds : A ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  have ht : Filter.Tendsto (fun t : ℝ => x + (t * -(f u)⁻¹) • u) (nhds 0) (nhds x) := by
    have : Continuous (fun t : ℝ => x + (t * -(f u)⁻¹) • u) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), x + (t * -(f u)⁻¹) • u ∈ A :=
    (ht.eventually hnhds).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htA, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have := hA htA
  simp only [mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at this
  rw [hfx] at this
  have : t * -(f u)⁻¹ * f u = -t := by field_simp
  have htp : (0 : ℝ) < t := htpos
  linarith
end PlankProblem
