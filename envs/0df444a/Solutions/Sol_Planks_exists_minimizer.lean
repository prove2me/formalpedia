-- Prove2me | solution 1 for Planks.exists_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:37:48.200999+00:00
-- url     : https://prove2.me/submissions/d4c2f81b-bc7a-45d1-b6b7-2b09c16b5ed9

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
namespace Planks
theorem _root_.solution (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ y ∈ admissible ℓ, IsMinOn (objF ℓ) (admissible ℓ) y ∧
      objF ℓ y ≤ Fintype.card ι := by
  have hxS : x ∈ admissible ℓ := ⟨hx, fun i => by
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    rw [h i]; nlinarith⟩
  have hcl : IsClosed (admissible ℓ) := by
    have : admissible ℓ = (⋂ a, ⋂ b, {y : ι → E | inner ℝ (y a) (y b) = if a = b then 1 else 0}) ∩
        ⋂ i, {y : ι → E | 1 ≤ 2 * (Fintype.card ι : ℝ) * (ℓ i (y i)) ^ 2} := by
      ext y; simp [admissible, orthonormal_iff_ite]
    rw [this]
    exact IsClosed.inter (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (by fun_prop) continuous_const)
      (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop))
  have hbdd : Bornology.IsBounded (admissible ℓ) := by
    refine (Metric.isBounded_closedBall (x := (0 : ι → E)) (r := 1)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hy.1.1 i).le
  have hcpt : IsCompact (admissible ℓ) := Metric.isCompact_of_isClosed_isBounded hcl hbdd
  have hcont : ContinuousOn (objF ℓ) (admissible ℓ) := by
    unfold objF
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_) 2
    intro h0
    have := hy.2 i
    rw [h0] at this
    norm_num at this
  obtain ⟨y, hy, hmin⟩ := hcpt.exists_isMinOn ⟨x, hxS⟩ hcont
  refine ⟨y, hy, hmin, ?_⟩
  calc objF ℓ y ≤ objF ℓ x := hmin hxS
    _ = Fintype.card ι := by simp [objF, h]
end Planks
