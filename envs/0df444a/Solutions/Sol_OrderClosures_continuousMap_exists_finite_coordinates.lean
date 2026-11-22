-- Prove2me | solution 1 for OrderClosures.continuousMap_exists_finite_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:09.177726+00:00
-- url     : https://prove2.me/submissions/cddfe5c6-09c8-43f7-b06a-aa9836631399

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_Positive_continuous


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    {I : Type u} {K : Set (I → Bool)} (f : C(K, ℝ)) (x : K)
    {V : Set ℝ} (hV : IsOpen V) (hxV : f x ∈ V) :
    ∃ F : Finset I, ∀ y : K, (∀ i ∈ F, y.1 i = x.1 i) → f y ∈ V := by
  have hopen : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  rcases isOpen_induced_iff.mp hopen with ⟨W, hW, hWeq⟩
  have hxW : x.1 ∈ W := by
    have : x ∈ f ⁻¹' V := hxV
    rw [← hWeq] at this
    exact this
  rcases isOpen_pi_iff.mp hW x.1 hxW with ⟨F, v, hv, hvW⟩
  refine ⟨F, fun y hy ↦ ?_⟩
  have hyv : y.1 ∈ (F : Set I).pi v := by
    intro i hi
    rw [hy i (Finset.mem_coe.mp hi)]
    exact (hv i (Finset.mem_coe.mp hi)).2
  have hyW := hvW hyv
  have : y ∈ Subtype.val ⁻¹' W := hyW
  rw [hWeq] at this
  exact this
end OrderClosures
