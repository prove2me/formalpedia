-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.sheets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:30.082929+00:00
-- url     : https://prove2.me/submissions/18550b5b-77d1-41ff-9a54-dba12030b20d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_Sheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution : sheetsStatement.{u} := by
  intro n M _ z U u hcov w hw hfin
  obtain ⟨_, W, hwW, hW, _, H, hH⟩ := hcov w hw
  have : Finite (z ⁻¹' {w}) := hfin.to_subtype
  let e : Fin (Nat.card (z ⁻¹' {w})) ≃ (z ⁻¹' {w}) := (Finite.equivFin _).symm
  classical
  let s : Fin (Nat.card (z ⁻¹' {w})) → V n → M :=
    fun i v => if hv : v ∈ W then (H.symm (⟨v, hv⟩, e i)).1 else (e i).1
  have hs : ∀ i v (hv : v ∈ W), s i v = (H.symm (⟨v, hv⟩, e i)).1 := fun i v hv => dif_pos hv
  have hzs : ∀ i, ∀ v ∈ W, z (s i v) = v := by
    intro i v hv
    rw [hs i v hv]
    have := hH (H.symm (⟨v, hv⟩, e i))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hinj : ∀ v (hv : v ∈ W) i j, s i v = s j v → i = j := by
    intro v hv i j hij
    rw [hs i v hv, hs j v hv] at hij
    have h2 := congrArg (fun y => (H y).2)
      (Subtype.ext hij : H.symm (⟨v, hv⟩, e i) = H.symm (⟨v, hv⟩, e j))
    simp only [Homeomorph.apply_symm_apply] at h2
    exact e.injective h2
  have hsurj : ∀ v (hv : v ∈ W) (y : M), z y = v → ∃ i, s i v = y := by
    intro v hv y hy
    have hyW : y ∈ z ⁻¹' W := by
      show z y ∈ W
      rw [hy]; exact hv
    refine ⟨e.symm (H ⟨y, hyW⟩).2, ?_⟩
    rw [hs _ v hv]
    simp only [Equiv.apply_symm_apply]
    have h1 : (H ⟨y, hyW⟩).1 = ⟨v, hv⟩ := Subtype.ext (by rw [hH]; exact hy)
    have h3 : H.symm (⟨v, hv⟩, (H ⟨y, hyW⟩).2) = ⟨y, hyW⟩ := by
      rw [← h1]; simp
    rw [h3]
  refine ⟨W, Nat.card (z ⁻¹' {w}), s, hW, hwW, ?_, hzs, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have : W.domRestrict (s i) = fun v : W => (H.symm (v, e i)).1 := by
      funext v
      exact hs i v.1 v.2
    rw [this]
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · intro v hv
    have hfv : (z ⁻¹' {v}).Finite := by
      refine (Set.finite_range fun i => s i v).subset ?_
      intro y hy
      obtain ⟨i, hi⟩ := hsurj v hv y hy
      exact ⟨i, hi⟩
    unfold fiberVals
    rw [dif_pos hfv]
    have hF : hfv.toFinset = Finset.univ.map ⟨fun i => s i v, fun i j h => hinj v hv i j h⟩ := by
      ext y
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
      constructor
      · intro hy; exact hsurj v hv y hy
      · rintro ⟨i, rfl⟩; exact hzs i v hv
    rw [hF, Finset.map_val, Multiset.map_map]
    rfl
end ReciprocityTheory.L2DbarEstimates.Norm
