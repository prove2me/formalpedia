-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.OswLocFin.exists_nhds_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:22.903291+00:00
-- url     : https://prove2.me/submissions/b8c8ec1c-edc0-44ee-b90e-1abb7421ff96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_NhdsInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin
open Filter Topology
namespace PositivityTheory.SiegelWeilFormula.OswLocFin
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {Φ : G → ℂ} (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ U ∈ nhds (0 : G), ∀ Y, ∀ Z ∈ U, Φ (Y + Z) = Φ Y := by
  obtain ⟨hlc, hcs⟩ := hΦ
  have hT : ∀ x : G, {z : G | Φ (x + z) = Φ x} ∈ 𝓝 (0 : G) := by
    intro x
    have hopen : IsOpen {z : G | Φ (x + z) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    exact hopen.mem_nhds (by simp)
  choose V₁ hV₁ hV₁s using fun x => exists_nhds_zero_half (hT x)
  choose V₂ hV₂ hV₂s using fun x => exists_nhds_half_neg (hT x)
  have hU : ∀ x : G, {y : G | y - x ∈ V₁ x ∩ V₂ x} ∈ 𝓝 x := by
    intro x
    have ht : Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 (x - x)) := (continuous_sub_right x).tendsto x
    rw [sub_self] at ht
    exact ht (Filter.inter_mem (hV₁ x) (hV₂ x))
  obtain ⟨t, -, hcover⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => {y : G | y - x ∈ V₁ x ∩ V₂ x}) (fun x _ => hU x)
  refine ⟨⋂ x ∈ t, V₁ x ∩ V₂ x, (Filter.biInter_finset_mem t).mpr fun x _ =>
    Filter.inter_mem (hV₁ x) (hV₂ x), fun Y Z hZ => ?_⟩
  have hZ' : ∀ x ∈ t, Z ∈ V₁ x ∩ V₂ x := Set.mem_iInter₂.mp hZ
  by_cases hY : Y ∈ tsupport Φ
  · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hY)
    have hx' : Y - x ∈ V₁ x ∩ V₂ x := hx
    have h1 : Φ (x + (Y - x + Z)) = Φ x := hV₁s x _ hx'.1 Z (hZ' x hxt).1
    have h2 : Φ (x + (Y - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
    rw [show x + (Y - x + Z) = Y + Z by abel] at h1
    rw [show x + (Y - x + 0) = Y by abel] at h2
    rw [h1, h2]
  · by_cases hYZ : Y + Z ∈ tsupport Φ
    · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hYZ)
      have hx' : Y + Z - x ∈ V₁ x ∩ V₂ x := hx
      have h1 : Φ (x + (Y + Z - x - Z)) = Φ x := hV₂s x _ hx'.2 Z (hZ' x hxt).2
      have h2 : Φ (x + (Y + Z - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
      rw [show x + (Y + Z - x - Z) = Y by abel] at h1
      rw [show x + (Y + Z - x + 0) = Y + Z by abel] at h2
      rw [h1, h2]
    · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYZ]
end PositivityTheory.SiegelWeilFormula.OswLocFin
