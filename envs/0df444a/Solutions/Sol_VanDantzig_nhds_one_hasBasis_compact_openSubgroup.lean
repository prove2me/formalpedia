-- Prove2me | solution 1 for VanDantzig.nhds_one_hasBasis_compact_openSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:15:18.188067+00:00
-- url     : https://prove2.me/submissions/3032cafe-ed01-43e0-8f63-3588e71112b2

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_VanDantzig_nhds_one_hasBasis_compact_openSubgroup

open Set

/-- Every neighbourhood of `1` in a Hausdorff, locally compact, totally disconnected topological
group contains a compact open subgroup (van Dantzig). -/
theorem exists_compact_openSubgroup_sub_mem_nhds {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK, hKU, hKcompact⟩ := local_compact_nhds hU
  obtain ⟨W, hW, hOne, hWK⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp hK
  have hW : IsClopen W := hW
  have hWcompact := hKcompact.of_isClosed_subset hW.isClosed hWK
  let H := MulAction.stabilizer G W
  have hsubset : (H : Set G) ⊆ W := by
    intro g hg
    have hgW : g • W = W := MulAction.mem_stabilizer_iff.mp hg
    simpa [hgW, smul_eq_mul] using (smul_mem_smul_set (a := g) hOne)
  let O : Set (G × G) := {p | p.1 * p.2 ∈ W ∧ p.1⁻¹ * p.2 ∈ W}
  have hO : IsOpen O := (hW.isOpen.preimage continuous_mul).inter
    (hW.isOpen.preimage (continuous_fst.inv.mul continuous_snd))
  have honeW : ({1} : Set G) ×ˢ W ⊆ O := by
    rintro ⟨g, w⟩ ⟨hg, hw⟩
    change g = 1 at hg
    subst g
    simpa [O] using hw
  obtain ⟨V, T, hV, _, hOneV, hWT, hVT⟩ :=
    generalized_tube_lemma isCompact_singleton hWcompact hO honeW
  have hHopen : IsOpen (H : Set G) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (hV.mem_nhds (hOneV (mem_singleton 1))) fun g hg ↦ ?_
    apply MulAction.mem_stabilizer_iff.mpr
    refine subset_antisymm (smul_set_subset_iff.mpr ?_) ?_
    · exact fun w hw ↦ (hVT (mk_mem_prod hg (hWT hw))).1
    · intro w hw
      exact mem_smul_set_iff_inv_smul_mem.mpr (hVT (mk_mem_prod hg (hWT hw))).2
  let J : OpenSubgroup G := ⟨H, hHopen⟩
  exact ⟨J, hWcompact.of_isClosed_subset J.isClosed hsubset, hsubset.trans (hWK.trans hKU)⟩

end Sol_VanDantzig_nhds_one_hasBasis_compact_openSubgroup

theorem solution (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K : OpenSubgroup G => (K : Set G)) := by
  refine ⟨fun W ↦ ⟨Sol_VanDantzig_nhds_one_hasBasis_compact_openSubgroup.exists_compact_openSubgroup_sub_mem_nhds, ?_⟩⟩
  rintro ⟨H, _, hHW⟩
  exact Filter.mem_of_superset H.mem_nhds_one hHW
