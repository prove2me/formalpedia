-- Prove2me | solution 1 for TopGroupoid.TopologicalGroupoid.isClosed_composable_and_compactlyGenerated_eq_induced
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:50:18.630306+00:00
-- url     : https://prove2.me/submissions/2edb4421-3ce4-4836-88aa-76defafa80b7

import Definitions.Def_TopGroupoid_TopologicalGroupoid
import Theorems.Thm_CGWH_isClosed_setOf_eq
import Theorems.Thm_CGWH_weaklyHausdorffSpace_pi_and_prod
import Theorems.Thm_CGWH_weaklyHausdorffSpace_subtype_and_compactlyGenerated

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_TopGroupoid_TopologicalGroupoid_isClosed_composable_and_compactlyGenerated_eq_induced

/-- Test maps are continuous into the `k`-ification. -/
theorem continuous_test {Y : Type u} [tY : TopologicalSpace Y] (S : CompHaus.{u}) (g : C(S, Y)) :
    Continuous[inferInstance, compactlyGenerated.{u} Y] g := by
  let f : (Σ (i : (T : CompHaus.{u}) × C(T, Y)), i.fst) → Y := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices ∀ (i : (T : CompHaus.{u}) × C(T, Y)),
      Continuous[inferInstance, compactlyGenerated.{u} Y] (fun (a : i.fst) ↦ f ⟨i, a⟩) from
    this ⟨S, g⟩
  rw [← @continuous_sigma_iff]
  apply continuous_coinduced_rng

/-- The `k`-ification is finer than the original topology. -/
theorem k_le {Y : Type u} [tY : TopologicalSpace Y] : compactlyGenerated.{u} Y ≤ tY := by
  rw [← continuous_id_iff_le]
  exact continuous_from_compactlyGenerated id (fun S g => g.continuous)

/-- `k` is functorial. -/
theorem k_map {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {f : Y → Z}
    (hf : Continuous f) : Continuous[compactlyGenerated.{u} Y, compactlyGenerated.{u} Z] f := by
  exact continuous_from_compactlyGenerated (t := compactlyGenerated.{u} Z) f
    (fun S g => continuous_test S ⟨f ∘ g, hf.comp g.continuous⟩)

/-- The `k`-ification is compactly generated. -/
theorem k_cg {Y : Type u} [tY : TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (compactlyGenerated.{u} Y) := by
  refine @UCompactlyGeneratedSpace.mk Y (compactlyGenerated.{u} Y) ?_
  rw [← continuous_id_iff_le]
  exact continuous_from_compactlyGenerated (X := Y) (Y := Y)
    (t := @compactlyGenerated.{u} Y (compactlyGenerated.{u} Y)) id
    (fun S g => @continuous_test Y (compactlyGenerated.{u} Y) S
      (@ContinuousMap.mk S Y _ (compactlyGenerated.{u} Y) g (continuous_test S g)))

/-- A closed subspace of a compactly generated space is compactly generated. -/
theorem cg_of_closed {W : Type u} [TopologicalSpace W] [UCompactlyGeneratedSpace.{u} W]
    {A : Set W} (hA : IsClosed A) : UCompactlyGeneratedSpace.{u} A := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs => ?_
  have hcl : IsClosed (Subtype.val '' s : Set W) := by
    refine UCompactlyGeneratedSpace.isClosed fun S f => ?_
    have hT : IsClosed (f ⁻¹' A) := hA.preimage f.continuous
    haveI : CompactSpace (f ⁻¹' A) := isCompact_iff_compactSpace.1 hT.isCompact
    let g : C(CompHaus.of (f ⁻¹' A), A) :=
      ⟨fun t => ⟨f t.1, t.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have h1 := hs (CompHaus.of (f ⁻¹' A)) g
    have h2 : f ⁻¹' (Subtype.val '' s) = Subtype.val '' (g ⁻¹' s) := by
      ext t
      constructor
      · rintro ⟨a, ha, hat⟩
        exact ⟨⟨t, by show f t ∈ A; rw [← hat]; exact a.2⟩, by
          show (⟨f t, _⟩ : A) ∈ s
          convert ha using 1
          exact Subtype.ext hat.symm, rfl⟩
      · rintro ⟨t', ht', rfl⟩
        exact ⟨g t', ht', rfl⟩
    rw [h2]
    exact hT.isClosedEmbedding_subtypeVal.isClosedMap _ h1
  have : s = Subtype.val ⁻¹' (Subtype.val '' s) :=
    (Set.preimage_image_eq s Subtype.val_injective).symm
  rw [this]
  exact hcl.preimage continuous_subtype_val

/-- Continuity out of a compactly generated space is tested on compact Hausdorff probes. -/
theorem cont_from_cg' {W Y : Type u} (tW : TopologicalSpace W)
    (h : @UCompactlyGeneratedSpace.{u} W tW) (tY : TopologicalSpace Y) (f : W → Y)
    (hf : ∀ (S : CompHaus.{u}) (g : S → W), @Continuous S W _ tW g → @Continuous S Y _ tY (f ∘ g)) :
    @Continuous W Y tW tY f := by
  letI := tW
  letI := tY
  exact continuous_from_uCompactlyGeneratedSpace f (fun S g => hf S g g.continuous)

end Sol_TopGroupoid_TopologicalGroupoid_isClosed_composable_and_compactlyGenerated_eq_induced

open TopGroupoid
open Sol_TopGroupoid_TopologicalGroupoid_isClosed_composable_and_compactlyGenerated_eq_induced

theorem solution
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (R × R)]
        {p : R × R | G.src p.1 = G.tgt p.2} ∧
      TopologicalSpace.compactlyGenerated.{u} {p : R × R // G.src p.1 = G.tgt p.2} =
        TopologicalSpace.induced Subtype.val (TopologicalSpace.compactlyGenerated.{u} (R × R)) ∧
      @CompactlyGeneratedSpace {p : R × R // G.src p.1 = G.tgt p.2}
        (TopologicalSpace.induced Subtype.val (TopologicalSpace.compactlyGenerated.{u} (R × R))) ∧
      @CGWH.WeaklyHausdorffSpace {p : R × R // G.src p.1 = G.tgt p.2}
        (TopologicalSpace.induced Subtype.val
          (TopologicalSpace.compactlyGenerated.{u} (R × R))) := by
  haveI := G.compactlyGeneratedSpace_obj
  haveI := G.weaklyHausdorffSpace_obj
  haveI := G.compactlyGeneratedSpace_arr
  haveI := G.weaklyHausdorffSpace_arr
  have c1 : Continuous[compactlyGenerated.{u} (R × R), _] (fun p : R × R => G.src p.1) :=
    continuous_le_dom k_le (G.continuous_src.comp continuous_fst)
  have c2 : Continuous[compactlyGenerated.{u} (R × R), _] (fun p : R × R => G.tgt p.2) :=
    continuous_le_dom k_le (G.continuous_tgt.comp continuous_snd)
  have hcl : IsClosed[compactlyGenerated.{u} (R × R)] {p : R × R | G.src p.1 = G.tgt p.2} :=
    @CGWH.isClosed_setOf_eq (R × R) X (compactlyGenerated.{u} (R × R)) _ k_cg _ _ _ c1 c2
  have hcg : @CompactlyGeneratedSpace {p : R × R // G.src p.1 = G.tgt p.2}
      (TopologicalSpace.induced Subtype.val (TopologicalSpace.compactlyGenerated.{u} (R × R))) :=
    @cg_of_closed (R × R) (compactlyGenerated.{u} (R × R)) k_cg _ hcl
  have hwhprod : CGWH.WeaklyHausdorffSpace (R × R) := CGWH.weaklyHausdorffSpace_pi_and_prod.2 R R
  have hwhk : @CGWH.WeaklyHausdorffSpace (R × R) (compactlyGenerated.{u} (R × R)) :=
    (CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated (R × R)).2
  refine ⟨hcl, ?_, hcg, ?_⟩
  · apply le_antisymm
    · rw [← continuous_id_iff_le]
      exact continuous_induced_rng.2 (k_map continuous_subtype_val)
    · rw [← continuous_id_iff_le]
      refine cont_from_cg' _ hcg _ id (fun S g hg => ?_)
      have hg' : Continuous g := continuous_le_rng (induced_mono k_le) hg
      exact continuous_test S ⟨g, hg'⟩
  · exact (@CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated (R × R)
      (compactlyGenerated.{u} (R × R)) hwhk).1 _
