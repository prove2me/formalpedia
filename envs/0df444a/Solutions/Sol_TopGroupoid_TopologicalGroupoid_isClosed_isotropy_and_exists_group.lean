-- Prove2me | solution 1 for TopGroupoid.TopologicalGroupoid.isClosed_isotropy_and_exists_group
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:54:33.88401+00:00
-- url     : https://prove2.me/submissions/ef30ac01-fd67-4d0b-a347-c6259b72978c

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_TopGroupoid_TopologicalGroupoid_isClosed_isotropy_and_exists_group

/-- The test maps from compact Hausdorff spaces are continuous into the `k`-ification. -/
theorem continuous_test {Y : Type u} [tY : TopologicalSpace Y] (S : CompHaus.{u}) (g : C(S, Y)) :
    Continuous[inferInstance, compactlyGenerated.{u} Y] g := by
  let f : (Σ (i : (T : CompHaus.{u}) × C(T, Y)), i.fst) → Y := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices ∀ (i : (T : CompHaus.{u}) × C(T, Y)),
      Continuous[inferInstance, compactlyGenerated.{u} Y] (fun (a : i.fst) ↦ f ⟨i, a⟩) from
    this ⟨S, g⟩
  rw [← @continuous_sigma_iff]
  apply continuous_coinduced_rng

/-- Functoriality of the `k`-ification. -/
theorem k_map {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {f : Y → Z}
    (hf : Continuous f) : Continuous[compactlyGenerated.{u} Y, compactlyGenerated.{u} Z] f :=
  continuous_from_compactlyGenerated (t := compactlyGenerated.{u} Z) f
    (fun S g => continuous_test S ⟨f ∘ g, hf.comp g.continuous⟩)

/-- The `k`-ification is finer than the original topology. -/
theorem k_le {Y : Type u} [tY : TopologicalSpace Y] : compactlyGenerated.{u} Y ≤ tY := by
  rw [← continuous_id_iff_le]
  exact continuous_from_compactlyGenerated id (fun S g => g.continuous)

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

/-- A weakly Hausdorff space is `T₁`: a point is the image of the one-point compact Hausdorff
space. -/
theorem t1_of_wh {Y : Type u} [TopologicalSpace Y] [CGWH.WeaklyHausdorffSpace Y] : T1Space Y := by
  refine ⟨fun y => ?_⟩
  have h := CGWH.WeaklyHausdorffSpace.isClosed_range (PUnit.{u + 1}) (fun _ => y)
    continuous_const
  have e : Set.range (fun _ : PUnit.{u + 1} => y) = {y} := Set.range_const
  rw [e] at h
  exact h

/-- Every subspace of a weakly Hausdorff space is weakly Hausdorff. -/
theorem wh_subtype {Y : Type u} [TopologicalSpace Y] [CGWH.WeaklyHausdorffSpace Y] (A : Set Y) :
    CGWH.WeaklyHausdorffSpace A := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  have h := CGWH.WeaklyHausdorffSpace.isClosed_range K (Subtype.val ∘ f)
    (continuous_subtype_val.comp hf)
  have e : Set.range f = Subtype.val ⁻¹' Set.range (Subtype.val ∘ f) := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  rw [e]
  exact h.preimage continuous_subtype_val

theorem comp' {A B C : Type u} (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (tC : TopologicalSpace C) {g : B → C} {f : A → B} (hg : @Continuous B C tB tC g)
    (hf : @Continuous A B tA tB f) : @Continuous A C tA tC (fun a => g (f a)) := by
  letI := tA; letI := tB; letI := tC
  exact hg.comp hf

theorem cc {X : Type u} {R : Type u} (G : TopGroupoid.SetGroupoid X R) {g g' h h' : R}
    (hg : g = g') (hh : h = h') (H : G.src g = G.tgt h) (H' : G.src g' = G.tgt h') :
    G.comp ⟨(g, h), H⟩ = G.comp ⟨(g', h'), H'⟩ := by subst hg hh; rfl

end Sol_TopGroupoid_TopologicalGroupoid_isClosed_isotropy_and_exists_group

open TopGroupoid Sol_TopGroupoid_TopologicalGroupoid_isClosed_isotropy_and_exists_group in
theorem solution
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) (x : X) :
    IsClosed (G.isotropy x) ∧
      CompactlyGeneratedSpace (G.isotropy x) ∧
      CGWH.WeaklyHausdorffSpace (G.isotropy x) ∧
      ∃ _ : Group (G.isotropy x),
        (∀ g h : G.isotropy x,
          ((g * h : G.isotropy x) : R) = G.comp ⟨((g : R), (h : R)), g.2.1.trans h.2.2.symm⟩) ∧
        ((1 : G.isotropy x) : R) = G.unit x ∧
        (∀ g : G.isotropy x, ((g⁻¹ : G.isotropy x) : R) = G.inv g) ∧
        Continuous (fun g : G.isotropy x => g⁻¹) ∧
        Continuous[TopologicalSpace.compactlyGenerated.{u} (G.isotropy x × G.isotropy x), _]
          (fun p : G.isotropy x × G.isotropy x => p.1 * p.2) := by
  haveI := G.compactlyGeneratedSpace_obj
  haveI := G.weaklyHausdorffSpace_obj
  haveI := G.compactlyGeneratedSpace_arr
  haveI := G.weaklyHausdorffSpace_arr
  haveI : T1Space X := t1_of_wh
  have hcl : IsClosed (G.isotropy x) :=
    ((isClosed_singleton (x := x)).preimage G.continuous_src).inter
      ((isClosed_singleton (x := x)).preimage G.continuous_tgt)
  refine ⟨hcl, cg_of_closed hcl, wh_subtype _, ?_⟩
  letI iM : Mul (G.isotropy x) := ⟨fun g h => ⟨G.comp ⟨(g.1, h.1), g.2.1.trans h.2.2.symm⟩, by
      refine ⟨?_, ?_⟩
      · rw [G.src_comp]; exact h.2.1
      · rw [G.tgt_comp]; exact g.2.2⟩⟩
  letI iO : One (G.isotropy x) := ⟨⟨G.unit x, G.src_unit x, G.tgt_unit x⟩⟩
  letI iI : Inv (G.isotropy x) := ⟨fun g => ⟨G.inv g.1, by
      refine ⟨?_, ?_⟩
      · rw [G.src_inv]; exact g.2.2
      · rw [G.tgt_inv]; exact g.2.1⟩⟩
  refine ⟨Group.ofLeftAxioms ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    exact Subtype.ext (G.comp_assoc a b c _ _).symm
  · rintro ⟨a, ha1, ha2⟩
    exact Subtype.ext ((cc G.toSetGroupoid (congrArg G.unit ha2.symm) rfl _ _).trans
      (G.unit_comp a))
  · rintro ⟨a, ha1, ha2⟩
    exact Subtype.ext ((G.inv_comp a).trans (congrArg G.unit ha1))
  · intro g h; rfl
  · rfl
  · intro g; rfl
  · exact (G.continuous_inv.comp continuous_subtype_val).subtype_mk _
  · have hm : Continuous (fun p : G.isotropy x × G.isotropy x =>
        (⟨(p.1.1, p.2.1), p.1.2.1.trans p.2.2.2.symm⟩ : {p : R × R // G.src p.1 = G.tgt p.2})) :=
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    have h1 := comp' _ _ _ G.continuous_comp (k_map hm)
    exact continuous_induced_rng.2 h1
