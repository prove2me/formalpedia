-- Prove2me | solution 1 for TopGroupoid.exists_topologicalGroupoid_action
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:58:42.789798+00:00
-- url     : https://prove2.me/submissions/1faa4e9e-3980-46b9-94d5-b6015b7827a2

import Definitions.Def_TopGroupoid_TopologicalGroupoid
import Theorems.Thm_CGWH_weaklyHausdorffSpace_pi_and_prod
import Theorems.Thm_CGWH_weaklyHausdorffSpace_subtype_and_compactlyGenerated

open Topology TopologicalSpace

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Sol_TopGroupoid_exists_topologicalGroupoid_action

/-- The `k`-ification `k(Y)`: the type `Y` with the topology `compactlyGenerated Y`. -/
def KS (Y : Type u) : Type u := Y

instance instTopKS (Y : Type u) [TopologicalSpace Y] : TopologicalSpace (KS Y) :=
  TopologicalSpace.compactlyGenerated.{u} Y

/-- Test maps from compact Hausdorff spaces are continuous into the `k`-ification. -/
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

/-- A continuous map out of a compactly generated space is continuous into the `k`-ification. -/
theorem cont_to_k {W Y : Type u} [TopologicalSpace W] [CompactlyGeneratedSpace W]
    [TopologicalSpace Y] {f : W → Y} (hf : Continuous f) :
    Continuous[inferInstance, compactlyGenerated.{u} Y] f :=
  continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated (k_map hf)

/-- The `k`-ification is compactly generated. -/
theorem k_cg {Y : Type u} [tY : TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (compactlyGenerated.{u} Y) := by
  refine @UCompactlyGeneratedSpace.mk Y (compactlyGenerated.{u} Y) ?_
  rw [← continuous_id_iff_le]
  exact continuous_from_compactlyGenerated (X := Y) (Y := Y)
    (t := @compactlyGenerated.{u} Y (compactlyGenerated.{u} Y)) id
    (fun S g => @continuous_test Y (compactlyGenerated.{u} Y) S
      (@ContinuousMap.mk S Y _ (compactlyGenerated.{u} Y) g (continuous_test S g)))

theorem comp' {A B C : Type u} (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (tC : TopologicalSpace C) {g : B → C} {f : A → B} (hg : @Continuous B C tB tC g)
    (hf : @Continuous A B tA tB f) : @Continuous A C tA tC (fun a => g (f a)) := by
  letI := tA; letI := tB; letI := tC
  exact hg.comp hf

theorem prod_mk' {W Y Z : Type u} (tW : TopologicalSpace W) [TopologicalSpace Y]
    [TopologicalSpace Z] {f : W → Y} {g : W → Z} (hf : @Continuous W Y tW _ f)
    (hg : @Continuous W Z tW _ g) : @Continuous W (Y × Z) tW _ (fun w => (f w, g w)) := by
  letI := tW
  exact hf.prodMk hg

theorem cont_to_k' {W Y : Type u} (tW : TopologicalSpace W)
    (h : @UCompactlyGeneratedSpace.{u} W tW) [TopologicalSpace Y] {f : W → Y}
    (hf : @Continuous W Y tW _ f) : @Continuous W Y tW (compactlyGenerated.{u} Y) f := by
  letI := tW
  haveI := h
  exact cont_to_k hf

end Sol_TopGroupoid_exists_topologicalGroupoid_action

open TopGroupoid Sol_TopGroupoid_exists_topologicalGroupoid_action

theorem solution
    {G X : Type u} [Group G] [TopologicalSpace G] [CompactlyGeneratedSpace G]
    [CGWH.WeaklyHausdorffSpace G] [TopologicalSpace X] [CompactlyGeneratedSpace X]
    [CGWH.WeaklyHausdorffSpace X] [MulAction G X]
    (hmul : Continuous[TopologicalSpace.compactlyGenerated.{u} (G × G), _]
      (fun p : G × G => p.1 * p.2))
    (hinv : Continuous (fun g : G => g⁻¹))
    (hact : Continuous[TopologicalSpace.compactlyGenerated.{u} (G × X), _]
      (fun p : G × X => p.1 • p.2)) :
    ∃ 𝒢 : @TopologicalGroupoid X (G × X) _ (TopologicalSpace.compactlyGenerated.{u} (G × X)),
      (∀ p : G × X, 𝒢.src p = p.2) ∧
      (∀ p : G × X, 𝒢.tgt p = p.1 • p.2) ∧
      (∀ x : X, 𝒢.unit x = (1, x)) ∧
      (∀ p : G × X, 𝒢.inv p = (p.1⁻¹, p.1 • p.2)) ∧
      ∀ (p q : G × X) (h : 𝒢.src p = 𝒢.tgt q), 𝒢.comp ⟨(p, q), h⟩ = (p.1 * q.1, q.2) := by
  let 𝒮 : SetGroupoid X (KS (G × X)) :=
    { src := fun p : G × X => p.2, tgt := fun p : G × X => p.1 • p.2,
      comp := fun p => ((p.1.1 : G × X).1 * (p.1.2 : G × X).1, (p.1.2 : G × X).2),
      unit := fun x => ((1, x) : G × X), inv := fun p : G × X => (p.1⁻¹, p.1 • p.2),
      tgt_comp := by
        rintro ⟨⟨⟨g, x⟩, ⟨g', x'⟩⟩, h⟩
        change x = g' • x' at h
        change (g * g') • x' = g • x
        rw [h, mul_smul]
      src_comp := fun _ => rfl
      comp_assoc := fun g h k _ _ => Prod.ext (mul_assoc _ _ _).symm rfl
      src_unit := fun _ => rfl, tgt_unit := fun x => one_smul G x
      comp_unit := fun g => Prod.ext (mul_one _) rfl
      unit_comp := fun g => Prod.ext (one_mul _) rfl
      src_inv := fun _ => rfl
      tgt_inv := fun g => inv_smul_smul _ _
      comp_inv := fun g => Prod.ext (mul_inv_cancel _) rfl
      inv_comp := fun g => Prod.ext (inv_mul_cancel _) rfl }
  haveI hwp : CGWH.WeaklyHausdorffSpace (G × X) := CGWH.weaklyHausdorffSpace_pi_and_prod.2 G X
  have hwh : CGWH.WeaklyHausdorffSpace (KS (G × X)) :=
    (CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated (G × X)).2
  have hcgk : CompactlyGeneratedSpace (KS (G × X)) := k_cg (Y := G × X)
  have hfst : Continuous (fun p : KS (G × X) => (p : G × X).1) :=
    continuous_le_dom k_le continuous_fst
  have hsnd : Continuous (fun p : KS (G × X) => (p : G × X).2) :=
    continuous_le_dom k_le continuous_snd
  have hact' : Continuous (fun p : KS (G × X) => (p : G × X).1 • (p : G × X).2) := hact
  let 𝒢 : TopologicalGroupoid X (KS (G × X)) :=
    { toSetGroupoid := 𝒮
      compactlyGeneratedSpace_obj := inferInstance
      weaklyHausdorffSpace_obj := inferInstance
      compactlyGeneratedSpace_arr := hcgk
      weaklyHausdorffSpace_arr := hwh
      continuous_src := hsnd
      continuous_tgt := hact'
      continuous_unit := cont_to_k (Y := G × X) (continuous_const.prodMk continuous_id)
      continuous_inv :=
        cont_to_k' (Y := G × X) _ hcgk ((hinv.comp hfst).prodMk hact')
      continuous_comp := by
        have hpair : Continuous (fun p : {p : KS (G × X) × KS (G × X) //
            𝒮.src p.1 = 𝒮.tgt p.2} => (((p.1.1 : G × X).1, (p.1.2 : G × X).1) : G × G)) :=
          (hfst.comp (continuous_fst.comp continuous_subtype_val)).prodMk
            (hfst.comp (continuous_snd.comp continuous_subtype_val))
        have h1 := comp' _ _ _ hmul (k_map hpair)
        have h2 : Continuous (fun p : {p : KS (G × X) × KS (G × X) //
            𝒮.src p.1 = 𝒮.tgt p.2} => (p.1.2 : G × X).2) :=
          hsnd.comp (continuous_snd.comp continuous_subtype_val)
        exact cont_to_k' (Y := G × X) _ k_cg (prod_mk' _ h1 (continuous_le_dom k_le h2)) }
  exact ⟨𝒢, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
