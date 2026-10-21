-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P35.ambientLocalContractibility_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:53:10.931473+00:00
-- url     : https://prove2.me/submissions/4b45bd71-d2b2-4011-8f5e-29fd6c79049c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35
open QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

theorem g62i_part1 {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (h : AmbientLocallyContractibleAt (x, y)) : AmbientLocallyContractibleAt y := by
  obtain ⟨U, hU, hH⟩ := h
  let V : Set Y := (fun y' => (x, y')) ⁻¹' U
  have hV : V ∈ 𝓝 y := by
    have hc : ContinuousAt (fun y' : Y => (x, y')) y := by fun_prop
    exact hc.preimage_mem_nhds hU
  refine ⟨V, hV, ?_⟩
  let ι : C(V, U) := ⟨fun v => ⟨(x, v.1), v.2⟩, by fun_prop⟩
  have h2 := (ContinuousMap.Homotopic.refl (ContinuousMap.snd : C(X × Y, Y))).comp
    (hH.comp (ContinuousMap.Homotopic.refl ι))
  convert h2 using 1 <;> (ext; rfl)

theorem g62i_part2 {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (y : Y) (h : AmbientLocallyContractibleAt y) (x : X) :
    AmbientLocallyContractibleAt (x, y) := by
  obtain ⟨V, hV, hH⟩ := h
  refine ⟨(univ : Set X) ×ˢ V, prod_mem_nhds univ_mem hV, ?_⟩
  obtain ⟨x0, hx0⟩ := id_nullhomotopic X
  let π1 : C(((univ : Set X) ×ˢ V : Set (X × Y)), X) := ⟨fun u => u.1.1, by fun_prop⟩
  let π2 : C(((univ : Set X) ×ˢ V : Set (X × Y)), V) := ⟨fun u => ⟨u.1.2, (mem_prod.1 u.2).2⟩, by fun_prop⟩
  have hA : ContinuousMap.Homotopic π1 (ContinuousMap.const _ x) := by
    have h1 := hx0.comp (ContinuousMap.Homotopic.refl π1)
    have h3 : ContinuousMap.Homotopic (ContinuousMap.const ((univ : Set X) ×ˢ V : Set (X × Y)) x0)
        (ContinuousMap.const _ x) := ⟨(PathConnectedSpace.somePath x0 x).toHomotopyConst⟩
    exact h1.trans h3
  have hB := hH.comp (ContinuousMap.Homotopic.refl π2)
  have hP := ContinuousMap.Homotopic.prodMk hA hB
  convert hP using 1 <;> (ext <;> rfl)

/-- Lemma 10.3, PDF pp. 39–40: both product assertions, with the ambient
contraction convention of Definition 10.1. No global nonemptiness assumption is added. -/
theorem solution
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] :
    (∀ (x : X) (y : Y), AmbientLocallyContractibleAt (x, y) →
      AmbientLocallyContractibleAt y) ∧
    (ContractibleSpace X → ∀ y : Y, AmbientLocallyContractibleAt y →
      ∀ x : X, AmbientLocallyContractibleAt (x, y)) :=
  ⟨fun x y h => g62i_part1 x y h, fun _ y h x => g62i_part2 y h x⟩
