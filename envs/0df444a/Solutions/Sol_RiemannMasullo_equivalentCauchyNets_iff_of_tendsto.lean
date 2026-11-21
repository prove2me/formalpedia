-- Prove2me | solution 1 for RiemannMasullo.equivalentCauchyNets_iff_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:31:08.610461+00:00
-- url     : https://prove2.me/submissions/e0270146-c4b5-479c-990b-0d3d837a8a17

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L90-L100
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo
universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J K : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  [Preorder K] [Nonempty K] [IsDirectedOrder K]


theorem solution [T2Space E] {f : J → E} {g : K → E} {x y : E}
    (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) :
    EquivalentCauchyNets f g ↔ x = y := by
  rw [EquivalentCauchyNets, ← prod_atTop_atTop_eq]
  have hsub : Tendsto (fun p : J × K ↦ f p.1 - g p.2) (atTop ×ˢ atTop) (𝓝 (x - y)) :=
    (hf.comp tendsto_fst).sub (hg.comp tendsto_snd)
  constructor
  · rintro ⟨_, _, hzero⟩
    exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)
  · rintro rfl
    exact ⟨hf.cauchy_map, hg.cauchy_map, by simpa only [sub_self] using hsub⟩
