-- Prove2me | solution 1 for P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:26.313794+00:00
-- url     : https://prove2.me/submissions/0c1757b9-176e-40fd-b3b8-72a20cbdf74a

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Theorems.Thm_P2M_Projectivization_measurable_mk__201516f83fba
public import Theorems.Thm_P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
namespace Projectivization
theorem _root_.solution [MeasurableSpace V] [BorelSpace V]
    {α : Type*} [MeasurableSpace α] (g : ℙ K V → α) :
    Measurable g ↔ Measurable (g ∘ (mk' K : _ → ℙ K V)) := by
  refine ⟨fun hg => hg.comp measurable_mk', fun hg => ?_⟩
  intro B hB
  -- Transport along `borel_eq_map_mk'`.
  have : BorelSpace ({ v : V // v ≠ 0 }) := Subtype.borelSpace _
  have h_subtype :
      @MeasurableSet { v : V // v ≠ 0 } (borel _) ((mk' K : _ → ℙ K V) ⁻¹' (g ⁻¹' B)) := by
    rw [← ‹BorelSpace ({ v : V // v ≠ 0 })›.measurable_eq]
    exact hg hB
  have h1 : @MeasurableSet (ℙ K V)
              (MeasurableSpace.map (mk' K : _ → ℙ K V) (borel _))
              (g ⁻¹' B) :=
    MeasurableSpace.map_def.mpr h_subtype
  rwa [borel_eq_map_mk'] at h1
end Projectivization
