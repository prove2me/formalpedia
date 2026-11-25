-- Prove2me | solution 1 for PI.VolStabW.measure_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:46.133387+00:00
-- url     : https://prove2.me/submissions/4eb452dd-57cc-4698-93f2-c078ec543cf7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
namespace PI.VolStabW
theorem _root_.solution {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (Λ L : AddSubgroup V) (hΛL : Λ ≤ L)
    (hL : MeasurableSet (L : Set V)) (hΛ : MeasurableSet (Λ : Set V)) (hfin : Λ.relIndex L ≠ 0) :
    μ L = (Λ.relIndex L : ENNReal) * μ Λ := by
  have emb : MeasurableEmbedding ((↑) : L → V) := MeasurableEmbedding.subtype_coe hL
  have hadd : ∀ g : L, Measurable (fun x : L => g + x) := fun g =>
    ((measurable_const_add (g : V)).comp measurable_subtype_coe).subtype_mk
  have : MeasurableAdd L := ⟨hadd, fun g =>
    ((measurable_add_const (g : V)).comp measurable_subtype_coe).subtype_mk⟩
  have : (Λ.addSubgroupOf L).FiniteIndex := ⟨hfin⟩
  have : (μ.comap ((↑) : L → V)).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (hadd g) hs, emb.comap_apply, emb.comap_apply]
    have e : ((↑) : L → V) '' ((fun x : L => g + x) ⁻¹' s) =
        (fun x : V => (g : V) + x) ⁻¹' (((↑) : L → V) '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g + y, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hxL : x ∈ L := by
          have : x = (z : V) - g := by rw [hzx]; abel
          rw [this]
          exact L.sub_mem z.2 g.2
        refine ⟨⟨x, hxL⟩, ?_, rfl⟩
        have : g + (⟨x, hxL⟩ : L) = z := Subtype.ext (by simp [hzx])
        rw [this]
        exact hz
    rw [e, measure_preimage_add]
  have key := AddSubgroup.index_mul_measure (Λ.addSubgroupOf L)
    (measurable_subtype_coe hΛ) (μ.comap ((↑) : L → V))
  rw [emb.comap_apply, emb.comap_apply, Set.image_univ, Subtype.range_coe] at key
  have e2 : ((↑) : L → V) '' ((Λ.addSubgroupOf L : AddSubgroup L) : Set L) = Λ := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hΛL hx⟩, hx, rfl⟩
  rw [e2] at key
  rw [← key]
  rfl
end PI.VolStabW
