-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.haarOn_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:57.291648+00:00
-- url     : https://prove2.me/submissions/880f9f6b-f694-4c8a-8224-1e9058c0eb89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_map_comap_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Abs
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
private theorem abs_inv_lemma (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G)
    (hνc : ν (S : Set G)ᶜ = 0) (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant := by
  have hemb : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmc : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := map_comap_subgroup S hS ν hνc
  refine ⟨fun s => ?_⟩
  have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x : S => s * x)).map Subtype.val = ν := by
    rw [Measure.map_map hemb.measurable (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : S => s * x) = (fun y : G => (s : G) * y) ∘ Subtype.val := by
      funext x; simp
    rw [hc, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmc]
    exact hνi s s.2
  calc Measure.map (fun x : S => s * x) (ν.comap Subtype.val)
      = ((Measure.map (fun x : S => s * x) (ν.comap Subtype.val)).map Subtype.val).comap
          Subtype.val := (hemb.comap_map _).symm
    _ = ν.comap Subtype.val := by rw [h1]
private theorem abs_scal_lemma_2 (S : Subgroup G) [LocallyCompactSpace S] (la : Measure S)
    [SigmaFinite la] [la.IsMulLeftInvariant] (h0 : la ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ la = c • (haar : Measure S) := by
  haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : S)
  have hKpos : 0 < (haar : Measure S) K :=
    lt_of_lt_of_le (isOpen_interior.measure_pos haar ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩)
      (measure_mono interior_subset)
  have hKtop : (haar : Measure S) K ≠ ⊤ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul (s := K) la (haar : Measure S) hKpos.ne' hKtop
  refine ⟨la K / haar K, ?_, ?_, heq⟩
  · intro hc; rw [hc, zero_smul] at heq; exact h0 heq
  · intro hc
    rw [hc] at heq
    have hsp : ∀ i, (haar : Measure S) (spanningSets la i) = 0 := by
      intro i
      have h1 : ((⊤ : ℝ≥0∞) • (haar : Measure S)) (spanningSets la i) < ⊤ := by
        rw [← heq]; exact measure_spanningSets_lt_top la i
      rw [Measure.smul_apply, smul_eq_mul] at h1
      by_contra hne
      rw [ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have hu : (haar : Measure S) Set.univ = 0 := by
      rw [← iUnion_spanningSets la]; exact measure_iUnion_null hsp
    exact (isOpen_univ.measure_pos haar ⟨1, trivial⟩).ne' hu
end Abs
end PI.NMeasInv.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) (hμ : HaarOn H μ) :
    (∀ K : Set G, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set G, IsOpen U → (U ∩ (H : Set G)).Nonempty → 0 < μ U := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  have hmc := map_comap_subgroup H hH μ hc
  haveI := abs_inv_lemma H hH μ hc hi
  haveI : SigmaFinite (μ.comap (Subtype.val : H → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmc]; exact hσ)
  have hne : μ.comap (Subtype.val : H → G) ≠ 0 := by
    intro h; apply h0; rw [← hmc, h, Measure.map_zero]
  obtain ⟨c, hc0, hct, hceq⟩ := abs_scal_lemma_2 H (μ.comap (Subtype.val : H → G)) hne
  have hμeq : μ = c • (haar : Measure H).map Subtype.val := by
    rw [← hmc, hceq, Measure.map_smul]
  constructor
  · intro K hK
    rw [hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hK.isClosed.measurableSet,
      smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top
      ((hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top)
  · intro U hU hne'
    rw [hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hU.measurableSet, smul_eq_mul]
    obtain ⟨x, hxU, hxH⟩ := hne'
    have hpos : 0 < (haar : Measure H) (Subtype.val ⁻¹' U) :=
      (hU.preimage continuous_subtype_val).measure_pos haar ⟨⟨x, hxH⟩, hxU⟩
    exact ENNReal.mul_pos hc0 hpos.ne'
end PI.NMeasInv.UnitaryGroupMassFormula
