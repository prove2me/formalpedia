-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.onG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:13.594503+00:00
-- url     : https://prove2.me/submissions/fbb6502a-6cc8-4688-b0ae-2b5b9ad29f45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
private theorem isEmbedding_MG_val : Topology.IsEmbedding (MG.val : MG G hG → MtM m) :=
  ⟨⟨rfl⟩, fun _ _ hxy => Subtype.ext hxy⟩
private theorem measurableEmbedding_MG_val :
    MeasurableEmbedding (MG.val : MG G hG → MtM m) := by
  have hr : Set.range (MG.val : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hc : IsClosed (Set.range (MG.val : MG G hG → MtM m)) := by
    rw [hr]
    exact hG.1.preimage (f := fun x : MtM m => Matrix.of x) continuous_id
  exact (Topology.IsClosedEmbedding.mk isEmbedding_MG_val hc).measurableEmbedding
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
end
end

set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, onG hG μ = c • (Measure.haar : Measure (MG G hG)) := by
  haveI := hμ.1
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  haveI : SigmaFinite (onG hG μ) := by
    refine ⟨⟨⟨fun n => MG.val ⁻¹' spanningSets μ n, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
    · show μ.comap MG.val _ < ⊤
      rw [hMe.comap_apply]
      exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  have hkey : ∀ h z : MG G hG, MG.val (h * z) = lmulQ (MG.toM h) (MG.val z) := by
    intro h z
    show MG.toM (h * z) = _
    rw [toM_mul']
    rfl
  haveI : Measure.IsMulLeftInvariant (onG hG μ) := by
    refine ⟨fun h => Measure.ext fun s hs => ?_⟩
    have hA : Measurable (lmulQ (MG.toM h) : MtM m → MtM m) := by
      refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
      have hf : (fun x : MtM m => lmulQ (MG.toM h) x i j) = fun x => ∑ k, MG.toM h i k * x k j := by
        funext x
        simp only [lmulQ, Matrix.mul_apply, Matrix.of_apply]
      rw [hf]
      exact continuous_finset_sum _ fun k _ => by fun_prop
    have hvs : MeasurableSet (MG.val '' s) := hMe.measurableSet_image.2 hs
    have hinvA : Measure.map (lmulQ (MG.toM h)) μ = μ := hμ.2.2.2 _ h.2
    rw [Measure.map_apply (measurable_const_mul h) hs]
    show μ.comap MG.val _ = μ.comap MG.val _
    rw [hMe.comap_apply, hMe.comap_apply]
    apply le_antisymm
    · calc μ (MG.val '' ((h * ·) ⁻¹' s)) ≤ μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            apply measure_mono
            rintro _ ⟨z, hz, rfl⟩
            exact ⟨h * z, hz, hkey h z⟩
        _ = μ (MG.val '' s) := by
            rw [← Measure.map_apply hA hvs, hinvA]
    · calc μ (MG.val '' s) = μ (lmulQ (MG.toM h) ⁻¹' (MG.val '' s)) := by
            rw [← Measure.map_apply hA hvs, hinvA]
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s) ∪ {x | Matrix.of x ∉ G}) := by
            apply measure_mono
            intro y hy
            by_cases hyG : Matrix.of y ∈ G
            · left
              obtain ⟨w, hw, hwy⟩ := hy
              obtain ⟨z, hz⟩ : ∃ z : MG G hG, MG.val z = y := ⟨⟨y, hyG⟩, rfl⟩
              refine ⟨z, ?_, hz⟩
              have hEq : h * z = w := by
                apply hMe.injective
                rw [hkey, hz, hwy]
              show h * z ∈ s
              rw [hEq]
              exact hw
            · right
              exact hyG
        _ ≤ μ (MG.val '' ((h * ·) ⁻¹' s)) + μ {x | Matrix.of x ∉ G} := measure_union_le _ _
        _ = μ (MG.val '' ((h * ·) ⁻¹' s)) := by rw [hμ.2.2.1, add_zero]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (MG G hG)) := inferInstance
  have hK0 : (Measure.haar : Measure (MG G hG)) K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  exact ⟨_, measure_eq_div_smul (onG hG μ) Measure.haar hK0 hKt⟩
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
