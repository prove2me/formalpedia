-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.rightInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:04.087152+00:00
-- url     : https://prove2.me/submissions/ee88f947-c055-4c63-938f-070eea0da88d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_mul_right_haar
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_onG_eq
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
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ)
    (h1 : ∀ g : MG G hG, Measure.modularCharacterFun g = 1) : IsRightInvM G μ := by
  obtain ⟨c, hc⟩ := onG_eq μ hμ
  have hMe : MeasurableEmbedding (MG.val : MG G hG → MtM m) := measurableEmbedding_MG_val
  have hback : Measure.map MG.val (onG hG μ) = μ := by
    show Measure.map MG.val (μ.comap MG.val) = μ
    rw [hMe.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hset : {x | ¬ x ∈ Set.range (MG.val : MG G hG → MtM m)} = {x | Matrix.of x ∉ G} := by
      ext x
      constructor
      · intro hx hxG
        exact hx ⟨⟨x, hxG⟩, rfl⟩
      · rintro hx ⟨z, rfl⟩
        exact hx z.2
    rw [hset]
    exact hμ.2.2.1
  intro s hs
  have hR : Measurable (rmulQ s : MtM m → MtM m) := by
    refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
    have hf : (fun x : MtM m => rmulQ s x i j) = fun x => ∑ k, x i k * s k j := by
      funext x
      simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
    rw [hf]
    exact continuous_finset_sum _ fun k _ => by fun_prop
  have hgkey : (rmulQ s) ∘ MG.val = MG.val ∘ (· * mk hG s hs) := by
    funext z
    show _ = MG.toM (z * mk hG s hs)
    rw [toM_mul', toM_mk]
    rfl
  have hinv : Measure.map (· * mk hG s hs) (onG hG μ) = onG hG μ := by
    rw [hc, Measure.map_smul, map_mul_right_haar, h1, one_smul]
  rw [← hback, Measure.map_map hR hMe.measurable, hgkey,
    ← Measure.map_map hMe.measurable (measurable_mul_const _), hinv]
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
