-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.fubini_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:58.392795+00:00
-- url     : https://prove2.me/submissions/ab3c27a3-e1c6-4173-b71e-080e90c748cc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inG_nU_herm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_scalar_section
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_gset_sub_dom
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inG_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_scalar_section_mul_conjugate_section


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (p q : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    (hψ : IsSingTest ψ) :
    ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ =
      ∫ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hU0 : ∀ g : M2 n, InG g → g ∈ {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := fun g hg =>
    ⟨(gset_sub_dom hg).2.1, (gset_sub_dom hg).2.2.1⟩
  have hf0c : ContinuousOn (f0 (n := n) p q) {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
    (contDiffOn_scalar_section p q).continuousOn
  have hf0ne : ∀ k, f0 p q (ι k) ≠ 0 := fun k h => by
    have := scalar_section_mul_conjugate_section ((hK (ι k)).2 ⟨k, rfl⟩) p q; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : Continuous fun k => (f0 p q (ι k))⁻¹ :=
    (hf0c.comp_continuous hι (fun k => hU0 _ (hιG k))).inv₀ hf0ne
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set F : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => f0 p q (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 *
    (f0 p q (ι z.1))⁻¹ with hFdef
  have hFc : Continuous F :=
    ((hf0c.comp_continuous hmap (fun z => hU0 _ (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hc.comp continuous_fst)
  have hFs : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport F) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFdef, h0]
  have hFi : Integrable F (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ = ∫ x, F (k, x) := by
    intro k; rw [← integral_mul_const]
  have e2 : ∀ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x = ∫ k, F (k, x) ∂μ := by
    intro x; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFdef, mul_assoc]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap (f := fun k x => F (k, x)) hFi
end PositivityTheory.Rg.Sw.LVs
