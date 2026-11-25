-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSheetAreaLintegral_proof_51c6f53859bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:19.668968+00:00
-- url     : https://prove2.me/submissions/0b879c13-0963-43f6-a2af-f72ad1fa3686

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal
namespace GroundTheory.Heights₂.Heights
namespace ConeSheetAreaLintegral
theorem _root_.solution (hPar : ConeSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetAreaLintegral.Statement := by
  classical
  intro n e S hS P Ψ F hP hΨ hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e S hS P Ψ hP hΨ

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i x => S *ᵥ fun p => s i.1 i.2 x ⟨(), p⟩ with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := by
    intro i
    have h1 : DifferentiableOn ℂ (fun x => fun p : Fin n => s i.1 i.2 x ⟨(), p⟩) (U i.1) :=
      differentiableOn_pi.2 fun p => differentiableOn_pi.1 ((hUD i.1).2.2.2 i.2) ⟨(), p⟩
    exact (Matrix.mulVecLin S).toContinuousLinearMap.differentiable.comp_differentiableOn h1

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i x =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun x => ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) *
          gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) with hG_def

  have hGD : ∀ k, ∀ x ∈ D k, G x = ∑ j : Fin (N k), H ⟨k, j⟩ x := by
    intro k x hx
    obtain ⟨hfe, hinjx, hsh⟩ := hfib k x ((hUD k).2.2.1 hx)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjx, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex : ∃ γ, IsSheet P Ψ x (segre (s k j x)) γ := ⟨s k j, (hsh j).1⟩
    have hch : chosenSheet P Ψ x (segre (s k j x)) =ᶠ[𝓝 x] s k j := by
      have : chosenSheet P Ψ x (segre (s k j x)) = hex.choose := by
        simp only [chosenSheet, dif_pos hex]
      rw [this]
      exact (hsh j).2 _ hex.choose_spec
    have hval : chosenSheet P Ψ x (segre (s k j x)) x = s k j x := hch.eq_of_nhds
    have hgram : gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x (segre (s k j x)) x' ⟨(), i⟩) x =
        gramVol (v ⟨k, j⟩) x :=
      gramVol_congr (hch.fun_comp fun f => S *ᵥ fun i => f ⟨(), i⟩)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun x =>
    ∑' k, (D k).indicator (fun x => ∑ j : Fin (N k), H ⟨k, j⟩ x) x with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ x ∂(volume : Measure (Fin e → ℂ)), x ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k x hk]
    intro k' hk'
    exact indicator_of_notMem (fun h => (hdisj hk').le_bot ⟨h, hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun x => ∑ j : Fin (N k), H ⟨k, j⟩ x) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ x, G x = ∑' i : Σ k, Fin (N k), ∫⁻ x in D i.1, H i x := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), F y
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ y in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F y
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hA := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hA]
  exact congrArg _ hRHS.symm
end ConeSheetAreaLintegral
end GroundTheory.Heights₂.Heights
