-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ParamPieceInt_exists_sheet_964cabc34eb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:45.470143+00:00
-- url     : https://prove2.me/submissions/a6d921ec-e5f0-464c-ae04-5f9a226284e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamPieceInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamPieceInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ParamPieceInt
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ParamPieceInt
theorem _root_.solution {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} {r r' : ℝ} {N : Set (Fin n → ℂ)}
    (hσ : DifferentiableOn ℂ σ (Metric.ball 0 r)) (hinj : Set.InjOn σ (Metric.ball 0 r))
    (hN : IsOpen N) (hrr : r' < r)
    (hprop : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r')
    (hcov : zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r)
    {w : Fin d → ℂ} (hw : w ∈ Metric.ball 0 r) (hwN : σ w ∈ N)
    (hdet : LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) :
    ∃ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt W A (σ w) s ∧
      ∀ᶠ v in 𝓝 w, s (A *ᵥ σ v) = σ v := by
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hstrict : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) w := by
    have he : (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g w := by
      ext1 v
      simp
    rw [he]
    exact (hgan w hw).hasStrictFDerivAt
  obtain ⟨e, heg, hwe⟩ : ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
      (e : (Fin d → ℂ) → Fin d → ℂ) = g ∧ w ∈ e.source :=
    ⟨hstrict.toOpenPartialHomeomorph g, hstrict.toOpenPartialHomeomorph_coe,
      hstrict.mem_toOpenPartialHomeomorph_source⟩

  have hdetc : ContinuousAt (fun v => (fderiv ℂ g v).det) w :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (hgan w hw).fderiv.continuousAt
  have h1 : ∀ᶠ v in 𝓝 w, v ∈ Ω := hΩo.mem_nhds ⟨hw, hwN⟩
  have h2 : ∀ᶠ v in 𝓝 w, v ∈ e.source := e.open_source.mem_nhds hwe
  have hev : ∀ᶠ v in 𝓝 w, (v ∈ Ω ∧ v ∈ e.source) ∧ (fderiv ℂ g v).det ≠ 0 :=
    (h1.and h2).and (hdetc.eventually_ne hdet)
  obtain ⟨O, hOp, hOo, hwO⟩ := eventually_nhds_iff.1 hev
  have hsymm : ∀ v ∈ O, e.symm (g v) = v := fun v hv => by
    rw [← heg]; exact e.left_inv (hOp v hv).1.2
  set U : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' O with hU
  have hUo : IsOpen U := e.isOpen_inter_preimage_symm hOo
  have hgU : ∀ v ∈ O, g v ∈ U := fun v hv =>
    ⟨by rw [← heg]; exact e.map_source (hOp v hv).1.2, by
      show e.symm (g v) ∈ O; rw [hsymm v hv]; exact hv⟩
  have hright : ∀ y ∈ U, g (e.symm y) = y := fun y hy => by
    rw [← heg]; exact e.right_inv hy.1
  have hsymmd : ∀ y ∈ U, DifferentiableAt ℂ e.symm y := by
    intro y hy
    have hv : e.symm y ∈ O := hy.2
    have hd := (hOp _ hv).2
    have hf : HasFDerivAt (e : (Fin d → ℂ) → Fin d → ℂ)
        (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) (e.symm y) := by
      have he : (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g (e.symm y) := by
        ext1 v
        simp
      rw [he, heg]
      exact (hgan _ (hOp _ hv).1.1.1).differentiableAt.hasFDerivAt
    exact (e.hasFDerivAt_symm hy.1 hf).differentiableAt
  refine ⟨σ ∘ e.symm, ⟨U, hUo, hgU w hwO, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    exact ((hσ.differentiableAt (Metric.isOpen_ball.mem_nhds (hOp _ hv).1.1.1)).comp y
      (hsymmd y hy)).differentiableWithinAt
  · show σ (e.symm (g w)) = σ w
    rw [hsymm w hwO]
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    refine ⟨hright y hy, ?_⟩
    exact (hprop _ (hOp _ hv).1.1.1 (hOp _ hv).1.1.2).1
  ·
    set K : Set (Fin d → ℂ) := Metric.closedBall 0 r' \ O with hK
    have hKb : K ⊆ Metric.ball 0 r := fun v hv => Metric.closedBall_subset_ball hrr hv.1
    have hKc : IsCompact (σ '' K) :=
      ((isCompact_closedBall 0 r').diff hOo).image_of_continuousOn (hσ.continuousOn.mono hKb)
    have hwK : σ w ∉ σ '' K := by
      rintro ⟨k, hk, hkw⟩
      exact hk.2 (hinj (hKb hk) hw hkw ▸ hwO)
    refine ⟨N ∩ (σ '' K)ᶜ, (hN.inter hKc.isClosed.isOpen_compl).mem_nhds ⟨hwN, hwK⟩, ?_⟩
    rintro x' ⟨hx'Z, hx'N, hx'K⟩ -
    obtain ⟨v, hvb, rfl⟩ := hcov ⟨hx'Z, hx'N⟩
    have hvr : ‖v‖ ≤ r' := (hprop v hvb hx'N).2
    have hvO : v ∈ O := by
      by_contra hvO
      exact hx'K ⟨v, ⟨mem_closedBall_zero_iff.2 hvr, hvO⟩, rfl⟩
    show σ v = σ (e.symm (g v))
    rw [hsymm v hvO]
  · filter_upwards [hOo.mem_nhds hwO] with v hv
    show σ (e.symm (g v)) = σ v
    rw [hsymm v hv]
end GroundTheory.Heights₂.Heights.ParamPieceInt
