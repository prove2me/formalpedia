-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isSimpleSheetPt_of_injective_6b1dc600c13c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:35.693793+00:00
-- url     : https://prove2.me/submissions/63c01232-8c05-4167-b010-569d988b10b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_inv_smul_eq_cons_954153cdf7f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_ratio_smul_cons_60856f0cf16b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_segre_scaleBlock_71f3a993f711
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_proj_segre_36c3e8284232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt


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
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj IsMultiHomogIdeal mcPts segre fibre IsSheet scaleBlock
  scaleBlock_mem_zeroLocus segre_differentiableAt osgood fibreFinite)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {B : Set (Fin e → ℂ)} (hB : IsOpen B)
    (hγ : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hyB : y ∈ B)
    (huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1))
    (h0 : Ψ' (segre (γ y)) 0 ≠ 0)
    (hinj : Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y)) :
    IsSimpleSheetPt P Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) := by
  have hK : Nonempty K := hP.1
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) 0).continuousAt.continuousWithinAt
  set D := B ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := hcont0.isOpen_inter_preimage hB isOpen_compl_singleton
  have hyD : y ∈ D := ⟨hyB, h0⟩
  have hτd : DifferentiableOn ℂ τ D := fun y' hy' =>
    (differentiableAt_ratio Ψ' (hγ y' hy'.1).1 hy'.2).differentiableWithinAt
  have hτa : AnalyticAt ℂ τ y := SheetOnlyNull.analyticOnNhd_of_differentiableOn hDo hτd y hyD
  have hτc : ContDiffAt ℂ 1 τ y := hτa.contDiffAt
  set L := (LinearEquiv.ofInjectiveEndo (fderiv ℂ τ y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    hinj).toContinuousLinearEquiv with hLdef
  have hτL : HasFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) y :=
    hτa.differentiableAt.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  set φ := hτc.toOpenPartialHomeomorph τ hτL one_ne_zero with hφdef
  have hφτ : ∀ y', φ y' = τ y' := fun y' => rfl
  have hysrc : y ∈ φ.source := hτc.mem_toOpenPartialHomeomorph_source hτL one_ne_zero
  have hytgt : τ y ∈ φ.target := hτc.image_mem_toOpenPartialHomeomorph_target hτL one_ne_zero
  have hsymm_y : φ.symm (τ y) = y := φ.left_inv hysrc
  have hsymmc : ContDiffAt ℂ 1 φ.symm (τ y) :=
    φ.contDiffAt_symm (f₀' := L) hytgt (by rw [hsymm_y]; exact hτL) (by rw [hsymm_y]; exact hτc)
  have hev_D : ∀ᶠ t in 𝓝 (τ y), φ.symm t ∈ D :=
    hsymmc.continuousAt.preimage_mem_nhds (by rw [hsymm_y]; exact hDo.mem_nhds hyD)
  have hev_d : ∀ᶠ t in 𝓝 (τ y), DifferentiableAt ℂ φ.symm t :=
    (hsymmc.eventually (by simp)).mono fun t ht => ht.differentiableAt one_ne_zero
  have hev_t : ∀ᶠ t in 𝓝 (τ y), t ∈ φ.target := φ.open_target.mem_nhds hytgt
  set γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun t => scaleBlock k0 (Ψ' (segre (γ (φ.symm t))) 0)⁻¹ (γ (φ.symm t)) with hγ'def
  have hγ'd : ∀ t, φ.symm t ∈ D → DifferentiableAt ℂ φ.symm t → DifferentiableAt ℂ γ' t := by
    intro t ht hdt
    have hg : DifferentiableAt ℂ (fun t => γ (φ.symm t)) t := (hγ _ ht.1).1.comp t hdt
    have hc : DifferentiableAt ℂ (fun t => (Ψ' (segre (γ (φ.symm t))) 0)⁻¹) t :=
      ((differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ _ ht.1).1) 0).fun_inv ht.2).comp t hdt
    refine differentiableAt_pi.2 fun p => ?_
    simp only [hγ'def, scaleBlock]
    split_ifs
    · exact hc.fun_mul (differentiableAt_pi.1 hg p)
    · exact (differentiableAt_const _).fun_mul (differentiableAt_pi.1 hg p)
  have hsheet : IsSheet P Ψ' (τ y) ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) γ' := by
    refine ⟨by simp only [hγ'def, hsymm_y, segre_scaleBlock], ?_⟩
    filter_upwards [hev_D, hev_d, hev_t] with t h1 h2 h3
    refine ⟨hγ'd t h1 h2, scaleBlock_mem_zeroLocus P hPh k0 (inv_ne_zero h1.2) (hγ _ h1.1).2.1, ?_⟩
    simp only [hγ'def, segre_scaleBlock, map_smul]
    rw [inv_smul_eq_cons _ h1.2]
    exact congrArg _ (φ.right_inv h3)
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  set w' := (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y) with hw'def
  have hΨw' : Ψ w' = (Ψ' (segre (γ y)) 0)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
    rw [hw'def, map_smul, (hγ y hyB).2.2]
  have hw'0 : Ψ w' 0 ≠ 0 := by
    rw [hΨw']
    simpa using h0
  let m : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) → (Fin e → ℂ) × (((k : K) → ι k) → ℂ) :=
    fun q => (ratio (Ψ q.2), (Ψ q.2 0)⁻¹ • q.2)
  have hm0 : m (τ y, w') = (y, segre (γ y)) := by
    refine Prod.ext ?_ ?_
    · show ratio (Ψ w') = y
      rw [hΨw', ratio_smul_cons (inv_ne_zero h0)]
    · show (Ψ w' 0)⁻¹ • w' = segre (γ y)
      rw [hΨw', hw'def]
      simp [h0]
  have h2 : Continuous fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 := hΨc.comp continuous_snd
  have h20 : ContinuousAt (fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 0) (τ y, w') :=
    ((continuous_apply 0).comp h2).continuousAt
  have hmc : ContinuousAt m (τ y, w') := by
    refine ContinuousAt.prodMk ?_ ?_
    · refine continuousAt_pi.2 fun i => ?_
      exact ContinuousAt.div (f := fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 i.succ)
        ((continuous_apply i.succ).comp h2).continuousAt h20 hw'0
    · exact (h20.inv₀ hw'0).smul continuous_snd.continuousAt
  have hm : Tendsto m (𝓝 (τ y, w')) (𝓝 (y, segre (γ y))) := hm0 ▸ hmc.tendsto
  have hev1 := hm.eventually huniq
  have hev2 : ∀ᶠ q in 𝓝 (τ y, w'), (m q).1 ∈ φ.source :=
    ((continuous_fst.tendsto _).comp hm).eventually (φ.open_source.mem_nhds hysrc)
  have hev3 : ∀ᶠ q in 𝓝 (τ y, w'), Ψ q.2 0 ≠ 0 := h20.eventually_ne hw'0
  refine ⟨τ y, γ', hsheet, ?_⟩
  filter_upwards [hev1, hev2, hev3] with q hq1 hq2 hq3 hqf
  obtain ⟨z, hz, hzs, hΨ'z⟩ := hqf
  have hfib : (m q).2 ∈ fibre P Ψ (m q).1 := by
    have := smul_mem_fibre hPh hz Ψ (by rw [hzs]; exact hq3)
    rw [hzs] at this
    exact this
  have hE : (Ψ q.2 0)⁻¹ • q.2 = segre (γ (ratio (Ψ q.2))) := hq1 hfib
  have hs' : Ψ' (segre (γ (ratio (Ψ q.2)))) = (Ψ q.2 0)⁻¹ • (Fin.cons 1 q.1 : Fin (e + 1) → ℂ) := by
    rw [← hE, map_smul, hΨ'z]
  have hτs : τ (ratio (Ψ q.2)) = q.1 := by
    show ratio (Ψ' (segre (γ (ratio (Ψ q.2))))) = q.1
    rw [hs', ratio_smul_cons (inv_ne_zero hq3)]
  have hsymm_q : φ.symm q.1 = ratio (Ψ q.2) := by
    rw [← hτs]
    exact φ.left_inv hq2
  show q.2 = segre (scaleBlock k0 (Ψ' (segre (γ (φ.symm q.1))) 0)⁻¹ (γ (φ.symm q.1)))
  rw [hsymm_q, segre_scaleBlock, hs', ← hE]
  simp [hq3]
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
