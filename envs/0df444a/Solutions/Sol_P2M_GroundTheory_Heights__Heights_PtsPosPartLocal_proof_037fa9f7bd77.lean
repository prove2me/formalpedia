-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_proof_037fa9f7bd77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:29.365056+00:00
-- url     : https://prove2.me/submissions/c4e1a4f7-24e9-4d4a-b8a2-b52a4553278f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_smul_1b1c64fe724f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_eq_smul_nrm_72fe6565cf56
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiable_map_874caf0283f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_nrm_d1e525da6af0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_mem_fibre_55d042252cc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_ptsPosDens_eq_9e6f21b19b8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
import Theorems.Thm_ReciprocityTheory_AnForm_A_lintegral_image_eq_lintegral_normSq_det_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pot_contDiffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


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
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open PtsPosPartLocal
namespace GroundTheory.Heights₂.Heights
namespace PtsPosPartLocal
theorem _root_.solution : PtsPosPartLocal.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g z hP _ _ hL _ hg _ hs hs'
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨y₀, γ₀, U, N, hU, hN, hq₀, hseg₀, hγ₀, hNp⟩ := exists_local hs
  obtain ⟨y₀', γ₀', U', N', hU', hN', hq₀', hseg₀', hγ₀', hNp'⟩ := exists_local hs'

  have hz0 : Ψ (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀ y₀ (hNp _ hq₀).1).2.2 0
    rw [hseg₀, h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hz0' : Ψ' (segre z) 0 ≠ 0 := by
    intro h0
    have h := congrFun (hγ₀' y₀' (hNp' _ hq₀').1).2.2 0
    rw [hseg₀', h0, inv_zero, zero_smul, map_zero] at h
    simp at h
  have hN0 : (crd Ψ (segre z), nrm Ψ (segre z)) ∈ N := by
    have h1 : Ψ (nrm Ψ (segre z)) = Fin.cons 1 y₀ := by
      rw [← (hγ₀ y₀ (hNp _ hq₀).1).2.2, hseg₀]
      rfl
    have h2 : crd Ψ (segre z) = y₀ := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀
  have hN0' : (crd Ψ' (segre z), nrm Ψ' (segre z)) ∈ N' := by
    have h1 : Ψ' (nrm Ψ' (segre z)) = Fin.cons 1 y₀' := by
      rw [← (hγ₀' y₀' (hNp' _ hq₀').1).2.2, hseg₀']
      rfl
    have h2 : crd Ψ' (segre z) = y₀' := by
      funext i
      simp [crd, h1]
    rw [h2]
    exact hq₀'

  set WS : Set (((k : K) → ι k) → ℂ) := {w | Ψ w 0 ≠ 0 ∧ Ψ' w 0 ≠ 0 ∧ (crd Ψ w, nrm Ψ w) ∈ N ∧
    (crd Ψ' w, nrm Ψ' w) ∈ N'} with hWSdef
  have hWS : IsOpen WS := by
    refine isOpen_iff_mem_nhds.mpr fun w hw => ?_
    have c0 : ContinuousAt (fun w => Ψ w 0) w := (differentiableAt_coord w 0).continuousAt
    have c0' : ContinuousAt (fun w => Ψ' w 0) w := (differentiableAt_coord w 0).continuousAt
    filter_upwards [c0.eventually_ne hw.1, c0'.eventually_ne hw.2.1,
      ((continuousAt_crd hw.1).prodMk (continuousAt_nrm hw.1)).eventually (hN.mem_nhds hw.2.2.1),
      ((continuousAt_crd hw.2.1).prodMk (continuousAt_nrm hw.2.1)).eventually (hN'.mem_nhds hw.2.2.2)]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hWSs : ∀ t : ℂ, t ≠ 0 → ∀ w, t • w ∈ WS ↔ w ∈ WS := by
    intro t ht w
    have e1 : ∀ Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), Φ (t • w) 0 ≠ 0 ↔ Φ w 0 ≠ 0 :=
      fun Φ => by simp [map_smul, ht]
    simp only [hWSdef, Set.mem_setOf_eq, e1, crd_smul ht, nrm_smul ht]
  refine ⟨segre ⁻¹' WS, hWS.preimage continuous_segre, ⟨hz0, hz0', hN0, hN0'⟩,
    fun c z' hc => ?_, fun E _ hE hEW => ?_⟩
  · show segre (fun p => c p.1 * z' p) ∈ WS ↔ segre z' ∈ WS
    rw [segre_smul]
    exact hWSs _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k) _

  have hl : ∀ y, ptsPosDens P Ψ (pot L) (E.indicator g) y = (U ∩ γ₀ ⁻¹' E).indicator
      (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y :=
    ptsPosDens_eq hL hg hE hU hγ₀ hN hNp fun z' hz' _ => (hEW hz').2.2.1
  have hl' : ∀ y, ptsPosDens P Ψ' (pot L) (E.indicator g) y = (U' ∩ γ₀' ⁻¹' E).indicator
      (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y :=
    ptsPosDens_eq hL hg hE hU' hγ₀' hN' hNp' fun z' hz' _ => (hEW hz').2.2.2
  simp_rw [hl, hl']

  have hγ₀an : AnalyticOnNhd ℂ γ₀ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ₀ y hy).1
  have hγ₀'an : AnalyticOnNhd ℂ γ₀' U' := analyticOnNhd_of_diffOn hU' fun y hy => (hγ₀' y hy).1
  set Φ : (Fin e → ℂ) → Fin (e + 1) → ℂ := fun y => Ψ (segre (γ₀' y)) with hΦdef
  have hΦan : AnalyticOnNhd ℂ Φ U' := analyticOnNhd_of_diffOn hU' fun y hy =>
    (differentiable_map (Ψ := Ψ) _).comp y (segre_differentiableAt (hγ₀' y hy).1)
  set O' := U' ∩ γ₀' ⁻¹' (segre ⁻¹' WS) with hO'def
  have hO' : IsOpen O' := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hγ₀' y hy).1.continuousAt.continuousWithinAt) hU' (hWS.preimage continuous_segre)
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y => crd Ψ (segre (γ₀' y)) with hτdef
  have hτeq : τ = fun y (i : Fin e) => (Φ y 0)⁻¹ * Φ y i.succ := funext fun y => crd_eq _
  have hτan : AnalyticOnNhd ℂ τ O' := fun y hy => by
    rw [hτeq]
    exact analyticAt_pi_iff.mpr fun i =>
      (AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy.2.1).mul
        (analyticAt_pi_iff.mp (hΦan y hy.1) i.succ)
  have hτU : ∀ y ∈ O', τ y ∈ U ∧ segre (γ₀ (τ y)) = nrm Ψ (segre (γ₀' y)) := fun y hy => by
    have hq : (τ y, nrm Ψ (segre (γ₀' y))) ∈ N := hy.2.2.2.1
    obtain ⟨h1, h2⟩ := hNp _ hq
    exact ⟨h1, (h2 (nrm_mem_fibre hPh k0 (hγ₀' y hy.1).2.1 hy.2.1)).symm⟩

  set c : (Fin e → ℂ) → K → ℂ := fun y => Function.update (fun _ => (1 : ℂ)) k0 (Φ y 0)⁻¹ with hcdef
  have hc_ne : ∀ y, Φ y 0 ≠ 0 → ∀ k, c y k ≠ 0 := by
    intro y h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∀ y, ∏ k, c y k = (Φ y 0)⁻¹ := fun y => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  set γt : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y => bsmul (c y) (γ₀' y) with hγtdef
  have hγtseg : ∀ y, segre (γt y) = nrm Ψ (segre (γ₀' y)) := fun y => by
    show segre (fun p => c y p.1 * γ₀' y p) = _
    rw [segre_smul, hprod]
    rfl

  have hcmp : ∀ y ∈ O', (γ₀ (τ y) ∈ E ↔ γ₀' y ∈ E) ∧ g (γ₀ (τ y)) = g (γ₀' y) ∧
      maDensity (fun j y' => pot L j (γ₀' y')) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det := by
    intro y hy
    obtain ⟨hτy, hsy⟩ := hτU y hy
    have hblk : ∀ k, ∃ i, γ₀ (τ y) ⟨k, i⟩ ≠ 0 := (hγ₀ _ hτy).2.1.1
    have hseg : segre (γ₀ (τ y)) = segre (γt y) := hsy.trans (hγtseg y).symm
    have hy0 : Φ y 0 ≠ 0 := hy.2.1
    have hmemE : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
        ((fun p => c p.1 * z p) ∈ E) = (z ∈ E) := fun c z hc => propext (hE c z hc)
    have hE1 : (γt y ∈ E) = (γ₀ (τ y) ∈ E) := apply_eq_of_segre_eq hmemE hblk hseg
    have hE2 : (γt y ∈ E) = (γ₀' y ∈ E) := hmemE (c y) (γ₀' y) (hc_ne y hy0)
    have hg1 : g (γt y) = g (γ₀ (τ y)) := apply_eq_of_segre_eq hg hblk hseg
    have hg2 : g (γt y) = g (γ₀' y) := hg (c y) (γ₀' y) (hc_ne y hy0)
    refine ⟨by rw [← hE1, hE2], by rw [← hg1, hg2], ?_⟩
    have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := fun k => by
      by_cases hk : k = k0
      · subst hk
        simp only [hcdef, Function.update_self]
        exact AnalyticAt.inv (f := fun y => Φ y 0) (analyticAt_pi_iff.mp (hΦan y hy.1) 0) hy0
      · simp only [hcdef, Function.update_of_ne hk]
        exact analyticAt_const
    have hγ'a : AnalyticAt ℂ γ₀' y := hγ₀'an y hy.1
    have hγta : AnalyticAt ℂ γt y :=
      analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ'a p)
    have hτa : AnalyticAt ℂ τ y := hτan y hy
    have hγτa : AnalyticAt ℂ (fun y' => γ₀ (τ y')) y := (hγ₀an _ hτy).comp hτa
    have h1 : maDensity (fun j y' => pot L j (γt y')) y = maDensity (fun j y' => pot L j (γ₀' y')) y :=
      maDensity_bsmul (c := fun k y' => c y' k) hL hγ'a (hγ₀' y hy.1).2.1.1 hca (fun k => hc_ne y hy0 k)
        (Eventually.of_forall fun y' => rfl)
    have h2 : maDensity (fun j y' => pot L j (γt y')) y =
        maDensity (fun j y' => pot L j (γ₀ (τ y'))) y :=
      maDensity_eq_of_segre hL hγτa hγta hblk (by
        filter_upwards [hO'.mem_nhds hy] with y' hy'
        exact (hτU y' hy').2.trans (hγtseg y').symm)
    have h3 : maDensity (fun j y' => pot L j (γ₀ (τ y'))) y =
        maDensity (fun j y' => pot L j (γ₀ y')) (τ y) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun j y' => pot L j (γ₀ y')) τ y hτa fun j =>
        pot_contDiffAt (hL j) (hγ₀an _ hτy) hblk
    rw [← h1, h2, h3]

  have hback : ∀ y ∈ O', y = crd Ψ' (nrm Ψ (segre (γ₀' y))) := by
    intro y hy
    have h1 : crd Ψ' (segre (γ₀' y)) = y := crd_of_eq (hγ₀' y hy.1).2.2
    have h2 := crd_smul (Ψ := Ψ') hy.2.1 (nrm Ψ (segre (γ₀' y)))
    rw [← eq_smul_nrm hy.2.1, h1] at h2
    exact h2
  have hτinj : Set.InjOn τ O' := by
    intro y₁ h₁ y₂ h₂ h
    have e₁ := (hτU y₁ h₁).2
    have e₂ := (hτU y₂ h₂).2
    rw [h] at e₁
    rw [hback y₁ h₁, hback y₂ h₂, ← e₁, ← e₂]

  have hsupp : ∀ y ∈ U ∩ γ₀ ⁻¹' E, y ∈ τ '' O' := by
    intro y hy
    have hz₁ := hγ₀ y hy.1
    have hw₁ : segre (γ₀ y) ∈ WS := hEW hy.2
    have hfib := nrm_mem_fibre (Ψ := Ψ') hPh k0 hz₁.2.1 hw₁.2.1
    obtain ⟨hy'U, hy'seg⟩ := hNp' _ hw₁.2.2.2
    have hseg' := hy'seg hfib
    refine ⟨crd Ψ' (segre (γ₀ y)), ⟨hy'U, ?_⟩, ?_⟩
    · show segre (γ₀' (crd Ψ' (segre (γ₀ y)))) ∈ WS
      rw [← hseg']
      exact (hWSs _ (inv_ne_zero hw₁.2.1) _).2 hw₁
    · show crd Ψ (segre (γ₀' (crd Ψ' (segre (γ₀ y))))) = y
      rw [← hseg']
      show crd Ψ ((Ψ' (segre (γ₀ y)) 0)⁻¹ • segre (γ₀ y)) = y
      rw [crd_smul (inv_ne_zero hw₁.2.1)]
      exact crd_of_eq hz₁.2.2
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
          (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => hsupp y ?_).symm
        by_contra h
        exact hy (by simp [Set.indicator_of_notMem h])
    _ = ∫⁻ y in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ y).det) *
          ENNReal.ofReal ((U ∩ γ₀ ⁻¹' E).indicator
            (fun y => max (g (γ₀ y) * maDensity (fun j y' => pot L j (γ₀ y')) y) 0) (τ y)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ y in O', ENNReal.ofReal ((U' ∩ γ₀' ⁻¹' E).indicator
          (fun y => max (g (γ₀' y) * maDensity (fun j y' => pot L j (γ₀' y')) y) 0) y) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun y hy => ?_
        obtain ⟨hE', hg', hma⟩ := hcmp y hy
        by_cases hyE : γ₀' y ∈ E
        · rw [Set.indicator_of_mem (show τ y ∈ U ∩ γ₀ ⁻¹' E from ⟨(hτU y hy).1, hE'.2 hyE⟩),
            Set.indicator_of_mem (show y ∈ U' ∩ γ₀' ⁻¹' E from ⟨hy.1, hyE⟩)]
          rw [hg', hma, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (show τ y ∉ U ∩ γ₀ ⁻¹' E from fun hm => hyE (hE'.1 hm.2)),
            Set.indicator_of_notMem (show y ∉ U' ∩ γ₀' ⁻¹' E from fun hm => hyE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun y hy => ?_
        have hyE : y ∈ U' ∩ γ₀' ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        exact ⟨hyE.1, hEW hyE.2⟩
end PtsPosPartLocal
end GroundTheory.Heights₂.Heights
