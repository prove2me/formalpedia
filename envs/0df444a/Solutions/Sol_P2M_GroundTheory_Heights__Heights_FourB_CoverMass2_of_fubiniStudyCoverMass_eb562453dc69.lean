-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverMass2_of_fubiniStudyCoverMass_eb562453dc69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:21.188603+00:00
-- url     : https://prove2.me/submissions/20fc2eaf-a1e9-4a85-ade3-c9093dff042f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open OpenSetChart
namespace GroundTheory.Heights₂.Heights.FourB
namespace CoverMass2
theorem _root_.solution (hA : FubiniStudyCoverMass.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement := by
  intro D M Z z δ hB
  obtain ⟨hM, hZ, hz, hmaps, hcov, hfib⟩ := hB
  rcases M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hZc : Zᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      rw [h, Measure.measure_univ_eq_zero] at hZ
      exact NeZero.ne (volume : Measure (Fin D → ℂ)) hZ
    obtain ⟨w, hw⟩ := hZc
    have h1 := hfib w hw
    have h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅ := by simp
    rw [h0, Set.encard_empty] at h1
    have hδ : δ = 0 := by exact_mod_cast h1.symm
    subst hδ
    simp
  ·
    have hδ : δ ≠ 0 := by
      intro h0
      have h1 := hfib (z x₀) (hmaps hx₀)
      have hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀} := ⟨hx₀, rfl⟩
      rw [h0, Nat.cast_zero, Set.encard_eq_zero] at h1
      rw [h1] at hmem
      exact hmem

    have hZcl : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨-, U, hwU, hU, -, H, hH⟩ := hcov w hw
      obtain ⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by
        rw [← Set.encard_pos, hfib w hw]
        exact_mod_cast Nat.pos_of_ne_zero hδ
      let i : (fun x : M => z x) ⁻¹' {w} := ⟨⟨x, hxM⟩, hxw⟩
      refine ⟨U, fun v hv => ?_, hU, hwU⟩
      have h1 : v = z (H.symm (⟨v, hv⟩, i)).1 := by
        simpa using hH (H.symm (⟨v, hv⟩, i))
      rw [h1]
      exact hmaps (H.symm (⟨v, hv⟩, i)).1.2

    have han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M := fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)
    let A := atlas hM x₀ hx₀
    let q : M → Fin D → ℂ := fun x => z x
    let u : M → ℝ := fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)
    have hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M := by
      refine contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum
        fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn
          (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)
      positivity
    have hu : A.Smooth u := by
      intro j
      refine (hsm.mono Set.inter_subset_left).congr fun y hy => ?_
      show u (retract x₀ hx₀ y) = _
      simp only [u, q, retract_of_mem hx₀ hy.1]
    have hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ := by
      refine ⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ,
        ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩
      · intro x
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
          fun _ _ => analyticOnNhd_const, ?_⟩
        ext y
        simp
      · simp
      · intro i j y hy
        exact ((han i) y hy.1).congr
          (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)
      · have hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ := by
          ext x
          simpa using hmaps x.2
        exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
      · intro w hw
        rw [← hfib w hw, ← Subtype.val_injective.encard_image]
        congr 1
        ext y
        simp [q, and_comm]
      · intro x y _
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩
        intro v _
        simp [LocPot.ofFun, u]
    have key := (hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2
    rw [maMeasure_univ] at key
    rw [← key]
    refine setLIntegral_congr_fun hM.measurableSet fun y hy => ?_
    show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)
    congr 1
    refine maDens_congr_germ' fun _ => ?_
    filter_upwards [hM.mem_nhds hy] with y' hy'
    simp only [u, q, retract_of_mem hx₀ hy']
    ring
end CoverMass2
end GroundTheory.Heights₂.Heights.FourB
