-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_of_found_5deccf67aa12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:10.718052+00:00
-- url     : https://prove2.me/submissions/66780f9c-b5e1-439c-93e1-f192a7ebf5c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_weight
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjPotMassPos
theorem _root_.solution (hD : ProjPotDens.Statement) : ProjPotMassPos.Statement := by
  intro K _ ι _ P J n R V BV hH hV C hC hCF
  obtain ⟨x, hxC, hxF⟩ := hCF
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have hPot : ∀ _ : Fin n, IsPotential BV (multiprojPot R V) := fun _ =>
    ProjPotMassPos.isPotential_multiprojPot hH
  have hCont := locDensCont BV (fun _ => multiprojPot R V) hPot
  have hDs := hD K ι P J n R V BV hH
  have hMI : MIntegrable BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ)) := by
    intro i Kc hK hKc
    have hS : IsOpen ((BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C) :=
      (BV.chart i).isOpen_inter_preimage_symm hC
    refine IntegrableOn.congr_fun ((((hCont i).mono hK).integrableOn_compact hKc).indicator
      hS.measurableSet) (fun y hy => ?_) hKc.measurableSet
    by_cases hyC : (BV.chart i).symm y ∈ C
    · rw [Set.indicator_of_mem (show y ∈ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        ⟨hK hy, hyC⟩), Set.indicator_of_mem hyC, one_mul]
    · rw [Set.indicator_of_notMem (show y ∉ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        fun h => hyC h.2), Set.indicator_of_notMem hyC, zero_mul]
  have hPn : Nonempty (ChartPartition BV) := existsPartition BV
  unfold mInt
  rw [dif_pos hPn]
  unfold integralWith
  set χ := hPn.some
  have hnn : ∀ i, ∀ y ∈ (BV.chart i).target, 0 ≤ χ.χ i ((BV.chart i).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart i).symm y) *
        locDens BV (fun _ => multiprojPot R V) i y := fun i y hy =>
    mul_nonneg (mul_nonneg (χ.nonneg i _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (hDs i y hy).1
  obtain ⟨j, hj⟩ : ∃ j, 0 < χ.χ j x := by
    by_contra h
    push Not at h
    have h1 := χ.sum_eq_one x
    have h2 : ∑ j, χ.χ j x ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith
  refine Finset.sum_pos' (fun i _ => setIntegral_nonneg (BV.chart i).open_target.measurableSet
    (hnn i)) ⟨j, Finset.mem_univ _, ?_⟩
  have hxj : x ∈ (BV.chart j).source := χ.tsupport_subset j (subset_tsupport _ hj.ne')
  set u := BV.chart j x
  have hut : u ∈ (BV.chart j).target := (BV.chart j).map_source hxj
  have hsu : (BV.chart j).symm u = x := (BV.chart j).left_inv hxj
  have hχc : ContinuousAt (fun y => χ.χ j ((BV.chart j).symm y)) u := by
    have h := (χ.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt ((BV.chart j).open_target.mem_nhds hut)
  have hev : ∀ᶠ y in 𝓝 u, y ∈ (BV.chart j).target ∧ 0 < χ.χ j ((BV.chart j).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart j).symm y) *
        locDens BV (fun _ => multiprojPot R V) j y := by
    have hC' : ∀ᶠ y in 𝓝 u, (BV.chart j).symm y ∈ C :=
      ((BV.chart j).continuousAt_symm hut).preimage_mem_nhds (by rw [hsu]; exact hC.mem_nhds hxC)
    have hD' : ∀ᶠ y in 𝓝 u, 0 < locDens BV (fun _ => multiprojPot R V) j y :=
      ((hCont j).continuousAt ((BV.chart j).open_target.mem_nhds hut)).eventually
        (lt_mem_nhds ((hDs j u hut).2 (by rw [hsu]; exact hxF)))
    have hχ' : ∀ᶠ y in 𝓝 u, 0 < χ.χ j ((BV.chart j).symm y) :=
      hχc.eventually (lt_mem_nhds (show 0 < χ.χ j ((BV.chart j).symm u) by rw [hsu]; exact hj))
    filter_upwards [(BV.chart j).open_target.mem_nhds hut, hC', hD', hχ'] with y h1 h2 h3 h4
    refine ⟨h1, mul_pos (mul_pos h4 ?_) h3⟩
    rw [Set.indicator_of_mem h2]
    exact one_pos
  obtain ⟨W, hWs, hWo, huW⟩ := mem_nhds_iff.mp hev
  have hint := integrableOn_weight BV χ (fun _ => multiprojPot R V) _ hMI j
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem (BV.chart j).open_target.measurableSet (hnn j)) hint]
  refine lt_of_lt_of_le (hWo.measure_pos volume ⟨u, huW⟩) (measure_mono fun y hy => ?_)
  exact ⟨(hWs hy).2.ne', (hWs hy).1⟩
end ProjPotMassPos
end GroundTheory.Heights₂.Heights.Targets
