-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:45.149818+00:00
-- url     : https://prove2.me/submissions/727c1294-1a1a-42c6-89da-168c2526af0f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ImportsAlt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dense_Mset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_holo_flat_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_holo_restrict_open
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isCoveringMapOn_of_proper
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_iteratedFDeriv_eq_zero_of_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ne_zero_of_overlap_ne_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_norm_section_ratio_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ratio_pow_chart_independent
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_vanishing_order_transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hNORM : NORMAll.{u} n) : ZEROStatement n Y ι La := by
  intro A L N w w0 s De m Nsec hconn hD hF hDe hwC hN hNC hvan
  obtain ⟨C2, hC2⟩ := hwC
  obtain ⟨C1, hC1⟩ := hNC
  set MS := A.Mset w0 s De with hMS
  have hw0 : A.IsSec L w0 := hD.isSection_denom
  have hs := hD.sec_s
  let Uf : Y → ℂ := fun y => Nsec (A.pick y) y / w0 (A.pick y) y ^ m

  have hHolo : Holo n (flatStein A hD hF).z (fun y : MS => Uf y) := by
    refine (holo_flat_iff A hD hF Uf).2 (fun i => ?_)
    have hNd := hN.1 i
    have hwd := hw0.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at hNd hwd
    have hne : ∀ v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' MS,
        ((w0 i ∘ (A.chart i).symm) v) ^ m ≠ 0 := fun v hv =>
      pow_ne_zero _ (ne_zero_of_overlap_ne_zero A L w0 hw0 i (A.pick _) _ ((A.chart i).map_target hv.1)
        (A.mem_pick _) hv.2.1)
    refine ((hNd.mono Set.inter_subset_left).mul
      (((hwd.mono Set.inter_subset_left).pow m).inv hne)).congr (fun v hv => ?_)
    simp only [Function.comp_apply, Uf]
    rw [ratio_pow_chart_independent A L m Nsec w0 hN hw0 (A.pick _) i _ (A.mem_pick _)
      ((A.chart i).map_target hv.1), div_eq_mul_inv]
    rfl
  let U : Set (V n) := {v : V n | MvPolynomial.eval (fun i => v i) De ≠ 0}
  have hUo : IsOpen U := isOpen_ne_fun
    ((MvPolynomial.continuous_eval (p := De)).comp (by fun_prop)) continuous_const

  have key : ∀ x0 : MS, Uf x0 = 0 := by
    intro x0
    have hM'o : IsOpen (connectedComponent x0) := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨e, hxe, -⟩ := hF.localHomeo x
      have hTo : IsOpen (connectedComponentIn e.target (e x)) :=
        e.open_target.connectedComponentIn
      have hxT : e x ∈ connectedComponentIn e.target (e x) :=
        mem_connectedComponentIn (e.map_source hxe)
      have hTs : connectedComponentIn e.target (e x) ⊆ e.target := connectedComponentIn_subset _ _
      have hW : IsOpen (e.symm '' connectedComponentIn e.target (e x)) := by
        rw [e.symm_image_eq_source_inter_preimage hTs]
        exact e.isOpen_inter_preimage hTo
      have hWc : IsPreconnected (e.symm '' connectedComponentIn e.target (e x)) :=
        isPreconnected_connectedComponentIn.image _ (e.continuousOn_symm.mono hTs)
      have hxW : x ∈ e.symm '' connectedComponentIn e.target (e x) := ⟨e x, hxT, e.left_inv hxe⟩
      have hsub : e.symm '' connectedComponentIn e.target (e x) ⊆ connectedComponent x0 := by
        rw [connectedComponent_eq hx]
        exact hWc.subset_connectedComponent hxW
      exact Filter.mem_of_superset (hW.mem_nhds hxW) hsub
    have : Nonempty (connectedComponent x0) := ⟨⟨x0, mem_connectedComponent⟩⟩
    have : ConnectedSpace (connectedComponent x0) :=
      Subtype.connectedSpace isConnected_connectedComponent
    let z' : connectedComponent x0 → V n := fun x => A.zmap w0 s (x : MS)
    have hzU : ∀ x, z' x ∈ U := fun x => (x : MS).2.2
    have hloc : IsLocalHomeomorph z' :=
      hF.localHomeo.comp hM'o.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hprop : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z' ⁻¹' K) := by
      intro K hK hKU
      have h1 := hF.proper K hK (fun v hv => hKU hv)
      have h2 : IsCompact (Subtype.val ⁻¹' (A.zmap w0 s ⁻¹' K) : Set MS) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
        exact h1
      have h3 : IsCompact (Subtype.val ⁻¹' (Subtype.val ⁻¹' (A.zmap w0 s ⁻¹' K) : Set MS) :
          Set (connectedComponent x0)) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_comm]
        exact h2.inter_right isClosed_connectedComponent
      exact h3
    obtain ⟨hcov, hfin⟩ := isCoveringMapOn_of_proper z' U hUo hzU hloc hprop
    have hH' := holo_restrict_open _ _ hHolo (connectedComponent x0) hM'o
    have hbd : ∀ x : connectedComponent x0, ‖Uf ((x : MS) : Y)‖ ≤
        Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖z' x‖ ^ 2) ^ ((m : ℝ) / 2) := fun x =>
      norm_section_ratio_le A L m w w0 s Nsec C1 C2 hC1 hC2 _ (x : MS).2.1
    have hv' : ∀ x : connectedComponent x0, z' x = 0 →
        VanishesBeyond n z' (fun x : connectedComponent x0 => Uf ((x : MS) : Y)) x m := by
      intro x hx e he hxe k hk
      have hyS : ((x : MS) : Y) ∈ A.zeroSet s := by
        intro k'
        have h := congrArg (fun v : V n => v k') hx
        simp only [z', zmap, PiLp.toLp_apply, PiLp.zero_apply] at h
        exact (div_eq_zero_iff.1 h).resolve_right (x : MS).2.1
      obtain ⟨C, hC⟩ := vanishing_order_transfer A L m w0 s Nsec hw0 hs hN ((x : MS) : Y) (x : MS).2.1
        (hF.deriv_ne _ (x : MS).2) (hvan _ hyS)
        (fun t : connectedComponent x0 => ((t : MS) : Y))
        (continuous_subtype_val.comp continuous_subtype_val) e he x hxe rfl
      have hex : z' x = e x := he hxe
      rw [hex]
      exact iteratedFDeriv_eq_zero_of_bound _ e.target (e x) e.open_target (e.map_source hxe)
        (hH' e he) m ⟨C, hC⟩ k hk
    have hzero := hNORM (connectedComponent x0) z' De
      (fun x : connectedComponent x0 => Uf ((x : MS) : Y)) (Real.sqrt (max C1 0 * |C2| ^ m)) m
      hDe hcov hzU hfin ‹_› hH' hbd hv'
    exact congrFun hzero ⟨x0, mem_connectedComponent⟩

  intro i y hy
  have hzM : ∀ y' ∈ (A.chart i).source ∩ MS, Nsec i y' = 0 := by
    intro y' hy'
    have h := key ⟨y', hy'.2⟩
    simp only [Uf] at h
    have h0 : Nsec (A.pick y') y' = 0 :=
      (div_eq_zero_iff.1 h).resolve_right (pow_ne_zero _ hy'.2.1)
    rw [hN.2 i (A.pick y') y' (Set.mem_univ _) hy'.1 (A.mem_pick y'), h0, mul_zero]
  have hcont : ContinuousOn (Nsec i) (A.chart i).source := by
    have hNd := hN.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at hNd
    refine (hNd.continuousOn.comp (A.chart i).continuousOn (fun y hy => (A.chart i).map_source hy)).congr
      (fun y hy => ?_)
    simp [(A.chart i).left_inv hy]
  have hEq := Set.EqOn.of_subset_closure (f := Nsec i) (g := fun _ => (0 : ℂ)) hzM hcont
    continuousOn_const Set.inter_subset_left
    ((dense_Mset A hD hF).open_subset_closure_inter (A.chart i).open_source)
  exact hEq hy
end ReciprocityTheory.L2DbarEstimates.Y
