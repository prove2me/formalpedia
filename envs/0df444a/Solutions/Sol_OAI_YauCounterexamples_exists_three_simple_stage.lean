-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_simple_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:19:35.318514+00:00
-- url     : https://prove2.me/submissions/8831fffd-89c0-4dca-b8ee-7bc11b2b2170

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_three_exact_stage
import Theorems.Thm_OAI_YauCounterexamples_three_pin_near

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma matrix_iteratedFDeriv_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {A : E → Matrix ι κ ℝ} {x : E} (hA : ContDiffAt ℝ ∞ A x)
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => A y i j) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ m A x‖ ≤ ε := by
  apply ContinuousMultilinearMap.opNorm_le_bound hε
  intro v
  have hp := Finset.prod_nonneg (fun k (_ : k ∈ Finset.univ) => norm_nonneg (v k))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε hp)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε hp)).mpr
  intro j
  let L : Matrix ι κ ℝ →L[ℝ] ℝ := (ContinuousLinearMap.proj j : (κ → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix ι κ ℝ →L[ℝ] (κ → ℝ))
  have he : iteratedFDeriv ℝ m (fun y => A y i j) x v = (iteratedFDeriv ℝ m A x v) i j :=
    congrArg (fun T => T v) (L.iteratedFDeriv_comp_left hA (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
  rw [← he]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb i j) hp)

variable [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.matrixJetInst1
attribute [local instance] OAI.YauCounterexamples.matrixJetInst2
attribute [local instance] OAI.YauCounterexamples.matrixJetInst3
attribute [local instance] OAI.YauCounterexamples.matrixJetInst4
attribute [local instance] OAI.YauCounterexamples.matrixJetMatrixMapNorm
lemma metricMatrixForm_iterated_jet_bound
    {A : E → Matrix (CoordIndex E) (CoordIndex E) ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ m (fun y => A y i j) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ m (fun y => metricMatrixForm (A y)) x‖ ≤ ‖metricMatrixFormCLM (E:=E)‖*ε := by
  classical
  let L := metricMatrixFormCLM (E:=E)
  change ‖iteratedFDeriv ℝ m (L ∘ A) x‖ ≤ ‖L‖*ε
  erw [L.iteratedFDeriv_comp_left hA (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (matrix_iteratedFDeriv_norm_le hA m hε hb) (norm_nonneg L))
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartTensorNeighborhoodInst1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst1
attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst2
attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst3
attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst4
omit [T2Space M] in
lemma chartTensorOfMetric_sub (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (g h : SmoothMetric E M)
    (hg : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x)
    (hh : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → h.inner x = g₀.inner x) :
    ((chartTensorOfMetric g₀ p K ht h hh - chartTensorOfMetric g₀ p K ht g hg) : E → MetricForm E) =
      fun y => metricMatrixForm (metricCoefficients h p y - metricCoefficients g p y) := by
  funext y
  change (chartMetricForm h p y-chartMetricForm g₀ p y) -
    (chartMetricForm g p y-chartMetricForm g₀ p y) = _
  rw [sub_sub_sub_cancel_right]
  exact (map_sub (metricMatrixFormCLM (E:=E)) _ _).symm

omit [T2Space M] in
lemma chartTensorRepresentation_neighborhood (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (g : SmoothMetric E M)
    (hg : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x)
    (U : Set 𝓓_{K}(E,MetricForm E)) (hU : U ∈ 𝓝 (chartTensorOfMetric g₀ p K ht g hg)) :
    IsSmoothNeighborhood g {h | ∀ hh, chartTensorOfMetric g₀ p K ht h hh ∈ U} := by
  classical
  let : NormedAddCommGroup
      (Matrix (CoordIndex E) (CoordIndex E) ℝ →L[ℝ] CoordinateForm E) :=
    inferInstanceAs (NormedAddCommGroup
      ((CoordIndex E → CoordIndex E → ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)))
  obtain ⟨s,r,hr,hs⟩ := (ContDiffMapSupportedIn.withSeminorms ℝ E (MetricForm E) ⊤ K).mem_nhds_iff _ _ |>.mp hU
  let C : ℝ := max ‖metricMatrixFormCLM (E:=E)‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let ε := r/(2*C)
  have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hC)
  let test (m : ℕ) (i j : CoordIndex E) : CoordinateTest E M :=
    ⟨p,K,K.isCompact,ht ▸ subset_univ _,m,i,j⟩
  let tests := s.toList.flatMap (fun m => (Finset.univ : Finset (CoordIndex E × CoordIndex E)).toList.map
    (fun ij => test m ij.1 ij.2))
  refine ⟨tests,ε,hε,?_⟩
  intro h hh hhe
  apply hs
  rw [Seminorm.mem_ball]
  apply Seminorm.finset_sup_apply_lt hr
  intro m hm
  have htst (i j : CoordIndex E) : test m i j ∈ tests := by
    simp only [tests,List.mem_flatMap,Finset.mem_toList,List.mem_map]
    exact ⟨m,hm,⟨(i,j),Finset.mem_univ _,rfl⟩⟩
  have hb : (ContDiffMapSupportedIn.seminorm ℝ E (MetricForm E) ⊤ K m)
      (chartTensorOfMetric g₀ p K ht h hhe - chartTensorOfMetric g₀ p K ht g hg) ≤
      ‖metricMatrixFormCLM (E:=E)‖*ε := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (mul_nonneg (norm_nonneg _) hε.le) _ _).mpr
    intro y hy
    change ‖iteratedFDeriv ℝ m (fun y =>
      chartTensorOfMetric g₀ p K ht h hhe y - chartTensorOfMetric g₀ p K ht g hg y) y‖ ≤ _
    rw [show (fun y => chartTensorOfMetric g₀ p K ht h hhe y -
      chartTensorOfMetric g₀ p K ht g hg y) = fun y =>
        metricMatrixForm (metricCoefficients h p y - metricCoefficients g p y) from
      chartTensorOfMetric_sub g₀ p K ht g h hg hhe]
    refine metricMatrixForm_iterated_jet_bound ?_ m hε.le ?_
    · apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact ((contDiffOn_metricCoefficient h p i j).contDiffAt (ht ▸ univ_mem)).sub
        ((contDiffOn_metricCoefficient g p i j).contDiffAt (ht ▸ univ_mem))
    · intro i j
      exact (hh (test m i j) (htst i j) y hy).le
  apply lt_of_le_of_lt hb
  calc
    ‖metricMatrixFormCLM (E:=E)‖*ε ≤ C*ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
    _ = r/2 := by dsimp [ε]; field_simp
    _ < r := by linarith
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma three_regular_nonzero (u : ThreeManifold → ℝ) (hreg : ThreeRegular u) : u≠0 := by
  intro hu
  have hh := hreg threeProfileCenter (by rw [hu]; rfl)
  apply hh
  simp only [hu,Function.comp_def,Pi.zero_apply]
  exact fderiv_const_apply 0

local instance threeStageFormNorm_rcea348_1 : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeStageFormSpace_rcea348_1 : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
theorem exists_three_simple_stage_oai :
    ∃ R : ℝ, 0<R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ r : ℝ, 0 < r → ∀ hrR : r<R/2, (hext : ThreeExterior g r) →
      ∀ A : ℝ, 0 ≤ A → ∀ M : ℕ, ∀ U : Set (ThreeTensor R), IsOpen U →
      threeTensorOf R g (hext.mono hrR.le)∈U →
      ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric ThreeModel ThreeManifold,
      ∃ c : ℝ, 0 < c ∧ ∃ hcR : c<R/2, ∃ he : ThreeExterior h c,
      threeTensorOf R h (he.mono hcR.le)∈U ∧
      ∃ u : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u≠0 ∧
        (∀ q, -laplaceBeltrami h u q=productFrequency k*u q) ∧
        ThreeRegular u ∧ ThreeSimple h u (productFrequency k) ∧ ThreeSignAbove R u (A*(k:ℝ)) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hstage⟩ := exists_three_exact_stage
  refine ⟨R,hR,N,hN,h0N,?_⟩
  intro g hg r hr hrR hext A hA M U hU hgU
  let a := (2*r+R/2)/3
  let b := (r+2*(R/2))/3
  have hra : r<a := by dsimp [a]; linarith
  have hab : a<b := by dsimp [a,b]; linarith
  have hbR : b<R/2 := by dsimp [b]; linarith
  let eg := threeExterior_support hrR.le hext
  let V : Set (SmoothMetric ThreeModel ThreeManifold) := {h | ∀ eh,
    chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
      (three_chart_target threeProfileCenter) h eh∈U}
  have hV : IsSmoothNeighborhood g V := chartTensorRepresentation_neighborhood threeBackgroundMetric
    threeProfileCenter (threeTensorSupport R) (three_chart_target threeProfileCenter) g eg U (hU.mem_nhds hgU)
  obtain ⟨e,hbe,heR,I,hIa,partition,hpart,ell,hell,ε,hε,hpacket⟩ :=
    hstage g hg a b (hr.trans hra) hab hbR (threeNormalInv '' closedBall 0 r)
      (threeNormalInv_closedBall_closed r) (image_mono (closedBall_subset_closedBall hra.le))
      (fun q hq v w => congrArg (fun T => T v w) (hext q hq)) A V hV
  have ht : Tendsto (fun m : ℕ => 4*m+1) atTop atTop :=
    tendsto_atTop_mono (fun m => show m ≤ 4*m+1 by omega) tendsto_id
  obtain ⟨m,⟨hm,hmM⟩,hm1⟩ := ((ht.eventually hpacket).and (eventually_ge_atTop M) |>.and (eventually_ge_atTop 1)).exists
  obtain ⟨ĝ,hĝN,u,hu,hue,hreg,hout,hscore⟩ := hm
  have heĝ : ThreeExterior ĝ e := by
    intro q hq
    ext v w
    exact ((hout q hq).1 v w).trans (congrArg (fun T => T v w)
      (hext q (fun hh => hq (image_mono (closedBall_subset_closedBall (hra.trans (hab.trans hbe)).le) hh))))
  let eĝ := threeExterior_support heR.le heĝ
  have hĝU := hĝN eĝ
  have hu0 : u≠0 := three_regular_nonzero u hreg
  let c := (e+R/2)/2
  have hec : e < c := by dsimp [c]; linarith
  have hcR : c<R/2 := by dsimp [c]; linarith
  obtain ⟨h,he,hhU,hhe,hsimple⟩ := three_pin_near ĝ hR hclean (hr.trans (hra.trans (hab.trans hbe)))
    hec hcR heĝ hm1 u hu hu0 hue (fun q hq => (hout q hq).2) U hU hĝU
  refine ⟨4*m+1,by omega,by omega,h,c,hr.trans (hra.trans (hab.trans (hbe.trans hec))),hcR,he,hhU,
    u,hu,hu0,hhe,hreg,hsimple,I,hIa.trans (closedBall_subset_closedBall (hab.trans hbR).le),
    partition,hpart,(fun j => ε/(productWaveFrequency (4*m+1)*ell j.val)),?_,?_⟩
  · intro j
    exact div_pos hε (mul_pos (lt_of_lt_of_le (by positivity : (0:ℝ)<(4*m+1:ℕ))
      (productWaveFrequency_bounds (k:=4*m+1) (by omega)).1) (hell j.val j.property))
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (productWaveFrequency_bounds (k:=4*m+1) (by omega)).1 hA)).trans_lt hscore
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_simple_stage_oai := @OAI.YauCounterexamples.exists_three_simple_stage_oai
