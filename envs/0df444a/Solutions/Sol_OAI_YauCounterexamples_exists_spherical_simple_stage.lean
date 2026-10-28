-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_simple_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:10:51.255153+00:00
-- url     : https://prove2.me/submissions/23849363-68c1-4a58-bfbf-9d1134c527e4

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_exact_stage
import Theorems.Thm_OAI_YauCounterexamples_spherical_pin_near

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
lemma spherical_regular_nonzero (u : Sphere 3 → ℝ)
    (hreg : ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm)
      ((chartAt (Euclidean 3) q) q) ≠ 0) : u ≠ 0 := by
  intro hu
  have hh := hreg sourcePole (by rw [hu]; rfl)
  apply hh
  simp only [hu,Function.comp_def,Pi.zero_apply]
  exact fderiv_const_apply 0
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_SphericalFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

local instance sphericalStageFormNorm_r2b12d0_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalStageFormSpace_r2b12d0_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem exists_spherical_simple_stage_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {R t s r a b c : ℝ} (hR : (1/5:ℝ) ≤ R) (hRt : R<t) (hts : t < s) (hsr : s < r)
    (hra : r<a) (hab : a<b) (hbc : b < c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g R)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (M : ℕ) (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (by linarith) hext) ∈ U) :
    ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric (Euclidean 3) (Sphere 3),
      ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      ∃ u : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
        (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
        SphericalRegular u ∧ SphericalSimple h u (sphereFrequency k) ∧
        SphericalSignAbove u (A*(k:ℝ)) := by
  classical
  have hRc : R < c := hRt.trans (hts.trans (hsr.trans (hra.trans (hab.trans hbc))))
  have hRsmall : R≤3/10 := (hRc.trans hc).le
  let eg := sphericalExterior_support hRsmall hext
  let N : Set (SmoothMetric (Euclidean 3) (Sphere 3)) := {h | ∀ eh,
    chartTensorOfMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole) h eh ∈ U}
  have hN : IsSmoothNeighborhood g N := chartTensorRepresentation_neighborhood g₀ sourcePole
    sphericalTensorSupport (sphere_chart_target sourcePole) g eg U (hU.mem_nhds hgU)
  obtain ⟨partition,hpart,ell,hell,ε,hε,hpacket⟩ := exists_spherical_exact_stage g₀ hg₀ g hg
    (hR.trans hRt.le) hts hsr hra hab (hbc.trans hc)
    (isClosed_le (sphericalRadius_continuous _ _) continuous_const)
    (fun q hq => (show sphericalRadius sourceAxisOne sourceAxisTwo q≤R from hq).trans_lt hRt)
    (fun q hq v w => congrArg (fun T => T v w) (hext q (lt_of_not_ge hq))) hmetric A N hN
  obtain ⟨k,⟨hkpacket,hkM⟩,hk3⟩ := (hpacket.and (eventually_ge_atTop M) |>.and (eventually_ge_atTop 3)).exists
  obtain ⟨ĝ,hĝN,u,hu,hue,hreg,hout,hscore⟩ := hkpacket
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have heĝ : sphericalExterior g₀ ĝ b := by
    intro q hq
    ext v w
    exact ((hout q hq).1 v w).trans (congrArg (fun T => T v w) (hext q (by linarith)))
  let eĝ := sphericalExterior_support (hbc.trans hc).le heĝ
  have hĝU := hĝN eĝ
  have hu0 : u ≠ 0 := spherical_regular_nonzero u hreg
  obtain ⟨h,he,hhU,hhe,hsimple⟩ := spherical_pin_near g₀ hg₀ ĝ hb0 hbc hc heĝ k hk3 u hu hu0 hue
    (fun q hq => (hout q hq).2) U hU hĝU
  refine ⟨k,hkM,hk3,h,he,hhU,u,hu,hu0,hhe,hreg,hsimple,partition,hpart,(fun j => ε/((k:ℝ)*ell j.val)),?_,hscore⟩
  intro j
  exact div_pos hε (mul_pos (by exact_mod_cast (show 0<k by omega)) (hell j.val j.property))
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_simple_stage_oai := @OAI.YauCounterexamples.exists_spherical_simple_stage_oai
