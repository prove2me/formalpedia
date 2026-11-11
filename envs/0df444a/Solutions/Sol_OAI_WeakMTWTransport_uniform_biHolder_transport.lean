-- Prove2me | solution 1 for OAI.WeakMTWTransport.uniform_biHolder_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:38:03.700763+00:00
-- url     : https://prove2.me/submissions/edc83995-da03-4776-9eb2-e10425fe441a

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A020
import Definitions.Def_OAIQ232A030
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_class_power

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

lemma cost_nonneg (x y : M) : 0 ≤ cost x y := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

variable [CompactSpace M] [Nonempty M]

lemma dualPair_contact_left {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) : ∃ y, contactGap u v x y = 0 := by
  rw [huv.1]
  exact cTransform_gap_zero hv x

omit [CompactSpace M] [Nonempty M] in
lemma contactGap_symm (u v : M → ℝ) (x y : M) :
    contactGap u v x y = contactGap v u y x := by
  dsimp [contactGap]
  rw [cost_symm x y]
  ring

lemma dualPair_contact_right {u v : M → ℝ} (hu : Continuous u)
    (huv : IsCostDualPair u v) (y : M) : ∃ x, contactGap u v x y = 0 := by
  obtain ⟨x, hx⟩ := dualPair_contact_left hu ⟨huv.2, huv.1⟩ y
  exact ⟨x, (contactGap_symm u v x y).trans hx⟩

lemma homeomorph_of_contact_bounds {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) (huv : IsCostDualPair u v) {alpha C : ℝ}
    (ha : 0 < alpha) (hC : 0 ≤ C)
    (hf : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤ C * dist x x' ^ alpha)
    (hr : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' ≤ C * dist y y' ^ alpha) :
    ∃ T : M ≃ₜ M, (∀ x, contactGap u v x (T x) = 0) ∧
      (∀ x x', dist (T x) (T x') ≤ C * dist x x' ^ alpha) ∧
      (∀ y y', dist (T.symm y) (T.symm y') ≤ C * dist y y' ^ alpha) := by
  classical
  choose T hT using dualPair_contact_left hv huv
  choose S hS using dualPair_contact_right hu huv
  have hST : Function.LeftInverse S T := by
    intro x
    apply dist_eq_zero.mp
    have hh := hr (S (T x)) x (T x) (T x) (hS (T x)) (hT x)
    exact le_antisymm (by simpa only [dist_self, Real.zero_rpow ha.ne', mul_zero] using hh)
      dist_nonneg
  have hTS : Function.RightInverse S T := by
    intro y
    apply dist_eq_zero.mp
    have hh := hf (S y) (S y) (T (S y)) y (hT (S y)) (hS y)
    exact le_antisymm (by simpa only [dist_self, Real.zero_rpow ha.ne', mul_zero] using hh)
      dist_nonneg
  have hf' (x x') : dist (T x) (T x') ≤ C * dist x x' ^ alpha :=
    hf x x' (T x) (T x') (hT x) (hT x')
  have hr' (y y') : dist (S y) (S y') ≤ C * dist y y' ^ alpha :=
    hr (S y) (S y') y y' (hS y) (hS y')
  have cont_of_bound (f : M → M)
      (h : ∀ x x', dist (f x) (f x') ≤ C * dist x x' ^ alpha) : Continuous f := by
    have holder : HolderWith ⟨C, hC⟩ ⟨alpha, ha.le⟩ f := by
      intro x x'
      simp only [edist_dist]
      have hh := ENNReal.ofReal_le_ofReal (h x x')
      rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg ha.le] at hh
      rw [show ENNReal.ofReal C = ENNReal.ofNNReal (NNReal.mk C hC) from
        ENNReal.ofReal_coe_nnreal (p := NNReal.mk C hC)] at hh
      exact hh
    exact holder.continuous ha
  exact ⟨⟨⟨T, S, hST, hTS⟩, cont_of_bound T hf', cont_of_bound S hr'⟩,
    hT, hf', hr'⟩

omit [CompactSpace M] [Nonempty M] in

lemma contactGap_le_of_contact {u v : M → ℝ} {D : ℝ≥0}
    (hu : LipschitzWith D u) (hD : ∀ x y : M, dist x y ≤ D)
    {x x' y : M} (hcontact : contactGap u v x' y = 0) :
    contactGap u v x y ≤ (2 * D) * dist x x' := by
  have hdu := hu.dist_le_mul x x'
  rw [Real.dist_eq, abs_le] at hdu
  have hdc := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y)).2
  dsimp [contactGap] at hcontact ⊢
  linarith

omit [CompactSpace M] [Nonempty M] in

lemma contact_section_zero_diameter {u v : M → ℝ} {x y y' : M} {K alpha r0 : ℝ}
    (ha : 0 < alpha) (hr0 : 0 < r0)
    (hsection : ∀ r, 0 < r → r < r0 →
      ∀ z ∈ gapSection u v x r, ∀ z' ∈ gapSection u v x r,
        dist z z' ≤ K * r ^ alpha)
    (hy : contactGap u v x y = 0) (hy' : contactGap u v x y' = 0) :
    dist y y' = 0 := by
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 r0) := by
    rw [closure_Ioo hr0.ne]
    exact ⟨le_rfl, hr0.le⟩
  have hc : Continuous (fun r : ℝ => K * r ^ alpha) :=
    continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hh := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := dist y y')) hc.continuousWithinAt
    (fun r hr => hsection r hr.1 hr.2 y (by simpa [gapSection, hy] using hr.1.le)
      y' (by simpa [gapSection, hy'] using hr.1.le))
  apply le_antisymm _ dist_nonneg
  simpa only [Real.zero_rpow ha.ne', mul_zero] using hh

omit [CompactSpace M] [Nonempty M] in

lemma global_contact_bound_of_local {u v : M → ℝ} {D K alpha delta : ℝ}
    (hD : ∀ y y' : M, dist y y' ≤ D) (hK : 0 ≤ K) (ha : 0 < alpha)
    (hdelta : 0 < delta)
    (hlocal : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' < delta → dist y y' ≤ K * dist x x' ^ alpha) :
    ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤ (K + max D 0 / delta ^ alpha) * dist x x' ^ alpha := by
  intro x x' y y' hy hy'
  have hrpow : 0 ≤ dist x x' ^ alpha := Real.rpow_nonneg dist_nonneg _
  have hdap : 0 < delta ^ alpha := Real.rpow_pos_of_pos hdelta _
  by_cases hd : dist x x' < delta
  · exact (hlocal x x' y y' hy hy' hd).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
        (div_nonneg (le_max_right D 0) hdap.le)) hrpow)
  · have hmono : delta ^ alpha ≤ dist x x' ^ alpha :=
      Real.rpow_le_rpow hdelta.le (le_of_not_gt hd) ha.le
    calc
      dist y y' ≤ max D 0 := (hD y y').trans (le_max_left D 0)
      _ = (max D 0 / delta ^ alpha) * delta ^ alpha := by
        rw [div_mul_cancel₀ _ hdap.ne']
      _ ≤ (max D 0 / delta ^ alpha) * dist x x' ^ alpha :=
        mul_le_mul_of_nonneg_left hmono (div_nonneg (le_max_right D 0) hdap.le)
      _ ≤ (K + max D 0 / delta ^ alpha) * dist x x' ^ alpha :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hrpow

omit [CompactSpace M] [Nonempty M] in

lemma contact_bound_of_section_bound {u v : M → ℝ} {D : ℝ≥0}
    (hu : LipschitzWith D u) (hD : ∀ x y : M, dist x y ≤ D)
    {K alpha r0 : ℝ} (hK : 0 ≤ K) (ha : 0 < alpha) (hr0 : 0 < r0)
    (hsection : ∀ x r, 0 < r → r < r0 →
      ∀ y ∈ gapSection u v x r, ∀ y' ∈ gapSection u v x r,
        dist y y' ≤ K * r ^ alpha) :
    ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist y y' ≤
        (K * (2 * D + 1) ^ alpha + D / (r0 / (2 * D + 1)) ^ alpha) *
          dist x x' ^ alpha := by
  let L : ℝ := 2 * D + 1
  have hL : 0 < L := by dsimp [L] <;> positivity
  have hlocal : ∀ x x' y y', contactGap u v x y = 0 → contactGap u v x' y' = 0 →
      dist x x' < r0 / L → dist y y' ≤ (K * L ^ alpha) * dist x x' ^ alpha := by
    intro x x' y y' hy hy' hd
    by_cases heq : x = x'
    · subst x'
      rw [contact_section_zero_diameter ha hr0 (hsection x) hy hy', dist_self,
        Real.zero_rpow ha.ne', mul_zero]
    · have hdist : 0 < dist x x' := dist_pos.mpr heq
      have hr : 0 < L * dist x x' := mul_pos hL hdist
      have hr' : L * dist x x' < r0 := by
        have hm := (lt_div_iff₀ hL).mp hd
        nlinarith
      have hgap : contactGap u v x y' ≤ L * dist x x' :=
        (contactGap_le_of_contact hu hD hy').trans
          (mul_le_mul_of_nonneg_right (by dsimp [L] <;> linarith) hdist.le)
      have hh := hsection x (L * dist x x') hr hr' y
        (by simpa [gapSection, hy] using hr.le) y' hgap
      rw [Real.mul_rpow hL.le hdist.le, ← mul_assoc] at hh
      exact hh
  have hh := global_contact_bound_of_local hD
    (mul_nonneg hK (Real.rpow_nonneg hL.le _)) ha (div_pos hr0 hL) hlocal
  simpa only [L, max_eq_left D.coe_nonneg] using hh

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

omit [MetricSpace M] [BorelSpace M] in

lemma integral_densityMeasure {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) (f : M → ℝ) :
    (∫ x, f x ∂densityMeasure vol rho) = ∫ x, f x * rho x ∂vol := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hrho.1.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [density_nonnegative hlam hrho] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

variable [CompactSpace M]

lemma integrable_continuous_compact {mu : Measure M} [IsFiniteMeasure mu]
    {f : M → ℝ} (hf : Continuous f) : Integrable f mu := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC x (mem_univ x)))

lemma integrable_cost_map {mu : Measure M} [IsFiniteMeasure mu]
    {S : M → M} (hS : Measurable S) : Integrable (fun x => cost x (S x)) mu := by
  have hcost : Continuous (fun z : M × M => cost z.1 z.2) := by
    exact ((continuous_fst.dist continuous_snd).pow 2).div_const 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcost.continuousOn
  exact Integrable.of_bound
    ((hcost.stronglyMeasurable.comp_measurable (measurable_id.prodMk hS)).aestronglyMeasurable) C
    (Filter.Eventually.of_forall (fun x => hC (x, S x) (mem_univ _)))

lemma integrable_comp_transport {mu nu : Measure M} [IsFiniteMeasure nu]
    {f : M → ℝ} {S : M → M} (hf : Continuous f) (hS : Measurable S)
    (hpush : Measure.map S mu = nu) : Integrable (fun x => f (S x)) mu := by
  have hh := integrable_continuous_compact (mu := nu) hf
  rw [← hpush, integrable_map_measure hf.aestronglyMeasurable hS.aemeasurable] at hh
  exact hh

lemma integral_contactGap_transport {mu nu : Measure M} [IsFiniteMeasure mu]
    [IsFiniteMeasure nu] {u v : M → ℝ} {S : M → M}
    (hu : Continuous u) (hv : Continuous v) (hS : Measurable S)
    (hpush : Measure.map S mu = nu) :
    (∫ x, contactGap u v x (S x) ∂mu) =
      (∫ x, u x ∂mu) + (∫ x, cost x (S x) ∂mu) + (∫ y, v y ∂nu) := by
  have hiu := integrable_continuous_compact (mu := mu) hu
  have hic := integrable_cost_map (mu := mu) hS
  have hiv := integrable_comp_transport hv hS hpush
  have hadd : (∫ x, contactGap u v x (S x) ∂mu) =
      (∫ x, u x + cost x (S x) ∂mu) + ∫ x, v (S x) ∂mu := by
    simpa only [contactGap, Pi.add_apply] using integral_add (hiu.add hic) hiv
  rw [hadd, integral_add hiu hic]
  congr 1
  rw [← hpush, integral_map_of_stronglyMeasurable hS hv.stronglyMeasurable]

lemma isOptimalMap_of_dual_contact {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ} {T : M → M}
    (hlam : 0 < lam) (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    (hu : Continuous u) (hv : Continuous v)
    (hgap : ∀ x y, 0 ≤ contactGap u v x y)
    (hT : Measurable T) (hpush : Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1)
    (hcontact : ∀ x, contactGap u v x (T x) = 0) :
    IsOptimalMap vol rho0 rho1 T := by
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨hT, hpush, ?_⟩
  intro S hS hpushS
  rw [← integral_densityMeasure hlam hrho0, ← integral_densityMeasure hlam hrho0]
  have hzero : (∫ x, contactGap u v x (T x) ∂densityMeasure vol rho0) = 0 := by
    simp only [hcontact, integral_zero]
  have hnonneg : 0 ≤ ∫ x, contactGap u v x (S x) ∂densityMeasure vol rho0 :=
    integral_nonneg (fun x => hgap x (S x))
  rw [integral_contactGap_transport hu hv hT hpush] at hzero
  rw [integral_contactGap_transport hu hv hS hpushS] at hnonneg
  linarith

lemma optimalMap_ae_eq_of_singleton_contacts {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ} {T S : M → M}
    (hlam : 0 < lam) (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    (hu : Continuous u) (hv : Continuous v)
    (hgap : ∀ x y, 0 ≤ contactGap u v x y)
    (hT : Measurable T) (hpush : Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1)
    (hcontact : ∀ x, contactGap u v x (T x) = 0)
    (hsingle : ∀ x y, contactGap u v x y = 0 → y = T x)
    (hS : IsOptimalMap vol rho0 rho1 S) :
    S =ᵐ[densityMeasure vol rho0] T := by
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  have hzero : (∫ x, contactGap u v x (T x) ∂densityMeasure vol rho0) = 0 := by
    simp only [hcontact, integral_zero]
  have hle := hS.2.2 T hT hpush
  rw [← integral_densityMeasure hlam hrho0, ← integral_densityMeasure hlam hrho0] at hle
  rw [integral_contactGap_transport hu hv hT hpush] at hzero
  have hnonneg : ∀ᵐ x ∂densityMeasure vol rho0, 0 ≤ contactGap u v x (S x) :=
    Filter.Eventually.of_forall (fun x => hgap x (S x))
  have hgapint : Integrable (fun x => contactGap u v x (S x)) (densityMeasure vol rho0) :=
    ((integrable_continuous_compact hu).add (integrable_cost_map hS.1)).add
      (integrable_comp_transport hv hS.1 hS.2.1)
  have hgapzero : (∫ x, contactGap u v x (S x) ∂densityMeasure vol rho0) = 0 := by
    have hnn := integral_nonneg_of_ae hnonneg
    rw [integral_contactGap_transport hu hv hS.1 hS.2.1] at hnn ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hgapint).mp hgapzero
  filter_upwards [hae] with x hx
  exact hsingle x (S x) hx

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

lemma cTransform_zero : cTransform (fun _ : M => (0 : ℝ)) = fun _ => 0 := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff continuous_const]
    intro y
    linarith [cost_nonneg x y]
  · have h := cTransform_gap_nonneg (v := fun _ : M => (0 : ℝ)) continuous_const x x
    simpa [contactGap, cost] using h

lemma boundedCTransform_apply (v : M →ᵇ ℝ) (x : M) :
    boundedCTransform v x = cTransform v x := rfl

lemma boundedCTransform_nonexpansive : LipschitzWith 1 (boundedCTransform (M := M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  rw [Real.dist_eq, abs_le]
  have hbound (a b : M →ᵇ ℝ) : cTransform a x - cTransform b x ≤ dist a b := by
    rw [sub_le_iff_le_add, cTransform_le_iff a.continuous]
    intro y
    have hg := cTransform_gap_nonneg b.continuous x y
    have hd := BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) y
    rw [Real.dist_eq, abs_le] at hd
    dsimp [contactGap] at hg
    linarith [hd.1]
  constructor
  · have hh := hbound w v
    rw [dist_comm w v] at hh
    change -dist v w ≤ cTransform v x - cTransform w x
    linarith
  · exact hbound v w

omit [Nonempty M] in

lemma isCompact_bounded_lipschitz (D : ℝ≥0) (H : ℝ) :
    IsCompact {f : M →ᵇ ℝ | LipschitzWith D f ∧ ∀ x, |f x| ≤ H} := by
  let A : Set (M →ᵇ ℝ) := {f | LipschitzWith D f ∧ ∀ x, |f x| ≤ H}
  have hclosed : IsClosed A := by
    apply IsClosed.inter
    · exact (isClosed_setOfPred_lipschitzWith (α := M) (β := ℝ) D).preimage
        (BoundedContinuousFunction.continuous_coe : Continuous (fun f : M →ᵇ ℝ => (f : M → ℝ)))
    · change IsClosed {f : M →ᵇ ℝ | ∀ x, |f x| ≤ H}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro x
      exact isClosed_le ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe).abs
        continuous_const
  apply BoundedContinuousFunction.arzela_ascoli₂ (Icc (-H) H) isCompact_Icc A hclosed
  · intro f x hf
    exact abs_le.mp (hf.2 x)
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro eps heps
    refine ⟨eps / ((D : ℝ) + 1), by positivity, ?_⟩
    intro y hy f
    have h := f.property.1.dist_le_mul y x
    have hstrict : (D : ℝ) * dist y x < eps := by
      have hy' := hy
      have hD : 0 ≤ (D : ℝ) := D.coe_nonneg
      have he := (lt_div_iff₀ (show 0 < (D : ℝ) + 1 by positivity)).mp hy'
      nlinarith [dist_nonneg (x := y) (y := x)]
    simpa only [dist_comm] using h.trans_lt hstrict

lemma isClosed_normalizedDualPairs (x0 : M) : IsClosed (normalizedDualPairs x0) := by
  apply IsClosed.inter
  · exact isClosed_eq (((continuous_apply x0).comp
      BoundedContinuousFunction.continuous_coe).comp continuous_fst) continuous_const
  · apply IsClosed.inter
    · exact isClosed_eq (boundedCTransform_nonexpansive.continuous.comp continuous_snd) continuous_fst
    · exact isClosed_eq (boundedCTransform_nonexpansive.continuous.comp continuous_fst) continuous_snd

lemma normalizedDualPairs_nonempty (x0 : M) : (normalizedDualPairs x0).Nonempty := by
  refine ⟨(0, 0), rfl, ?_, ?_⟩ <;>
    apply BoundedContinuousFunction.ext <;>
    intro x <;>
    exact congrFun cTransform_zero x

lemma normalizedDualPairs_bounds {D : ℝ≥0} (hD : ∀ x y : M, dist x y ≤ D)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ normalizedDualPairs x0) :
    (LipschitzWith D uv.1 ∧ ∀ x, |uv.1 x| ≤ (D : ℝ) ^ 2) ∧
      (LipschitzWith D uv.2 ∧ ∀ x, |uv.2 x| ≤ (D : ℝ) ^ 2) := by
  have hu : (uv.1 : M → ℝ) = cTransform uv.2 := congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.2.1.symm
  have hv : (uv.2 : M → ℝ) = cTransform uv.1 := congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.2.2.symm
  have hLu : LipschitzWith D uv.1 := by
    rw [hu]
    exact cTransform_lipschitz uv.2.continuous hD
  have hLv : LipschitzWith D uv.2 := by
    rw [hv]
    exact cTransform_lipschitz uv.1.continuous hD
  have hbu (x : M) : |uv.1 x| ≤ (D : ℝ) ^ 2 := by
    have hh := hLu.dist_le_mul x x0
    rw [h.1, Real.dist_eq, sub_zero] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (hD x x0) D.coe_nonneg])
  refine ⟨⟨hLu, hbu⟩, hLv, ?_⟩
  intro x
  rw [abs_le, hv]
  constructor
  · have hh := cTransform_gap_nonneg uv.1.continuous x x0
    rw [contactGap, h.1, cost] at hh
    have hdist := hD x x0
    have hd0 : 0 ≤ dist x x0 := dist_nonneg
    nlinarith [D.coe_nonneg, sq_nonneg ((D : ℝ) - dist x x0)]
  · rw [cTransform_le_iff uv.1.continuous]
    intro y
    have hb := (abs_le.mp (hbu y)).1
    linarith [cost_nonneg x y]

lemma isCompact_normalizedDualPairs (x0 : M) : IsCompact (normalizedDualPairs x0) := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M), Metric.diam_nonneg⟩
  have hD (x y : M) : dist x y ≤ D :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  refine ((isCompact_bounded_lipschitz D ((D : ℝ) ^ 2)).prod
    (isCompact_bounded_lipschitz D ((D : ℝ) ^ 2))).of_isClosed_subset
      (isClosed_normalizedDualPairs x0) ?_
  intro uv huv
  exact normalizedDualPairs_bounds hD huv

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma integral_boundedContinuous_lipschitz (mu : Measure M) [IsProbabilityMeasure mu] :
    LipschitzWith 1 (fun f : M →ᵇ ℝ => ∫ x, f x ∂mu) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have heq : (∫ x, f x ∂mu) - (∫ x, g x ∂mu) = ∫ x, (f - g) x ∂mu :=
    (integral_sub (f.integrable mu) (g.integrable mu)).symm
  rw [heq]
  exact (f - g).norm_integral_le_norm mu

omit [CompactSpace M] [Nonempty M] in
lemma continuous_dualObjective (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] : Continuous (dualObjective mu nu) :=
  ((integral_boundedContinuous_lipschitz mu).continuous.comp continuous_fst).add
    ((integral_boundedContinuous_lipschitz nu).continuous.comp continuous_snd)

lemma exists_minimizing_normalizedDualPair (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (x0 : M) :
    ∃ uv ∈ normalizedDualPairs x0, IsMinOn (dualObjective mu nu) (normalizedDualPairs x0) uv := by
  exact (isCompact_normalizedDualPairs x0).exists_isMinOn (normalizedDualPairs_nonempty x0)
    (continuous_dualObjective mu nu).continuousOn

omit [MeasurableSpace M] [BorelSpace M] in
lemma normalizeDualPair_mem (x0 : M) (v : M →ᵇ ℝ) :
    normalizeDualPair x0 v ∈ normalizedDualPairs x0 := by
  let a := boundedCTransform v
  change (a x0 + -a x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => cTransform a y + a x0) x = a x + -a x0
    rw [cTransform_add_const (continuous_cTransform a.continuous)]
    have hh := congrFun (cTransform_triple v.continuous) x
    change cTransform (cTransform a) x = a x at hh
    exact (congrArg (fun t : ℝ => t - a x0) hh).trans (by ring)
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => a y + -a x0) x = cTransform a x + a x0
    rw [cTransform_add_const a.continuous]
    ring

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

lemma dualObjective_normalize_le (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (x0 : M) (u v : M →ᵇ ℝ)
    (h : ∀ x y, 0 ≤ contactGap u v x y) :
    dualObjective mu nu (normalizeDualPair x0 v) ≤ dualObjective mu nu (u,v) := by
  rw [normalizeDualPair, dualObjective_add_constants]
  apply add_le_add
  · apply integral_mono (boundedCTransform v |>.integrable mu) (u.integrable mu)
    intro x
    rw [boundedCTransform_apply, cTransform_le_iff v.continuous]
    intro y
    have hh := h x y
    dsimp [contactGap] at hh
    linarith
  · apply integral_mono (boundedCTransform (boundedCTransform v) |>.integrable nu)
      (v.integrable nu)
    exact cTransform_cTransform_le v.continuous

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_twoMountain (x y₀ y₁ : M) : Continuous (twoMountain x y₀ y₁) :=
  (continuous_const.sub (continuous_cost_left y₀)).max (continuous_const.sub (continuous_cost_left y₁))

omit [CompactSpace M] [Nonempty M] in
lemma twoMountain_self (x y₀ y₁ : M) : twoMountain x y₀ y₁ x=0 := by simp [twoMountain]

lemma cTransform_eq_of_lower_mountain {f : M → ℝ} (hf : Continuous f)
    {x y : M} (hx : f x=0) (hm : ∀ z, cost x y-cost z y≤f z) :
    cTransform f y = -cost x y := by
  apply le_antisymm
  · rw [cTransform_le_iff hf]
    intro z
    rw [cost_symm y z]
    linarith [hm z]
  · have hh := cTransform_gap_nonneg hf y x
    rw [contactGap,cost_symm y x,hx] at hh
    linarith

lemma cTransform_twoMountain_left (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₀ = -cost x y₀ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_left _ _)

lemma cTransform_twoMountain_right (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₁ = -cost x y₁ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_right _ _)

lemma cTransform_cTransform_twoMountain (x y₀ y₁ : M) :
    cTransform (cTransform (twoMountain x y₀ y₁))=twoMountain x y₀ y₁ := by
  funext z
  apply le_antisymm (cTransform_cTransform_le (continuous_twoMountain x y₀ y₁) z)
  apply max_le
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₀
    rw [contactGap,cTransform_twoMountain_left] at h
    linarith
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₁
    rw [contactGap,cTransform_twoMountain_right] at h
    linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalMetricCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
local notation "𝒥" => 𝓘(ℝ,E)

lemma exists_lipschitzOn_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ball (extChartAt 𝓘(ℝ,E) x x) r ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,E) x).symm
        (ball (extChartAt 𝓘(ℝ,E) x x) r) := by
  let (y : E) : ENorm (TangentSpace 𝒥 y →L[ℝ]
      TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)) :=
    inferInstanceAs (ENorm (E →L[ℝ] TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝒥 x
  obtain ⟨r,hrpos,hr⟩ : ∃ r > 0,
      ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} := by
    have hh := inter_mem (extChartAt_target_mem_nhdsWithin (I := 𝒥) x) hC
    have hh' : (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} ∈
        𝓝 (extChartAt 𝒥 x x) := by
      simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hh ⊢
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    exact Metric.mem_nhds_iff.mp hh'
  refine ⟨C,r,hrpos,fun y hy => (hr hy).1,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt 𝒥 x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝒥 x).target ∩
      {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)}) := by
    simp only [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap,η]
    exact ((convex_ball _ _).segment_subset hu hv).trans hr
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hh : riemannianEDist 𝒥 ((extChartAt 𝒥 x).symm u) ((extChartAt 𝒥 x).symm v) ≤
      pathELength 𝒥 γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝒥)]
  apply hh.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hd1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hd 1)
  rw [hd1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in

lemma hausdorff_nondifferentiable_chart_image_null {u : M → ℝ} {K C : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) {r : ℝ}
    (hr : ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target)
    (hC : LipschitzOnWith C (extChartAt 𝒥 x).symm (ball (extChartAt 𝒥 x x) r)) :
    (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ (extChartAt 𝒥 x).symm '' ball (extChartAt 𝒥 x x) r ∧
        ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  let B : Set E := {z | z ∈ ball (extChartAt 𝒥 x x) r ∧
    ¬ DifferentiableAt ℝ (u ∘ (extChartAt 𝒥 x).symm) z}
  have hB : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E) B = 0 := by
    have hh := (hu.comp_lipschitzOnWith hC).ae_differentiableWithinAt_of_mem
      (μ := (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E))
    apply measure_mono_null _ (ae_iff.mp hh)
    intro z hz hdiff
    exact hz.2 ((hdiff hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))
  have himage : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      ((extChartAt 𝒥 x).symm '' B) = 0 := by
    apply le_antisymm ?_ (by positivity)
    have hh := (hC.mono (show B ⊆ ball (extChartAt 𝒥 x x) r from fun _ h => h.1)).hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    simpa only [hB,mul_zero] using hh
  apply measure_mono_null _ himage
  rintro y ⟨⟨z,hz,rfl⟩,hnot⟩
  refine ⟨z,⟨hz,?_⟩,rfl⟩
  intro hdiff
  apply hnot
  have hsrc : (extChartAt 𝒥 x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝒥 x).map_target (hr hz)
  have hD : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (u ∘ (extChartAt 𝒥 x).symm)
      ((extChartAt 𝒥 x) ((extChartAt 𝒥 x).symm z)) := by
    rw [(extChartAt 𝒥 x).right_inv (hr hz)]
    exact hdiff.mdifferentiableAt
  have hh := hD.comp ((extChartAt 𝒥 x).symm z)
    (mdifferentiableAt_extChartAt (I := 𝒥) hsrc)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds hsrc] with w hw
  have hw' : w ∈ (extChartAt 𝒥 x).source := by simpa only [extChartAt_source] using hw
  simp only [Function.comp_apply,(extChartAt 𝒥 x).left_inv hw']

lemma exists_nhds_nondifferentiable_null {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) :
    ∃ U ∈ 𝓝 x, (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ U ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  obtain ⟨C,r,hrpos,hr,hC⟩ := exists_lipschitzOn_inverse_chart (E := E) x
  let U := (extChartAt 𝒥 x).source ∩
    (extChartAt 𝒥 x) ⁻¹' ball (extChartAt 𝒥 x x) r
  have hU : U ∈ 𝓝 x := by
    apply inter_mem
    · simpa only [extChartAt_source] using chart_source_mem_nhds E x
    · exact (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hrpos)
  refine ⟨U,hU,?_⟩
  apply measure_mono_null _ (hausdorff_nondifferentiable_chart_image_null hu x hr hC)
  intro y hy
  exact ⟨⟨(extChartAt 𝒥 x) y,hy.1.2,(extChartAt 𝒥 x).left_inv hy.1.1⟩,hy.2⟩

lemma lipschitz_ae_mdifferentiable [CompactSpace M] {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M),
      MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u x := by
  classical
  choose U hUnhds hUnull using exists_nhds_nondifferentiable_null (E := E) hu
  obtain ⟨s,_,hs⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hUnhds x)
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ x ∈ (s : Set M),
    {y | y ∈ U x ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y})
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy⟩
  · exact (measure_biUnion_null_iff s.countable_toSet).mpr (fun x _ => hUnull x)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ManifoldLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [MetricSpace M] [ChartedSpace F M]
  [IsManifold 𝓘(ℝ,F) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsContinuousRiemannianBundle F (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsRiemannianManifold 𝓘(ℝ,F) M]

lemma contMDiffAt_exists_lipschitzOn {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith C f U := by
  let χ := extChartAt 𝓘(ℝ,F) (f x)
  have hχ : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) 1 χ (f x) :=
    contMDiffAt_extChartAt
  obtain ⟨D,V,hV,hD⟩ := (((hχ.comp x hf).contDiffAt)).exists_lipschitzOnWith
  obtain ⟨C,r,hr,hsub,hC⟩ := exists_lipschitzOn_inverse_chart (E := F) (f x)
  let U := V ∩ f ⁻¹' (χ.source ∩ χ ⁻¹' ball (χ (f x)) r)
  have hU : U ∈ 𝓝 x := by
    apply inter_mem hV
    apply hf.continuousAt.preimage_mem_nhds
    exact inter_mem (extChartAt_source_mem_nhds (f x))
      (hχ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr))
  refine ⟨C*D,U,hU,?_⟩
  have hmaps : MapsTo (χ ∘ f) U (ball (χ (f x)) r) := fun _ hy => hy.2.2
  have hcomp := hC.comp (hD.mono inter_subset_left) hmaps
  intro y hy z hz
  have hh := hcomp hy hz
  change edist (χ.symm (χ (f y))) (χ.symm (χ (f z))) ≤ _ at hh
  rwa [χ.left_inv hy.2.1,χ.left_inv hz.2.1] at hh

lemma contMDiffOn_exists_lipschitzOn_compact {f : E → M} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x∈K, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, LipschitzOnWith C f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨C,U,hU,hC⟩ := contMDiffAt_exists_lipschitzOn (hf x hx)
  exact ⟨C,U,mem_nhdsWithin_of_mem_nhds hU,hC⟩

end

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma movingNormal_trivialization_exp {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)
      = riemannianExp x p := by
  rw [movingNormal_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hx),
    (extChartAt 𝓘(ℝ,Model n) a).left_inv hx,
    Trivialization.symmL_continuousLinearMapAt]
  change x∈(chartAt (Model n) a).source
  simpa only [extChartAt_source] using hx

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_lipschitz_near_base (R : ℝ) (a : M) :
    ∃ L : ℝ≥0, ∃ K ∈ 𝓝 a, ∀ x∈K, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤R → ‖q‖≤R → dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖ := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  let Bnn : ℝ≥0 := ⟨B,hBpos.le⟩
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let P := (χ '' K) ×ˢ closedBall (0 : Model n) (B*R)
  have hPc : IsCompact P :=
    (hKc.image_of_continuousOn ((continuousOn_extChartAt a).mono (fun x hx => (hKs hx).1))).prod
      (isCompact_closedBall _ _)
  obtain ⟨C,hC⟩ := contMDiffOn_exists_lipschitzOn_compact hPc
    (f := movingNormal a) (fun z hz => (movingNormal_contMDiffAt (by
      obtain ⟨x,hx,hxz⟩ := hz.1
      rw [←hxz]
      exact χ.map_source (hKs hx).1)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨C*Bnn,K,hKn,?_⟩
  intro x hx p q hp hq
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm p).trans (mul_le_mul (hKs hx).2.le hp (norm_nonneg _) hBpos.le)
  have hqP : (χ x,A q)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm q).trans (mul_le_mul (hKs hx).2.le hq (norm_nonneg _) hBpos.le)
  have hd := hC.dist_le_mul _ hpP _ hqP
  rw [movingNormal_trivialization_exp (hKs hx).1,movingNormal_trivialization_exp (hKs hx).1] at hd
  have hdist : dist (χ x,A p) (χ x,A q)≤B*‖p-q‖ := by
    rw [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,dist_eq_norm,←map_sub]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  calc
    _≤(C:ℝ)*dist (χ x,A p) (χ x,A q) := hd
    _≤(C:ℝ)*(B*‖p-q‖) := mul_le_mul_of_nonneg_left hdist C.coe_nonneg
    _=↑(C*Bnn : ℝ≥0)*‖p-q‖ := by change (C:ℝ)*(B*‖p-q‖)=(C:ℝ)*B*‖p-q‖; ring

lemma exists_uniform_exp_lipschitz (R : ℝ) :
    ∃ L : ℝ≥0, ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤R → ‖q‖≤R → dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖ := by
  classical
  choose L K hKn hK using exp_lipschitz_near_base (n := n) (M := M) R
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  let C : ℝ≥0 := s.sup L
  refine ⟨C,?_⟩
  intro x p q hp hq
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  apply (hK a x hxa p q hp hq).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast (Finset.le_sup (f := L) ha)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Midpoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

lemma power_reduction_exponent {beta : ℝ} (hb : 0 < beta) :
    0 < min beta 1 / 2 ∧ min beta 1 / 2 ≤ 1 := by
  constructor
  · exact div_pos (lt_min hb (by norm_num)) (by norm_num)
  · have := min_le_right beta (1 : ℝ)
    linarith

lemma scalar_power_small {r beta C0 F : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C0) (hF : F ≤ C0 * r ^ beta) :
    F + r ≤ (C0 + 1) * r ^ (min beta 1) := by
  have hpow := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left beta 1)
  have hlin : r ≤ r ^ min beta 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right beta 1)
  nlinarith [mul_le_mul_of_nonneg_left hpow hC]

lemma scalar_sqrt_power_bound {r beta C0 F : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C0) (hF : F ≤ C0 * r ^ beta) :
    Real.sqrt (8 * (F + r)) ≤
      Real.sqrt (8 * (C0 + 1)) * r ^ (min beta 1 / 2) := by
  have hsmall := scalar_power_small hr hr1 hC hF
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 8))
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 8 * (C0 + 1))] at h
  have heq : Real.sqrt (r ^ min beta 1) = r ^ (min beta 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rwa [heq] at h

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
lemma isCompact_gapSection {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
    IsCompact (gapSection u v x r) := by
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_const.add (continuous_cost_right x)).add hv) continuous_const

lemma gapSection_nonempty {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    (gapSection u v x r).Nonempty := by
  obtain ⟨y, hy⟩ := dualPair_contact_left hv huv x
  exact ⟨y, by simpa only [gapSection, mem_ofPred_eq, hy] using hr⟩

lemma sectionOscillation_extrema {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y0 ∈ gapSection u v x r, ∃ y1 ∈ gapSection u v x r,
      (∀ y ∈ gapSection u v x r, v y0 ≤ v y) ∧
      (∀ y ∈ gapSection u v x r, v y ≤ v y1) ∧
      sectionOscillation u v x r = v y1 - v y0 := by
  have hc := isCompact_gapSection (u := u) hv x r
  have hn := gapSection_nonempty hv huv x hr
  obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn hn hv.continuousOn
  obtain ⟨y1, hy1, hmax⟩ := hc.exists_isMaxOn hn hv.continuousOn
  have hleast : IsLeast (v '' gapSection u v x r) (v y0) := by
    refine ⟨mem_image_of_mem v hy0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hgreatest : IsGreatest (v '' gapSection u v x r) (v y1) := by
    refine ⟨mem_image_of_mem v hy1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨y0, hy0, y1, hy1, fun _ hy => hmin hy, fun _ hy => hmax hy,
    by rw [sectionOscillation, hleast.csInf_eq, hgreatest.csSup_eq]⟩

lemma sectionOscillation_le_diam_sq {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation u v x r ≤ Metric.diam (univ : Set M) ^ 2 := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M), Metric.diam_nonneg⟩
  have hD (x y : M) : dist x y ≤ D :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have hLip : LipschitzWith D v := by
    rw [huv.2]
    exact cTransform_lipschitz hu hD
  obtain ⟨y0, _, y1, _, _, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  have hh := hLip.dist_le_mul y1 y0
  rw [Real.dist_eq] at hh
  rw [heq]
  calc
    v y1 - v y0 ≤ |v y1 - v y0| := le_abs_self _
    _ ≤ (D : ℝ) * dist y1 y0 := hh
    _ ≤ (D : ℝ) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left (hD y1 y0) D.coe_nonneg]

variable [MeasurableSpace M] [BorelSpace M]

lemma densityDualClass_nonempty {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity vol lam cap rho) (x0 : M) :
    (densityDualClass vol lam cap x0).Nonempty := by
  obtain ⟨rho, hrho⟩ := hclass
  have := densityMeasure_probability hlam hrho
  let mu := densityMeasure vol rho
  obtain ⟨uv, huv, hmin⟩ := exists_minimizing_normalizedDualPair mu mu x0
  refine ⟨uv, huv, rho, rho, hrho, hrho, ?_⟩
  intro a b hab
  exact (hmin (normalizeDualPair_mem x0 b)).trans
    (dualObjective_normalize_le mu mu x0 a b hab)

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

omit [BorelSpace M] in
lemma classSectionOscillations_bddAbove {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {r : ℝ} (hr : 0 ≤ r) : BddAbove (classSectionOscillations vol lam cap x0 r) := by
  refine ⟨Metric.diam (univ : Set M) ^ 2, ?_⟩
  rintro _ ⟨uv, huv, x, rfl⟩
  exact sectionOscillation_le_diam_sq uv.1.continuous uv.2.continuous
    (densityDualClass_isDual huv) x hr

omit [BorelSpace M] in
lemma sectionOscillation_le_classOscillation {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (huv : uv ∈ densityDualClass vol lam cap x0)
    (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation uv.1 uv.2 x r ≤ classOscillation vol lam cap x0 r := by
  exact le_csSup (classSectionOscillations_bddAbove hr) ⟨uv, huv, x, rfl⟩

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_gap (x0 : M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) (x y : M) :
    contactGap (reverseNormalizedPair x0 uv).1 (reverseNormalizedPair x0 uv).2 x y =
      contactGap uv.1 uv.2 y x := by
  change (uv.2 x + -uv.2 x0) + cost x y + (uv.1 y + uv.2 x0) = _
  rw [contactGap, cost_symm y x]
  ring

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_DoubleMountain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_left {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₀ : p₀∈minimizingVectors x) :
    p₀∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₀,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_left]
  ring

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_right {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₁ : p₁∈minimizingVectors x) :
    p₁∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₁,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_right]
  ring

lemma WeakMTW.double_mountain (hmtw : WeakMTW (n := n) (M := M)) {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x}
    (hp₀ : p₀∈minimizingVectors x) (hp₁ : p₁∈minimizingVectors x)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a • p₀+b • p₁∈minimizingVectors x ∧ ∀ z : M,
      cost x (riemannianExp x (a • p₀+b • p₁))-cost z (riemannianExp x (a • p₀+b • p₁)) ≤
        max (cost x (riemannianExp x p₀)-cost z (riemannianExp x p₀))
          (cost x (riemannianExp x p₁)-cost z (riemannianExp x p₁)) := by
  let f := twoMountain x (riemannianExp x p₀) (riemannianExp x p₁)
  have hp : a • p₀+b • p₁∈convexHull ℝ (activeLogs (n := n) (cTransform f) x) :=
    (convex_convexHull _ _)
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_left hp₀))
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_right hp₁)) ha hb hab
  obtain ⟨hmin,hsup⟩ := hmtw.active_hull_global_support
    (continuous_cTransform (continuous_twoMountain x _ _)) hp
  refine ⟨hmin,?_⟩
  intro z
  have hh := hsup z
  rw [cTransform_cTransform_twoMountain,twoMountain_self] at hh
  change 0+cost x (riemannianExp x (a • p₀+b • p₁))≤
    twoMountain x (riemannianExp x p₀) (riemannianExp x p₁) z+
      cost z (riemannianExp x (a • p₀+b • p₁)) at hh
  exact sub_le_iff_le_add.mpr (by simpa only [zero_add,twoMountain] using hh)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LiftedSections
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma cost_minimizingVector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : cost x (riemannianExp x p)=‖p‖^2/2 := by
  unfold cost
  rw [show dist x (riemannianExp x p)=‖p‖ from hp]

lemma mem_liftedGapSection_iff {u v : M → ℝ} {x : M} {r : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} :
    p∈liftedGapSection u v x r ↔ p∈minimizingVectors x ∧ riemannianExp x p∈gapSection u v x r := by
  constructor
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma liftedGapSection_image (u v : M → ℝ) (x : M) (r : ℝ) :
    riemannianExp x '' liftedGapSection (n := n) u v x r=gapSection u v x r := by
  apply Subset.antisymm
  · rintro y ⟨p,hp,rfl⟩
    exact (mem_liftedGapSection_iff.mp hp).2
  · intro y hy
    obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
    exact ⟨p,mem_liftedGapSection_iff.mpr ⟨hp,by rwa [hpy]⟩,hpy⟩

variable [Nonempty M]

lemma WeakMTW.convex_liftedGapSection (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    (x : M) (r : ℝ) : Convex ℝ (liftedGapSection (n := n) u v x r) := by
  intro p hp q hq a b ha hb hab
  have hp' := mem_liftedGapSection_iff.mp hp
  have hq' := mem_liftedGapSection_iff.mp hq
  obtain ⟨hm,hcomp⟩ := hmtw.double_mountain hp.1 hq.1 ha hb hab
  rw [mem_liftedGapSection_iff]
  refine ⟨hm,?_⟩
  change u x+cost x (riemannianExp x (a • p+b • q))+v (riemannianExp x (a • p+b • q)) ≤ r
  have HB : cTransform u (riemannianExp x (a • p+b • q))≤
      r-u x-cost x (riemannianExp x (a • p+b • q)) := by
    rw [cTransform_le_iff hu]
    intro z
    rw [cost_symm (riemannianExp x (a • p+b • q)) z]
    have hcp := dualPair_gap_nonneg hv huv z (riemannianExp x p)
    have hcq := dualPair_gap_nonneg hv huv z (riemannianExp x q)
    have hpS : u x+cost x (riemannianExp x p)+v (riemannianExp x p) ≤ r := hp'.2
    have hqS : u x+cost x (riemannianExp x q)+v (riemannianExp x q) ≤ r := hq'.2
    have hpB : cost x (riemannianExp x p)-cost z (riemannianExp x p) ≤ r-u x+u z := by
      dsimp [contactGap] at hcp
      linarith [hpS]
    have hqB : cost x (riemannianExp x q)-cost z (riemannianExp x q) ≤ r-u x+u z := by
      dsimp [contactGap] at hcq
      linarith [hqS]
    have hmax := (hcomp z).trans (max_le hpB hqB)
    linarith
  rw [huv.2]
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SectionDiameter
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SectionDiameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.liftedGapSection_diameter_sq (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    {x : M} {r : ℝ} (hr : 0 ≤ r) {p q : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈liftedGapSection u v x r) (hq : q∈liftedGapSection u v x r) :
    ‖p-q‖^2≤8*(r+sectionOscillation u v x r) := by
  let m := (1/2:ℝ) • p+(1/2:ℝ) • q
  have hm : m∈liftedGapSection u v x r :=
    (hmtw.convex_liftedGapSection hu hv huv x r) hp hq (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨y₀,_,y₁,_,hmin,hmax,heq⟩ := sectionOscillation_extrema hv huv x hr
  have hpS := (mem_liftedGapSection_iff.mp hp).2
  have hqS := (mem_liftedGapSection_iff.mp hq).2
  have hmS := (mem_liftedGapSection_iff.mp hm).2
  have hpl := hmin _ hpS
  have hql := hmin _ hqS
  have hmu := hmax _ hmS
  have hpm := hp.2
  have hqm := hq.2
  have hmn := dualPair_gap_nonneg hv huv x (riemannianExp x m)
  rw [contactGap,cost_minimizingVector hm.1] at hmn
  have norm_m : ‖m‖^2=(‖p‖^2+‖q‖^2)/2-‖p-q‖^2/4 := by
    have hpar := parallelogram_law_with_norm ℝ p q
    dsimp [m]
    rw [←smul_add,norm_smul]
    norm_num
    nlinarith [hpar]
  rw [heq]
  nlinarith [norm_m]

end SectionDiameter
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveDifferentiability
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma activeLog_derivative_eq {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ activeLogs v x)
    {D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) D 0) :
    D = innerSL ℝ p := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    cTransform v (riemannianExp x h) + 2 * normalCost x ((1/2:ℝ) • p) h
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hh := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    linarith
  have hf : HasFDerivAt f (D - innerSL ℝ p) 0 := by
    apply (hD.add ((normalCost_hasFDerivAt_zero hID).const_mul 2)).congr_fderiv
    ext h
    simp only [_root_.add_apply,_root_.sub_apply,
      _root_.smul_apply,innerSL_apply_apply,inner_neg_left,
      real_inner_smul_left,smul_eq_mul]
    ring
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hf)

lemma activeLogs_subsingleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    (activeLogs (n := n) v x).Subsingleton := by
  have hD' : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have he := ((contMDiff_riemannianExp_fiber (n := n) x 0).mdifferentiableAt (by simp))
    have hD0 : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hD
    exact (hD0.comp 0 he).differentiableAt
  intro p hp q hq
  have hh := (activeLog_derivative_eq hv hp hD'.hasFDerivAt).symm.trans
    (activeLog_derivative_eq hv hq hD'.hasFDerivAt)
  apply ext_inner_right ℝ
  intro h
  exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) hh

lemma contact_singleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y = 0)
    (hz : contactGap (cTransform v) v x z = 0) : y = z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hp' : p ∈ activeLogs v x := ⟨hp,by simpa only [hep] using hy⟩
  have hq' : q ∈ activeLogs v x := ⟨hq,by simpa only [heq] using hz⟩
  have he := activeLogs_subsingleton_of_mdifferentiable hv hD hp' hq'
  exact hep.symm.trans ((congrArg (riemannianExp x) he).trans heq)

variable [MeasurableSpace M] [BorelSpace M]

lemma lipschitz_ae_mdifferentiable_metricVolume {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(metricVolume (M := M) n), MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) := continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  have hh := lipschitz_ae_mdifferentiable (E := Model n) hu
  have hh' : ∀ᵐ x ∂(Measure.hausdorffMeasure (n : ℝ) : Measure M),
      MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
    simpa [Model] using hh
  exact Measure.smul_absolutelyContinuous.ae_le hh'

lemma cTransform_ae_singleton_contacts [Nonempty M] {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂(metricVolume (M := M) n),
      ∀ y z : M, contactGap (cTransform v) v x y = 0 →
        contactGap (cTransform v) v x z = 0 → y = z := by
  have hlip := cTransform_lipschitz hv (D := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩)
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  filter_upwards [lipschitz_ae_mdifferentiable_metricVolume (n := n) hlip] with x hx
  exact fun y z hy hz => contact_singleton_of_mdifferentiable hv hx hy hz

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContinuousClosedRelationSelector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace WeakMTWTransport

lemma continuousAt_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R) {x : X}
    (hx : ∀ y, (x,y) ∈ R → y = T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let B : Set (X × Y) := R ∩ {z | ε ≤ dist z.2 (T x)}
  have hB : IsClosed B :=
    hR.inter (isClosed_le continuous_const (continuous_snd.dist continuous_const))
  have hclosed : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hxB : x ∈ (Prod.fst '' B)ᶜ := by
    rintro ⟨⟨a,b⟩, hab, hax⟩
    change a = x at hax
    subst a
    have hb := hx b hab.1
    have hdist := hab.2
    change ε ≤ dist b (T x) at hdist
    rw [hb,dist_self] at hdist
    exact (not_le.mpr hε) hdist
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,?_⟩
  intro a ha
  apply lt_of_not_ge
  intro han
  exact hd ha ⟨(a,T a),⟨hT a,han⟩,rfl⟩

lemma aemeasurable_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, (x,y) ∈ R → y = T x) : AEMeasurable T μ := by
  let S : Set X := {x | ∀ y, (x,y) ∈ R → y = T x}
  have hS : ∀ᵐ x ∂μ, x ∈ S := hsingle
  have hSnull : NullMeasurableSet S μ := by
    have he : (univ : Set X) =ᵐ[μ] S := by
      filter_upwards [hS] with x hx
      exact propext ⟨fun _ => hx, fun _ => mem_univ x⟩
    exact nullMeasurableSet_univ.congr he
  have hc : ContinuousOn T S := by
    intro x hx
    exact (continuousAt_closed_relation_selector hR hT hx).continuousWithinAt
  have hm := hc.aemeasurable₀ hSnull
  rwa [Measure.restrict_eq_self_of_ae_mem hS] at hm

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CompactAE
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section CompactAE
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in

lemma contact_gap_control_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, contactGap u v x z ≤ δ → f y - f z ≤ ε := by
  let G : M → ℝ := fun z => contactGap u v x z
  let B : Set M := {z | ε ≤ f y - f z}
  have hG : Continuous G := (continuous_const.add (continuous_cost_right x)).add v.continuous
  have hB : IsCompact B := (isClosed_le continuous_const
    (continuous_const.sub f.continuous)).isCompact
  by_cases hne : B.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hB.exists_isMinOn hne hG.continuousOn
    have hpos : 0 < G z := by
      apply lt_of_le_of_ne (hgap z)
      intro he
      have heq := hsingle z he.symm
      change ε ≤ f y - f z at hz
      rw [heq,sub_self] at hz
      exact (not_le.mpr hε) hz
    refine ⟨G z / 2,half_pos hpos,?_⟩
    intro w hw
    by_contra hn
    have hm := hmin (le_of_lt (lt_of_not_ge hn))
    change G z ≤ contactGap u v x w at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z _
    by_contra hn
    exact hne ⟨z,le_of_lt (lt_of_not_ge hn)⟩

lemma transform_perturbation_upper_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ →
      cTransform (fun z => v z + t * f z) x ≤ u x - t * f y + t * ε := by
  obtain ⟨δ,hδ,hcontrol⟩ := contact_gap_control_at u v x y hsingle hgap f hε
  have hden : 0 < 2 * ‖f‖ + 1 := by positivity
  refine ⟨δ / (2 * ‖f‖ + 1),div_pos hδ hden,?_⟩
  intro t ht htτ
  have htd : t * (2 * ‖f‖ + 1) ≤ δ := (le_div_iff₀ hden).mp htτ
  have htbound : t * (2 * ‖f‖) ≤ δ := by nlinarith
  rw [cTransform_le_iff (v := fun z => v z + t * f z)
    (v.continuous.add (continuous_const.mul f.continuous))]
  intro z
  have hg := hgap z
  have hbound : t * (f y - f z) ≤ contactGap u v x z + t * ε := by
    by_cases hs : contactGap u v x z ≤ δ
    · have hh := mul_le_mul_of_nonneg_left (hcontrol z hs) ht.le
      nlinarith
    · have hf1 := BoundedContinuousFunction.norm_coe_le_norm f y
      have hf2 := BoundedContinuousFunction.norm_coe_le_norm f z
      rw [Real.norm_eq_abs,abs_le] at hf1 hf2
      have hw : f y - f z ≤ 2 * ‖f‖ := by linarith [hf1.2,hf2.1]
      have hh := mul_le_mul_of_nonneg_left hw ht.le
      have hte : 0 ≤ t * ε := mul_nonneg ht.le hε.le
      linarith
  dsimp [contactGap] at hbound
  nlinarith

lemma transformedDifferenceQuotient_apply (v f : M →ᵇ ℝ) (t : ℝ) (x : M) :
    transformedDifferenceQuotient v f t x =
      (cTransform (fun z => v z + t * f z) x - cTransform v x) / t := by
  simp only [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply,boundedCTransform_apply,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  rfl

lemma transformedDifferenceQuotient_norm_le (v f : M →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : M) :
    ‖transformedDifferenceQuotient v f t x‖ ≤ ‖f‖ := by
  have hh := boundedCTransform_nonexpansive (M := M) |>.dist_le_mul (v + t • f) v
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht] at hh
  have hp := BoundedContinuousFunction.norm_coe_le_norm
    (boundedCTransform (v + t • f) - boundedCTransform v) x
  have hbound := hp.trans hh
  rw [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,norm_smul,
    Real.norm_eq_abs,abs_inv,abs_of_pos ht]
  exact (inv_mul_le_iff₀ ht).mpr hbound

lemma transformedDifferenceQuotient_tendsto_at (v f : M →ᵇ ℝ) (x y : M)
    (hcontact : contactGap (cTransform v) v x y = 0)
    (hsingle : ∀ z, contactGap (cTransform v) v x z = 0 → z = y)
    {s : ℕ → ℝ} (hs : ∀ j, 0 < s j) (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => transformedDifferenceQuotient v f (s j) x) atTop (𝓝 (-f y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨τ,hτ,hup⟩ := transform_perturbation_upper_at (boundedCTransform v) v x y
    hsingle (cTransform_gap_nonneg v.continuous x) f (half_pos hε)
  have hevent : ∀ᶠ j in atTop, s j ≤ τ :=
    (hlim.eventually (eventually_lt_nhds hτ)).mono fun _ h => h.le
  filter_upwards [hevent] with j hj
  rw [transformedDifferenceQuotient_apply,Real.dist_eq,sub_neg_eq_add,abs_lt]
  have hu := hup (s j) (hs j) hj
  have hl := cTransform_gap_nonneg
    (v.continuous.add (continuous_const.mul f.continuous) :
      Continuous (fun z => v z + s j * f z)) x y
  change cTransform (fun z => v z + s j * f z) x ≤
    cTransform v x - s j * f y + s j * (ε/2) at hu
  dsimp only [contactGap] at hcontact
  change 0 ≤ cTransform (fun z => v z + s j * f z) x + cost x y + (v y + s j * f y) at hl
  have hlo : -f y ≤ (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j := by
    apply (le_div_iff₀ (hs j)).mpr
    nlinarith
  have hhi : (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j ≤ -f y + ε/2 := by
    apply (div_le_iff₀ (hs j)).mpr
    nlinarith
  constructor <;> linarith

variable [MeasurableSpace M] [BorelSpace M]

lemma dual_minimum_ae_integral_eq (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b))
    (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) = ∫ y, f y ∂ν := by
  have hle (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) ≤ ∫ y, f y ∂ν := by
    let s : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have hs (j : ℕ) : 0 < s j := by dsimp [s] <;> positivity
    have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun j => ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ)
        atTop (𝓝 (∫ x, -f (T x) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      · intro j
        exact (transformedDifferenceQuotient v f (s j)).continuous.aestronglyMeasurable
      · exact integrable_const _
      · intro j
        exact Eventually.of_forall (transformedDifferenceQuotient_norm_le v f (hs j))
      · filter_upwards [hsingle] with x hx
        exact transformedDifferenceQuotient_tendsto_at v f x (T x) (hcontact x) hx hs hslim
    have hineq (j : ℕ) : -(∫ y, f y ∂ν) ≤
        ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ := by
      let a := boundedCTransform (v + s j • f)
      let b : M →ᵇ ℝ := v + s j • f
      have hi := hmin a b (cTransform_gap_nonneg b.continuous)
      have hb : (∫ y, b y ∂ν) = (∫ y, v y ∂ν) + s j * ∫ y, f y ∂ν := by
        change (∫ y, v y + s j * f y ∂ν) = _
        rw [integral_add (v.integrable ν) ((f.integrable ν).const_mul (s j)),
          integral_const_mul]
      have hq : (∫ x, transformedDifferenceQuotient v f (s j) x ∂μ) =
          ((∫ x, a x ∂μ) - (∫ x, boundedCTransform v x ∂μ)) / s j := by
        change (∫ x, (s j)⁻¹ * (a x - boundedCTransform v x) ∂μ) = _
        rw [integral_const_mul,integral_sub (a.integrable μ) ((boundedCTransform v).integrable μ)]
        rw [div_eq_mul_inv,mul_comm]
      rw [hq]
      apply (le_div_iff₀ (hs j)).mpr
      change (∫ x, boundedCTransform v x ∂μ) + (∫ y, v y ∂ν) ≤
        (∫ x, a x ∂μ) + (∫ y, b y ∂ν) at hi
      rw [hb] at hi
      nlinarith
    have hbound := ge_of_tendsto' hlim hineq
    rw [integral_neg] at hbound
    linarith
  apply le_antisymm (hle f)
  have hneg := hle (-f)
  simp only [BoundedContinuousFunction.neg_apply,integral_neg] at hneg
  linarith

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma cost_contact_relation_isClosed (u v : M →ᵇ ℝ) :
    IsClosed {z : M × M | contactGap u v z.1 z.2 = 0} := by
  apply isClosed_eq _ continuous_const
  exact ((u.continuous.comp continuous_fst).add
    (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
    (v.continuous.comp continuous_snd)

lemma dual_minimum_ae_pushforward (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b)) :
    AEMeasurable T μ ∧ Measure.map T μ = ν := by
  have hT : AEMeasurable T μ := aemeasurable_closed_relation_selector
    (cost_contact_relation_isClosed (boundedCTransform v) v) hcontact hsingle
  refine ⟨hT,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT f.continuous.aestronglyMeasurable]
  exact dual_minimum_ae_integral_eq μ ν v T hcontact hsingle hmin f

end CompactAE
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_MeasureContacts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport

section MeasureContacts
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma dual_minimum_swap {μ ν : Measure M} {u v : M →ᵇ ℝ}
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (u,v) ≤ dualObjective μ ν (a,b)) :
    ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective ν μ (v,u) ≤ dualObjective ν μ (a,b) := by
  intro a b hab
  have hh := hmin b a (fun x y => by rw [contactGap_symm]; exact hab y x)
  simpa only [dualObjective,add_comm] using hh

end MeasureContacts

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_RiemannianTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport
section RiemannianTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma dual_minimizer_rough_transport {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ T S : M → M,
      (∀ x, contactGap u v x (T x) = 0) ∧
      (∀ y, contactGap u v (S y) y = 0) ∧
      (∀ᵐ x ∂(metricVolume n), ∀ y, contactGap u v x y = 0 → y = T x) ∧
      (∀ᵐ y ∂(metricVolume n), ∀ x, contactGap u v x y = 0 → x = S y) ∧
      AEMeasurable T (densityMeasure (metricVolume n) rho0) ∧
      AEMeasurable S (densityMeasure (metricVolume n) rho1) ∧
      Measure.map T (densityMeasure (metricVolume n) rho0) = densityMeasure (metricVolume n) rho1 ∧
      Measure.map S (densityMeasure (metricVolume n) rho1) = densityMeasure (metricVolume n) rho0 := by
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho0) :=
    densityMeasure_probability hlam hrho0
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho1) :=
    densityMeasure_probability hlam hrho1
  have hcontactT : ∀ x : M, ∃ y : M, contactGap u v x y = 0 := by
    intro x
    obtain ⟨y,hy,_⟩ := exists_cTransform_contact v.continuous x
    refine ⟨y,?_⟩
    simp only [contactGap,hdual.1,hy]
    ring
  have hcontactS : ∀ y : M, ∃ x : M, contactGap u v x y = 0 := by
    intro y
    obtain ⟨x,hx,_⟩ := exists_cTransform_contact u.continuous y
    refine ⟨x,?_⟩
    rw [contactGap_symm]
    simp only [contactGap,hdual.2,hx]
    ring
  choose T hT using hcontactT
  choose S hS using hcontactS
  have hsingleT : ∀ᵐ x ∂(metricVolume n),
      ∀ y, contactGap u v x y = 0 → y = T x := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) v.continuous] with x hx
    intro y hy
    exact hx y (T x) (by simpa only [← hdual.1] using hy)
      (by simpa only [← hdual.1] using hT x)
  have hsingleS : ∀ᵐ y ∂(metricVolume n),
      ∀ x, contactGap u v x y = 0 → x = S y := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) u.continuous] with y hy
    intro x hx
    apply hy x (S y)
    · simpa only [← hdual.2,← contactGap_symm u v x y] using hx
    · simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y
  have hmaybeT := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) v T
    (by simpa only [← hdual.1] using hT)
    (by
      have he := (withDensity_absolutelyContinuous (metricVolume n)
        (fun x => ENNReal.ofReal (rho0 x))).ae_le hsingleT
      filter_upwards [he] with x hx
      intro y hy
      exact hx y (by simpa only [← hdual.1] using hy))
    (by
      have he : boundedCTransform v = u := by
        ext x; exact congrFun hdual.1.symm x
      simpa only [he] using hmin)
  have hmaybeS := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho1) (densityMeasure (metricVolume n) rho0) u S
    (by intro y; simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y)
    (by
      filter_upwards [(withDensity_absolutelyContinuous (metricVolume n) _).ae_le hsingleS] with y hy
      intro x hx
      apply hy x
      simpa only [← hdual.2,← contactGap_symm u v x y] using hx)
    (by
      have he : boundedCTransform u = v := by
        ext x; exact congrFun hdual.2.symm x
      simpa only [he] using dual_minimum_swap hmin)
  exact ⟨T,S,hT,hS,hsingleT,hsingleS,hmaybeT.1,hmaybeS.1,hmaybeT.2,hmaybeS.2⟩

end RiemannianTransport
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_AECertificates
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section PowerEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.section_diameter_of_exp_bound (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {L : ℝ≥0} (hL : ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤Metric.diam (univ : Set M) → ‖q‖≤Metric.diam (univ : Set M) →
      dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖)
    {x : M} {r : ℝ} (hr : 0 ≤ r) {y y' : M}
    (hy : y∈gapSection u v x r) (hy' : y'∈gapSection u v x r) :
    dist y y'≤L*Real.sqrt (8*(sectionOscillation u v x r+r)) := by
  rw [←liftedGapSection_image (n := n) u v x r] at hy hy'
  obtain ⟨p,hp,rfl⟩ := hy
  obtain ⟨q,hq,rfl⟩ := hy'
  have hb : ∀ w∈minimizingVectors (n := n) x, ‖w‖≤Metric.diam (univ : Set M) := by
    intro w hw
    rw [←show dist x (riemannianExp x w)=‖w‖ from hw]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  apply (hL x p q (hb p hp.1) (hb q hq.1)).trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  apply Real.le_sqrt_of_sq_le
  simpa only [add_comm] using hmtw.liftedGapSection_diameter_sq hu hv hdual hr hp hq

variable [MeasurableSpace M]

lemma WeakMTW.contact_bounds_of_class_power (hmtw : WeakMTW (n := n) (M := M))
    {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hpower : HasPowerUpperBound (classOscillation vol lam cap x0)) :
    ∃ alpha C : ℝ, 0<alpha ∧ alpha≤1 ∧ 0≤C ∧
      ∀ uv∈densityDualClass vol lam cap x0,
        ∀ x x' y y' : M,
          contactGap uv.1 uv.2 x y=0 → contactGap uv.1 uv.2 x' y'=0 →
          dist y y'≤C*dist x x'^alpha := by
  obtain ⟨beta,C0,r0,hbeta,hC0,hr0,hpow⟩ := hpower
  obtain ⟨L,hL⟩ := exists_uniform_exp_lipschitz (n := n) (M := M) (Metric.diam (univ : Set M))
  let alpha := min beta 1/2
  let r1 := min r0 1
  let K : ℝ := L*Real.sqrt (8*(C0+1))
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  have hD : ∀ x y : M, dist x y≤D := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have hr1 : 0 < r1 := lt_min hr0 (by norm_num)
  have hK : 0≤K := by dsimp [K] <;> positivity
  have ha := power_reduction_exponent hbeta
  let C := K*(2*D+1)^alpha+D/(r1/(2*D+1))^alpha
  have hC : 0≤C := by dsimp [C] <;> positivity
  refine ⟨alpha,C,ha.1,ha.2,hC,?_⟩
  intro uv huv
  have hdual := densityDualClass_isDual huv
  have hu : LipschitzWith D uv.1 := hdual.1.symm ▸ cTransform_lipschitz uv.2.continuous hD
  apply contact_bound_of_section_bound hu hD hK ha.1 hr1
  intro x r hr hrr y hy y' hy'
  have hF := (sectionOscillation_le_classOscillation huv x hr.le).trans
    (hpow r hr (hrr.trans_le (min_le_left _ _)))
  have hs := scalar_sqrt_power_bound hr (hrr.le.trans (min_le_right _ _)) hC0.le hF
  calc
    _≤(L:ℝ)*Real.sqrt (8*(sectionOscillation uv.1 uv.2 x r+r)) :=
      hmtw.section_diameter_of_exp_bound uv.1.continuous uv.2.continuous hdual hL hr.le hy hy'
    _≤(L:ℝ)*(Real.sqrt (8*(C0+1))*r^alpha) := mul_le_mul_of_nonneg_left hs L.coe_nonneg
    _=K*r^alpha := by dsimp [K] <;> ring

variable [BorelSpace M]

lemma WeakMTW.transport_endpoint_of_class_power (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (x0 : M)
    (hpower : HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0)) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  obtain ⟨alpha,C,ha,ha1,hC,H⟩ := hmtw.contact_bounds_of_class_power hpower
  refine ⟨alpha,C,ha,ha1,hC,?_⟩
  intro rho0 rho1 hrho0 hrho1
  have := densityMeasure_probability hlam hrho0
  have := densityMeasure_probability hlam hrho1
  obtain ⟨uv,huv,hmin⟩ := exists_minimizing_normalizedDualPair
    (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) x0
  have hm : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) uv≤
      dualObjective (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) (a,b) := by
    intro a b hab
    exact (hmin (normalizeDualPair_mem x0 b)).trans
      (dualObjective_normalize_le _ _ x0 a b hab)
  have hclass : uv∈densityDualClass (metricVolume n) lam cap x0 :=
    ⟨huv,rho0,rho1,hrho0,hrho1,hm⟩
  have hdual := densityDualClass_isDual hclass
  have hf := H uv hclass
  have hr : ∀ x x' y y' : M, contactGap uv.1 uv.2 x y=0 →
      contactGap uv.1 uv.2 x' y'=0 → dist x x'≤C*dist y y'^alpha := by
    intro x x' y y' hy hy'
    exact H _ (densityDualClass_reverse hlam hclass) y y' x x'
      (by rwa [reverseNormalizedPair_gap]) (by rwa [reverseNormalizedPair_gap])
  obtain ⟨T,hT,hTf,hTr⟩ := homeomorph_of_contact_bounds
    uv.1.continuous uv.2.continuous hdual ha hC hf hr
  have hs : ∀ x y, contactGap uv.1 uv.2 x y=0 → y=T x := by
    intro x y hy
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [dist_self,Real.zero_rpow ha.ne',mul_zero] using hf x x y (T x) hy (hT x)
  obtain ⟨S,_,hS,_,_,_,_,_,hpush,_⟩ := dual_minimizer_rough_transport hlam hrho0 hrho1 hdual hm
  have hST : S=T := funext (fun x => hs x (S x) (hS x))
  rw [hST] at hpush
  have hgap := dualPair_gap_nonneg uv.2.continuous hdual
  refine ⟨T,isOptimalMap_of_dual_contact hlam hrho0 hrho1
    uv.1.continuous uv.2.continuous hgap T.continuous.measurable hpush hT,?_,hTf,hTr⟩
  intro S hS
  exact optimalMap_ae_eq_of_singleton_contacts hlam hrho0 hrho1
    uv.1.continuous uv.2.continuous hgap T.continuous.measurable hpush hT hs hS

end PowerEndpoint
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

theorem uniform_biHolder_transport_oai
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ, Model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsRiemannianManifold 𝓘(ℝ, Model n) M]
    [MeasurableSpace M] [BorelSpace M]
    (hmtw : WeakMTW (n := n) (M := M))
    (lam cap : ℝ) (hlam : 0 < lam) (hcap : lam ≤ cap)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity (metricVolume n) lam cap rho) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  classical
  let x0:M:=Classical.choice (inferInstance:Nonempty M)
  exact hmtw.transport_endpoint_of_class_power hlam x0
    (hmtw.class_power (by omega) hlam hcap x0 (densityDualClass_nonempty hlam hclass x0))

end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.uniform_biHolder_transport_oai.{u_1} := @OAI.WeakMTWTransport.uniform_biHolder_transport_oai.{u_1}
