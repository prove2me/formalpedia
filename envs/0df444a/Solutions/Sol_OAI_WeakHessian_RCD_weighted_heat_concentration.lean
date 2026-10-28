-- Prove2me | solution 1 for OAI.WeakHessian.RCD.weighted_heat_concentration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:04:38.07247+00:00
-- url     : https://prove2.me/submissions/a2dc0254-eff0-4ce2-b758-126429e786b2

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

theorem weakGradient_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    weakGradient m f =ᵐ[m] weakGradient (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact weakGradient_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientTendstoNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

section NormConvergence
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_tendsto_of_norm_tendsto {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) := by
  let fm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • fn n + (1/2 : ℝ) • f
  let Dm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • Dn n + (1/2 : ℝ) • D
  have hmid (n : ℕ) : IsLocalWeakUpperGradient m (fm n) (Dm n) := by
    exact convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (fn n, Dn n)) (y := WithLp.toLp 2 (f,D))
      (hn n) hD (by norm_num) (by norm_num) (by norm_num)
  have hfm : Tendsto fm atTop (𝓝 f) := by
    have H := (hf.const_smul (1/2 : ℝ)).add
      (tendsto_const_nhds (x := (1/2 : ℝ) • f))
    simpa only [← add_smul, show (1/2:ℝ)+(1/2)=1 by norm_num, one_smul] using H
  have hlow (a : ℝ) (ha : a < ‖D‖) : ∀ᶠ n in atTop, a < ‖Dm n‖ := by
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    have H := hfm.eventually ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)
    filter_upwards [H] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dm n,hmid n,hle⟩)
  have hupper (n : ℕ) : ‖Dm n‖ ≤ (‖Dn n‖+‖D‖)/2 := by
    calc
      ‖Dm n‖ ≤ ‖(1/2 : ℝ) • Dn n‖ + ‖(1/2 : ℝ) • D‖ := norm_add_le _ _
      _ = (‖Dn n‖+‖D‖)/2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        ring
  have hmajor : Tendsto (fun n => (‖Dn n‖+‖D‖)/2) atTop (𝓝 ‖D‖) := by
    convert (hNorm.add_const ‖D‖).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hmidNorm : Tendsto (fun n => ‖Dm n‖) atTop (𝓝 ‖D‖) := by
    apply tendsto_order.mpr
    refine ⟨hlow, fun b hb => ?_⟩
    filter_upwards [hmajor.eventually (gt_mem_nhds hb)] with n hn'
    exact (hupper n).trans_lt hn'
  have hsq (n : ℕ) : ‖Dn n - D‖^2 = 2*‖Dn n‖^2+2*‖D‖^2-4*‖Dm n‖^2 := by
    have hm : ‖Dm n‖ = ‖Dn n+D‖/2 := by
      simp only [Dm, ← smul_add, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      ring
    rw [hm]
    nlinarith [parallelogram_law_with_norm ℝ (Dn n) D]
  have hs : Tendsto (fun n => ‖Dn n-D‖^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    convert ((hNorm.pow 2).const_mul 2 |>.add_const (2*‖D‖^2)).sub
      ((hmidNorm.pow 2).const_mul 4) using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using H

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.norm_le {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    {E : Lp ℝ 2 m} (hE : IsLocalWeakUpperGradient m f E) : ‖D‖ ≤ ‖E‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hD.2 E hE, hD.1.2.1, hE.2.1] with x hx hd he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg he] using hx

lemma IsMinimalLocalWeakUpperGradient.tendsto_of_norm_tendsto
    {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) :=
  upperGradient_tendsto_of_norm_tendsto hn hf hD.1 (fun _ hE => hD.norm_le hE) hNorm
end NormConvergence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfMapLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma integrable_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    Integrable (fun x => u x*f x) m :=
  hi.mul_bdd f.continuous.aestronglyMeasurable (ae_of_all _ fun x => f.norm_coe_le_norm x)

omit [BorelSpace X] [ProperSpace X] in
lemma norm_integral_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    ‖∫ x,u x*f x ∂m‖ ≤ ‖f‖*(∫ x,‖u x‖ ∂m) := by
  have H := norm_integral_le_of_norm_le (f := fun x => u x*f x) (hi.norm.const_mul ‖f‖) (by
    apply ae_of_all
    intro x
    rw [norm_mul,mul_comm ‖f‖]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
  simpa only [integral_const_mul] using H

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_left {u v : X → ℝ} (hu : Integrable u m)
    (hv : Integrable v m) (q : X →ᵇ ℝ) :
    (∫ x,(v x-u x)*q x ∂m) = (∫ x,v x*q x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hv q) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_right {u : X → ℝ} (hu : Integrable u m)
    (q r : X →ᵇ ℝ) :
    (∫ x,u x*(r-q) x ∂m) = (∫ x,u x*r x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hu r) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [BoundedContinuousFunction.sub_apply]; ring)

omit [ProperSpace X] in
lemma tendsto_bounded_pairing_L1 {ι : Type*} {l : Filter ι}
    {u : ι → X → ℝ} {v : X → ℝ} (hu : ∀ i,Integrable (u i) m) (hv : Integrable v m)
    {q : ι → X →ᵇ ℝ} {r : X →ᵇ ℝ} (hq : Tendsto q l (𝓝 r))
    (hL1 : Tendsto (fun i => ∫ x,‖u i x-v x‖ ∂m) l (𝓝 0)) :
    Tendsto (fun i => ∫ x,u i x*q i x ∂m) l (𝓝 (∫ x,v x*r x ∂m)) := by
  have hD : Tendsto (fun i => ‖q i-r‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hq.sub (tendsto_const_nhds (x := r))).norm
  have H (i : ι) : ‖(∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m)‖ ≤
      ‖q i-r‖*(∫ x,‖v x‖ ∂m)+‖q i‖*(∫ x,‖u i x-v x‖ ∂m) := by
    have he : (∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m) =
        (∫ x,v x*(q i-r) x ∂m)+(∫ x,(u i x-v x)*q i x ∂m) := by
      rw [integral_bounded_pairing_sub_right hv,integral_bounded_pairing_sub_left hv (hu i)]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_integral_bounded_pairing hv _)
      (norm_integral_bounded_pairing ((hu i).sub hv) _))
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm H
  simpa only [zero_mul,mul_zero,add_zero] using (hD.mul_const _).add (hq.norm.mul hL1)

end WeakHessianTransport
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfMapNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma boundedHopfMap_norm_le (f : X →ᵇ ℝ) (t : ℝ) : ‖boundedHopfMap f t‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  by_cases ht : 0 < t
  · rw [boundedHopfMap_apply_pos f ht,Real.norm_eq_abs]
    exact abs_le.mpr ⟨lower_le_hopfLax (fun x => (boundedContinuous_bounds f x).1) ht x,
      (hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x).trans (boundedContinuous_bounds f x).2⟩
  · simpa only [boundedHopfMap,dite_eq_right ht] using f.norm_coe_le_norm x

end WeakHessianTransport
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactHopfDualLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile231
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma hopf_diff_of_local_bound (f g : X →ᵇ ℝ) (x : X) {B ε : ℝ}
    (hB : 0 ≤ B) (hf : ∀ y,|f y| ≤ B) (hg : ∀ y,|g y| ≤ B)
    (hfg : ∀ y,dist x y ≤ B+2 → |f y-g y| ≤ ε) :
    |hopfLax f 1 x-hopfLax g 1 x| ≤ ε := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun z => (abs_le.mp (hf z)).1) (by norm_num : (0:ℝ)<1) x
  obtain ⟨z,hz⟩ := exists_hopf_minimizer g.continuous (fun z => (abs_le.mp (hg z)).1) (by norm_num : (0:ℝ)<1) x
  have hdist (q : X →ᵇ ℝ) (hq : ∀ y,|q y| ≤ B) (w : X)
      (hw : hopfObjective q 1 x w = hopfLax q 1 x) : dist x w ≤ B+2 :=
    hopf_minimizer_distance_le (fun z => (abs_le.mp (hq z)).1) (fun z => (abs_le.mp (hq z)).2)
      (by norm_num) (by positivity) (by nlinarith [sq_nonneg B]) hw
  have H₁ := hopfLax_le_objective (fun z => (abs_le.mp (hf z)).1) (by norm_num : (0:ℝ)<1) x z
  have H₂ := hopfLax_le_objective (fun z => (abs_le.mp (hg z)).1) (by norm_num : (0:ℝ)<1) x y
  have ey := abs_le.mp (hfg y (hdist f hf y hy))
  have ez := abs_le.mp (hfg z (hdist g hg z hz))
  dsimp only [hopfObjective] at hy hz H₁ H₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma exists_compact_hopf_approx (f : X →ᵇ ℝ) (o : X) (hL : GloballyLipschitz (f:X→ℝ)) :
    ∃ fs : ℕ → X →ᵇ ℝ,
      (∀ n,HasCompactSupport (fs n:X→ℝ) ∧ GloballyLipschitz (fs n:X→ℝ)) ∧
      (∀ n x,|fs n x| ≤ ‖f‖) ∧
      (∀ x,Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧
      (∀ x,Tendsto (fun n => boundedHopfMap (fs n) 1 x) atTop (𝓝 (boundedHopfMap f 1 x))) := by
  have hb (x : X) : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hη (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg _ _ _)]
    exact radialCutoff_le_one _ _ _
  have hfb (n : ℕ) (x : X) : ‖f x*radialCutoff o n x‖ ≤ ‖f‖ := by
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (hb x) (hη n x) (abs_nonneg _) (norm_nonneg f)).trans_eq (mul_one _)
  let fs (n : ℕ) : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x*radialCutoff o n x) (f.continuous.mul (radialCutoff_lipschitz o n).continuous) ‖f‖ (hfb n)
  have hfs (n : ℕ) (x : X) : fs n x = f x*radialCutoff o n x := rfl
  have hfsb (n : ℕ) (x : X) : |fs n x| ≤ ‖f‖ := by simpa only [hfs,Real.norm_eq_abs] using hfb n x
  refine ⟨fs,?_,hfsb,?_,?_⟩
  · intro n
    refine ⟨(radialCutoff_compact o n).mul_left,?_⟩
    exact ⟨_, lipschitz_mul_bounded hL.choose_spec (radialCutoff_lipschitz o n) hb (hη n)⟩
  · intro x
    simpa only [hfs,mul_one] using (tendsto_const_nhds.mul (radialCutoff_tendsto o x) :
      Tendsto (fun n => f x*radialCutoff o n x) atTop (𝓝 (f x*1)))
  · intro x
    have he (n : ℕ) (y : X) : |f y-fs n y| ≤ ‖f‖*dist y o/((n:ℝ)+1) := by
      rw [hfs,← mul_one_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one _ _ _))]
      have hηe : 1-radialCutoff o n y ≤ dist y o/((n:ℝ)+1) := by
        have H := le_max_right (0:ℝ) (1-dist y o/((n:ℝ)+1))
        change 1-max 0 (1-dist y o/((n:ℝ)+1)) ≤ _
        linarith
      simpa only [mul_div_assoc] using mul_le_mul (hb y) hηe
        (sub_nonneg.mpr (radialCutoff_le_one _ _ _)) (norm_nonneg f)
    let E (n : ℕ) := ‖f‖*(dist x o+‖f‖+2)/((n:ℝ)+1)
    have hE (n : ℕ) : |hopfLax f 1 x-hopfLax (fs n) 1 x| ≤ E n := by
      apply hopf_diff_of_local_bound f (fs n) x (norm_nonneg f) hb (hfsb n)
      intro y hy
      apply (he n y).trans
      have hd : dist y o ≤ dist x o+‖f‖+2 := by
        have H := dist_triangle y x o
        rw [dist_comm y x] at H
        linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (norm_nonneg f)) (by positivity)
    have hEt : Tendsto E atTop (𝓝 0) := by
      have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (‖f‖*(dist x o+‖f‖+2))
      simpa only [E,mul_one_div,mul_zero] using H
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n,hn⟩ := (Metric.tendsto_atTop.mp hEt) ε hε
    refine ⟨n,fun b hb' => ?_⟩
    rw [Real.dist_eq,boundedHopfMap_apply_pos (fs b) (by norm_num),boundedHopfMap_apply_pos f (by norm_num),abs_sub_comm]
    apply (hE b).trans_lt
    have H := hn b hb'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by dsimp [E]; positivity)] at H
    exact H

variable [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X]

lemma exists_proper_coupling_cost_of_compact_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (o : X) (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, HasCompactSupport (f:X→ℝ) → GloballyLipschitz (f:X→ℝ) →
      (∫ x,boundedHopfMap f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal B := by
  apply exists_proper_coupling_cost_of_hopf_bound μ ν B
  intro f hL
  obtain ⟨fs,hfs,hb,hlim,hQlim⟩ := exists_compact_hopf_approx f o hL
  have hnorm (n : ℕ) : ‖fs n‖ ≤ ‖f‖ := by
    apply BoundedContinuousFunction.norm_le (norm_nonneg f) |>.mpr
    intro x
    simpa only [Real.norm_eq_abs] using hb n x
  have hfn : Tendsto (fun n => ∫ x,fs n x ∂ν) atTop (𝓝 (∫ x,f x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (fs n).continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb n x
    · exact ae_of_all _ hlim
  have hQn : Tendsto (fun n => ∫ x,boundedHopfMap (fs n) 1 x ∂μ) atTop
      (𝓝 (∫ x,boundedHopfMap f 1 x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (boundedHopfMap (fs n) 1).continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact ae_of_all _ fun x => ((boundedHopfMap (fs n) 1).norm_coe_le_norm x).trans
        ((boundedHopfMap_norm_le (fs n) 1).trans (hnorm n))
    · exact ae_of_all _ hQlim
  have H := le_of_tendsto (hQn.sub hfn) (Eventually.of_forall fun n => hdual (fs n) (hfs n).1 (hfs n).2)
  simpa only [boundedHopfMap_apply_pos f (by norm_num : (0:ℝ)<1)] using H
end WeakHessianTransport

end
end InlinedFile231

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LipschitzDerivQuadraticRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

lemma lipschitzOn_deriv_quadratic_remainder {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    |φ b - φ a - ψ a*(b-a)| ≤ (L:ℝ)*|b-a|^2 := by
  have hseg := hs.segment_subset ha hb
  have H := (convex_segment a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => φ x - φ a - ψ a*(x-a))
    (f' := fun x => ψ x-ψ a) (C := (L:ℝ)*|b-a|)
    (fun x hx => by
      convert ((hφ x (hseg hx)).sub_const (φ a)).sub
        (((hasDerivAt_id x).sub_const a).const_mul (ψ a)) |>.hasDerivWithinAt using 1 <;>
        first | rfl | simp)
    (fun x hx => by
      calc
        ‖ψ x - ψ a‖ ≤ (L:ℝ)*‖x-a‖ := hψ.norm_sub_le (hseg hx) ha
        _ ≤ (L:ℝ)*|b-a| := mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hx) L.coe_nonneg)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using H

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivWithinAt_integral_lipschitzOn {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {S : Set (Lp ℝ 2 m)}
    (hS : ∀ v ∈ S, ∀ᵐ x ∂m, v x ∈ s)
    (hi : ∀ v ∈ S, Integrable (fun x => φ (v x)) m)
    {u : Lp ℝ 2 m} (hu : u ∈ S) (hwu : MemLp (fun x => ψ (u x)) 2 m) :
    HasFDerivWithinAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ (hwu.toLp (fun x => ψ (u x)))) S u := by
  let w : Lp ℝ 2 m := hwu.toLp (fun x => ψ (u x))
  have hw : (w : X → ℝ) =ᵐ[m] fun x => ψ (u x) := MemLp.coeFn_toLp _
  have herr (v : Lp ℝ 2 m) (hv : v ∈ S) :
      |(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ| ≤ (L:ℝ)*‖v-u‖^2 := by
    have hvv : Integrable (fun x => (v-u) x*(v-u) x) m :=
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp (v-u))
    have hn : (∫ x, (v-u) x*(v-u) x ∂m) = ‖v-u‖^2 := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial] using real_inner_self_eq_norm_sq (v-u)
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_sub (hi v hv) (hi u hu)]
    have hii : Integrable (fun x => φ (v x) - φ (u x)) m := (hi v hv).sub (hi u hu)
    rw [← integral_sub hii (show Integrable (fun x => (v-u) x*w x) m from
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp w))]
    calc
      |∫ x, φ (v x) - φ (u x) - (v-u) x * w x ∂m| ≤
          ∫ x, (L:ℝ)*((v-u) x*(v-u) x) ∂m := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hvv.const_mul (L:ℝ))
        filter_upwards [hw,Lp.coeFn_sub v u,hS v hv,hS u hu] with x hx ha hvs hus
        rw [hx,ha]
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        have H := lipschitzOn_deriv_quadratic_remainder hs hφ hψ hus hvs
        rw [sq_abs] at H
        simpa only [pow_two,mul_comm] using H
      _ = (L:ℝ)*‖v-u‖^2 := by rw [integral_const_mul,hn]
  have h0 : Tendsto (fun v : Lp ℝ 2 m => v-u) (𝓝[S] u) (𝓝 0) := by
    simpa only [sub_self,id_eq] using ((tendsto_id : Tendsto (fun v : Lp ℝ 2 m => v) (𝓝 u) (𝓝 u)).mono_left nhdsWithin_le_nhds).sub_const u
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply (IsBigO.of_bound (L:ℝ) ?_).trans_isLittleO
    ((isLittleO_norm_pow_id (show 1 < (2:ℕ) by norm_num)).comp_tendsto h0)
  filter_upwards [eventually_mem_nhdsWithin] with v hv
  change ‖(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ‖ ≤ (L:ℝ)*‖‖v-u‖^2‖
  simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_of_nonneg (norm_nonneg _)] using herr v hv

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivAt_integral_quadratic {φ ψ : ℝ → ℝ} {L : ℝ≥0}
    (hφ : ∀ x, HasDerivAt φ (ψ x) x) (hψ : LipschitzWith L ψ)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ ((hψ.comp_memLp hψ0 (Lp.memLp u)).toLp (ψ ∘ u))) u := by
  have hi (v : Lp ℝ 2 m) : Integrable (fun x => φ (v x)) m := by
    apply ((Lp.memLp v).integrable_sq.const_mul (L:ℝ)).mono'
      ((show Continuous φ from continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
    apply Eventually.of_forall
    intro x
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun x _ => hφ x) hψ.lipschitzOnWith (a := 0) (b := v x) (mem_univ _) (mem_univ _)
    simpa only [hφ0,hψ0,sub_zero,zero_mul,Real.norm_eq_abs,sq_abs] using H
  apply hasFDerivWithinAt_univ.mp
  exact hasFDerivWithinAt_integral_lipschitzOn convex_univ (fun x _ => hφ x) hψ.lipschitzOnWith
    (fun v _ => Eventually.of_forall fun x => mem_univ (v x)) (fun v _ => hi v)
    (mem_univ u) (hψ.comp_memLp hψ0 (Lp.memLp u))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerHeat_add (h : QuadraticCheegerEnergy m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cheegerHeat h (t+s) = cheegerHeat h t * cheegerHeat h s := realHeat_add m _ ht hs

lemma cheegerHeat_bounded (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {B : ℝ} (hB : 0 ≤ B) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ B := by
  have hu' : ∀ᵐ x ∂m, u x ∈ Icc (-B) B := hu.mono fun _ hx => abs_le.mp hx
  exact (cheegerHeat_interval h ht (neg_nonpos.mpr hB) hB u hu').mono fun _ hx => abs_le.mpr hx

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatInverseSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma heatInverseSymbol_continuous (t : ℝ) : Continuous (heatInverseSymbol t) := by
  have hc := expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  simp only [Polynomial.eval_X] at hc
  exact continuous_const.mul (hc.comp (continuous_id.div_const t))

lemma heatInverseSymbol_mul {t : ℝ} (ht : 0 < t) (s : ℝ) :
    s * heatInverseSymbol t s = heatSymbol t s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_mul, heatSymbol_nonpos ht le_rfl]
  · rw [heatInverseSymbol, heatSymbol, ite_eq_right ht.ne', inv_div]
    field_simp

lemma heatSymbol_maps_range {t : ℝ} (ht : 0 < t) (s : ℝ) :
    heatSymbol t s = s*heatInverseSymbol t s := (heatInverseSymbol_mul ht s).symm

lemma resolventHeat_eq_resolvent_mul {R : H →L[ℂ] H} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) :
    resolventHeat R t = R*cfc (heatInverseSymbol t) R := by
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  calc
    resolventHeat R t = cfc (fun s : ℝ => s*heatInverseSymbol t s) R :=
      cfc_congr fun s _ => heatSymbol_maps_range ht s
    _ = cfc (fun s : ℝ => s) R*cfc (heatInverseSymbol t) R :=
      cfc_mul _ _ _ continuous_id.continuousOn (heatInverseSymbol_continuous t).continuousOn
    _ = _ := by rw [hid]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatGeneratorOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_3_rc13f10_1 : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
lemma realHeat_mem_range {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) : realHeat m R t u ∈ R.toLinearMap.range := by
  refine ⟨realCfc m R (heatInverseSymbol t) u, ?_⟩
  apply ofRealLp_injective m
  change ofRealLp m (R (realCfc m R (heatInverseSymbol t) u)) = _
  rw [← complexify_ofReal m R, ofReal_realCfc, ofReal_realHeat,
    resolventHeat_eq_resolvent_mul (complexify_positive m hR) ht]
  rfl

end WeakHessianFunctional
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_hasFormGenerator {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    ∃ A, hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u) A := by
  obtain ⟨v,hv⟩ := realHeat_mem_range m hQ.resolvent_positive ht u
  change hQ.resolvent v = realHeat m hQ.resolventLinear t u at hv
  refine ⟨hQ.resolvent v-v, ?_⟩
  rw [← hv]
  exact hQ.isFormGenerator_resolvent v

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FiniteOnBoundedSets.of_le_smul (hfinite : FiniteOnBoundedSets m) {C : ℝ≥0}
    (hν : ν ≤ (C:ℝ≥0∞) • m) : FiniteOnBoundedSets ν := by
  intro s hs
  have H : (C:ℝ≥0∞)*m s < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite s hs)
  exact lt_of_le_of_lt (hν s) (by simpa only [Measure.smul_apply,smul_eq_mul] using H)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalGradientParallelogram.change_measure (hpar : LocalGradientParallelogram m)
    {C D : ℝ≥0} (hm : m ≤ (C:ℝ≥0∞) • ν) (hν : ν ≤ (D:ℝ≥0∞) • m) :
    LocalGradientParallelogram ν := by
  intro f g hf hg
  have hfm := (localSobolev_iff_of_comparable hm hν f).mpr hf
  have hgm := (localSobolev_iff_of_comparable hm hν g).mpr hg
  apply (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  filter_upwards [hpar f g hfm hgm,weakGradient_eq_of_comparable hm hν f,
    weakGradient_eq_of_comparable hm hν g,
    weakGradient_eq_of_comparable hm hν (fun x => f x+g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x-g x)] with x hp hf hg hplus hminus
  rwa [hf,hg,hplus,hminus] at hp

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ChangeLpLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_toLp {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Lp.LpToLpOfMeasureLeSMul hc hν (hf.toLp f) =
      (hf.of_measure_le_smul hc hν).toLp f := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν (hf.toLp f)).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.coeFn_toLp).trans
      (hf.of_measure_le_smul hc hν).coeFn_toLp.symm)

omit [MetricSpace X] [BorelSpace X] in
lemma tendsto_toLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {fs : ℕ → X → ℝ} {f : X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m)
    (h : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ((hfs n).of_measure_le_smul hc hν).toLp (fs n))
      atTop (𝓝 ((hf.of_measure_le_smul hc hν).toLp f)) := by
  have H := (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν).continuous.tendsto _ |>.comp h
  simpa only [Function.comp_def, changeLp_toLp] using H

omit [BorelSpace X] in
lemma FiniteOnBoundedSets.of_measure_le_smul (hm : FiniteOnBoundedSets m)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m) : FiniteOnBoundedSets ν := by
  intro B hB
  exact lt_of_le_of_lt (hν B) (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hm B hB))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientNormTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_norm_tendsto_of_sq_upper {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, ‖Dn n‖^2 ≤ ‖D‖^2+ε n) :
    Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    filter_upwards [hf.eventually
      ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dn n,hn n,hle⟩)
  · intro b hb
    have hbpos : 0 < b := lt_of_le_of_lt (norm_nonneg D) hb
    have hgap : 0 < b^2-‖D‖^2 := by nlinarith [norm_nonneg D]
    filter_upwards [hε.eventually (gt_mem_nhds hgap)] with n hn'
    nlinarith [hbound n, norm_nonneg (Dn n)]

lemma exists_lipschitz_strong_slopes (hfinite : FiniteOnBoundedSets m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ hDs : ∀ n, MemLp (fun x => (localSlope (fs n) x).toReal) 2 m,
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
        Tendsto (fun n => (hDs n).toLp (fun x => (localSlope (fs n) x).toReal))
          atTop (𝓝 D) := by
  have hex (n : ℕ) := cheegerEnergy_lt_approx (f := f)
    (a := ENNReal.ofReal (‖D‖^2/2+1/((n:ℝ)+1)))
    (by rw [henergy]; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (lt_add_of_pos_right _ (by positivity)))
    (ε := 1/((n:ℝ)+1)) (by positivity)
  choose fs hLip hfs hdist hEn using hex
  have hfin (n : ℕ) : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) : MemLp (fun x => (localSlope (fs n) x).toReal) 2 m :=
    memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  have hfn : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hDn (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) := by
    exact (localSlope_isLocalWeakUpperGradient hfinite (hLip n).choose_spec).congr_ae
      (hfs n).coeFn_toLp.symm (hDs n).coeFn_toLp.symm
  have hbound (n : ℕ) : ‖Dn n‖^2 ≤ ‖D‖^2 + 2*(1/((n:ℝ)+1)) := by
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' : ‖Dn n‖^2/2 < ‖D‖^2/2+1/((n:ℝ)+1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    linarith
  refine ⟨fs,hLip,hfs,hDs,hfn,?_⟩
  apply hD.tendsto_of_norm_tendsto hDn hfn
  exact upperGradient_norm_tendsto_of_sq_upper hDn hfn (fun _ hE => hD.norm_le hE)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))) hbound

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyComparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

lemma cheegerEnergy_eq_of_comparable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (hfinite : FiniteOnBoundedSets m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D‖^2/2) := by
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 ν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν
  obtain ⟨fs,hLip,hfs,hDs,hf,hG⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  have hfn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hfs (Lp.memLp f)
    (by simpa only [Lp.toLp_coeFn] using hf)
  have hDn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hDs (Lp.memLp D)
    (by simpa only [Lp.toLp_coeFn] using hG)
  have hDf : ((Lp.memLp D).of_measure_le_smul ENNReal.coe_ne_top hν).toLp (D : X → ℝ) = T D := rfl
  rw [hDf] at hDn
  have he : Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂ν) atTop (𝓝 (ENNReal.ofReal (‖T D‖^2/2))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hDn.norm.pow 2).div_const 2)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact half_lintegral_localSlope_eq (hLip n).choose_spec
      ((hDs n).of_measure_le_smul ENNReal.coe_ne_top hν)
  have hle : cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖T D‖^2/2) := by
    have H := cheegerEnergy_le_liminf
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
      (fun n => ⟨hLip n,(hfs n).of_measure_le_smul ENNReal.coe_ne_top hν⟩)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
        (fun n => (hfs n).of_measure_le_smul ENNReal.coe_ne_top hν)
        (f : X → ℝ) ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)).mp hfn)
    rwa [he.liminf_eq] at H
  have hDν : IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (T D) :=
    (hD.change_measure hm hν).congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D).symm
  obtain ⟨D',hD',hlo⟩ := exists_minimalGradient_energy_le_cheeger
    (hfinite.of_measure_le_smul ENNReal.coe_ne_top hν)
    ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have heq : D' = T D := Lp.ext (hD'.ae_eq hDν)
  rw [heq] at hlo
  exact le_antisymm hle hlo

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevCheegerEnergyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma cheegerEnergy_integral_of_comparable (hfinite : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy ν f = ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂ν)/2) := by
  let f' := hf.1.toLp f
  let D' := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (f' : X → ℝ) (D' : X → ℝ) :=
    (weakGradient_isMinimal hf.2.1.2).congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (f' : X → ℝ) = ENNReal.ofReal (‖D'‖^2/2) := by
    rw [cheegerEnergy_congr_ae hf.1.coeFn_toLp,hID f hf,norm_toLp_sq_eq_integral]
  have H := cheegerEnergy_eq_of_comparable hfinite hm hν hD he
  have ha : (f' : X → ℝ) =ᵐ[ν] f := (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.1.coeFn_toLp
  rw [cheegerEnergy_congr_ae ha] at H
  rw [H]
  congr 2
  let Dν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D'
  have heq : Dν = (hf.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).toLp (weakGradient m f) :=
    changeLp_toLp ENNReal.coe_ne_top hν hf.2.2
  change ‖Dν‖^2 = _
  rw [heq,norm_toLp_sq_eq_integral]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_DecayWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma densityMeasure_probability_of_integrable (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) (hmass : ∫ x,u x ∂m = 1) :
    IsProbabilityMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hu,hmass,ENNReal.ofReal_one]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TruncatedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal

lemma truncatedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (truncatedLog a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (truncatedLog_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (truncatedLog a) = (fun x => (max a x)⁻¹) from funext (truncatedLog_deriv ha)]
  exact (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))

lemma truncatedLog_eq {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    truncatedLog a x = Real.log x := by
  have H : (∫ s in a..x, (max a s)⁻¹) = Real.log x-Real.log a := by
    calc
      (∫ s in a..x, (max a s)⁻¹) = ∫ s in a..x, s⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hax] at hs
        exact congrArg Inv.inv (max_eq_right hs.1)
      _ = Real.log x-Real.log a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          rw [uIcc_of_le hax] at hs
          exact Real.hasDerivAt_log (ne_of_gt (ha.trans_le hs.1))
        · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt (ha.trans_le hs.1))).intervalIntegrable_of_Icc hax
  dsimp only [truncatedLog]
  rw [H]
  ring

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

lemma regularizedEntropy_zero (a : ℝ) : regularizedEntropy a 0 = 0 := by
  simp [regularizedEntropy]
lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedLog a) ((max a (x+a))⁻¹) x := by
  simpa only [regularizedLog,Function.comp_def,mul_one] using!
    ((truncatedLog_hasDeriv ha (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub_const (Real.log a)
lemma regularizedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedLog a) x = (max a (x+a))⁻¹ := (regularizedLog_hasDeriv ha x).deriv
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]
lemma regularizedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedLog a) x| ≤ a⁻¹ := by
  rw [regularizedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a (x+a))))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma regularizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedEntropy a) (regularizedLog a x) x := by
  have hc := (regularizedLog_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-(Real.log a+1)*x := by
  let F : ℝ → ℝ := fun y => (y+a)*Real.log (y+a)-(Real.log a+1)*y
  have hF (y : ℝ) (hy : y ∈ uIcc 0 x) : HasDerivAt F (regularizedLog a y) y := by
    rw [uIcc_of_le hx] at hy
    have hypos : 0 < y+a := by linarith [hy.1]
    have H := ((Real.hasDerivAt_mul_log hypos.ne').comp y ((hasDerivAt_id y).add_const a)).sub
      ((hasDerivAt_id y).const_mul (Real.log a+1))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    rw [regularizedLog_eq ha hy.1]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((regularizedLog_contDiff ha).continuous.intervalIntegrable 0 x)
  change regularizedEntropy a x = F x-F 0 at H
  rw [H]
  dsimp [F]
  ring_nf

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma regularizedEntropy_hasFDeriv {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, regularizedEntropy a (v x) ∂m)
      (innerSL ℝ ((regularizedLog_memLp ha u).toLp (fun x => regularizedLog a (u x)))) u :=
  hasFDerivAt_integral_quadratic (regularizedEntropy_hasDeriv ha) (regularizedLog_lipschitz ha)
    (regularizedEntropy_zero a) (regularizedLog_zero a) u

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiffLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.comp_contDiff_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) :
    Sobolev m (φ ∘ f) := by
  have hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ (L:ℝ) :=
    ae_of_all _ (fun x => norm_deriv_le_of_lipschitz hLip)
  have hmeas : AEStronglyMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf.1.aemeasurable).abs.aestronglyMeasurable
  apply Sobolev.of_upperGradient hfinite (hLip.comp_memLp hzero hf.1)
    ((weakGradient_isMinimal hf.2.1.2).1.comp_contDiff hf.1.aemeasurable hφ hB)
  simpa only [mul_comm] using memLp_mul_bounded hf.2.2 hmeas (by simpa only [abs_abs] using hB)

lemma IsLaplacian.regularizedLog_identity (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {a : ℝ} (ha : 0 < a) :
    (∫ x, A x * regularizedLog a (u x) ∂m) =
      -(∫ x, (weakGradient m u x)^2 / (u x+a) ∂m) := by
  have hv := hu.1.comp_contDiff_lipschitz hfinite (regularizedLog_contDiff ha)
    (regularizedLog_lipschitz ha) (regularizedLog_zero a)
  have hgamma := gamma_comp_contDiff hfinite hpar hu.1.2.1 hu.1.2.1
    (regularizedLog_contDiff ha) hv.2.1.1 (ae_of_all _ (fun x => regularizedLog_deriv_bound ha (u x)))
  have heq : (∫ x, gamma m u (regularizedLog a ∘ u) x ∂m) =
      (∫ x, (weakGradient m u x)^2/(u x+a) ∂m) := by
    apply integral_congr_ae
    filter_upwards [gamma_comm (m := m) u (regularizedLog a ∘ u), hgamma,
      gamma_self (m := m) u,hun] with x hc hg hs hx
    rw [hc,hg,hs,regularizedLog_deriv ha,max_eq_right (by linarith : a ≤ u x+a)]
    exact inv_mul_eq_div _ _
  have H := hu.2.2 (regularizedLog a ∘ u) hv
  rw [heq] at H
  simp only [Function.comp_apply] at H
  linarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_FormAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma regularizedLog_weighted_gamma (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u f : X → ℝ}
    (hu : Sobolev m u) (hf : Sobolev m f)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    (fun x => (u x+ε)*gamma m f (regularizedLog ε ∘ u) x) =ᵐ[m] gamma m f u := by
  have hr := hu.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
  filter_upwards [gamma_comp_contDiff hfin hpar hu.2.1 hf.2.1
    (regularizedLog_contDiff hε) hr.2.1.1
    (ae_of_all _ fun x => regularizedLog_deriv_bound hε (u x)),
    gamma_comm (m := m) f (regularizedLog ε ∘ u),gamma_comm (m := m) u f,hun]
    with x hc h1 h2 hn
  rw [h1,hc,regularizedLog_deriv hε,max_eq_right (by linarith : ε ≤ u x+ε),h2]
  have hnz : u x+ε ≠ 0 := ne_of_gt (by linarith)
  field_simp

lemma weighted_gradient_add_smul (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {ρ : X → ℝ} (hρm : AEStronglyMeasurable ρ m) {B : ℝ}
    (hρb : ∀ᵐ x ∂m, |ρ x| ≤ B) (c : ℝ) :
    (∫ x, ρ x*(weakGradient m (f+c•g : Lp ℝ 2 m) x)^2 ∂m) =
      (∫ x, ρ x*(weakGradient m f x)^2 ∂m) +
      2*c*(∫ x, ρ x*gamma m f g x ∂m) +
      c^2*(∫ x, ρ x*(weakGradient m g x)^2 ∂m) := by
  have hfe : Integrable (fun x => ρ x*(weakGradient m f x)^2) m :=
    hf.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hge : Integrable (fun x => ρ x*(weakGradient m g x)^2) m :=
    hg.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hfge : Integrable (fun x => ρ x*gamma m f g x) m :=
    (integrable_gamma hfin hf hg).bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hre : (f+c•g : Lp ℝ 2 m) =ᵐ[m] (fun x => f x+c*g x) := by
    filter_upwards [Lp.coeFn_add f (c•g),Lp.coeFn_smul c g] with x ha hc
    simp only [ha,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ∫ x, ρ x*(weakGradient m f x)^2+
        2*c*(ρ x*gamma m f g x)+c^2*(ρ x*(weakGradient m g x)^2) ∂m := by
      apply integral_congr_ae
      filter_upwards [weakGradient_congr_ae hre,
        weakGradient_linear_combination_sq hfin hpar hf.2.1 hg.2.1 c] with x hre hx
      rw [hre,hx]; ring
    _ = _ := by
      have h1 := integral_add (hfe.add (hfge.const_mul (2*c))) (hge.const_mul (c^2))
      have h2 := integral_add hfe (hfge.const_mul (2*c))
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2,integral_const_mul,integral_const_mul]

lemma FormActionBound.logarithmic_shift_exact
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) (hv : FormActionBound m (fun x => u x+ε) v A)
    (t : ℝ) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    FormActionBound m (fun x => u x+ε) (v+t•L)
      (A-2*t*⟪v+t•L,r⟫_ℝ+t^2*⟪L,r⟫_ℝ) := by
  dsimp only
  let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
  have hre : (r : X → ℝ) =ᵐ[m] regularizedLog ε ∘ (u : X → ℝ) :=
    (regularizedLog_memLp hε u).coeFn_toLp
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae hre).mpr
    (hu.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  have hρm : AEStronglyMeasurable (fun x => u x+ε) m :=
    (Lp.memLp u).aestronglyMeasurable.add_const ε
  have hρb : ∀ᵐ x ∂m, |u x+ε| ≤ B+ε := by
    filter_upwards [hub] with x hx
    exact (abs_add_le _ _).trans (by rw [abs_of_pos hε]; linarith)
  have hcross (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      (∫ x, (u x+ε)*gamma m f r x ∂m) = -⟪L,f⟫_ℝ := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, gamma m f u x ∂m := by
        apply integral_congr_ae
        filter_upwards [gamma_congr_ae (Filter.EventuallyEq.rfl : (f : X → ℝ) =ᵐ[m] f) hre,
          regularizedLog_weighted_gamma hfin hpar hu.1 hf hun hε] with x h1 h2
        rw [h1]; exact h2
      _ = ∫ x, gamma m u f x ∂m := integral_congr_ae (gamma_comm _ _)
      _ = _ := by
        rw [hu.2.2 f hf]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [RCLike.inner_apply,conj_trivial]; ring
  have hrq : (∫ x, (u x+ε)*(weakGradient m r x)^2 ∂m) = -⟪L,r⟫_ℝ := by
    rw [← hcross r hr]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (r : X → ℝ)] with x hx
    rw [hx]
  change FormActionBound m (fun x => u x+ε) (v+t•L)
    (A-2*t*⟪v+t•L,r⟫_ℝ+t^2*⟪L,r⟫_ℝ)
  intro f hf
  have hfr : Sobolev m (f+t•r : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hr.const_mul t))
    filter_upwards [Lp.coeFn_add f (t•r),Lp.coeFn_smul t r] with x ha hs
    simp only [ha,hs,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := hv (f+t•r) hfr
  rw [weighted_gradient_add_smul hfin hpar hf hr hρm hρb t,hcross f hf,hrq] at H
  simp only [inner_add_right,inner_smul_right,inner_add_left,real_inner_smul_left] at H ⊢
  nlinarith

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FormActionBound.mono {ρ : X → ℝ} {v : Lp ℝ 2 m} {A B : ℝ}
    (h : FormActionBound m ρ v A) (hAB : A ≤ B) : FormActionBound m ρ v B :=
  fun f hf => by linarith [h f hf]

lemma FormActionBound.logarithmic_shift
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) (hv : FormActionBound m (fun x => u x+ε) v A)
    (t : ℝ) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    FormActionBound m (fun x => u x+ε) (v+t•L) (A-2*t*⟪v+t•L,r⟫_ℝ) := by
  apply (hv.logarithmic_shift_exact hfin hpar hu hun hub hε t).mono
  have hi : ⟪L,(regularizedLog_memLp hε u).toLp
      (fun x => regularizedLog ε (u x))⟫_ℝ ≤ 0 := by
    rw [L2.inner_def]
    have he : (∫ x, inner ℝ (L x) ((regularizedLog_memLp hε u).toLp
        (fun x => regularizedLog ε (u x)) x) ∂m) =
        ∫ x, L x * regularizedLog ε (u x) ∂m := by
      apply integral_congr_ae
      filter_upwards [(regularizedLog_memLp hε u).coeFn_toLp] with x hx
      simp only [hx,RCLike.inner_apply,conj_trivial]; ring
    rw [he,hu.regularizedLog_identity hfin hpar hun hε]
    apply neg_nonpos.mpr
    exact integral_nonneg_of_ae (hun.mono fun x hx =>
      div_nonneg (sq_nonneg _) (by linarith))
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hi)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_DensityHamiltonJacobi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma FormActionBound.hamiltonJacobi_slope
    {u W : ℝ → Lp ℝ 2 m} {s q A ε : ℝ} {v : Lp ℝ 2 m}
    (hu : HasDerivAt u v s) (hqs : 0 < q+s)
    (hS : Sobolev m (W s : X → ℝ))
    (hΓ : MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hun : ∀ z, s < z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ z, s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : FormActionBound m (fun x => u s x+ε) v A) :
    ∀ r, (A+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r →
      ∀ᶠ z in 𝓝[>] s, slope (fun t => ⟪W t,u t⟫_ℝ) s z < r := by
  let Γ : Lp ℝ 2 m := hΓ.toLp (fun x => (weakGradient m (W s) x)^2)
  have hΓe : Γ =ᵐ[m] fun x => (weakGradient m (W s) x)^2 := hΓ.coeFn_toLp
  have hpair (z : ℝ) : ⟪Γ,u z⟫_ℝ = ∫ x, u z x*(weakGradient m (W s) x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΓe] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real]
  have hρΓ : Integrable (fun x => u s x*(weakGradient m (W s) x)^2) m :=
    (L2.integrable_inner (u s) Γ).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have hE : (∫ x, (u s x+ε)*(weakGradient m (W s) x)^2 ∂m) =
      ⟪Γ,u s⟫_ℝ+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hρΓ (hS.2.2.integrable_sq.const_mul ε),integral_const_mul,← hpair s]
  have hAa := hA (W s) hS
  rw [hE,real_inner_comm (W s) v] at hAa
  have hder : HasDerivAt (fun z => ⟪W s,u z⟫_ℝ) ⟪W s,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s (W s)).inner ℝ hu
  have hsl : Tendsto (slope (fun z => ⟪W s,u z⟫_ℝ) s) (𝓝[>] s) (𝓝 ⟪W s,v⟫_ℝ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] s) (𝓝 s) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun z => -(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      slope (fun z => ⟪W s,u z⟫_ℝ) s z) (𝓝[>] s)
      (𝓝 (-⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ)) := by
    have hdnom : Tendsto (fun z => 2*(q+z)) (𝓝[>] s) (𝓝 (2*(q+s))) :=
      (tendsto_const_nhds.add hid).const_mul 2
    have hpl : Tendsto (fun z => ⟪Γ,u z⟫_ℝ) (𝓝[>] s) (𝓝 ⟪Γ,u s⟫_ℝ) :=
      (continuousAt_const.inner hu.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have HH := (((tendsto_const_nhds (x := -(q+s))).div hdnom
      (by positivity : 2*(q+s) ≠ 0)).mul hpl).add hsl
    convert HH using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp [hqs.ne']
  intro r hr
  have hlt : -⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ < r := by linarith
  filter_upwards [hlim.eventually_lt_const hlt,self_mem_nhdsWithin] with z hz hzs
  change s < z at hzs
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field,slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hzs)).mpr
  have hiW : Integrable (fun x => (W z x-W s x)*u z x) m :=
    (L2.integrable_inner (u z) (W z)).sub (L2.integrable_inner (u z) (W s)) |>.congr (by
      filter_upwards [] with x
      simp only [RCLike.inner_apply,RCLike.conj_to_real,Pi.sub_apply]
      ring)
  have hiΓ : Integrable (fun x => (weakGradient m (W s) x)^2*u z x) m :=
    (L2.integrable_inner Γ (u z)).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have H := integral_mono_ae hiW (hiΓ.const_mul (-(z-s)*(q+s)/(2*(q+z)))) (by
    filter_upwards [hHJ z hzs,hun z hzs] with x hx hn
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx hn)
  have hI : (∫ x, (W z x-W s x)*u z x ∂m) = ⟪W z-W s,u z⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (W z) (W s)] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm,Pi.sub_apply]
  rw [hI,integral_const_mul] at H
  have hIΓ : (∫ x, (weakGradient m (W s) x)^2*u z x ∂m) = ⟪Γ,u z⟫_ℝ := by
    rw [hpair]; congr 1; funext x; ring
  rw [hIΓ,inner_sub_left] at H
  have he : (-(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      (⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ)/(z-s))*(z-s) =
      (-(z-s)*(q+s)/(2*(q+z)))*⟪Γ,u z⟫_ℝ+⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ := by
    field_simp [sub_ne_zero.mpr hzs.ne']; ring
  rw [he]
  linarith

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

variable {X : Type*} [MeasurableSpace X]

lemma absolutelyContinuous_exponentialMeasure {m μ : Measure X} {V : X → ℝ}
    (hV : Measurable V) : μ ≪ exponentialMeasure m V ↔ μ ≪ m := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) := by fun_prop
  have hpos : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ 0 :=
    ae_of_all m fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  exact ⟨fun h => h.trans (withDensity_absolutelyContinuous _ _),
    fun h => h.trans (withDensity_absolutelyContinuous' hmeas.aemeasurable hpos)⟩

lemma llr_exponentialMeasure {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {V : X → ℝ} (hμ : μ ≪ m) (hV : Measurable V) :
    llr μ (exponentialMeasure m V) =ᵐ[μ] fun x => llr μ m x - V x := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) := by fun_prop
  have hpos : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ 0 :=
    ae_of_all m fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have htop : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ ∞ :=
    ae_of_all m fun _ => ENNReal.ofReal_ne_top
  have hrn := Measure.rnDeriv_withDensity_right μ m hmeas.aemeasurable hpos htop
  filter_upwards [hμ.ae_eq hrn, Measure.rnDeriv_pos hμ,
    hμ.ae_le (Measure.rnDeriv_lt_top μ m)] with x hx hp ht
  change Real.log (μ.rnDeriv (exponentialMeasure m V) x).toReal =
    Real.log (μ.rnDeriv m x).toReal - V x
  dsimp only [exponentialMeasure]
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (inv_ne_zero (Real.exp_ne_zero _))
      (ENNReal.toReal_ne_zero.mpr ⟨hp.ne', ht.ne⟩), Real.log_inv, Real.log_exp]
  ring

lemma finiteEntropy_exponentialMeasure_iff {m μ : Measure X}
    [SigmaFinite m] [IsFiniteMeasure μ] {V : X → ℝ}
    (hV : Measurable V) (hVi : Integrable V μ) :
    FiniteEntropy (exponentialMeasure m V) μ ↔ FiniteEntropy m μ := by
  constructor
  · rintro ⟨ha, hi⟩
    have ha' := (absolutelyContinuous_exponentialMeasure hV).mp ha
    refine ⟨ha', ?_⟩
    have hs : Integrable (fun x => llr μ m x - V x) μ :=
      hi.congr (llr_exponentialMeasure ha' hV)
    have hh : Integrable (fun x => (llr μ m x - V x) + V x) μ := hs.add hVi
    simpa only [sub_add_cancel] using hh
  · rintro ⟨ha, hi⟩
    exact ⟨(absolutelyContinuous_exponentialMeasure hV).mpr ha,
      (hi.sub hVi).congr (llr_exponentialMeasure ha hV).symm⟩

theorem entropyReal_exponentialMeasure {m μ : Measure X}
    [SigmaFinite m] [IsFiniteMeasure μ] {V : X → ℝ}
    (hμ : FiniteEntropy m μ) (hV : Measurable V) (hVi : Integrable V μ) :
    entropyReal (exponentialMeasure m V) μ = entropyReal m μ - ∫ x, V x ∂μ := by
  rw [entropyReal, integral_congr_ae (llr_exponentialMeasure hμ.1 hV),
    integral_sub hμ.2 hVi, entropyReal]

end WeakHessian

open Set Filter MeasureTheory InformationTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_MulLogFenchel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

lemma mul_log_fenchel {r a : ℝ} (hr : 0 ≤ r) : r*a-Real.exp a+r ≤ r*Real.log r := by
  rcases hr.eq_or_lt with hr|hr
  · simp only [← hr,zero_mul,add_zero,sub_nonpos]
    exact (Real.exp_pos _).le
  · have H := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos a) hr)
    rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at H
    have := (mul_le_mul_of_nonneg_left H hr.le)
    simp only [mul_sub,mul_div_cancel₀ _ hr.ne',mul_one] at this
    nlinarith

universe u

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyDensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m μ : Measure X}
variable [SigmaFinite m] [IsProbabilityMeasure μ]

lemma entropyReal_le_log_density_cap (hμ : FiniteEntropy m μ)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal m μ ≤ Real.log B := by
  have hr := hμ.1.ae_le (rnDeriv_le_of_le_smul hd)
  have hp := Measure.rnDeriv_pos hμ.1
  have ht := hμ.1.ae_le (Measure.rnDeriv_lt_top μ m)
  have hlog : ∀ᵐ x ∂μ,llr μ m x ≤ Real.log B := by
    filter_upwards [hr,hp,ht] with x hx hp ht
    change Real.log (μ.rnDeriv m x).toReal ≤ Real.log B
    apply (Real.log_le_log_iff (ENNReal.toReal_pos hp.ne' ht.ne)
      (show 0 < (B : ℝ) from hB)).mpr
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)
  simpa only [entropyReal,integral_const,probReal_univ,one_smul] using
    integral_mono_ae hμ.2 (integrable_const (Real.log (B : ℝ))) hlog

lemma entropyReal_lower_confinement (hμ : FiniteEntropy m μ) {V : X → ℝ}
    (hV : Integrable V μ) (he : Integrable (fun x => Real.exp (-V x)) m) :
    1-(∫ x,V x ∂μ)-(∫ x,Real.exp (-V x) ∂m) ≤ entropyReal m μ := by
  have hρ := Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)
  have hp := (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hV
  have hl := (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono_ae ((hp.neg.sub he).add hρ) hl (ae_of_all _ fun x => by
    have H := mul_log_fenchel (r := (μ.rnDeriv m x).toReal) (a := -V x) ENNReal.toReal_nonneg
    simpa only [mul_neg,Pi.add_apply,Pi.sub_apply,Pi.neg_apply] using H)
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at H
  have hiA := integral_add (hp.neg.sub he) hρ
  have hiS := integral_sub hp.neg he
  simp only [Pi.sub_apply,Pi.neg_apply] at hiA hiS
  rw [hiA,hiS,integral_neg,
    integral_toReal_rnDeriv_mul hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1] at H
  simp only [probReal_univ] at H
  linarith

lemma entropyReal_exponential_upper (hμ : FiniteEntropy m μ)
    {V : X → ℝ} (hV : Measurable V) {C : ℝ} (hC : ∀ x,|V x| ≤ C)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal (exponentialMeasure m V) μ ≤ Real.log B - ∫ x,V x ∂μ := by
  have hi : Integrable V μ := Integrable.of_bound hV.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  rw [entropyReal_exponentialMeasure hμ hV hi]
  exact sub_le_sub_right (entropyReal_le_log_density_cap hμ hB hd) _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma quadraticTransportCost_eq_integral [SecondCountableTopology X] {q : Measure (X×X)}
    (hq : QuadraticTransportCost q ≠ ∞) :
    QuadraticTransportCost q = ENNReal.ofReal (∫ p : X×X, dist p.1 p.2^2 ∂q) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_squared_distance_of_cost hq)
    (ae_of_all _ fun _ => sq_nonneg _)]
  simp only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg]

end WeakHessian
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropySlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile5
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_le_sqrt_integral_sq {m : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x,f x*g x ∂m) ≤ Real.sqrt (∫ x,f x^2 ∂m)*Real.sqrt (∫ x,g x^2 ∂m) := by
  have he : (∫ x,f x*g x ∂m) = ⟪hf.toLp f,hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he,← norm_toLp_sq_eq_integral hf,← norm_toLp_sq_eq_integral hg,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

end WeakHessian

end
end InlinedFile5

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RegularizedEntropyIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma regularizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    Integrable (fun x => regularizedEntropy a (u x)) m := by
  apply ((Lp.memLp u).integrable_sq.const_mul a⁻¹).mono'
    ((show Continuous (regularizedEntropy a) from continuous_iff_continuousAt.mpr
      (fun y => (regularizedEntropy_hasDeriv ha y).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun y _ => regularizedEntropy_hasDeriv ha y) (regularizedLog_lipschitz ha).lipschitzOnWith
      (a := 0) (b := u x) (mem_univ _) (mem_univ _)
    simpa only [regularizedEntropy_zero,regularizedLog_zero,zero_mul,sub_zero,Real.norm_eq_abs,sq_abs,NNReal.coe_mk] using! H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RenormalizedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

lemma renormalizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    renormalizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-x := by
  rw [renormalizedEntropy,regularizedEntropy_eq ha hx]
  ring

lemma renormalizedEntropy_lower {a x w : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hw : 0 < w) :
    x*Real.log w-w ≤ renormalizedEntropy a x := by
  by_cases hz : x = 0
  · simp only [hz,renormalizedEntropy,regularizedEntropy_zero,mul_zero,zero_add,zero_mul,zero_sub]
    linarith
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have H := Real.log_le_sub_one_of_pos (div_pos hw hxp)
  rw [Real.log_div hw.ne' hxp.ne'] at H
  have HH := mul_le_mul_of_nonneg_left H hx
  have hdiv : x*(w/x-1)=w-x := by field_simp
  rw [hdiv] at HH
  have hxlog := mul_le_mul_of_nonneg_left (Real.log_le_log hxp (le_add_of_nonneg_right ha.le)) hx
  have halog := mul_le_mul_of_nonneg_left (Real.log_le_log ha (le_add_of_nonneg_left hx)) ha.le
  rw [renormalizedEntropy_eq ha hx]
  nlinarith

lemma renormalizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (renormalizedEntropy a) (regularizedLog a x+Real.log a) x := by
  simpa only [renormalizedEntropy,Pi.add_apply,id_eq,mul_one] using! (regularizedEntropy_hasDeriv ha x).add
    ((hasDerivAt_id x).const_mul (Real.log a))

lemma renormalizedEntropy_upper {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    renormalizedEntropy a x ≤ x^2/2 := by
  let F (y : ℝ) := renormalizedEntropy a y-y^2/2
  have hd (y : ℝ) : HasDerivAt F (regularizedLog a y+Real.log a-y) y := by
    convert! (renormalizedEntropy_hasDeriv ha y).sub (((hasDerivAt_id y).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (simp only [id_eq]; ring)
  have H : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Ici 0)
      rw [regularizedLog_eq ha hy0]
      have HH := Real.log_le_sub_one_of_pos (by linarith : 0 < y+a)
      linarith
  have HH := H (show (0:ℝ) ∈ Ici 0 from (by simp)) hx hx
  have hF0 : F 0 = 0 := by simp [F,renormalizedEntropy,regularizedEntropy_zero]
  rw [hF0] at HH
  dsimp [F] at HH
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_le_one (n : ℕ) : fisherEpsilon n ≤ 1 := by
  unfold fisherEpsilon
  exact (div_le_one (by positivity)).mpr (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RadialEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile30
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma squareDensity_entropy_eq [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    entropyReal m (squareDensityMeasure m w) = ∫ x,w x^2*Real.log (w x^2) ∂m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density hac]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma squareDensity_finiteEntropy_iff [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    FiniteEntropy m (squareDensityMeasure m w) ↔ Integrable (fun x => w x^2*Real.log (w x^2)) m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [FiniteEntropy,and_iff_right hac,← integrable_rnDeriv_mul_log_iff hac]
  apply integrable_congr
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

end WeakHessian

end
end InlinedFile30

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma renormalizedEntropy_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => renormalizedEntropy (fisherEpsilon n) x) atTop (𝓝 (reducedEntropy x)) := by
  have h1 := Real.continuous_mul_log.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x)).add fisherEpsilon_tendsto)
  have h2 := Real.continuous_mul_log.continuousAt.tendsto.comp fisherEpsilon_tendsto
  convert! (h1.sub h2).sub_const x using 1
  · ext n
    exact renormalizedEntropy_eq (fisherEpsilon_pos n) hx
  · simp only [reducedEntropy,add_zero,zero_mul,sub_zero]

lemma renormalizedEntropy_abs_bound {a x V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    |renormalizedEntropy a x| ≤ x^2/2+|x*V|+Real.exp (-V) := by
  have hl := renormalizedEntropy_lower ha hx (Real.exp_pos (-V))
  rw [Real.log_exp,mul_neg] at hl
  have hu := renormalizedEntropy_upper ha ha1 hx
  exact abs_le.mpr ⟨by linarith [le_abs_self (x*V),sq_nonneg x],
    by linarith [abs_nonneg (x*V),Real.exp_pos (-V)]⟩

lemma reducedEntropy_abs_bound {x V : ℝ} (hx : 0 ≤ x) :
    |reducedEntropy x| ≤ x^2/2+|x*V|+Real.exp (-V) :=
  le_of_tendsto ((renormalizedEntropy_tendsto hx).abs)
    (Eventually.of_forall (fun n => renormalizedEntropy_abs_bound (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply (((hu.integrable_sq.div_const 2).add hUV.norm).add hV).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [hun] with x hx
  simpa only [Real.norm_eq_abs,Pi.add_apply,reducedEntropy,Pi.sub_apply,id_eq] using! reducedEntropy_abs_bound (V := V x) hx

lemma tendsto_integral_renormalizedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => u x^2/2+‖u x*V x‖+Real.exp (-V x))
  · intro n
    exact (continuous_iff_continuousAt.mpr fun y =>
      (renormalizedEntropy_hasDeriv (fisherEpsilon_pos n) y).continuousAt).comp_aestronglyMeasurable hu.aestronglyMeasurable
  · exact ((hu.integrable_sq.div_const 2).add hUV.norm).add hV
  · intro n
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs] using renormalizedEntropy_abs_bound (V := V x)
      (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx
  · exact hun.mono (fun x hx => renormalizedEntropy_tendsto hx)
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_InitialHeatLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_mul_tendsto_L2 {ι : Type*} {l : Filter ι}
    {u : ι → Lp ℝ 2 m} {v : Lp ℝ 2 m} (hu : Tendsto u l (𝓝 v))
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n => ∫ x, u n x*f x ∂m) l (𝓝 (∫ x, v x*f x ∂m)) := by
  let F : Lp ℝ 2 m := hf.toLp f
  have hp (w : Lp ℝ 2 m) : (∫ x, w x*f x ∂m) = ⟪F,w⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [F,hx,RCLike.inner_apply,RCLike.conj_to_real]
  simp_rw [hp]
  exact tendsto_const_nhds.inner hu

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_tendsto_nonneg
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hθ : Tendsto θ l (𝓝 t)) (hn : ∀ᶠ i in l, 0 ≤ θ i) :
    Tendsto (fun i => cheegerHeat h (θ i) u) l (𝓝 (cheegerHeat h t u)) :=
  ((cheegerHeat_continuousOn hfin h u) t ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hθ,hn⟩)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfEnergyLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile87
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma continuousOn_integral_boundedHopfMap (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (fun s => ∫ x,boundedHopfMap f s x ∂m) (Ici 0) := by
  intro t ht
  have H := tendsto_bounded_pairing_L1 (m := m)
    (u := fun _ : ℝ => fun _ : X => (1:ℝ)) (v := fun _ : X => (1:ℝ))
    (fun _ => integrable_const _) (integrable_const _)
    (q := boundedHopfMap f) (r := boundedHopfMap f t)
    (continuousOn_boundedHopfMap hf t ht) (by simpa using (tendsto_const_nhds (x := (0:ℝ)) : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[Ici 0] t) (𝓝 0)))
  change Tendsto _ _ _
  simpa using H

end WeakHessianTransport

end
end InlinedFile87

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_GeneratorSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile46
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_eq_square_sqrt (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) :
    densityMeasure m u = squareDensityMeasure m (fun x => Real.sqrt (u x)) := by
  apply withDensity_congr_ae
  filter_upwards [hun] with x hx
  rw [Real.sq_sqrt hx]

end WeakHessian

end
end InlinedFile46

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile48
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_finiteEntropy [SigmaFinite m] (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    [IsFiniteMeasure (densityMeasure m u)] {V : X → ℝ}
    (hUV : Integrable (fun x => u x*V x) m) (hV : Integrable (fun x => Real.exp (-V x)) m) :
    FiniteEntropy m (densityMeasure m u) := by
  have he := densityMeasure_eq_square_sqrt u hun
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_finiteEntropy_iff (Lp.stronglyMeasurable u |>.measurable.sqrt)]
  have H := (integrable_reducedEntropy (Lp.memLp u) hun hUV hV).add hi
  apply H.congr
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,Pi.add_apply,reducedEntropy]
  ring

end WeakHessian

end
end InlinedFile48

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEVI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile51
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma entropyReal_eq_reducedDensity (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hi : Integrable u m) (hr : Integrable (fun x => reducedEntropy (u x)) m)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u) :
    entropyReal m (μ:Measure X) = (∫ x,reducedEntropy (u x) ∂m)+1 := by
  have hmass : (∫ x,u x ∂m) = 1 := by
    have H := integral_densityMeasure m u hun (fun _ => (1:ℝ))
    rw [← hμ] at H
    simpa using H.symm
  have he := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_entropy_eq (Lp.stronglyMeasurable u |>.measurable.sqrt),← hmass,← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,reducedEntropy,sub_add_cancel]

end WeakHessian

end
end InlinedFile51

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_StrongEntropyConfinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.exists_strong_entropy_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  let d := |C|+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hCd : C < d := by dsimp [d]; linarith [le_abs_self C]
  have hvol := cd_ball_volume_bound hN hcd hfull hfin o
  have hbase : MemLp (fun x => Real.exp (-(d*dist x o))) 2 m := by
    simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le
      (show C < 2*d by linarith) hvol
  have hbI : Integrable (fun x => Real.exp (-(d*dist x o))) m := by
    simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le hCd hvol
  refine ⟨2*d,by positivity,?_,?_,?_,?_,?_⟩
  · simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*d by linarith) hvol
  · simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*(2*d) by linarith) hvol
  · apply (hbase.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*d*dist x o)*Real.exp (-(2*d*dist x o))| ≤ |2*Real.exp (-(d*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      have H := (Real.mul_exp_neg_le_exp_neg_one (d*dist x o)).trans
        (show Real.exp (-1) ≤ 1 by rw [Real.exp_le_one_iff]; norm_num)
      have he : (2*d*dist x o)*Real.exp (-(2*d*dist x o)) =
          2*(d*dist x o*Real.exp (-(d*dist x o)))*Real.exp (-(d*dist x o)) := by
        rw [show -(2*d*dist x o) = -(d*dist x o)+(-(d*dist x o)) by ring,Real.exp_add]
        ring
      rw [he]
      nlinarith [Real.exp_pos (-(d*dist x o))]
  · convert! hbase using 1; funext x; congr 1; ring
  · convert! hbI using 1; funext x; congr 1; ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LipschitzMulDist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_mul_dist (o : X) (a : ℝ) :
    LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |a*dist x o-a*dist y o| ≤ |a| * dist x y
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile130
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => cheegerHeat h s u) (cheegerHeat h t A) t := by
  have hc := cheegerHeat_continuousOn hfin h A
  have hat := (hc t ht.le).continuousAt (Ici_mem_nhds ht)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := (hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) t ht) hat).add_const u
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [cheegerHeat_integral_generator hfin h hu hs.le, sub_add_cancel]
end WeakHessian

end
end InlinedFile130

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatPositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile131
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_positive (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t) :
    ∃ A : Lp ℝ 2 m, (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A ∧
      HasDerivAt (fun s => cheegerHeat h s u) A t := by
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨B,hB⟩ := Q.heat_hasFormGenerator m (half_pos ht) u
  change Q.IsFormGenerator (cheegerHeat h (t/2) u) B at hB
  let A := cheegerHeat h (t/2) B
  have hg := Q.formGenerator_heat m hB (t/2)
  have he : cheegerHeat h (t/2) (cheegerHeat h (t/2) u) = cheegerHeat h t u := by
    have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (half_pos ht).le (half_pos ht).le)
    simpa only [add_halves,mul_apply_eq_comp] using H.symm
  change Q.IsFormGenerator (cheegerHeat h (t/2) (cheegerHeat h (t/2) u)) A at hg
  refine ⟨A,he ▸ hg,?_⟩
  have HD := cheegerHeat_deriv_at_generator hfin h hB (half_pos ht)
  have hc := (hasDerivAt_id t).sub_const (t/2)
  have H := HD.scomp_of_eq t hc (by rw [id_eq, sub_half] : t/2 = id t-t/2)
  simp only [Function.comp_def,one_smul,id_eq] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
    (cheegerHeat_add h (show 0 ≤ s-t/2 by linarith) (half_pos ht).le)
  simpa only [sub_add_cancel,mul_apply_eq_comp] using H
end WeakHessian

end
end InlinedFile131

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile181
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2) := by
  rw [hrcd.1.global_cheegerEnergy_eq_weakGradient hfin o hf,norm_toLp_sq_eq_integral]

omit [SigmaFinite m] in
lemma RCD.weighted_cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B)
    {f : X → ℝ} (hf : Sobolev (exponentialMeasure m V) f) :
    cheegerEnergy (exponentialMeasure m V) f =
      ENNReal.ofReal ((∫ x,(weakGradient (exponentialMeasure m V) f x)^2
        ∂exponentialMeasure m V)/2) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hfm := (sobolev_exponentialMeasure_iff hB f).mpr hf
  have H := cheegerEnergy_integral_of_comparable hfin
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν hfm
  rw [H]
  congr 2
  apply integral_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (weakGradient_exponentialMeasure (m := m) hB f)] with x hx
  rw [hx]

end WeakHessian

end
end InlinedFile181

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma cheegerHeat_tendsto_joint
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {u : ι → Lp ℝ 2 m}
    {T : ℝ} {v : Lp ℝ 2 m} (hT : 0 < T)
    (hθ : Tendsto θ l (𝓝 T)) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun z => cheegerHeat h (θ z) (u z)) l (𝓝 (cheegerHeat h T v)) := by
  have hc : ContinuousAt (fun s => cheegerHeat h s v) T :=
    ((cheegerHeat_continuousOn hfin h v) T hT.le).continuousAt (Ici_mem_nhds hT)
  have hz : ∀ᶠ z in l, 0 ≤ θ z :=
    (hθ.eventually (eventually_gt_nhds hT)).mono fun _ hz => hz.le
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ᶠ z in l, dist (cheegerHeat h (θ z) (u z)) (cheegerHeat h T v) ≤
      dist (u z) v + dist (cheegerHeat h (θ z) v) (cheegerHeat h T v) := by
    filter_upwards [hz] with z hz
    have h1 := dist_triangle (cheegerHeat h (θ z) (u z))
      (cheegerHeat h (θ z) v) (cheegerHeat h T v)
    have h2 := cheegerHeat_contractive h hz (u z) v
    exact h1.trans (add_le_add h2 le_rfl)
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hb
  simpa only [zero_add,Function.comp_def] using
    (tendsto_iff_dist_tendsto_zero.mp hu).add
      (tendsto_iff_dist_tendsto_zero.mp (hc.tendsto.comp hθ))

lemma cheegerHeat_diagonal_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s := by
  obtain ⟨L,hL,hLD⟩ := cheegerHeat_deriv_at_positive hfin h (u s) hpos
  refine ⟨L,hL,?_⟩
  have ha : HasDerivAt (fun z => cheegerHeat h (θ z) (u z-u s))
      (cheegerHeat h (θ s) v) s := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have H := cheegerHeat_tendsto_joint hfin h hpos
      (hθ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hu.tendsto_slope
    apply H.congr'
    exact Eventually.of_forall fun z => by
      simp only [slope_def_module,sub_self,map_zero,sub_zero,map_smul]
  have hb : HasDerivAt (fun z => cheegerHeat h (θ z) (u s)) (τ • L) s :=
    hLD.scomp s hθ
  apply (ha.add hb).congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply,map_sub,sub_add_cancel]

lemma cheegerHeat_diagonal_entropy_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m)
        ⟪cheegerHeat h (θ s) v + τ • L,
          (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).toLp
            (fun x => regularizedLog ε (cheegerHeat h (θ s) (u s) x))⟫_ℝ s := by
  obtain ⟨L,hL,hD⟩ := cheegerHeat_diagonal_hasDerivAt hfin h hθ hu hpos
  refine ⟨L,hL,hD,?_⟩
  have H := (regularizedEntropy_hasFDeriv hε (cheegerHeat h (θ s) (u s))).comp_hasDerivAt s hD
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  exact real_inner_comm _ _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_IntegratedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrated_hamiltonJacobi_action
    {W u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {q τ ε D : ℝ}
    (hq : 0 < q) (hε : 0 ≤ ε)
    (hW : ContinuousOn W (Icc 0 1)) (hu : ContinuousOn u (Icc 0 1))
    (hE : ContinuousOn E (Icc 0 1)) (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hWS : ∀ s ∈ Ico (0:ℝ) 1, Sobolev m (W s : X → ℝ))
    (hΓ : ∀ s ∈ Ico (0:ℝ) 1, MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hD : ∀ s ∈ Ico (0:ℝ) 1, (∫ x, (weakGradient m (W s) x)^2 ∂m) ≤ D)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ s z, 0 ≤ s → s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e)) :
    ⟪W 1,u 1⟫_ℝ-⟪W 0,u 0⟫_ℝ+τ*(E 1-E 0) ≤ P 1-P 0+ε*D/2 := by
  choose v e hd he hA using hA
  let J := fun s => ⟪W s,u s⟫_ℝ
  let B := fun s => J 0+(P s-P 0)-τ*(E s-E 0)+ε*D/2*s
  let B' := fun s => if hs : s ∈ Ico (0:ℝ) 1 then a s/2-τ*(e s hs)+ε*D/2 else 0
  have hB : ContinuousOn B (Icc 0 1) := by
    exact (((continuousOn_const.add (hP.sub continuousOn_const)).sub
      ((hE.sub continuousOn_const).const_mul τ)).add (continuousOn_const.mul continuousOn_id))
  have hB' (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt B (B' s) (Ici s) s := by
    dsimp only [B']
    rw [dite_eq_left hs]
    convert! (((((hP' s hs).sub_const (P 0)).const_add (J 0)).sub
      (((he s hs).sub_const (E 0)).const_mul τ)).add
      ((hasDerivAt_id s).const_mul (ε*D/2))).hasDerivWithinAt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have H := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := J) (B := B) (B' := B') (hW.inner hu)
    (by dsimp [B]; simp) hB hB' (by
      intro s hs r hr
      change B' s < r at hr
      dsimp only [B'] at hr
      rw [dite_eq_left hs] at hr
      have hineq : (a s-2*τ*(e s hs)+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r := by
        have HH := mul_le_mul_of_nonneg_left (hD s hs) hε
        linarith
      exact ((hA s hs).hamiltonJacobi_slope (hd s hs)
        (by linarith [hs.1]) (hWS s hs) (hΓ s hs)
        (fun z hz => hun z (by linarith [hs.1]))
        (fun z hz => hHJ s z hs.1 hz) r hineq).frequently) ⟨zero_le_one,le_rfl⟩
  dsimp only [B,J] at H
  linarith

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_PlanHeatEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma compact_dual_of_entropy_actions
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E : ℝ → ℝ → ℝ} {P a : ℝ → ℝ} {τ : ℝ}
    (hu : ContinuousOn u (Icc 0 1))
    (hE : ∀ ε, 0 < ε → ContinuousOn (E ε) (Icc 0 1))
    (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hA : ∀ ε, 0 < ε → ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt (E ε) e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e))
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    ∀ ε, 0 < ε →
      (∫ x, u 1 x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, u 0 x*boundedHopfMap f q x ∂m)+τ*(E ε 1-E ε 0) ≤ P 1-P 0+ε*compactHopfDualBound hfin o f hf hq/2 := by
  let data := compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)
  let W := data.choose
  obtain ⟨hWe,hWc,hWS,hΓ,hD,hHJ⟩ := data.choose_spec.choose_spec
  intro ε hε
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc 0 1) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_action (W := fun s => W (q+s)) hq hε.le
    (hWc.comp (by fun_prop) hmap) hu (hE ε hε) hP hP'
    (fun s hs => hWS _ (by linarith [hs.1]))
    (fun s hs => hΓ _ (by linarith [hs.1]))
    (fun s hs => hD _ (hmap ⟨hs.1,hs.2.le⟩)) hun
    (fun s z hs hsz => by
      have H := hHJ (q+s) (q+z) (by linarith) (by linarith)
      simpa only [add_sub_add_left_eq_sub] using H) (hA ε hε)
  have hpair (s : ℝ) (hs : 0 ≤ s) : ⟪W (q+s),u s⟫_ℝ =
      ∫ x, u s x*boundedHopfMap f (q+s) x ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWe (q+s) (by linarith)] with x hx
    simp only [W,hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair 1 zero_le_one,hpair 0 le_rfl] at H
  simpa only [add_zero,compactHopfDualBound,data] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEntropyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FormActionBound.zero {ρ : X → ℝ} (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) :
    FormActionBound m ρ (0 : Lp ℝ 2 m) 0 := by
  intro f _hf
  have H : 0 ≤ ∫ x, ρ x*(weakGradient m (f : X → ℝ) x)^2 ∂m :=
    integral_nonneg_of_ae (hρ.mono fun _ hx => mul_nonneg hx (sq_nonneg _))
  simpa only [inner_zero_left,mul_zero,sub_nonpos,zero_add] using H

lemma cheegerHeat_entropy_action
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {θ : ℝ → ℝ} {s τ ε : ℝ} (hθ : HasDerivAt θ τ s)
    (hpos : 0 < θ s) (hε : 0 < ε) :
    ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt (fun z => cheegerHeat h (θ z) u) v s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) u x) ∂m) e s ∧
      FormActionBound m (fun x => cheegerHeat h (θ s) u x+ε) v (-2*τ*e) := by
  obtain ⟨L,hL,hD,hE⟩ := cheegerHeat_diagonal_entropy_hasDerivAt hfin h hθ
    (hasDerivAt_const s u) hpos hε
  simp only [map_zero,zero_add] at hD hE
  refine ⟨_,_,hD,hE,?_⟩
  have hPb := cheegerHeat_bounded h hpos.le hB u hub
  have hPn := cheegerHeat_nonneg h hpos.le u hun
  have hA : FormActionBound m (fun x => cheegerHeat h (θ s) u x+ε) (0 : Lp ℝ 2 m) 0 :=
    FormActionBound.zero (hPn.mono fun _ hx => add_nonneg hx hε.le)
  have H := hA.logarithmic_shift hfin hpar
    (identified_isLaplacian_of_formGenerator hfin hID h _ _ hL) hPn hPb hε τ
  simpa only [zero_add,zero_sub,neg_mul] using H

lemma cheegerHeat_entropy_dual_positive
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, cheegerHeat h (δ+T) u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x, cheegerHeat h δ u x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) u x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ u x) ∂m)) ≤
      ε*compactHopfDualBound hfin o f hf hq/2 := by
  let U' := fun s : ℝ => cheegerHeat h (δ+T*s) u
  have hU'c : ContinuousOn U' (Icc 0 1) := by
    apply (cheegerHeat_continuousOn hfin h u).comp (by fun_prop)
    intro s hs
    exact add_nonneg hδ.le (mul_nonneg hT hs.1)
  let E := fun ε s => ∫ x, regularizedEntropy ε (U' s x) ∂m
  have hEc (ε : ℝ) (hε : 0 < ε) : ContinuousOn (E ε) (Icc 0 1) := by
    intro s hs
    exact ((regularizedEntropy_hasFDeriv hε (U' s)).continuousAt).comp_continuousWithinAt (hU'c s hs)
  have H := compact_dual_of_entropy_actions hfin o hU'c hEc
    (P := fun _ => 0) (a := fun _ => 0) (τ := T) continuousOn_const
    (fun s _ => by simpa using hasDerivAt_const s (0:ℝ))
    (fun s hs => cheegerHeat_nonneg h (add_nonneg hδ.le (mul_nonneg hT hs)) u hun)
    (by
      intro ε hε s hs
      have Hd : HasDerivAt (fun z : ℝ => δ+T*z) T s := by
        simpa only [id_eq,mul_one] using ((hasDerivAt_id s).const_mul T).const_add δ
      simpa only [zero_sub,neg_mul,U',E] using cheegerHeat_entropy_action hfin hID hpar h u hun hub hB
        Hd (add_pos_of_pos_of_nonneg hδ (mul_nonneg hT hs.1)) hε) f hf hq ε hε
  simpa only [U',E,mul_one,mul_zero,add_zero,sub_self,zero_add] using H

lemma cheegerHeat_entropy_dual
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T q : ℝ} (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, cheegerHeat h T u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x, u x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h T u x) ∂m)-
        (∫ x, regularizedEntropy ε (u x) ∂m)) ≤
      ε*compactHopfDualBound hfin o f hf hq/2 := by
  have h₀ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n+T) u) atTop
      (𝓝 (cheegerHeat h T u)) := cheegerHeat_tendsto_nonneg hfin h u hT
    (by simpa only [zero_add] using fisherEpsilon_tendsto.add_const T)
    (Eventually.of_forall fun n => add_nonneg (fisherEpsilon_pos n).le hT)
  have h₁ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n) u) atTop (𝓝 u) := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using
      cheegerHeat_tendsto_nonneg hfin h u (le_refl 0) fisherEpsilon_tendsto
        (Eventually.of_forall fun n => (fisherEpsilon_pos n).le)
  have hE₀ := ((regularizedEntropy_hasFDeriv hε (cheegerHeat h T u)).continuousAt).tendsto.comp h₀
  have hE₁ := ((regularizedEntropy_hasFDeriv hε u).continuousAt).tendsto.comp h₁
  have hL := ((integral_mul_tendsto_L2 h₀
    (boundedHopfMap_memLp_compact hfin f o hf (by linarith : 0 < q+1))).sub
    (integral_mul_tendsto_L2 h₁ (boundedHopfMap_memLp_compact hfin f o hf hq))).add
    ((hE₀.sub hE₁).const_mul T)
  exact le_of_tendsto hL (Eventually.of_forall fun n =>
    cheegerHeat_entropy_dual_positive hfin o hID hpar h u hun hub hB
      (fisherEpsilon_pos n) hT hq f hf hε)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropyDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_renormalizedEntropy_eq (u : Lp ℝ 2 m) (hu : Integrable u m)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x,renormalizedEntropy ε (u x) ∂m) =
      (∫ x,regularizedEntropy ε (u x) ∂m)+Real.log ε*(∫ x,u x ∂m) := by
  simp only [renormalizedEntropy]
  rw [integral_add (regularizedEntropy_integrable hε u) (hu.const_mul _),integral_const_mul]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma tendsto_regularizedEntropy_difference (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => (∫ x,regularizedEntropy (fisherEpsilon n) (u x) ∂m)-
      (∫ x,regularizedEntropy (fisherEpsilon n) (v x) ∂m)) atTop
      (𝓝 ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (v x) ∂m))) := by
  have H := (tendsto_integral_renormalizedEntropy (Lp.memLp u) hun huV hV).sub
    (tendsto_integral_renormalizedEntropy (Lp.memLp v) hvn hvV hV)
  simpa only [integral_renormalizedEntropy_eq u hu (fisherEpsilon_pos _),
    integral_renormalizedEntropy_eq v hv (fisherEpsilon_pos _),hm,add_sub_add_right_eq_sub] using H

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma entropy_dual_of_regularized (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m)
    {A B T D : ℝ} (hd : ∀ ε : ℝ,0 < ε →
      A+T*((∫ x,regularizedEntropy ε (u x) ∂m)-
        (∫ x,regularizedEntropy ε (v x) ∂m)) ≤ B+ε*D) :
    A+T*((∫ x,reducedEntropy (u x) ∂m)-
      (∫ x,reducedEntropy (v x) ∂m)) ≤ B := by
  have H := le_of_tendsto_of_tendsto
    ((tendsto_regularizedEntropy_difference u v hu hv hm hun hvn huV hvV hV).const_mul T |>.const_add A)
    (fisherEpsilon_tendsto.mul_const D |>.const_add B)
    (Eventually.of_forall fun n => hd (fisherEpsilon n) (fisherEpsilon_pos n))
  simpa only [zero_mul,add_zero] using H

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_entropy_dual_reduced
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T q : ℝ} (hT : 0 ≤ T) (hq : 0 < q)
    (hui : Integrable u m) (hPi : Integrable (cheegerHeat h T u) m)
    (hm : (∫ x,cheegerHeat h T u x ∂m) = ∫ x,u x ∂m)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hPV : Integrable (fun x => cheegerHeat h T u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) :
    (∫ x,cheegerHeat h T u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x,u x*boundedHopfMap f q x ∂m)+
      T*((∫ x,reducedEntropy (cheegerHeat h T u x) ∂m)-
        (∫ x,reducedEntropy (u x) ∂m)) ≤ 0 := by
  apply entropy_dual_of_regularized (cheegerHeat h T u) u hPi hui hm
    (cheegerHeat_nonneg h hT u hun) hun hPV huV hV
    (D := compactHopfDualBound hfin o f hf hq/2)
  intro ε hε
  simpa only [zero_add,mul_div_assoc] using
    cheegerHeat_entropy_dual hfin o hID hpar h u hun hub hB hT hq f hf hε

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_IdentifiedConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile216
noncomputable section
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma identified_cheegerResolvent_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖(identified_cheegerResolvent_weighted hID hpar hfinite o h u ht hV hU hsmall).toLp
      (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x))‖ ≤ ‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2) := by
  have H := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
    (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) (by
      intro n
      have HD := identified_cheegerResolvent_davies hID hpar hfinite o h u ht (hV.min_const (n:ℝ))
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
      have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      exact pow_le_pow_left₀ (norm_nonneg _) (HD.trans
        (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)) 2)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (sub_pos.mpr hsmall).le)).mp
  rw [norm_toLp_sq_eq_integral]
  exact H.2

lemma identified_cheegerHeat_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ‖(identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1.toLp
        (fun x => cheegerHeat h t u x*Real.exp (V x))‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq_eq_integral,mul_pow,sq_exp_eq]
  have H := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).2
  simpa only [mul_assoc] using H

lemma identified_cheegerHeat_laplacian_integral_zero
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t A x ∂m) = 0 := by
  have hUt := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1
  have hAt := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA ht).1
  have hpar := hpar
  have hLap := identified_isLaplacian_of_formGenerator hfinite hID h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  exact hLap.integral_eq_zero hfinite hpar o (integrable_of_memLp_mul_exp hAt hdecay)
    (integrable_of_memLp_mul_exp (hLap.memLp_gradient_mul_exp hfinite hpar hV hUt hAt) hdecay)

lemma identified_cheegerHeat_mass_weighted_generator
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  let C := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)*
      ‖hdecay.toLp (fun x => Real.exp (-V x))‖
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x, cheegerHeat h s A x*radialCutoff o n x ∂m
  have hfn (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (radialCutoffLp hfinite o n)) (cheegerHeat h s A) := by
      funext s; exact integral_radialCutoff_eq_inner hfinite o n _
    rw [he]
    exact (innerSL ℝ (radialCutoffLp hfinite o n)).continuous.comp_continuousOn
      (cheegerHeat_continuousOn hfinite h A)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ C := by
    have hsW := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs.1).1
    have HH := integral_cutoff_le_weighted hsW hdecay
      (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [abs_of_nonneg (radialCutoff_nonneg o n x)] using radialCutoff_le_one o n x)
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (identified_cheegerHeat_weighted_norm hID hpar hfinite o h A hV hA hs.1).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop (𝓝 0) := by
    have H := integral_radialCutoff_tendsto o
      (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs).1 hdecay)
    rw [identified_cheegerHeat_laplacian_integral_zero hID hpar hfinite o h hu hV hU hA hdecay hs] at H
    exact H
  have htime : Tendsto (fun n => ∫ s in 0..t, fn n s) atTop (𝓝 0) := by
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Eventually.of_forall (fun n =>
        ((hfn n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc))
      (Eventually.of_forall (fun n => ae_of_all _ fun s hs =>
        hb n s (by rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)))
      (intervalIntegrable_const)
      (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le))
    simpa only [intervalIntegral.integral_zero] using H
  have hFTC (n : ℕ) : (∫ s in 0..t, fn n s) =
      (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (radialCutoffLp hfinite o n)
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := ((cheegerHeat_continuousOn hfinite h A).mono
      (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfinite h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_radialCutoff_eq_inner hfinite o n] using H
  have hsp := (integral_radialCutoff_tendsto o
    (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hdecay)).sub
      (integral_radialCutoff_tendsto o (integrable_of_memLp_mul_exp hU hdecay))
  rw [show (fun n => ∫ s in 0..t, fn n s) = (fun n =>
    (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m)) from funext hFTC] at htime
  exact sub_eq_zero.mp (tendsto_nhds_unique hsp htime)

lemma identified_cheegerHeat_mass_of_weighted_resolvents
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n, 0 < ts n)
    (hsmall : ∀ n, ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    identified_cheegerResolvent_weighted hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (identified_cheegerResolvent_weighted_norm hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := by
    have H := ((hW n).sub hU).const_smul ((ts n)⁻¹)
    apply MemLp.ae_eq _ H
    filter_upwards [Lp.coeFn_smul ((ts n)⁻¹) (us n-u),Lp.coeFn_sub (us n) u] with x hs hd
    dsimp only [As]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    ring
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have H1 := integral_tendsto_of_weighted_bound hdecay hfinite o hum hU hW hWnorm
  have hWt (n : ℕ) := (identified_cheegerHeat_weighted hID hpar hfinite o h (us n) hV (hW n) ht).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h t (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*t) := by
    exact (identified_cheegerHeat_weighted_norm hID hpar hfinite o h (us n) hV (hW n) ht).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have H2 := integral_tendsto_of_weighted_bound hdecay hfinite o
    ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hum)
    (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hWt hWtnorm
  have he (n : ℕ) : (∫ x,cheegerHeat h t (us n) x ∂m) = ∫ x,us n x ∂m :=
    identified_cheegerHeat_mass_weighted_generator hID hpar hfinite o h (hus n) hV (hW n) (hAw n) hdecay ht
  simp_rw [Function.comp_def,he] at H2
  exact tendsto_nhds_unique H2 H1

lemma identified_cheegerHeat_mass_localized
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact identified_cheegerHeat_mass_of_weighted_resolvents hID hpar hfinite o h u hV hU hdecay hpos hsmall hlim ht

end WeakHessian

end
end InlinedFile216

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile217
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_supported {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hd⟩ := hrcd.1.exists_decay_weight hN hfull hfin o
  have hW : LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |a*dist x o-a*dist y o| ≤ |a| * dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)
  have huW := memLp_exp_dist_of_support u ha.le o hR
  have hd' : MemLp (fun x => Real.exp (-(a*dist x o))) 2 ν := by
    simpa only [neg_mul] using hd.of_measure_le_smul (by simp : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞) hν
  refine ⟨integrable_of_memLp_mul_exp
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u hW huW ht).1 hd', ?_⟩
  exact identified_cheegerHeat_mass_localized hID hnpar hnfin o h u hW huW hd' ht

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_nonneg {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hu : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hi : Integrable u (exponentialMeasure m V)) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal)
    (exponentialMeasure_comparable (m := m) hBV).2
  have hsub := cheegerHeat_submass hnfin o h u hu hi ht
  refine ⟨hsub.1,le_antisymm hsub.2 ?_⟩
  have hχ (n : ℕ) : ∀ᵐ x ∂ν, |radialCutoff o n x| ≤ (1:ℝ) := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let us (n : ℕ) : Lp ℝ 2 ν := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (hχ n) u
  have he (n : ℕ) : us n =ᵐ[ν] fun x => u x*radialCutoff o n x := boundedMulLp_ae _ _ u
  have hs (n : ℕ) : ∀ᵐ x ∂ν, (n:ℝ)+1 ≤ dist x o → us n x = 0 := by
    filter_upwards [he n] with x hx hdist
    rw [hx]
    have hz : radialCutoff o n x = 0 := by
      apply max_eq_left
      have H : 1 ≤ dist x o/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by simpa using hdist)
      linarith
    rw [hz,mul_zero]
  have hle (n : ℕ) : ∀ᵐ x ∂ν, us n x ≤ u x := by
    filter_upwards [he n,hu] with x hx hpos
    rw [hx]
    exact mul_le_of_le_one_right hpos (radialCutoff_le_one o n x)
  have hmass (n : ℕ) := hrcd.weighted_heat_mass_supported hN hfull hfin o hBV h (us n) (hs n) ht
  have hbound (n : ℕ) : (∫ x,u x*radialCutoff o n x ∂ν) ≤ ∫ x,cheegerHeat h t u x ∂ν := by
    rw [← integral_congr_ae (he n),← (hmass n).2]
    exact integral_mono_ae (hmass n).1 hsub.1 (cheegerHeat_order h ht (us n) u (hle n))
  exact le_of_tendsto (integral_radialCutoff_tendsto o hi) (Eventually.of_forall hbound)

end WeakHessian

end
end InlinedFile217

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_EntropyCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [TopologicalSpace.SeparableSpace X] in
lemma compact_hopf_dual_zero_time (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) {B : ℝ}
    (hd : ∀ q : ℝ,0 < q → (∫ x,boundedHopfMap f (q+1) x ∂μ)-
      (∫ x,boundedHopfMap f q x ∂ν) ≤ B) :
    (∫ x,boundedHopfMap f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B := by
  obtain ⟨L,hL⟩ := hf
  have h₁ := ((continuousOn_integral_boundedHopfMap (m := μ) f hL) 1 (by norm_num : (1:ℝ) ∈ Ici 0)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨by simpa using fisherEpsilon_tendsto.add_const 1,
      Eventually.of_forall fun n => by simpa only [mem_Ici] using add_nonneg (fisherEpsilon_pos n).le zero_le_one⟩)
  have h₀ := ((continuousOn_integral_boundedHopfMap (m := ν) f hL) 0 (by simp : (0:ℝ) ∈ Ici 0)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨fisherEpsilon_tendsto,
      Eventually.of_forall fun n => (fisherEpsilon_pos n).le⟩)
  simpa only [boundedHopfMap_zero] using le_of_tendsto (h₁.sub h₀)
    (Eventually.of_forall fun n => hd (fisherEpsilon n) (fisherEpsilon_pos n))

lemma coupling_of_entropy_dual (o : X) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    [IsProbabilityMeasure (densityMeasure m u)] [IsProbabilityMeasure (densityMeasure m v)]
    {A T : ℝ}
    (hd : ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) →
      GloballyLipschitz (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,u x*boundedHopfMap f (q+1) x ∂m)-(∫ x,v x*boundedHopfMap f q x ∂m)+
        T*((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (v x) ∂m)) ≤ A) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure m u ∧ p.map Prod.snd = densityMeasure m v ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*(A-T*((∫ x,reducedEntropy (u x) ∂m)-
          (∫ x,reducedEntropy (v x) ∂m)))) := by
  apply exists_proper_coupling_cost_of_compact_hopf_bound _ _ o
  intro f hc hL
  apply compact_hopf_dual_zero_time _ _ f hL
  intro q hq
  rw [integral_densityMeasure m u hun,integral_densityMeasure m v hvn]
  have H := hd f hc hL q hq
  linarith

lemma cheegerHeat_entropy_coupling
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∫ x,u x ∂m = 1)
    (hPm : ∫ x,cheegerHeat h T u x ∂m = 1)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hPV : Integrable (fun x => cheegerHeat h T u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure m (cheegerHeat h T u) ∧ p.map Prod.snd = densityMeasure m u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*T*((∫ x,reducedEntropy (u x) ∂m)-
          (∫ x,reducedEntropy (cheegerHeat h T u x) ∂m))) := by
  let := densityMeasure_probability_of_integrable u hun (integrable_of_integral_eq_one hm) hm
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u)
    (cheegerHeat_nonneg h hT u hun) (integrable_of_integral_eq_one hPm) hPm
  have H := coupling_of_entropy_dual o (cheegerHeat h T u) u
    (cheegerHeat_nonneg h hT u hun) hun (T := T) (A := 0) (by
      intro f hc _ q hq
      exact cheegerHeat_entropy_dual_reduced hfin o hID hpar h u hun hub hB hT hq
        (integrable_of_integral_eq_one hm) (integrable_of_integral_eq_one hPm)
        (hPm.trans hm.symm) huV hPV hV f hc)
  simpa only [zero_sub, ← mul_neg, neg_sub, mul_assoc] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_WeightedEntropyCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma integrable_mul_of_exp_weights {u W : X → ℝ}
    (hu : MemLp (fun x => u x*Real.exp (W x)) 2 m)
    (hW : MemLp (fun x => W x*Real.exp (-W x)) 2 m) :
    Integrable (fun x => u x*W x) m := by
  apply (hu.integrable_mul hW).congr
  exact ae_of_all _ fun x => by
    change (u x*Real.exp (W x))*(W x*Real.exp (-W x)) = u x*W x
    rw [show (u x*Real.exp (W x))*(W x*Real.exp (-W x)) =
      (u x*W x)*(Real.exp (W x)*Real.exp (-W x)) by ring,
      ← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

lemma RCD.weighted_heat_entropy_tails {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0) :
    ∃ a : ℝ,0 < a ∧ Integrable (fun x => Real.exp (-(a*dist x o))) (exponentialMeasure m V) ∧
      Integrable (fun x => u x*(a*dist x o)) (exponentialMeasure m V) ∧
      ∀ t : ℝ,0 ≤ t → Integrable (fun x => cheegerHeat h t u x*(a*dist x o)) (exponentialMeasure m V) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hi,h2,hD,hh,hhi⟩ := hrcd.1.exists_strong_entropy_confinement hN hfull hfin o
  have hCt : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞ := by simp
  have hi' : Integrable (fun x => Real.exp (-(a*dist x o))) ν := by
    apply memLp_one_iff_integrable.mp
    exact (memLp_one_iff_integrable.mpr hi).of_measure_le_smul hCt hν
  have hD' : MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 ν :=
    hD.of_measure_le_smul hCt hν
  have huW := memLp_exp_dist_of_support u ha.le o hR
  refine ⟨a,ha,hi',integrable_mul_of_exp_weights huW hD',?_⟩
  intro t ht
  exact integrable_mul_of_exp_weights
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u (lipschitz_mul_dist o a) huW ht).1 hD'

lemma RCD.weighted_heat_entropy_coupling {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hmass : ∫ x,u x ∂exponentialMeasure m V = 1)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ B)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      p.map Prod.snd = densityMeasure (exponentialMeasure m V) u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*T*((∫ x,reducedEntropy (u x) ∂exponentialMeasure m V)-
          (∫ x,reducedEntropy (cheegerHeat h T u x) ∂exponentialMeasure m V))) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hi,huW,hPW⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hPm := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun
    (integrable_of_integral_eq_one hmass) hT
  exact cheegerHeat_entropy_coupling hnfin o hID hnpar h u hun hub hB hT hmass
    (hPm.2.trans hmass) huW (hPW T hT) hi

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_densityMeasure_iff (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (f : X → ℝ) : Integrable f (densityMeasure m u) ↔ Integrable (fun x => u x*f x) m := by
  rw [densityMeasure,integrable_withDensity_iff_integrable_smul'
    (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hun] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]

lemma RCD.weighted_heat_law_finiteEntropy {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} (hVm : Measurable V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m V = 1)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      FiniteEntropy (exponentialMeasure m V) (μ:Measure X) ∧ FiniteEntropy m (μ:Measure X) ∧
      Integrable (fun x => dist x o) (μ:Measure X) ∧
      entropyReal (exponentialMeasure m V) (μ:Measure X) = entropyReal m (μ:Measure X)-∫ x,V x ∂(μ:Measure X) := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) (exponentialMeasure_comparable (m := m) hBV).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  obtain ⟨c,hc,he,_,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hin := integrable_of_integral_eq_one hum
  have hp := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun hin hT
  have hPn := cheegerHeat_nonneg h hT u hun
  have hPm := hp.2.trans hum
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u) hPn hp.1 hPm
  let μ : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hE : FiniteEntropy ν (μ:Measure X) := densityMeasure_finiteEntropy _ hPn hp.1 (hPV T hT) he
  have hVi : Integrable V (μ:Measure X) := Integrable.of_bound hVm.aestronglyMeasurable BV
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hBV x)
  have hEm := (finiteEntropy_exponentialMeasure_iff hVm hVi).mp hE
  refine ⟨μ,rfl,hE,hEm,?_,entropyReal_exponentialMeasure hEm hVm hVi⟩
  have H := (integrable_densityMeasure_iff _ hPn _).mpr (hPV T hT)
  have H' := H.const_mul c⁻¹
  change Integrable (fun x => dist x o) (densityMeasure ν (cheegerHeat h T u))
  convert H' using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change dist x o = c⁻¹*(c*dist x o)
  rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

omit [SigmaFinite m] in
lemma RCD.weighted_heat_entropy_real_coupling {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m V = 1)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ B)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      p.map Prod.snd = densityMeasure (exponentialMeasure m V) u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤ ENNReal.ofReal
        (2*T*(entropyReal (exponentialMeasure m V) (densityMeasure (exponentialMeasure m V) u)-
          entropyReal (exponentialMeasure m V) (densityMeasure (exponentialMeasure m V) (cheegerHeat h T u)))) := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) (exponentialMeasure_comparable (m := m) hBV).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  obtain ⟨c,hc,he,huV,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hui := integrable_of_integral_eq_one hum
  have hp := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun hui hT
  have hPn := cheegerHeat_nonneg h hT u hun
  have hPm := hp.2.trans hum
  let := densityMeasure_probability_of_integrable u hun hui hum
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u) hPn hp.1 hPm
  let μ₀ : ProbabilityMeasure X := ⟨densityMeasure ν u,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let μ₁ : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have h0 := entropyReal_eq_reducedDensity u hun hui
    (integrable_reducedEntropy (Lp.memLp _) hun huV he) μ₀ rfl
  have h1 := entropyReal_eq_reducedDensity (cheegerHeat h T u) hPn hp.1
    (integrable_reducedEntropy (Lp.memLp _) hPn (hPV T hT) he) μ₁ rfl
  obtain ⟨p,hp,hp0,hp1,hcost⟩ := hrcd.weighted_heat_entropy_coupling hN hfull hfin o hBV h u hun hum hB hub hR hT
  refine ⟨p,hp,hp0,hp1,?_⟩
  change entropyReal ν (densityMeasure ν u) = _ at h0
  change entropyReal ν (densityMeasure ν (cheegerHeat h T u)) = _ at h1
  rw [h0,h1,add_sub_add_right_eq_sub]
  exact hcost

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CouplingConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [CompleteSpace X] [ProperSpace X] in
lemma coupling_firstMoment_le {μ ν : Measure X} {p : Measure (X×X)}
    [IsProbabilityMeasure p] (hp : IsCoupling p μ ν) (o : X)
    (hμ : Integrable (fun x => dist x o) μ) {r A : ℝ} (hA : 0 ≤ A)
    (hs : ∀ᵐ x ∂ν,dist x o ≤ r) (hc : QuadraticTransportCost p ≤ ENNReal.ofReal A) :
    (∫ x,dist x o ∂μ) ≤ r+Real.sqrt A := by
  have hpt : QuadraticTransportCost p ≠ ∞ := ne_of_lt (hc.trans_lt ENNReal.ofReal_lt_top)
  have hd : MemLp (fun z : X×X => dist z.1 z.2) 2 p :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hpt)
  have hdf := (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun x => dist x o) (p.map Prod.fst))
    measurable_fst.aemeasurable).mp (by rwa [hp.1])
  have hs' : ∀ᵐ z : X×X ∂p,dist z.2 o ≤ r :=
    ae_of_ae_map (μ := p) (f := Prod.snd) measurable_snd.aemeasurable (by rwa [hp.2])
  have hm : (∫ z : X×X,dist z.1 o ∂p) ≤ (∫ z : X×X,dist z.1 z.2 ∂p)+r := by
    have H := integral_mono_ae hdf ((hd.integrable (by norm_num)).add (integrable_const r))
      (hs'.mono fun z hz => by
        change dist z.1 o ≤ dist z.1 z.2+r
        linarith [dist_triangle z.1 z.2 o])
    simpa only [Function.comp_apply,Pi.add_apply,integral_add (hd.integrable (by norm_num)) (integrable_const r),
      integral_const,probReal_univ,one_smul] using H
  have hcs : (∫ z : X×X,dist z.1 z.2 ∂p) ≤ Real.sqrt (∫ z : X×X,dist z.1 z.2^2 ∂p) := by
    simpa using integral_mul_le_sqrt_integral_sq hd (memLp_const (1:ℝ))
  have he : (∫ z : X×X,dist z.1 z.2^2 ∂p) ≤ A := by
    rw [quadraticTransportCost_eq_integral hpt] at hc
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp hc
  rw [← hp.1,integral_map measurable_fst.aemeasurable (by fun_prop)]
  exact hm.trans (by linarith [hcs.trans (Real.sqrt_le_sqrt he)])

lemma firstMoment_entropy_absorption {y r T D a C c : ℝ}
    (hy : 0 ≤ y) (hr : 0 ≤ r) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (H : y ≤ r+Real.sqrt (2*T*(D+2*a*C+c*y))) :
    y^2 ≤ 4*r^2+8*T*D+16*(T*a)*C+16*T^2*c^2 := by
  have hq : 0 ≤ 2*T*(D+2*a*C+c*y) := by positivity
  have hs := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg (2*T*(D+2*a*C+c*y))
  have h1 : y^2 ≤ 2*r^2+4*T*(D+2*a*C+c*y) := by
    have hyq := (sq_le_sq₀ hy (add_nonneg hr hsn)).mpr H
    nlinarith [sq_nonneg (r-Real.sqrt (2*T*(D+2*a*C+c*y)))]
  nlinarith [sq_nonneg (y-4*T*c)]

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_SmoothedPlanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma density_zero_of_ae_law {u : Lp ℝ 2 m} (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {P : X → Prop} (hP : ∀ᵐ x ∂densityMeasure m u,P x) :
    ∀ᵐ x ∂m,¬P x → u x = 0 := by
  have H := (ae_withDensity_iff (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)).mp hP
  filter_upwards [H,hun] with x hx hn hnp
  have he : ENNReal.ofReal (u x) = 0 := by
    by_contra hz
    exact hnp (hx hz)
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp he) hn

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_abs_bound_probability {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x,|f x| ≤ B) :
    |∫ x,f x ∂μ| ≤ B := by
  have hi := Integrable.of_bound hf B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)
  apply abs_integral_le_integral_abs.trans
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_ae hi.abs (integrable_const B) (ae_of_all _ hB)

lemma RCD.weighted_heat_concentration_oai {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {F : X → ℝ} (hF : Continuous F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hun : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m (fun x => a*F x) = 1)
    {Bu : ℝ} (hBu : 0 ≤ Bu) (hub : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|u x| ≤ Bu)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ᵐ x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) u,dist x o ≤ r)
    {B : ℝ≥0} (hB : 0 < B)
    (hcap : densityMeasure (exponentialMeasure m (fun x => a*F x)) u ≤ (B:ℝ≥0∞) • m)
    {c : ℝ} (hc : 0 < c) (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) ∧
      FiniteEntropy m (μ:Measure X) ∧ Integrable (fun x => dist x o) (μ:Measure X) ∧
      (∫ x,dist x o ∂(μ:Measure X))^2 ≤
        4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1)+
          16*(T*a)*CF+16*T^2*c^2 := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) (V := fun x => a*F x)
      (fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a))).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hVb : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hVm : Measurable (fun x => a*F x) := (continuous_const.mul hF).measurable
  have hsupport : ∀ᵐ x ∂ν,r+1 ≤ dist x o → u x = 0 := by
    filter_upwards [density_zero_of_ae_law hun hs] with x hx hd
    exact hx (by linarith)
  obtain ⟨μ,hμ,hEν,hEm,hμi,heμ⟩ := hrcd.weighted_heat_law_finiteEntropy hN hfull hfin o hVm hVb h u hun hum hsupport hT
  obtain ⟨μ₀,hμ₀,hEν₀,hEm₀,hμi₀,heμ₀⟩ := hrcd.weighted_heat_law_finiteEntropy hN hfull hfin o hVm hVb h u hun hum hsupport (T := 0) le_rfl
  rw [cheegerHeat_zero] at hμ₀
  change (μ₀ : Measure X) = densityMeasure ν u at hμ₀
  have hupper : entropyReal ν (μ₀:Measure X) ≤ Real.log B-a*(∫ x,F x ∂(μ₀:Measure X)) := by
    have H := entropyReal_exponential_upper hEm₀ hVm hVb hB (by rwa [hμ₀])
    rwa [integral_const_mul] at H
  have hlower : 1-c*(∫ x,dist x o ∂(μ:Measure X))-(∫ x,Real.exp (-(c*dist x o)) ∂m)-
      a*(∫ x,F x ∂(μ:Measure X)) ≤ entropyReal ν (μ:Measure X) := by
    rw [heμ,integral_const_mul]
    have H := entropyReal_lower_confinement hEm (hμi.const_mul c) he
    rw [integral_const_mul] at H
    linarith
  let D := |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1
  let y := ∫ x,dist x o ∂(μ:Measure X)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hy : 0 ≤ y := integral_nonneg fun x => dist_nonneg
  have hCF : 0 ≤ CF := (abs_nonneg (F o)).trans (hFb o)
  have hdrop : entropyReal ν (μ₀:Measure X)-entropyReal ν (μ:Measure X) ≤ D+2*a*CF+c*y := by
    have hF0 := integral_abs_bound_probability hF.aestronglyMeasurable (μ := (μ₀:Measure X)) hFb
    have hF1 := integral_abs_bound_probability hF.aestronglyMeasurable (μ := (μ:Measure X)) hFb
    have H0 := (abs_le.mp hF0).1
    have H1 := (abs_le.mp hF1).2
    have hlog := le_abs_self (Real.log (B:ℝ))
    dsimp [D,y]
    nlinarith
  obtain ⟨p,hp,hp0,hp1,hcost⟩ := hrcd.weighted_heat_entropy_real_coupling hN hfull hfin o hVb h u hun hum hBu hub hsupport hT
  let := hp
  have hcost' : QuadraticTransportCost p ≤ ENNReal.ofReal (2*T*(D+2*a*CF+c*y)) := by
    apply hcost.trans
    apply ENNReal.ofReal_le_ofReal
    rw [← hμ₀,← hμ]
    exact mul_le_mul_of_nonneg_left hdrop (by positivity)
  have H := coupling_firstMoment_le (μ := (μ:Measure X))
    (ν := (μ₀:Measure X)) ⟨hp0.trans hμ.symm,hp1.trans hμ₀.symm⟩ o hμi
    (by positivity : 0 ≤ 2*T*(D+2*a*CF+c*y)) (by rwa [hμ₀]) hcost'
  refine ⟨μ,hμ,hEm,hμi,?_⟩
  exact firstMoment_entropy_absorption hy hr hT hD ha hCF hc.le H

end WeakHessian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.weighted_heat_concentration_oai.{u_1} := @OAI.WeakHessian.RCD.weighted_heat_concentration_oai.{u_1}
