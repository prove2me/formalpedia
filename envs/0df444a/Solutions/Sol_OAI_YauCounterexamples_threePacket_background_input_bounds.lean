-- Prove2me | solution 1 for OAI.YauCounterexamples.threePacket_background_input_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:32:47.383861+00:00
-- url     : https://prove2.me/submissions/05486699-e7ba-4fd0-97aa-a8c3102c79b5

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarPredPowerWeightBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma scalar_pred_power_weight_bound {r m a : ℝ} (hr : 0 ≤ r) (hm : 0 < m)
    (hma : m ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    m*r^(n-1) ≤ a^n+r^n := by
  have ha : 0 ≤ a := hm.le.trans hma
  have hn' : n-1+1=n := Nat.sub_add_cancel hn
  by_cases hmr : m ≤ r
  · calc
      _ ≤ r*r^(n-1) := mul_le_mul_of_nonneg_right hmr (pow_nonneg hr _)
      _ = r^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg ha _)
  · calc
      _ ≤ a*a^(n-1) := mul_le_mul hma (pow_le_pow_left₀ hr ((le_of_not_ge hmr).trans hma) (n-1))
        (pow_nonneg hr _) ha
      _ = a^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hr _)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith
lemma complex_power_envelope_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg hA _) hA (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_power_weighted_jets {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ K) hf.contDiffOn h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n x hx j hj
  let A := max ‖f x‖ (Real.exp (φ x))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ x := by
      have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hB x hx))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k f x‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using
        (le_max_left ‖f x‖ (Real.exp (φ x)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk x hx
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := complex_power_envelope_jet_bound hf x h n hA hT0 hraw j hj
  have hreal : ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      A^n*((n:ℝ)*T)^j := by
    calc
      _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
          (hf.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
      _ ≤ 1*(A^n*((n:ℝ)*T)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
        hp (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ x)+‖f x‖^n := by
    by_cases he : ‖f x‖ ≤ Real.exp (φ x)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hreal
  exact hreal.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ProductSphereFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma complexIdentityPlanar (z : ℂ) : planarLinear (1:ℂ) Complex.I z = z := by
  apply Complex.ext <;> simp [planarLinear_apply,Complex.inner,Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProductSphereFstPower
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_smooth (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_fstPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] OAI.YauCounterexamples.sphereN_dimension_fact
lemma threeComplexPower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threeComplexPower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z := by
  funext y
  have hh := congrFun (three_chart_symm p) y
  have h₁ := congrArg (fun q : ThreeAmbient => q.fst) hh
  have h₂ := congrArg (fun q : ThreeAmbient => q.snd) hh
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3) =
    roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst at h₁
  change (((chartAt ThreeModel p).symm y).2:ℂ) =
    roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd at h₂
  simp only [Function.comp_apply,threeComplexPower,h₁,h₂]
  simp only [productSphere_fstPower,productSphere_sndPower,Function.comp_apply]
  rw [complexIdentityPlanar]
  rfl
end


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeFirstNormedSpace
local instance threeFirstContinuousSMul_r91ce0d_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.sphereFirst_dimension_fact
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactExponentialEnvelopeLogBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_exponential_envelope_log_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n : ℝ, 0 ≤ n → ∀ x ∈ K,
      ‖fderiv ℝ (fun y => Real.exp (n*φ y)) x‖ ≤ H*n*Real.exp (n*φ x) := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (hφ.fderiv_right (m:=∞) (by simp)).continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n hn x hx
  have hd := (((hφ.differentiable (by simp)) x).hasFDerivAt.const_mul n).exp.fderiv
  rw [hd,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),abs_of_nonneg hn]
  calc
    _ ≤ Real.exp (n*φ x)*(n* max C 0) := by gcongr; exact (hC x hx).trans (le_max_left _ _)
    _ = _ := by ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma real_smooth_add_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f+h) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j h x‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  rw [iteratedFDeriv_add_apply (hf.of_le hj).contDiffAt (hh.of_le hj).contDiffAt]
  exact norm_add_le _ _

end


section
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

lemma real_power_variable_weighted_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C > 0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^k).re) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  obtain ⟨C,hC,hjet⟩ := real_power_weighted_jets hf hK (fun _ => -2*D)
    continuousOn_const h
  refine ⟨C,hC,?_⟩
  intro k hk x hx j hj
  have hp : (0:ℝ)≤k := Nat.cast_nonneg _
  have hν := productWaveFrequency_bounds hk
  have hν0 : 0≤productWaveFrequency k := hp.trans hν.1
  have hm : -D≤φ x := by
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    exact (neg_le_neg (le_max_left B 0)).trans ((neg_le_neg hb).trans (neg_abs_le _))
  have he : Real.exp ((k:ℝ)*(-2*D))≤Real.exp (productWaveFrequency k*φ x) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (2*(k:ℝ))*(-D) := by ring
      _ ≤ productWaveFrequency k*(-D) := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr hD)
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hν0
  exact (hjet k x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add he le_rfl) (by positivity))

lemma threeCoupled_split_powers (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    threeCoupled r k p =
      ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k).re+
      (((r:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k).re := by
  simp only [threeCoupled,threeCoupledComplex,threeComplexPower,pow_one,mul_pow,
    Complex.add_re,add_mul,productA,productB,mul_assoc]

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_NormPowerVariableWeightControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma norm_power_variable_weight_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) {φ : E → ℝ} (hφ : Continuous φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C>0, ∀ k : ℕ, 2≤k →
      ContDiff ℝ 1 (fun x => ‖f x‖^k) ∧
      ∀ x∈K, ‖fderiv ℝ (fun y => ‖f y‖^k) x‖ ≤
        C*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  let D := max R 0
  let B := max A 1
  let m := Real.exp (-2*D)
  have hB : 0<B := zero_lt_one.trans_le (le_max_right _ _)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨B/m,div_pos hB hm,?_⟩
  intro k hk
  have hk1 : 1≤k := by omega
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hν := productWaveFrequency_bounds hk1
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hfn : ContDiff ℝ 1 (fun x => ‖f x‖^k) := by
    simpa only [Real.rpow_natCast] using hf.norm_rpow hkR
  refine ⟨hfn,?_⟩
  intro x hx
  have hφlow : -D≤φ x := by
    have h := hR x hx
    rw [Real.norm_eq_abs] at h
    exact (neg_le_neg (le_max_left R 0)).trans ((neg_le_neg h).trans (neg_abs_le _))
  have hem : m^k≤Real.exp (productWaveFrequency k*φ x) := by
    dsimp [m]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr (le_max_right R 0))
    have h2 := mul_le_mul_of_nonneg_left hφlow hν0
    dsimp [D] at *
    nlinarith
  let W := Real.exp (productWaveFrequency k*φ x)+‖f x‖^k
  have hpred : ‖f x‖^(k-1)≤W/m := by
    apply (le_div_iff₀ hm).mpr
    have hh := scalar_pred_power_weight_bound (norm_nonneg (f x)) hm (le_refl m) hk1
    have ht := hh.trans (add_le_add hem le_rfl)
    simpa only [W,mul_comm] using ht
  have hnorm : ‖fderiv ℝ (fun y => ‖f y‖^k) x‖ ≤ (k:ℝ)*‖f x‖^(k-1)*B := by
    have hh := norm_fderiv_norm_rpow_le (x:=x) (hf.differentiable one_ne_zero) hkR
    have hcast : (k:ℝ)-1=((k-1:ℕ):ℝ) := by rw [Nat.cast_sub hk1]; norm_num
    rw [hcast,Real.rpow_natCast] at hh
    simp only [Real.rpow_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _)) (by positivity))
  calc
    _ ≤ (k:ℝ)*(W/m)*B := hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg _)) hB.le)
    _ ≤ productWaveFrequency k*(W/m)*B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hν.1 (by dsimp [W]; positivity)) hB.le
    _ = _ := by dsimp [W]; ring

lemma two_power_variable_weight_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set E} (hK : IsCompact K) :
    ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
      Differentiable ℝ (fun x => Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k) ∧
      (∀ x, 0<Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k) ∧
      (∀ x∈K, ∀ j≤2, ‖iteratedFDeriv ℝ j (fun y => (a y^k).re+(b y^k).re) x‖ ≤
        T*(productWaveFrequency k)^j*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k)) ∧
      (∀ x∈K, ‖fderiv ℝ (fun y => Real.exp (productWaveFrequency k*φ y)+‖a y‖^k+‖b y‖^k) x‖ ≤
        H*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k)) := by
  obtain ⟨A,hA,hAJ⟩ := real_power_variable_weighted_jets ha hK φ hφ.continuous.continuousOn 2
  obtain ⟨B,hB,hBJ⟩ := real_power_variable_weighted_jets hb hK φ hφ.continuous.continuousOn 2
  obtain ⟨C,hC,hCj⟩ := norm_power_variable_weight_control (ha.of_le (by simp)) hφ.continuous hK
  obtain ⟨D,hD,hDj⟩ := norm_power_variable_weight_control (hb.of_le (by simp)) hφ.continuous hK
  obtain ⟨H,hH,hHe⟩ := compact_exponential_envelope_log_bound hK hφ
  refine ⟨A+B,add_pos hA hB,H+C+D,by positivity,?_⟩
  intro k hk
  have hk1 : 1≤k := by omega
  have hν := productWaveFrequency_bounds hk1
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  obtain ⟨hak,hakJ⟩ := hCj k hk
  obtain ⟨hbk,hbkJ⟩ := hDj k hk
  have he : ContDiff ℝ ∞ (fun x => Real.exp (productWaveFrequency k*φ x)) := (contDiff_const.mul hφ).exp
  have hWe : Differentiable ℝ (fun x => Real.exp (productWaveFrequency k*φ x)) := he.differentiable (by simp)
  refine ⟨(hWe.add (hak.differentiable one_ne_zero)).add (hbk.differentiable one_ne_zero),fun x => by positivity,?_,?_⟩
  · intro x hx j hj
    let W := Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k
    have hwA : Real.exp (productWaveFrequency k*φ x)+‖a x‖^k≤W := le_add_of_nonneg_right (by positivity)
    have hwB : Real.exp (productWaveFrequency k*φ x)+‖b x‖^k≤W := by dsimp [W]; nlinarith [pow_nonneg (norm_nonneg (a x)) k]
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg k) hν.1 j
    have h1 := (hAJ k hk1 x hx j hj).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hA.le) hwA (by positivity) (by positivity))
    have h2 := (hBJ k hk1 x hx j hj).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hB.le) hwB (by positivity) (by positivity))
    exact (real_smooth_add_jet_bound (Complex.reCLM.contDiff.comp (ha.pow k))
      (Complex.reCLM.contDiff.comp (hb.pow k)) j x).trans (by
      change ‖iteratedFDeriv ℝ j (fun y => (a y^k).re) x‖+
        ‖iteratedFDeriv ℝ j (fun y => (b y^k).re) x‖ ≤ _
      calc
        _ ≤ A*(productWaveFrequency k)^j*W+B*(productWaveFrequency k)^j*W := add_le_add h1 h2
        _ = _ := by dsimp [W]; ring)
  · intro x hx
    have hea := hWe x
    have haa := hak.differentiable one_ne_zero x
    have hba := hbk.differentiable one_ne_zero x
    rw [fderiv_fun_add (hea.fun_add haa) hba,fderiv_fun_add hea haa]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    have h1 := hHe (productWaveFrequency k) hν0 x hx
    have h2 := hakJ x hx
    have h3 := hbkJ x hx
    calc
      _ ≤ H*productWaveFrequency k*Real.exp (productWaveFrequency k*φ x)+
          C*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k)+
          D*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖b x‖^k) := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hH hν0) (pow_nonneg (norm_nonneg (a x)) k),
        mul_nonneg (mul_nonneg hH hν0) (pow_nonneg (norm_nonneg (b x)) k),
        mul_nonneg (mul_nonneg hC.le hν0) (pow_nonneg (norm_nonneg (b x)) k),
        mul_nonneg (mul_nonneg hD.le hν0) (pow_nonneg (norm_nonneg (a x)) k)]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
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
attribute [local instance] OAI.YauCounterexamples.threePacketNormedSpace
local instance threePacketContinuousSMul_r91ce0d_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threePacketA_smooth : ContDiff ℝ ∞ threePacketA :=
  ((threeComplexPower_chart_smooth _ _ _ _).comp threeNormalEquiv.contDiff).comp normalWaveEquiv.contDiff
lemma threePacketB_smooth : ContDiff ℝ ∞ threePacketB :=
  contDiff_const.mul (((threeComplexPower_chart_smooth _ _ _ _).comp threeNormalEquiv.contDiff).comp normalWaveEquiv.contDiff)
lemma threePacket_back_eq (k : ℕ) :
    (threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv =
      (fun y => (threePacketA y^k).re+(threePacketB y^k).re) := by
  funext y
  exact threeCoupled_split_powers _ _ _
lemma threePacket_background_input_bounds_oai {φ : ThreeManifold → ℝ}
    (hφ : ContDiff ℝ ∞ (φ ∘ threeNormalInv)) {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
    ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
      Differentiable ℝ (threePacketWeight φ k) ∧ (∀ y, 0<threePacketWeight φ k y) ∧
      (∀ y∈S, ∀ j≤2,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv) y‖ ≤
          T*(productWaveFrequency k)^j*threePacketWeight φ k y) ∧
      (∀ y∈S, ‖fderiv ℝ (threePacketWeight φ k) y‖ ≤ H*productWaveFrequency k*threePacketWeight φ k y) := by
  obtain ⟨T,hT,H,hH,hinputs⟩ := two_power_variable_weight_control threePacketA_smooth threePacketB_smooth
    (hφ.comp normalWaveEquiv.contDiff) hS
  refine ⟨T,hT,H,hH,?_⟩
  intro k hk
  rw [threePacket_back_eq]
  exact hinputs k hk

end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threePacket_background_input_bounds_oai := @OAI.YauCounterexamples.threePacket_background_input_bounds_oai
