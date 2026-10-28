-- Prove2me | solution 1 for OAI.YauCounterexamples.localized_packet_sign_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:35:34.825452+00:00
-- url     : https://prove2.me/submissions/f27c3730-98ad-4872-976c-d296bcb92b57

import Mathlib
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_finite_near_far_sign_probability

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {I : Type*} [Fintype I]

lemma complexValueVector_inner (z w : I → ℂ) :
    ⟪complexValueVector z,complexValueVector w⟫ = ∑ i, ((starRingEnd ℂ (z i))*w i).re := by
  simp only [PiLp.inner_apply,complexValueVector,Fintype.sum_sum_type,
    RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    neg_mul,sub_neg_eq_add,Finset.sum_add_distrib, Sum.elim_inl, Sum.elim_inr]
  simp only [starRingEnd_apply, star_trivial]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma complexValueVector_norm_sq (z : I → ℂ) :
    ‖complexValueVector z‖^2 = ∑ i, ‖z i‖^2 := by
  rw [←real_inner_self_eq_norm_sq,complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,
    Complex.sq_norm]
  rw [Complex.normSq_apply]

end



open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PolynomialGaussianTailTendsto
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma quartic_inverse_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 < t ∧ 1 ≤ t^4 ∧ (t^4)⁻¹ ≤ t⁻¹ ∧ (Real.sqrt (t^4))⁻¹ ≤ 2/t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : Real.sqrt (t^4) = t^2 := by
    rw [show t^4 = (t^2)^2 by ring,Real.sqrt_sq (sq_nonneg t)]
  have h4 : 1 ≤ t^4 := one_le_pow₀ ht
  have h14 : (t^4)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (4 : ℕ) ≠ 0))
  have h12 : (t^2)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨ht0,h4,h14,?_⟩
  rw [hs]
  exact h12.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0])

lemma quartic_near_endpoint {t : ℝ} (ht : 1 ≤ t) (x y q : NormalWaveSpace)
    (hx : ‖x-q‖ ≤ t⁻¹) (hsep : t^4*‖y-x‖ ≤ 1) :
    ‖x-q‖ ≤ 2/t ∧ ‖y-q‖ ≤ 2/t := by
  obtain ⟨ht0,ht4,hinv,_⟩ := quartic_inverse_bounds ht
  have hyx : ‖y-x‖ ≤ (t^4)⁻¹ := by
    have hh : ‖y-x‖ ≤ 1/(t^4) := (le_div_iff₀ (show 0 < t^4 by positivity)).mpr (by nlinarith [hsep])
    simpa only [one_div] using hh
  have htinv : t⁻¹ ≤ 2/t := by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0]
  refine ⟨hx.trans htinv,?_⟩
  calc
    _ ≤ ‖y-x‖+‖x-q‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (y-x) (x-q)
    _ ≤ t⁻¹+t⁻¹ := add_le_add (hyx.trans hinv) hx
    _ = 2/t := by ring

lemma quartic_far_endpoint {t : ℝ} (ht : 2 ≤ t) (x y q : NormalWaveSpace)
    (hx : t⁻¹ < ‖x-q‖) (hsep : t^4*‖y-x‖ ≤ 1) :
    t^2/4 ≤ t^4*‖y-q‖^2 := by
  have ht0 : 0 < t := by linarith
  have ht4 : 0 < t^4 := by positivity
  have hyx : ‖y-x‖ ≤ (t^4)⁻¹ := by
    have hh : ‖y-x‖ ≤ 1/(t^4) := (le_div_iff₀ ht4).mpr (by nlinarith [hsep])
    simpa only [one_div] using hh
  have hpow : 2*t ≤ t^4 := by
    have hs : 4 ≤ t^2 := by nlinarith
    nlinarith [sq_nonneg (t^2-2),sq_nonneg (t-1)]
  have hinv : (t^4)⁻¹ ≤ (2*t)⁻¹ := inv_anti₀ (by positivity) hpow
  have htriangle : ‖x-q‖ ≤ ‖y-x‖+‖y-q‖ := by
    have h := norm_add_le (x-y) (y-q)
    rw [sub_add_sub_cancel,norm_sub_rev x y] at h
    exact h
  have hdist : (2*t)⁻¹ ≤ ‖y-q‖ := by
    have he : t⁻¹ = 2*(2*t)⁻¹ := by field_simp
    linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (2*t)⁻¹) hdist 2
  have hh := mul_le_mul_of_nonneg_left hs ht4.le
  have he : t^4*(2*t)⁻¹^2 = t^2/4 := by field_simp; ring
  rwa [he] at hh
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PacketAxisShift
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma packetAxisShift_step {n ε ℓ : ℝ} (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hℓ : 1 ≤ ℓ) (x : NormalWaveSpace) (j : Fin 3) :
    n*‖packetAxisShift x n ε ℓ j-x‖ ≤ 1 := by
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ
  simp only [packetAxisShift,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hε (mul_pos hn hℓ0).le)]
  simp only [EuclideanSpace.basisFun_apply,PiLp.norm_single,norm_one,mul_one]
  have he : n*(ε/(n*ℓ)) = ε/ℓ := by field_simp
  simpa only [mul_one,he] using (div_le_one hℓ0).mpr (hε1.trans hℓ)

lemma packetAxisShift_covector {n ε ℓ : ℝ} (hn : n ≠ 0) (hℓ : ℓ ≠ 0)
    (x : NormalWaveSpace) (j : Fin 3) (β : NormalWaveSpace →L[ℝ] ℝ) :
    n*β (packetAxisShift x n ε ℓ j-x) = ε/ℓ*β (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  simp only [packetAxisShift,add_sub_cancel_left,map_smul,smul_eq_mul]
  field_simp

lemma profile_exp_close (φ : NormalWaveSpace → ℝ) {H n : ℝ} (hn : 0 ≤ n)
    (hH : 0 ≤ H) (x y : NormalWaveSpace) (hstep : n*‖y-x‖ ≤ 1)
    (hφ : |φ y-φ x| ≤ H*‖y-x‖) :
    Real.exp (n*φ y) ≤ Real.exp H*Real.exp (n*φ x) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hφ) hn
  have hh' := mul_le_mul_of_nonneg_left hstep hH
  nlinarith

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactProfileUnitLipschitz
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma endpoint_norm_lower {u v : ℂ} {a ε : ℝ} (ha : 0 < a)
    (hε : ε ≤ 1/2) (θ : ℝ)
    (h : ‖u-(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖ ≤
      ε*‖(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖) :
    (a/2)*‖v‖ ≤ ‖u‖ := by
  have he : ‖(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖ = a*‖v‖ := by
    simp [Complex.norm_exp,abs_of_pos ha]
  have ht := norm_sub_norm_le ((a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v) u
  rw [norm_sub_rev,he] at ht
  rw [he] at h
  have hp := mul_le_mul_of_nonneg_right hε (mul_nonneg ha.le (norm_nonneg v))
  nlinarith
end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma packet_value_lower_of_endpoint (φ : NormalWaveSpace → ℝ)
    {q x : NormalWaveSpace} {n H M r : ℝ} (hn : 1 ≤ n) (hH : 0 ≤ H)
    (hr : 0 ≤ r) (hMr : M*r ≤ 1/2) (hstep : n*‖x-q‖ ≤ 1)
    (hd : ‖fderiv ℝ φ q‖ ≤ H) (hval : |φ x-φ q| ≤ H*‖x-q‖)
    (u : NormalWaveSpace → ℂ) (β : NormalWaveSpace →L[ℝ] ℝ)
    (huq : u q = Complex.exp ((n : ℂ)*(φ q : ℂ)))
    (hend : ‖u x-(Real.exp (n*fderiv ℝ φ q (x-q)) : ℂ)*
      Complex.exp (((n*β (x-q) : ℝ) : ℂ)*Complex.I)*u q‖ ≤
      (M*r)*‖(Real.exp (n*fderiv ℝ φ q (x-q)) : ℂ)*
      Complex.exp (((n*β (x-q) : ℝ) : ℂ)*Complex.I)*u q‖) :
    (Real.exp (-2*H)/2)*Real.exp (n*φ x) ≤ ‖u x‖ := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hd' : |n*fderiv ℝ φ q (x-q)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hn0]
    calc
      _ ≤ n*(‖fderiv ℝ φ q‖*‖x-q‖) := mul_le_mul_of_nonneg_left ((fderiv ℝ φ q).le_opNorm _) hn0
      _ ≤ n*(H*‖x-q‖) := by gcongr
      _ = H*(n*‖x-q‖) := by ring
      _ ≤ H := mul_le_of_le_one_right hH hstep
  have hv' : |n*(φ x-φ q)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hn0]
    calc
      _ ≤ n*(H*‖x-q‖) := mul_le_mul_of_nonneg_left hval hn0
      _ = H*(n*‖x-q‖) := by ring
      _ ≤ H := mul_le_of_le_one_right hH hstep
  rw [← abs_of_nonneg hr] at hMr hend
  have hl := endpoint_norm_lower (Real.exp_pos (n*fderiv ℝ φ q (x-q))) hMr
    (n*β (x-q)) hend
  have hnorm : ‖u q‖ = Real.exp (n*φ q) := by
    rw [huq,Complex.norm_exp]
    simp
  rw [hnorm] at hl
  refine le_trans ?_ hl
  have he : -2*H+n*φ x ≤ n*fderiv ℝ φ q (x-q)+n*φ q := by
    have h1 := (abs_le.mp hd').1
    have h2 := (abs_le.mp hv').2
    nlinarith
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_add,Real.exp_add] at hh
  nlinarith

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LocalizedPacketSignProbability
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace
section NearFarVectors
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma complexValueVector_component_le (v : I → ℂ) (i : I) :
    ‖v i‖ ≤ ‖complexValueVector v‖ := by
  have hs := Finset.single_le_sum (f := fun j => ‖v j‖^2) (s := Finset.univ)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [←complexValueVector_norm_sq] at hs
  nlinarith [norm_nonneg (v i),norm_nonneg (complexValueVector v)]

end NearFarVectors

end



section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma finite_packet_variance_lower {I : Type} [Fintype I]
    (φ : NormalWaveSpace → ℝ) {K : Set NormalWaveSpace}
    (q : I → NormalWaveSpace) (U : I → NormalWaveSpace → ℂ)
    (β : I → NormalWaveSpace →L[ℝ] ℝ) {n H M r : ℝ}
    (hn : 1 ≤ n) (hH : 0 ≤ H) (hr : 0 ≤ r) (hnr : n⁻¹ ≤ r) (hMr : M*r ≤ 1/2)
    (hq : ∀ i, q i ∈ K)
    (hφ : ∀ q ∈ K, ∀ x, ‖x-q‖ ≤ 1 → ‖fderiv ℝ φ x‖ ≤ H ∧ |φ x-φ q| ≤ H*‖x-q‖)
    (hu : ∀ i, U i (q i) = Complex.exp ((n : ℂ)*(φ (q i) : ℂ)))
    (hend : ∀ i x, ‖x-q i‖ ≤ r → n*‖x-q i‖ ≤ 1 →
      ‖U i x-(Real.exp (n*fderiv ℝ φ (q i) (x-q i)) : ℂ)*
        Complex.exp (((n*β i (x-q i) : ℝ) : ℂ)*Complex.I)*U i (q i)‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ (q i) (x-q i)) : ℂ)*
        Complex.exp (((n*β i (x-q i) : ℝ) : ℂ)*Complex.I)*U i (q i)‖)
    (x : NormalWaveSpace) (hcov : ∃ i, n*‖x-q i‖ ≤ 1) :
    ∃ i, n*‖x-q i‖ ≤ 1 ∧
      (Real.exp (-2*H)/2)*Real.exp (n*φ x) ≤ ‖U i x‖ := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨i,hi⟩ := hcov
  have hdist : ‖x-q i‖ ≤ n⁻¹ := by
    simpa only [mul_one] using (le_inv_mul_iff₀ hn0).mpr hi
  have hdist1 : ‖x-q i‖ ≤ 1 := hdist.trans ((inv_le_one₀ hn0).mpr hn)
  have hq0 : ‖q i-q i‖ ≤ 1 := by simp
  have hφx := hφ (q i) (hq i) x hdist1
  have hφq := hφ (q i) (hq i) (q i) hq0
  exact ⟨i,hi,packet_value_lower_of_endpoint φ hn hH hr hMr hi hφq.1 hφx.2
    (U i) (β i) (hu i) (hend i x (hdist.trans hnr) hi)⟩

lemma finite_packet_standardized_mean {I : Type} [Fintype I]
    (v : I → ℂ) {A m : ℝ} (hA : 0 < A) (hv : ∃ i, A ≤ ‖v i‖) (hm : |m| ≤ A) :
    |m/‖complexValueVector v‖| ≤ 1 := by
  classical
  obtain ⟨i,hi⟩ := hv
  have hnorm : A ≤ ‖complexValueVector v‖ := hi.trans (complexValueVector_component_le v i)
  rw [abs_div,abs_of_pos (hA.trans_le hnorm)]
  exact (div_le_one (hA.trans_le hnorm)).mpr (hm.trans hnorm)
end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

theorem localized_packet_sign_probability_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (φ : NormalWaveSpace → ℝ) (K : Set NormalWaveSpace)
      (q : I → NormalWaveSpace) (β : I → NormalWaveSpace →L[ℝ] ℝ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ)
      (H Hs ε ℓ t T c M δ : ℝ) (x : NormalWaveSpace),
      0 ≤ H → 0 ≤ Hs → 0 < ε → ε ≤ 1 → 1 ≤ ℓ → 2 ≤ t →
      0 < T → 0 < c → 0 ≤ M → 0 < δ → δ ≤ 1/16 → δ ≤ κ/96 →
      M*(2/t) ≤ δ/2 → (∀ i, q i ∈ K) → x ∈ K →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      (∀ y ∈ K, ∃ i, t^4*‖y-q i‖ ≤ 1) →
      (∀ q ∈ K, ∀ y, ‖y-q‖ ≤ 1 → ‖fderiv ℝ φ y‖ ≤ H ∧ |φ y-φ q| ≤ H*‖y-q‖) →
      (∀ j, Real.exp (-Hs) ≤ Real.exp ((ε/ℓ)*fderiv ℝ φ x
        (EuclideanSpace.basisFun (Fin 3) ℝ j))) →
      (∀ i, U i (q i) = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i) : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-q i‖^2)) →
      (∀ i a y, ‖a-q i‖ ≤ 2/t → ‖y-q i‖ ≤ 2/t → t^4*‖y-a‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖ ≤
        (M*(2/t))*‖(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖) →
      (∀ i, ‖x-q i‖ ≤ t⁻¹ →
        (∀ j, |ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 1) ∧
        κ ≤ ∑ j, (ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j))^2) →
      (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
        (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) →
      (∀ y ∈ K, |b y| ≤ (Real.exp (-2*H)/2)*Real.exp (t^4*φ y)) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  obtain ⟨p,hp,hprob⟩ := finite_near_far_sign_probability hκ hκ1
  refine ⟨p,hp,?_⟩
  intro I _ _ φ K q β U b H Hs ε ℓ t T c M δ x hH hHs hε hε1 hℓ ht hT hc hM hδ hδ1 hδκ hMr hq hx hy hcov hφ hαlo hcenter hloc hend hang hbudget hb
  have ht1 : 1 ≤ t := by linarith
  obtain ⟨ht0,hn1,hinv,hsqrt⟩ := quartic_inverse_bounds ht1
  have hn : 0 < t^4 := by positivity
  have hr : 0 ≤ 2/t := by positivity
  have hnr : (t^4)⁻¹ ≤ 2/t := hinv.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0])
  have hMrhalf : M*(2/t) ≤ 1/2 := by linarith
  let y : Fin 3 → NormalWaveSpace := packetAxisShift x (t^4) ε ℓ
  let α : Fin 3 → ℝ := fun j => Real.exp ((ε/ℓ)*fderiv ℝ φ x (EuclideanSpace.basisFun (Fin 3) ℝ j))
  let θ : I → Fin 3 → ℝ := fun i j => ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)
  let A := (Real.exp (-2*H)/2)*Real.exp (t^4*φ x)
  let τ := T*Real.exp H*Real.exp (t^4*φ x)*Real.exp (-c*t^2/4)
  let s : Finset I := Finset.univ.filter (fun i => ‖x-q i‖ ≤ t⁻¹)
  have hA : 0 < A := by dsimp [A]; positivity
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hstep (j) : t^4*‖y j-x‖ ≤ 1 := packetAxisShift_step hn hε.le hε1 hℓ x j
  have hlow (a) (ha : a ∈ K) : ∃ i, t^4*‖a-q i‖ ≤ 1 ∧
      (Real.exp (-2*H)/2)*Real.exp (t^4*φ a) ≤ ‖U i a‖ := by
    apply finite_packet_variance_lower φ q U β hn1 hH hr hnr hMrhalf hq hφ hcenter
      (fun i a ha hstep => hend i (q i) a (by simpa using hr) ha hstep) a (hcov a ha)
  obtain ⟨i₀,hi₀,hlo₀⟩ := hlow x hx
  have hi₀dist : ‖x-q i₀‖ ≤ t⁻¹ := by
    have hh : ‖x-q i₀‖ ≤ (t^4)⁻¹ := by
      simpa only [mul_one] using (le_inv_mul_iff₀ hn).mpr hi₀
    exact hh.trans hinv
  have hlarge : ∃ i ∈ s, A ≤ ‖U i x‖ := ⟨i₀,by simp [s,hi₀dist],hlo₀⟩
  have hnear (j i) (hi : i ∈ s) :
      ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x-U i (y j)‖ ≤
        (M*(2/t))*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x‖ := by
    have hix : ‖x-q i‖ ≤ t⁻¹ := (Finset.mem_filter.mp hi).2
    obtain ⟨hxq,hyq⟩ := quartic_near_endpoint ht1 x (y j) (q i) hix (hstep j)
    have hh := hend i x (y j) hxq hyq (hstep j)
    rw [packetAxisShift_covector hn.ne' (by linarith : ℓ ≠ 0) x j (fderiv ℝ φ x),
      packetAxisShift_covector hn.ne' (by linarith : ℓ ≠ 0) x j (β i)] at hh
    change ‖U i (y j)-(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x‖ ≤ _ at hh
    rw [norm_sub_rev]
    exact hh
  have hfar_at (a : NormalWaveSpace) (ha : t^4*‖a-x‖ ≤ 1)
      (hφa : Real.exp (t^4*φ a) ≤ Real.exp H*Real.exp (t^4*φ x))
      (i : I) (hi : i ∉ s) : ‖U i a‖ ≤ τ := by
    have hix : t⁻¹ < ‖x-q i‖ := lt_of_not_ge (by simpa [s] using hi)
    have hd := quartic_far_endpoint ht x a (q i) hix ha
    have hexp : Real.exp (-c*t^4*‖a-q i‖^2) ≤ Real.exp (-c*t^2/4) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hd hc.le]
    apply (hloc i a).trans
    dsimp [τ]
    calc
      _ ≤ T*(Real.exp H*Real.exp (t^4*φ x))*Real.exp (-c*t^2/4) := by gcongr
      _ = _ := by ring
  have hfar₀ (i) (hi : i ∉ s) : ‖U i x‖ ≤ τ := by
    apply hfar_at x (by simp) ?_ i hi
    exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp_iff.mpr hH)
  have hfar₁ (j i) (hi : i ∉ s) : ‖U i (y j)‖ ≤ τ := by
    have hd : ‖y j-x‖ ≤ 1 := by nlinarith [hstep j,norm_nonneg (y j-x)]
    exact hfar_at (y j) (hstep j) (profile_exp_close φ hn.le hH x (y j) (hstep j)
      (hφ x hx (y j) hd).2) i hi
  have hα (j) : 0 < α j := Real.exp_pos _
  have htail : (Fintype.card I : ℝ)*τ ≤ (δ/2)*Real.exp (-Hs)*A := by
    have hh := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos (t^4*φ x)).le
    dsimp [τ,A]
    calc
      _ = ((Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4))*Real.exp (t^4*φ x) := by ring
      _ ≤ ((δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2))*Real.exp (t^4*φ x) := hh
      _ = _ := by ring
  have ha01 : Real.exp (-Hs) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbasebudget : (Fintype.card I : ℝ)*τ ≤ δ*A := by
    apply htail.trans
    have hh := mul_le_mul_of_nonneg_left ha01 (mul_nonneg (half_pos hδ).le hA.le)
    nlinarith
  have hendbudget (j) : (Fintype.card I : ℝ)*τ ≤ (δ-M*(2/t))*α j*A := by
    apply htail.trans
    have hal : Real.exp (-Hs) ≤ α j := hαlo j
    have hh' : (δ/2)*Real.exp (-Hs) ≤ (δ-M*(2/t))*α j := by
      have hn' : δ/2 ≤ δ-M*(2/t) := by linarith
      exact mul_le_mul hn' hal (Real.exp_pos (-Hs)).le (by linarith)
    exact mul_le_mul_of_nonneg_right hh' hA.le
  have hstd : |b x/‖complexValueVector (fun i => U i x)‖| ≤ 1 :=
    finite_packet_standardized_mean _ hA ⟨i₀,hlo₀⟩ (hb x hx)
  have hstd' (j) : |b (y j)/‖complexValueVector (fun i => U i (y j))‖| ≤ 1 := by
    obtain ⟨i,_hi,hlo⟩ := hlow (y j) (hy j)
    exact finite_packet_standardized_mean _ (by positivity) ⟨i,hlo⟩ (hb (y j) (hy j))
  exact hprob I s (fun i => U i x) (fun j i => U i (y j)) α θ (b x) (fun j => b (y j))
    A (M*(2/t)) δ τ (fun _ => τ) hA (mul_nonneg hM hr) (by linarith) hτ (fun _ => hτ)
    hlarge hα hδ1 hδκ
    (fun i hi => (hang i (Finset.mem_filter.mp hi).2).1)
    (fun i hi => (hang i (Finset.mem_filter.mp hi).2).2)
    hfar₀ hbasebudget hendbudget hnear hfar₁ hstd hstd'

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.localized_packet_sign_probability_oai := @OAI.YauCounterexamples.localized_packet_sign_probability_oai
