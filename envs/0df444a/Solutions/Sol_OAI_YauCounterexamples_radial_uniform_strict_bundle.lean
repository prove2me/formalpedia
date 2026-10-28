-- Prove2me | solution 1 for OAI.YauCounterexamples.radial_uniform_strict_bundle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:40:16.397617+00:00
-- url     : https://prove2.me/submissions/ee28fb72-c9c5-4eb3-b30b-f62ee8135274

import Mathlib
import Definitions.Def_OAIQ070A007

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialLeadingTrace
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in

lemma exists_unit_common_kernel (hd : 3 ≤ Module.finrank ℝ E)
    (R T : E →L[ℝ] ℝ) : ∃ w : E, ‖w‖ = 1 ∧ R w = 0 ∧ T w = 0 := by
  classical
  let L : E →ₗ[ℝ] ℝ × ℝ := R.toLinearMap.prod T.toLinearMap
  have hn : ¬Function.Injective L := by
    intro h
    have hh := LinearMap.finrank_le_finrank_of_injective h
    have ht : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    rw [ht] at hh
    omega
  unfold Function.Injective at hn
  push Not at hn
  obtain ⟨v,z,he,hne⟩ := hn
  have hvz : v-z ≠ 0 := sub_ne_zero.mpr hne
  have hl : L (v-z) = 0 := by rw [map_sub,he,sub_self]
  have hR : R (v-z) = 0 := congrArg Prod.fst hl
  have hT : T (v-z) = 0 := congrArg Prod.snd hl
  refine ⟨‖v-z‖⁻¹ • (v-z),?_,?_,?_⟩
  · simp [norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvz)]
  · simp only [map_smul,hR,smul_zero]
  · simp only [map_smul,hT,smul_zero]

theorem radial_angular_witness (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2)) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ (a+q • r+e) w = 0 ∧
      R w = 0 ∧ 1/4 ≤ |T w| := by
  obtain ⟨w,hw,hAw,hRw⟩ := exists_unit_common_kernel hd
    (InnerProductSpace.toDual ℝ E (a+q • r+e)) R
  have hAw' : inner ℝ (a+q • r+e) w = 0 := hAw
  have hi : inner ℝ a w = -inner ℝ e w := by
    simpa only [inner_add_left,inner_smul_left,hr,hRw,mul_zero,add_zero,add_eq_zero_iff_eq_neg] using hAw'
  have hib : |inner ℝ a w| ≤ ‖a‖/2 := by
    rw [hi,abs_neg]
    have hh := abs_real_inner_le_norm e w
    rw [hw,mul_one] at hh
    exact hh.trans he
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c := inner ℝ a w / ‖a‖^2
  let v := w-c • a
  have hav : inner ℝ a v = 0 := by
    simp only [v,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,c]
    field_simp; ring
  have hc : ‖c • a‖ ≤ 1/2 := by
    have heq : ‖c • a‖ = |inner ℝ a w|/‖a‖ := by
      simp only [norm_smul,Real.norm_eq_abs,c,abs_div,abs_pow,abs_norm]
      field_simp
    rw [heq]
    exact (div_le_iff₀ han).mpr (by linarith)
  have hv : 1/2 ≤ ‖v‖ := by
    have hh : ‖w‖ ≤ ‖v‖ + ‖c • a‖ := by
      simpa only [v,sub_add_cancel] using norm_add_le (w-c • a) (c • a)
    rw [hw] at hh
    linarith
  have hRv : R v = 0 := by simp [v,hRw,hRa]
  have hTv : T v = T w := by simp [v,hTa]
  refine ⟨w,hw,hAw',hRw,?_⟩
  have hh := hco v hav
  rw [hRv,hTv,zero_pow (by norm_num : 2 ≠ 0),zero_add,Real.sqrt_sq_eq_abs] at hh
  linarith

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem radial_leading_trace (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (L A δ f b K f₂ : ℝ) (hL : 0 ≤ L) (_hA : 0 ≤ A) (hAL : A ≤ 3*L)
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f) :
    ∃ v : E, ‖v‖ = L ∧ inner ℝ (a+q • r+e) v = 0 ∧ R v = 0 ∧
      L^2/16*b - 288*K*δ^2*L^2*f^2 - 8*K*‖e‖^2 ≤
        f₂*(R (a+q • r+e))^2+b*(T (a+q • r+e))^2+
        f₂*(R v)^2+b*(T v)^2 := by
  obtain ⟨w,hw,haw,hRw,hTw⟩ := radial_angular_witness hd a r e ha q R T
    hr hRa hTa he hco
  have hrr : R r = ‖r‖^2 := by rw [←hr,real_inner_self_eq_norm_sq]
  have hRe : |R e| ≤ 2*‖e‖ := by
    rw [←hr]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hrn (norm_nonneg _))
  have hRsum : R (a+q • r+e) = q*‖r‖^2+R e := by simp [map_add,map_smul,hRa,hrr]
  have hRabs : |R (a+q • r+e)| ≤ 4*δ*A*f+2*‖e‖ := by
    rw [hRsum]
    have hh := abs_add_le (q*‖r‖^2) (R e)
    rw [abs_of_nonneg (mul_nonneg hq (sq_nonneg _))] at hh
    have hr2 : ‖r‖^2 ≤ 4 := by nlinarith [norm_nonneg r]
    have hq4 := mul_le_mul_of_nonneg_left hr2 hq
    nlinarith
  have hRL : |R (a+q • r+e)| ≤ 12*δ*L*f+2*‖e‖ := by
    have hh := mul_le_mul_of_nonneg_left hAL (show 0 ≤ 4*δ*f by positivity)
    nlinarith
  have hRsq : (R (a+q • r+e))^2 ≤ 288*δ^2*L^2*f^2+8*‖e‖^2 := by
    have hn : 0 ≤ 12*δ*L*f+2*‖e‖ := by positivity
    have hh := sq_le_sq₀ (abs_nonneg _) hn |>.mpr hRL
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (12*δ*L*f-2*‖e‖)]
  have hf₂ : -K ≤ f₂ := by linarith [neg_abs_le f₂]
  have hlow := mul_le_mul_of_nonneg_right hf₂ (sq_nonneg (R (a+q • r+e)))
  have hKbound := mul_le_mul_of_nonneg_left hRsq hK
  have hwT : (1/16:ℝ) ≤ (T w)^2 := by nlinarith [sq_abs (T w)]
  have hsT : L^2/16 ≤ (T (L • w))^2 := by
    simp only [map_smul,smul_eq_mul,mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hwT (sq_nonneg L)]
  have hbT := mul_le_mul_of_nonneg_left hsT hb
  simp only [map_smul,smul_eq_mul,mul_pow] at hbT
  refine ⟨L • w, ?_, ?_, ?_, ?_⟩
  · simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL,hw]
  · simp [inner_smul_right,haw]
  · simp [hRw]
  · simp only [map_smul,smul_eq_mul,hRw,mul_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
    nlinarith only [hlow,hKbound,hbT,mul_nonneg hb (sq_nonneg (T (a+q • r+e)))]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialTraceAbsorption
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem radial_trace_absorption (L b K S δ f e T : ℝ)
    (hb : 0 ≤ b) (hK : 0 ≤ K) (_hS : 0 ≤ S)
    (hf : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (htrace : L^2/16*b-288*K*δ^2*L^2*f^2-8*K*e^2 ≤ T) :
    L^2/32*b-8*K*e^2 ≤ T := by
  have h1 := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ 288*K*δ^2*L^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ L^2*b/32 by positivity)
  nlinarith only [h1,h2,htrace]
end YauCounterexamples

open Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialTransitionPositive
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
namespace YauCounterexamples

theorem radial_transition_positive (m C D t η T : ℝ)
    (hm : 0 < m) (ht : 0 ≤ t) (hη : η ≤ m/4)
    (hD : C^2 ≤ (D-C)*m)
    (htrace : m-C*t-C*Real.sqrt t-η+D*t ≤ T) : m/2 ≤ T := by
  have hs := Real.sq_sqrt ht
  have hn := sq_nonneg (m-2*C*Real.sqrt t)
  have hd := mul_le_mul_of_nonneg_right hD ht
  have hsmall : m*(C*Real.sqrt t) ≤ m^2/4+C^2*t := by
    nlinarith only [hs,hn]
  have hbound : m/2 ≤ m-C*t-C*Real.sqrt t-η+D*t := by
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith only [hsmall,hd,mul_le_mul_of_nonneg_right hη hm.le]
  exact hbound.trans htrace

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFullProfileMargin
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Metric
open scoped Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

lemma profileForm_diag_sub_bound (H : ProfileForm E) (a b : E) :
    |H a a - H b b| ≤ ‖H‖ * (‖a‖ + ‖b‖) * ‖a-b‖ := by
  have he : H a a - H b b = H (a-b) a + H b (a-b) := by
    simp only [map_sub, sub_apply]
    ring
  rw [he]
  calc
    _ ≤ ‖H (a-b) a‖ + ‖H b (a-b)‖ := norm_add_le _ _
    _ ≤ ‖H‖ * ‖a-b‖ * ‖a‖ + ‖H‖ * ‖b‖ * ‖a-b‖ :=
      add_le_add (H.le_opNorm₂ _ _) (H.le_opNorm₂ _ _)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in

theorem exists_transverse_unit_near (a a' v : E) (ha : a ≠ 0)
    (hv : ‖v‖ = 1) (hav : inner ℝ a' v = 0)
    (hsmall : ‖a'-a‖ ≤ ‖a‖ / 2) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ a w = 0 ∧
      ‖v-w‖ ≤ 2 * ‖a'-a‖ / ‖a‖ := by
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c := inner ℝ a v / ‖a‖^2
  let z := v - c • a
  have haz : inner ℝ a z = 0 := by
    dsimp [z,c]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hinner : |inner ℝ a v| ≤ ‖a'-a‖ := by
    have he : inner ℝ a v = inner ℝ (a-a') v := by
      rw [inner_sub_left, hav, sub_zero]
    rw [he]
    simpa [hv, norm_sub_rev] using abs_real_inner_le_norm (a-a') v
  have hcv : ‖c • a‖ ≤ ‖a'-a‖ / ‖a‖ := by
    calc
      _ = |inner ℝ a v| / ‖a‖ := by
        simp only [norm_smul, Real.norm_eq_abs, c, abs_div, abs_pow, abs_norm]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hinner han.le
  have hcvhalf : ‖c • a‖ ≤ 1/2 := hcv.trans ((div_le_iff₀ han).mpr (by linarith))
  have hzlower : 1/2 ≤ ‖z‖ := by
    have hh : ‖v‖ ≤ ‖z‖ + ‖c • a‖ := by
      simpa only [z, sub_add_cancel] using norm_add_le (v-c • a) (c • a)
    rw [hv] at hh
    linarith
  have hzn : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖z‖))
  let w := ‖z‖⁻¹ • z
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hdw : ‖w-z‖ ≤ ‖v-z‖ := by
    calc
      _ = |1-‖z‖| := by
        rw [show w-z = (‖z‖⁻¹-1) • z by dsimp [w]; rw [sub_smul, one_smul]]
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ = |(‖z‖⁻¹-1)*‖z‖| := by rw [abs_mul, abs_norm]
          _ = _ := by rw [sub_mul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzn), one_mul]
      _ ≤ _ := by simpa [hv] using abs_norm_sub_norm_le v z
  have hvz : ‖v-z‖ ≤ ‖a'-a‖ / ‖a‖ := by
    simpa [z] using hcv
  refine ⟨w,hw,?_,?_⟩
  · simp [w,inner_smul_right,haz]
  · calc
      _ ≤ ‖v-z‖ + ‖z-w‖ := norm_sub_le_norm_sub_add_norm_sub v z w
      _ = ‖v-z‖ + ‖w-z‖ := by rw [norm_sub_rev z w]
      _ ≤ ‖a'-a‖ / ‖a‖ + ‖a'-a‖ / ‖a‖ := add_le_add hvz (hdw.trans hvz)
      _ = _ := by ring
omit [FiniteDimensional ℝ E] in
lemma profileTrace_abs_bound (H : ProfileForm E) (a v : E) (R : ℝ)
    (ha : ‖a‖ ≤ R) (hv : ‖v‖ = 1) :
    |profileTrace H a v| ≤ ‖H‖ * (1 + 2*R^2) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have haa : |H a a| ≤ ‖H‖ * R^2 := by
    calc
      _ ≤ ‖H‖ * ‖a‖ * ‖a‖ := H.le_opNorm₂ a a
      _ ≤ ‖H‖ * R * R := mul_le_mul
        (mul_le_mul_of_nonneg_left ha (norm_nonneg H)) ha
        (norm_nonneg _) (mul_nonneg (norm_nonneg H) hR)
      _ = _ := by ring
  have hvv : |H v v| ≤ ‖H‖ := by simpa [hv] using H.le_opNorm₂ v v
  have hsq : ‖a‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr ha
  calc
    _ ≤ |H a a| + |(1+‖a‖^2) * H v v| := abs_add_le _ _
    _ = |H a a| + (1+‖a‖^2)*|H v v| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖a‖^2)]
    _ ≤ ‖H‖*R^2 + (1+R^2)*‖H‖ := add_le_add haa
      (mul_le_mul (by linarith) hvv (abs_nonneg _) (by positivity))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_sub_bound (H : ProfileForm E) (a a' v w : E) (R : ℝ)
    (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    |profileTrace H a' v - profileTrace H a w| ≤
      4*‖H‖*R*‖a'-a‖ + 2*‖H‖*(1+R^2)*‖v-w‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have hdiag : |H a' a' - H a a| ≤ 2*‖H‖*R*‖a'-a‖ := by
    calc
      _ ≤ ‖H‖*(‖a'‖+‖a‖)*‖a'-a‖ := profileForm_diag_sub_bound H a' a
      _ ≤ ‖H‖*(R+R)*‖a'-a‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add ha' ha) (norm_nonneg H)) (norm_nonneg _)
      _ = _ := by ring
  have hsq : |‖a'‖^2-‖a‖^2| ≤ 2*R*‖a'-a‖ := by
    rw [show ‖a'‖^2-‖a‖^2 = (‖a'‖-‖a‖)*(‖a'‖+‖a‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ ‖a'-a‖*(R+R) := mul_le_mul (abs_norm_sub_norm_le _ _) (add_le_add ha' ha)
        (by positivity) (norm_nonneg _)
      _ = _ := by ring
  have hvv : |H v v| ≤ ‖H‖ := by simpa [hv] using H.le_opNorm₂ v v
  have hvw : |H v v - H w w| ≤ 2*‖H‖*‖v-w‖ := by
    simpa [hv,hw,show (1:ℝ)+1=2 by norm_num,mul_comm,mul_left_comm]
      using profileForm_diag_sub_bound H v w
  have hsqa : ‖a‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr ha
  have he : profileTrace H a' v - profileTrace H a w =
      (H a' a'-H a a)+(‖a'‖^2-‖a‖^2)*H v v+
        (1+‖a‖^2)*(H v v-H w w) := by unfold profileTrace; ring
  rw [he]
  calc
    _ ≤ |H a' a'-H a a| + |(‖a'‖^2-‖a‖^2)*H v v| +
        |(1+‖a‖^2)*(H v v-H w w)| := (abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    _ = |H a' a'-H a a| + |‖a'‖^2-‖a‖^2| * |H v v| +
        (1+‖a‖^2)*|H v v-H w w| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖a‖^2)]
    _ ≤ 2*‖H‖*R*‖a'-a‖ + (2*R*‖a'-a‖)*‖H‖ +
        (1+R^2)*(2*‖H‖*‖v-w‖) := add_le_add
      (add_le_add hdiag (mul_le_mul hsq hvv (abs_nonneg _) (by positivity)))
      (mul_le_mul (by linarith) hvw (abs_nonneg _) (by positivity))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in

theorem profileTrace_base_lower (H : ProfileForm E) (a a' v : E)
    (m α B R : ℝ) (hm : m ≤ 1) (hα : 0 < α) (ha0 : α ≤ ‖a‖)
    (hH : ‖H‖ ≤ B) (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R)
    (hv : ‖v‖ = 1) (hav : inner ℝ a' v = 0)
    (hmargin : ∀ w, ‖w‖ = 1 → inner ℝ a w = 0 → m ≤ profileTrace H a w) :
    m - (4*B*R + 4*B*(1+R^2)/α + 2*(1+B*(1+2*R^2))/α) * ‖a'-a‖ ≤
      profileTrace H a' v := by
  have hB : 0 ≤ B := (norm_nonneg H).trans hH
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  have han : 0 < ‖a‖ := hα.trans_le ha0
  have haN : a ≠ 0 := norm_pos_iff.mp han
  let C₁ : ℝ := 4*B*R+4*B*(1+R^2)/α
  let C₂ : ℝ := 2*(1+B*(1+2*R^2))/α
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  change m-(C₁+C₂)*‖a'-a‖ ≤ _
  by_cases hsmall : ‖a'-a‖ ≤ ‖a‖/2
  · obtain ⟨w,hw,haw,hdw⟩ := exists_transverse_unit_near a a' v haN hv hav hsmall
    have hdw' : ‖v-w‖ ≤ 2*‖a'-a‖/α := hdw.trans
      (div_le_div_of_nonneg_left (by positivity) hα ha0)
    have hdiff : |profileTrace H a' v-profileTrace H a w| ≤ C₁*‖a'-a‖ := by
      calc
        _ ≤ 4*‖H‖*R*‖a'-a‖+2*‖H‖*(1+R^2)*‖v-w‖ :=
          profileTrace_sub_bound H a a' v w R ha ha' hv hw
        _ ≤ 4*B*R*‖a'-a‖+2*B*(1+R^2)*(2*‖a'-a‖/α) := add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) hR) (norm_nonneg _))
          (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) (by positivity))
            hdw' (norm_nonneg _) (by positivity))
        _ = _ := by dsimp [C₁]; ring
    have hh := neg_abs_le (profileTrace H a' v-profileTrace H a w)
    have hmm := hmargin w hw haw
    have hmore := mul_nonneg hC₂ (norm_nonneg (a'-a))
    nlinarith only [hdiff,hh,hmm,hmore]
  · have hd : α/2 ≤ ‖a'-a‖ := by linarith [not_le.mp hsmall]
    have hlarge : 1+B*(1+2*R^2) ≤ C₂*‖a'-a‖ := by
      calc
        _ = C₂*(α/2) := by dsimp [C₂]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hd hC₂
    have hbound : |profileTrace H a' v| ≤ B*(1+2*R^2) :=
      (profileTrace_abs_bound H a' v R ha' hv).trans
        (mul_le_mul_of_nonneg_right hH (by positivity))
    have hn := neg_abs_le (profileTrace H a' v)
    have hmore := mul_nonneg hC₁ (norm_nonneg (a'-a))
    nlinarith only [hm,hlarge,hbound,hn,hmore]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ProfileTraceAdd
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_norm_gain {a d : E} (had : inner ℝ a d = 0) (q : ℝ) :
    ‖a + q • d‖^2 = ‖a‖^2 + q^2 * ‖d‖^2 := by
  rw [norm_add_sq_real]
  simp [inner_smul_right,had,norm_smul, mul_pow]

theorem radial_gradient_no_loss (a r e : E) (had : inner ℝ a r = 0)
    (q ε : ℝ) (he : ‖e‖ ≤ ε*‖a‖) :
    (1-ε)*‖a‖ ≤ ‖a+q • r+e‖ := by
  have hsq := radial_norm_gain had q
  have hnorm : ‖a‖ ≤ ‖a+q • r‖ := by
    nlinarith [norm_nonneg a,norm_nonneg (a+q • r),mul_nonneg (sq_nonneg q) (sq_nonneg ‖r‖)]
  have htri : ‖a+q • r‖ ≤ ‖a+q • r+e‖+‖e‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+q • r+e) e
  linarith


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma profileTrace_add (H B : ProfileForm E) (a v : E) :
    profileTrace (H+B) a v = profileTrace H a v+profileTrace B a v := by
  simp only [profileTrace, add_apply]
  ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_smul (H : ProfileForm E) (c : ℝ) (a v : E) :
    profileTrace (c • H) a v = c*profileTrace H a v := by
  simp only [profileTrace, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_eq_scaled (H : ProfileForm E) (a v : E) (L : ℝ)
    (hL : L^2 = 1+‖a‖^2) :
    profileTrace H a v = H a a+H (L • v) (L • v) := by
  simp only [profileTrace, map_smul, smul_apply, smul_eq_mul]
  rw [←hL]
  ring

theorem radial_leading_profileTrace (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (A δ f b K S f₂ : ℝ) (hA : 0 ≤ A)
    (hAL : A ≤ 3*Real.sqrt (1+‖a+q • r+e‖^2))
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f)
    (hfS : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (B : ProfileForm E) (hB : ∀ u v, B u v = f₂*R u*R v+b*T u*T v) :
    ∃ v : E, ‖v‖ = 1 ∧ inner ℝ (a+q • r+e) v = 0 ∧
      (1+‖a+q • r+e‖^2)/32*b-8*K*‖e‖^2 ≤
        profileTrace B (a+q • r+e) v := by
  let aN := a+q • r+e
  let L := Real.sqrt (1+‖aN‖^2)
  have hLp : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hLsq : L^2 = 1+‖aN‖^2 := Real.sq_sqrt (by positivity)
  obtain ⟨w,hw,haw,hRw,htrace⟩ := radial_leading_trace hd a r e ha q R T hr hRa hTa
    he hrn hco L A δ f b K f₂ hLp.le hA hAL hδ hf hb hK h₂ hq hqA
  have ht : L^2/32*b-8*K*‖e‖^2 ≤ B aN aN+B w w := by
    have hh := radial_trace_absorption L b K S δ f ‖e‖
      (f₂*(R aN)^2+b*(T aN)^2+f₂*(R w)^2+b*(T w)^2)
      hb hK hS hfS hsmall htrace
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [hB,hB]
    dsimp [aN]
    ring
  let v : E := L⁻¹ • w
  have hscaled : L • v = w := by simp [v, smul_smul, ne_of_gt hLp]
  refine ⟨v,?_,?_,?_⟩
  · simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos hLp,hw,ne_of_gt hLp]
  · simp [v,inner_smul_right,haw]
  · have heq : profileTrace B aN v = B aN aN+B w w := by
      rw [profileTrace_eq_scaled B aN v L hLsq,hscaled]
    change (1+‖aN‖^2)/32*b-8*K*‖e‖^2 ≤ _
    rw [heq,←hLsq]
    exact ht

theorem radial_total_trace_lower (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (A δ f b K S f₂ : ℝ) (hA : 0 ≤ A)
    (hAL : A ≤ 3*Real.sqrt (1+‖a+q • r+e‖^2))
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f)
    (hfS : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (B H Er : ProfileForm E) (hB : ∀ u v, B u v = f₂*R u*R v+b*T u*T v)
    (m α Hmax Gmax c : ℝ) (hm : m ≤ 1) (hα : 0 < α) (ha0 : α ≤ ‖a‖)
    (hH : ‖H‖ ≤ Hmax) (hGa : ‖a‖ ≤ Gmax) (hGN : ‖a+q • r+e‖ ≤ Gmax)
    (hc : 0 ≤ c)
    (hmargin : ∀ w, ‖w‖ = 1 → inner ℝ a w = 0 → m ≤ profileTrace H a w) :
    ∃ v : E, ‖v‖ = 1 ∧ inner ℝ (a+q • r+e) v = 0 ∧
      m-(4*Hmax*Gmax+4*Hmax*(1+Gmax^2)/α+2*(1+Hmax*(1+2*Gmax^2))/α)*
         ‖q • r+e‖ - ‖Er‖*(1+2*Gmax^2) +
        c*((1+‖a+q • r+e‖^2)/32*b-8*K*‖e‖^2) ≤
      profileTrace (H+c • B+Er) (a+q • r+e) v := by
  obtain ⟨v,hv,hav,ht⟩ := radial_leading_profileTrace hd a r e ha q R T hr hRa hTa he hrn hco
    A δ f b K S f₂ hA hAL hδ hf hb hK hS h₂ hq hqA hfS hsmall B hB
  have hbase := profileTrace_base_lower H a (a+q • r+e) v m α Hmax Gmax
    hm hα ha0 hH hGa hGN hv hav hmargin
  have hd : a+q • r+e-a = q • r+e := by abel
  rw [hd] at hbase
  have herror := profileTrace_abs_bound Er (a+q • r+e) v Gmax hGN hv
  have helo := neg_abs_le (profileTrace Er (a+q • r+e) v)
  have hscaled := mul_le_mul_of_nonneg_left ht hc
  refine ⟨v,hv,hav,?_⟩
  rw [profileTrace_add,profileTrace_add,profileTrace_smul]
  linarith

omit [FiniteDimensional ℝ E] in

lemma radial_gradient_patch_bounds (a r e : E) (δ A χ f M F C N : ℝ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hf : 0 ≤ f) (hfF : f ≤ F) (hr : ‖r‖ ≤ 2) (ha : ‖a‖ ≤ M)
    (hC : 0 ≤ C) (hN : 1 ≤ N) (he : ‖e‖ ≤ C/N) :
    ‖a+(δ*A*χ*f) • r+e‖ ≤ M+2*δ*A*F+C ∧
      ‖(δ*A*χ*f) • r+e‖ ≤ (2*δ*A+C)*(χ*f+N⁻¹) := by
  have hN0 : 0 < N := by linarith
  have hqn : 0 ≤ δ*A*χ*f := by positivity
  have hq : δ*A*χ*f ≤ δ*A*F := by
    calc
      _ ≤ δ*A*1*f := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hχ1 (mul_nonneg hδ hA)) hf
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hfF (mul_nonneg hδ hA)
  have hnr : ‖(δ*A*χ*f) • r‖ ≤ 2*δ*A*χ*f := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hqn]
    nlinarith only [mul_le_mul_of_nonneg_left hr hqn]
  have hnrr : ‖(δ*A*χ*f) • r‖ ≤ 2*δ*A*F := by nlinarith only [hnr,hq]
  have hen : ‖e‖ ≤ C := he.trans ((div_le_iff₀ hN0).mpr (by nlinarith))
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (by linarith [ha,hnrr,hen]))
  · have hh := norm_add_le ((δ*A*χ*f) • r) e
    have h1 := mul_nonneg hC (mul_nonneg hχ hf)
    have h2 := mul_nonneg (show 0 ≤ 2*δ*A by positivity) (inv_nonneg.mpr hN0.le)
    rw [div_eq_mul_inv] at he
    nlinarith only [hh,hnr,he,h1,h2]

lemma radial_scaled_leading_lower (N δ A χ f b K e C R L₂ : ℝ)
    (hN : 0 < N) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hf : 0 ≤ f) (hb : f/R ≤ b)
    (hK : 0 ≤ K) (he0 : 0 ≤ e) (he : e ≤ C/N) (hR : 0 < R) (hL : 1 ≤ L₂) :
    (δ*A/(32*R))*N*(χ*f)-(8*K*δ*A*C^2)/N ≤
      N*δ*A*χ*(L₂/32*b-8*K*e^2) := by
  have hb0 : 0 ≤ b := (div_nonneg hf hR.le).trans hb
  have hcoeff : 0 ≤ N*δ*A*χ := by positivity
  have hpos : (δ*A/(32*R))*N*(χ*f) ≤ N*δ*A*χ*(L₂/32*b) := by
    calc
      _ = (N*δ*A*χ)*(f/R/32) := by ring
      _ ≤ (N*δ*A*χ)*(b/32) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hb (by norm_num)) hcoeff
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hcoeff
  have he2 : e^2 ≤ (C/N)^2 := (sq_le_sq₀ he0 (he0.trans he)).mpr he
  have herr : N*δ*A*χ*(8*K*e^2) ≤ (8*K*δ*A*C^2)/N := by
    calc
      _ ≤ N*δ*A*χ*(8*K*(C/N)^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he2 (by positivity)) hcoeff
      _ ≤ N*δ*A*1*(8*K*(C/N)^2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hχ1 (by positivity)) (by positivity)
      _ = _ := by field_simp
  nlinarith only [hpos,herr]

lemma radial_trace_collect_errors (m Cb Cg Cr Lr Clead C k N t d re lead τ : ℝ)
    (hN : 0 < N) (ht : 0 ≤ t) (hCb : 0 ≤ Cb) (hLr : 0 ≤ Lr)
    (h1 : Cb*Cg+Cr*Lr ≤ C) (h2 : Cr*Lr ≤ C)
    (h3 : Cb*Cg+Cr*Lr+Clead ≤ C)
    (hd : d ≤ Cg*(t+N⁻¹)) (hr : re ≤ Cr*(t+Real.sqrt t+N⁻¹))
    (hlead : k*N*t-Clead/N ≤ lead)
    (htrace : m-Cb*d-re*Lr+lead ≤ τ) :
    m-C*t-C*Real.sqrt t-C/N+k*N*t ≤ τ := by
  have hd' := mul_le_mul_of_nonneg_left hd hCb
  have hr' := mul_le_mul_of_nonneg_right hr hLr
  have htC := mul_le_mul_of_nonneg_right h1 ht
  have hsC := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg t)
  have heC := mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hN.le)
  rw [div_eq_mul_inv] at hlead ⊢
  nlinarith only [htrace,hlead,hd',hr',htC,hsC,heC]

theorem radial_uniform_strict_bundle_oai {X : Type*} {V : X → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (a : ∀ x, V x) (H : ∀ x, ProfileForm (V x)) (χ : X → ℝ)
    (r e : ℕ → ∀ x, V x) (R T : ℕ → ∀ x, V x →L[ℝ] ℝ)
    (f b f₂ : ℕ → X → ℝ) (B Er : ℕ → ∀ x, ProfileForm (V x))
    (m α M Hmax δ A K S R₀ Fmax Ce Cr : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hK : 0 ≤ K) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
    (hFmax : 0 ≤ Fmax) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
    (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖a x‖) (haM : ∀ x, ‖a x‖ ≤ M)
    (hHH : ∀ x, ‖H x‖ ≤ Hmax) (hAa : ∀ x, A ≤ 2*‖a x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (a x) w = 0 → m ≤ profileTrace (H x) (a x) w)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hf : ∀ N x, 0 ≤ f N x ∧ f N x ≤ Fmax)
    (hb : ∀ N x, f N x/R₀ ≤ b N x) (hfS : ∀ N x, (f N x)^2 ≤ S*b N x)
    (hf₂ : ∀ N x, |f₂ N x| ≤ K)
    (hr : ∀ N x v, inner ℝ (r N x) v = R N x v)
    (hRa : ∀ N x, R N x (a x) = 0) (hTa : ∀ N x, T N x (a x) = 0)
    (hrn : ∀ N x, ‖r N x‖ ≤ 2)
    (hco : ∀ N x v, inner ℝ (a x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((R N x v)^2+(T N x v)^2))
    (hB : ∀ N x u v, B N x u v = f₂ N x*R N x u*R N x v+b N x*T N x u*T N x v)
    (he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ))
    (hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop, ∀ x,
      profileStrict (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x)
        (a x+(δ*A*χ x*f N x) • r N x+e N x) ∧
      a x+(δ*A*χ x*f N x) • r N x+e N x ≠ 0 := by
  let G := M+2*δ*A*Fmax+Ce
  let Cg := 2*δ*A+Ce
  let Cb := 4*Hmax*G+4*Hmax*(1+G^2)/α+2*(1+Hmax*(1+2*G^2))/α
  let Lr := 1+2*G^2
  let Clead := 8*K*δ*A*Ce^2
  let C := 1+Cb*Cg+Cr*Lr+Clead
  let k := δ*A/(32*R₀)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hMG : M ≤ G := by dsimp [G]; linarith only [mul_nonneg (show 0 ≤ 2*δ*A by positivity) hFmax, hCe]
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have hLr : 0 ≤ Lr := by dsimp [Lr]; positivity
  have hClead : 0 ≤ Clead := by dsimp [Clead]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hCCg : Cb*Cg+Cr*Lr ≤ C := by dsimp [C]; linarith only [hClead]
  have hCCr : Cr*Lr ≤ C := by dsimp [C]; linarith only [mul_nonneg hCb hCg,hClead]
  have hCCe : Cb*Cg+Cr*Lr+Clead ≤ C := by dsimp [C]; linarith only [hClead]
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv (c : ℝ) : Tendsto (fun N : ℕ => c/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hNone : ∀ᶠ N : ℕ in atTop, (1:ℝ) ≤ (N:ℝ) := hnat.eventually (eventually_ge_atTop _)
  have heSmall := (hinv Ce).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < α/3))
  have hη := (hinv C).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < m/4))
  have hlarge : ∀ᶠ N : ℕ in atTop, (C+C^2/m)/k ≤ (N:ℝ) :=
    hnat.eventually (eventually_ge_atTop _)
  filter_upwards [he,hEr,hNone,heSmall,hη,hlarge] with N heN hErN hN1 heS hηN hLN x
  have hN : 0 < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  let q := δ*A*χ x*f N x
  let aN := a x+q • r N x+e N x
  let t := χ x*f N x
  have ht : 0 ≤ t := mul_nonneg (hχ x).1 (hf N x).1
  have hqn : 0 ≤ q := mul_nonneg (mul_nonneg (mul_nonneg hδ.le hA.le) (hχ x).1) (hf N x).1
  have hqA : q ≤ δ*A*f N x := by
    dsimp [q]
    simpa using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hχ x).2 (mul_nonneg hδ.le hA.le)) (hf N x).1
  have haNe : a x ≠ 0 := norm_pos_iff.mp (hα.trans_le (ha0 x))
  have hethird : ‖e N x‖ ≤ ‖a x‖/3 := (heN x).trans
    (heS.le.trans (div_le_div_of_nonneg_right (ha0 x) (by norm_num)))
  have hehalf : ‖e N x‖ ≤ ‖a x‖/2 := by linarith only [hethird,norm_nonneg (a x)]
  have had : inner ℝ (a x) (r N x) = 0 := by rw [real_inner_comm,hr,hRa]
  have hnl : (1-(1/3:ℝ))*‖a x‖ ≤ ‖aN‖ :=
    radial_gradient_no_loss (a x) (r N x) (e N x) had q (1/3) (by linarith only [hethird])
  have haNNe : aN ≠ 0 := norm_pos_iff.mp (by nlinarith only [ha0 x,hnl,hα])
  have hL : ‖aN‖ ≤ Real.sqrt (1+‖aN‖^2) := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ 1+‖aN‖^2 by positivity),
      Real.sqrt_nonneg (1+‖aN‖^2),norm_nonneg aN]
  have hAL : A ≤ 3*Real.sqrt (1+‖aN‖^2) := by linarith only [hAa x,hnl,hL]
  obtain ⟨haNG,hdiff⟩ := radial_gradient_patch_bounds (a x) (r N x) (e N x)
    δ A (χ x) (f N x) M Fmax Ce (N:ℝ) hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hf N x).2 (hrn N x) (haM x) hCe hN1 (heN x)
  have hb0 : 0 ≤ b N x := (div_nonneg (hf N x).1 hR₀.le).trans (hb N x)
  obtain ⟨v,hv,hav,htrace⟩ := radial_total_trace_lower (hd x) (a x) (r N x) (e N x) haNe q
    (R N x) (T N x) (hr N x) (hRa N x) (hTa N x) hehalf (hrn N x) (hco N x)
    A δ (f N x) (b N x) K S (f₂ N x) hA.le hAL hδ.le (hf N x).1 hb0 hK hS
    (hf₂ N x) hqn hqA (hfS N x) hsmall (B N x) (H x) (Er N x) (hB N x)
    m α Hmax G ((N:ℝ)*δ*A*χ x) hm1 hα (ha0 x) (hHH x) ((haM x).trans hMG)
    haNG (mul_nonneg (mul_nonneg (mul_nonneg hN.le hδ.le) hA.le) (hχ x).1) (hmargin x)
  have hscaled := radial_scaled_leading_lower (N:ℝ) δ A (χ x) (f N x) (b N x) K
    ‖e N x‖ Ce R₀ (1+‖aN‖^2) hN hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hb N x) hK (norm_nonneg _) (heN x) hR₀ (by linarith only [sq_nonneg ‖aN‖])
  have hτ := radial_trace_collect_errors m Cb Cg Cr Lr Clead C k (N:ℝ) t
    ‖q • r N x+e N x‖ ‖Er N x‖
    ((N:ℝ)*δ*A*χ x*((1+‖aN‖^2)/32*b N x-8*K*‖e N x‖^2))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hN ht hCb hLr hCCg hCCr hCCe hdiff (hErN x) hscaled htrace
  have hD : C^2 ≤ (k*(N:ℝ)-C)*m := by
    have hh := (div_le_iff₀ hk).mp hLN
    apply (div_le_iff₀ hm).mp
    nlinarith only [hh]
  have hpos := radial_transition_positive m C (k*(N:ℝ)) t (C/(N:ℝ))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hm ht hηN.le hD hτ
  exact ⟨⟨v,hv,hav,lt_of_lt_of_le (by positivity) hpos⟩,haNNe⟩



end YauCounterexamples
end

end OAI
end

theorem solution.{u_2, u_3} : type_of% @OAI.YauCounterexamples.radial_uniform_strict_bundle_oai.{u_2, u_3} := @OAI.YauCounterexamples.radial_uniform_strict_bundle_oai.{u_2, u_3}
