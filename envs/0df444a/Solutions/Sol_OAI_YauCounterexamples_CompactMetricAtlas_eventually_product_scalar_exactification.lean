-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:20:19.285196+00:00
-- url     : https://prove2.me/submissions/f4980a2e-eb17-4a2f-ba04-cd94d8ffa81f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ReciprocalIteratedDerivativeBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

lemma reciprocal_iterated_derivative_bound (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => 1/y) (Ioi 0) t‖ ≤ (j.factorial : ℝ) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_one_div j isOpen_Ioi ht0]
  have he : (-1-(j:ℤ)) = -((j+1 : ℕ):ℤ) := by omega
  dsimp only
  rw [he,zpow_neg,zpow_natCast]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg,abs_one,one_pow,
    Nat.abs_cast,one_mul,norm_inv]
  have hp : 1 ≤ t^(j+1) := one_le_pow₀ ht
  have hi : |(t^(j+1))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _))]
    exact inv_le_one_of_one_le₀ hp
  simpa only [mul_one,abs_inv,abs_pow] using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg j.factorial)

theorem normalized_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (hx : 1 ≤ f x)
    (h : ℕ) (D : ℝ)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤ (h.factorial : ℝ)^2*D^h := by
  let S := {y | 0 < f y}
  have hS : IsOpen S := isOpen_lt continuous_const hf.continuous
  have hxS : x ∈ S := zero_lt_one.trans_le hx
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => 1/y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => hy.ne')
  have hb := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn (show (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn (fun y (hy : y ∈ S) => hy) hxS
    (C:=(h.factorial:ℝ)) (D:=D) (fun j hj =>
      (reciprocal_iterated_derivative_bound j hx).trans (by exact_mod_cast Nat.factorial_le hj))
    (fun j hj hjh => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn (hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt hxS]
      exact hD j hj hjh)
  change ‖iteratedFDerivWithin ℝ h (fun y => 1/f y) S x‖ ≤ _ at hb
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt (zero_lt_one.trans_le hx).ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn hrec hxS] at hb
  simpa only [Function.comp_apply,pow_two,mul_assoc] using hb

theorem weighted_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (h : ℕ)
    {δ W M R : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hR : 0 ≤ R) (hx : δ*W^2 ≤ f x)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ M*R^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤
      (h.factorial : ℝ)^2 * (max 1 (M/δ)*R)^h / (δ*W^2) := by
  let c := δ*W^2
  have hc : 0 < c := mul_pos hδ (sq_pos_of_pos hW)
  let F : E → ℝ := fun y => c⁻¹*f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hxF : 1 ≤ F x := by
    dsimp only [F]
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hx)
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j F x‖ ≤ (max 1 (M/δ)*R)^j := by
    intro j hj hjh
    have hej : iteratedFDeriv ℝ j F x = c⁻¹ • iteratedFDeriv ℝ j f x := by
      simpa only [F,smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a:=c⁻¹) (x:=x) (hf.of_le
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)
    rw [hej,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹*‖iteratedFDeriv ℝ j f x‖ ≤ c⁻¹*(M*R^j*W^2) :=
        mul_le_mul_of_nonneg_left (hjet j hj hjh) (inv_nonneg.mpr hc.le)
      _ = (M/δ)*R^j := by dsimp only [c]; field_simp
      _ ≤ (max 1 (M/δ))^j*R^j := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))) (pow_nonneg hR j)
      _ = (max 1 (M/δ)*R)^j := (mul_pow _ _ _).symm
  have hb := normalized_reciprocal_jet_bound hF hxF h (max 1 (M/δ)*R) hD
  have hfx : f x ≠ 0 := (hc.trans_le hx).ne'
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt hfx).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  have he : (fun y => 1/F y) = fun y => c • (1/f y) := by
    funext y
    simp only [F,one_div,smul_eq_mul,mul_inv_rev,inv_inv]
    ring
  rw [he,iteratedFDeriv_const_smul_apply' hrec,norm_smul,
    Real.norm_eq_abs,abs_of_pos hc] at hb
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

lemma geometric_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
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

theorem weighted_quotient_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h : ℕ)
    {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  have hrec : ContDiff ℝ ∞ (fun y => 1/d y) := contDiff_const.div hd hdne
  have hinv : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => 1/d y) x‖ ≤
      ((h.factorial:ℝ)^2/(δ*W^2))*(max 1 (M/δ)*S)^j := by
    intro j hj
    have hb := weighted_reciprocal_jet_bound hd j hδ hW hS hx
      (fun i hi hij => hdj i hi (hij.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := hb
      _ ≤ (h.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := by
        gcongr
      _ = _ := by ring
  have hb := geometric_product_jet_bound hf hrec x h
    (F:=N*W^2) (G:=(h.factorial:ℝ)^2/(δ*W^2))
    (mul_nonneg hN (sq_nonneg _)) (by positivity) hR
    (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hS)
    (fun j hj => by simpa only [mul_assoc,mul_left_comm,mul_comm] using hfj j hj) hinv
  have he : (N*W^2)*((h.factorial:ℝ)^2/(δ*W^2)) = N*(h.factorial:ℝ)^2/δ := by
    field_simp
  simpa only [one_div,← div_eq_mul_inv,he] using hb

theorem frequency_weighted_quotient_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h B a D : ℕ)
    {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let δ : ℝ := 1/(2*n^(2*B))
  let N : ℝ := F*n^a/(n^D)
  let M : ℝ := C*n^10
  let q : ℝ := max 1 (2*C)
  let t : ℕ := 2*B+11
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hx' : δ*W^2 ≤ d x := by simpa only [δ,one_div,div_eq_mul_inv,mul_comm,one_mul] using hx
  have hfj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*n^j*W^2 := by
    intro j hj
    calc
      _ ≤ F*n^(a+j)/(n^D)*W^2 := hfj j hj
      _ = _ := by dsimp only [N]; rw [pow_add]; ring
  have hdj' : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j d x‖ ≤ M*n^j*W^2 := by
    intro j hj hjh
    calc
      _ ≤ C*n^(j+10)*W^2 := hdj j hj hjh
      _ = _ := by dsimp only [M]; rw [pow_add]; ring
  have hb := weighted_quotient_jet_bound hf hd hdne x h hδ hW hN hn0.le hn0.le hx' hfj' hdj'
  have heM : M/δ = 2*C*n^(2*B+10) := by
    dsimp only [M,δ]
    rw [pow_add]
    field_simp
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hpow : 1 ≤ n^(2*B+10) := one_le_pow₀ hn
  have hmax : max 1 (M/δ) ≤ q*n^(2*B+10) := by
    apply max_le
    · exact hq.trans (le_mul_of_one_le_right hq0 hpow)
    · rw [heM]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hn0.le _)
  have hsum : n+max 1 (M/δ)*n ≤ (1+q)*n^t := by
    have hnle : n ≤ n^t := by
      simpa only [pow_one] using pow_le_pow_right₀ hn (show 1 ≤ t by dsimp only [t]; omega)
    have hm : max 1 (M/δ)*n ≤ q*n^t := by
      calc
        _ ≤ (q*n^(2*B+10))*n := mul_le_mul_of_nonneg_right hmax hn0.le
        _ = q*n^t := by dsimp only [t]; rw [show 2*B+11=(2*B+10)+1 by omega,pow_succ]; ring
    calc
      _ ≤ n^t+q*n^t := add_le_add hnle hm
      _ = _ := by ring
  calc
    _ ≤ N*(h.factorial:ℝ)^2/δ*(n+max 1 (M/δ)*n)^h := hb
    _ ≤ N*(h.factorial:ℝ)^2/δ*((1+q)*n^t)^h := by
      gcongr
    _ = _ := by
      dsimp only [N,δ,t,q]
      simp only [mul_pow,pow_add,pow_mul]
      field_simp

theorem frequency_weighted_quotient_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h B a D : ℕ)
    {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  intro j hj
  apply (frequency_weighted_quotient_bound hf hd hdne x j B a D hn hW hF hx
    (fun i hi => hfj i (hi.trans hj)) (fun i hi hij => hdj i hi (hij.trans hj))).trans
  gcongr
  have := le_max_left (1:ℝ) (2*C)
  linarith

theorem frequency_weighted_product_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h a b D : ℕ) {n W F G : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*n^(b+j)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤
      (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hfj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ (F*n^a/(n^D)*W)*n^j := by
    intro j hj
    calc
      _ ≤ F*n^(a+j)/(n^D)*W := hfj j hj
      _ = _ := by rw [pow_add]; ring
  have hgj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ (G*n^b*W)*n^j := by
    intro j hj
    calc
      _ ≤ G*n^(b+j)*W := hgj j hj
      _ = _ := by rw [pow_add]; ring
  intro j hj
  calc
    _ ≤ (F*n^a/(n^D)*W)*(G*n^b*W)*(n+n)^j :=
      geometric_product_jet_bound hf hg x j (by positivity) (by positivity) hn0.le hn0.le
        (fun i hi => hfj' i (hi.trans hj)) (fun i hi => hgj' i (hi.trans hj))
    _ = (2^j*F*G)*n^(a+b+j)/(n^D)*W^2 := by
      rw [show n+n=2*n by ring,mul_pow]
      simp only [pow_add]
      ring
    _ ≤ (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
      gcongr
      norm_num

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivScalarDirection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem coordinateDivergence_mul (e : ι → E) (ρ f : E → ℝ) (X : ι → E → ℝ)
    (x : E) (hρ : DifferentiableAt ℝ ρ x) (hf : DifferentiableAt ℝ f x)
    (hX : ∀ i, DifferentiableAt ℝ (X i) x) (hρx : ρ x ≠ 0) :
    coordinateDivergence e ρ (fun i y => f y * X i y) x =
      f x * coordinateDivergence e ρ X x +
        ∑ i, fderiv ℝ f x (e i) * X i x := by
  have hprod (i : ι) : (fun y => ρ y * (f y * X i y)) =
      (fun y => f y * (ρ y * X i y)) := by funext y; ring
  unfold coordinateDivergence
  simp only [hprod, fderiv_fun_mul (d := fun y => ρ y * X _ y) hf (hρ.mul (hX _)),
    add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : ∑ i, ρ x * X i x * fderiv ℝ f x (e i) =
      ρ x * ∑ i, fderiv ℝ f x (e i) * X i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp

theorem contDiff_coordinateDivergence (e : ι → E) (ρ : E → ℝ) (X : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hρne : ∀ x, ρ x ≠ 0) : ContDiff ℝ ∞ (coordinateDivergence e ρ X) := by
  apply (hρ.inv hρne).mul
  apply ContDiff.sum
  intro i _
  exact ((hρ.mul (hX i)).fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_scalarCorrectionDenominator (e : ι → E) (n : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    ContDiff ℝ ∞ (scalarCorrectionDenominator e n U X) := by
  apply (contDiff_const.mul (hU.pow 2)).add
  apply ContDiff.sum
  intro i _
  exact ((hU.fderiv_right (by simp)).clm_apply contDiff_const).mul (hX i)


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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma norm_iteratedFDeriv_scalar_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma norm_iteratedFDeriv_scalar_sum (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (h : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ h (fun y => ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ h (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hf i).contDiffAt.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))))]
  exact norm_sum_le _ _

theorem scalar_denominator_jet_bound (e : ι → E) (U : E → ℝ) (X : ι → E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (x : E) (h : ℕ) {n W C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C)
    (hUj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (scalarCorrectionDenominator e n U X) x‖ ≤
      (2^h*C*C*(1+∑ i, ‖e i‖))*n^(j+10)*W^2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hu : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => U y*U y) x‖ ≤
      (2^h*C*C)*n^(8+j)*W^2 := by
    simpa only [pow_zero,div_one,show 4+4=8 from rfl] using
      frequency_weighted_product_bound hU hU x h 4 4 0 hn hW hC hC
        (fun j hj => by simpa only [pow_zero,div_one,Nat.add_comm] using hUj j (by omega))
        (fun j hj => by simpa only [Nat.add_comm] using hUj j (by omega))
  have hdu (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ U y (e i)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hdU (i : ι) (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)) x‖ ≤
        (‖e i‖*C)*n^(5+j)*W := by
    calc
      _ ≤ ‖e i‖*‖iteratedFDeriv ℝ (j+1) U x‖ := norm_iteratedFDeriv_scalar_direction hU _ _ _
      _ ≤ ‖e i‖*(C*n^((j+1)+4)*W) :=
        mul_le_mul_of_nonneg_left (hUj (j+1) (by omega)) (norm_nonneg _)
      _ = _ := by rw [show j+1+4=5+j by omega]; ring
  have hp (i : ι) : ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ ≤
        (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2 := by
    simpa only [pow_zero,div_one,show 5+5=10 from rfl] using
      frequency_weighted_product_bound (hdu i) (hX i) x h 5 5 0 hn hW
        (mul_nonneg (norm_nonneg _) hC) hC
        (fun j hj => by simpa only [pow_zero,div_one] using hdU i j hj)
        (fun j hj => by simpa only [Nat.add_comm] using hXj i j hj)
  intro j hj
  have hcj : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have hsc : ContDiff ℝ ∞ (fun y => n^2*(U y*U y)) := contDiff_const.mul (hU.mul hU)
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, fderiv ℝ U y (e i)*X i y) :=
    ContDiff.sum (fun i _ => (hdu i).mul (hX i))
  have he : scalarCorrectionDenominator e n U X =
      fun y => n^2*(U y*U y)+(∑ i, fderiv ℝ U y (e i)*X i y) := by
    funext y; simp only [scalarCorrectionDenominator,pow_two]
  rw [he]
  calc
    _ = ‖iteratedFDeriv ℝ j (fun y => n^2*(U y*U y)) x +
        iteratedFDeriv ℝ j (fun y => ∑ i, fderiv ℝ U y (e i)*X i y) x‖ := by
      rw [fun_iteratedFDeriv_add_apply ((hsc.of_le hcj).contDiffAt) ((hsum.of_le hcj).contDiffAt)]
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => n^2*(U y*U y)) x‖ +
        ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        (norm_iteratedFDeriv_scalar_sum _ (fun i => (hdu i).mul (hX i)) j x))
    _ = n^2*‖iteratedFDeriv ℝ j (fun y => U y*U y) x‖ +
        ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ := by
      rw [show (fun y => n^2*(U y*U y)) = (fun y => n^2 • (U y*U y)) by rfl,
        iteratedFDeriv_const_smul_apply' ((hU.mul hU).contDiffAt.of_le hcj),norm_smul,
        Real.norm_eq_abs,abs_of_nonneg (sq_nonneg n)]
    _ ≤ n^2*((2^h*C*C)*n^(8+j)*W^2)+
        ∑ i, (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hu j hj) (sq_nonneg _))
        (Finset.sum_le_sum fun i _ => hp i j hj)
    _ = _ := by
      have hs : (∑ i, (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2) =
          (2^h*C*C)*n^(10+j)*W^2*(∑ i, ‖e i‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hs]
      simp only [pow_add]
      ring

lemma constant_product_jet_bound {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (h : ℕ)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hb := geometric_product_jet_bound hf hg x j (R:=1) (S:=1) hF hG
    zero_le_one zero_le_one
    (fun i hi => by simpa only [one_pow,mul_one] using hfj i (hi.trans hj))
    (fun i hi => by simpa only [one_pow,mul_one] using hgj i (hi.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hb
    _ ≤ F*G*(1+1)^h := by gcongr; norm_num
    _ = _ := by norm_num; ring

theorem coordinate_divergence_jet_bound (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρne : ∀ y, ρ y ≠ 0)
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (x : E) (h : ℕ)
    {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  have hρZ (i : ι) : ContDiff ℝ ∞ (fun y => ρ y*Z i y) := hρ.mul (hZ i)
  have hp (i : ι) := constant_product_jet_bound hρ (hZ i) x (h+1) hC hF hρj (hZj i)
  have hdf (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ((hρZ i).fderiv_right (by simp)).clm_apply contDiff_const
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ContDiff.sum (fun i _ => hdf i)
  have hs : ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ ≤
        (∑ i, ‖e i‖)*(2^(h+1)*C*F) := by
    intro j hj
    calc
      _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ :=
        norm_iteratedFDeriv_scalar_sum _ hdf j x
      _ ≤ ∑ i, ‖e i‖*(2^(h+1)*C*F) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (norm_iteratedFDeriv_scalar_direction (hρZ i) (e i) j x).trans
          (mul_le_mul_of_nonneg_left (hp i (j+1) (by omega)) (norm_nonneg _))
      _ = _ := by rw [Finset.sum_mul]
  have hb := constant_product_jet_bound (hρ.inv hρne) hsum x h hC
    (show 0 ≤ (∑ i, ‖e i‖)*(2^(h+1)*C*F) by positivity) hρij hs
  intro j hj
  apply (hb j hj).trans_eq
  rw [show 2*h+1=h+(h+1) by omega,pow_add]
  ring

theorem scalar_denominator_lower {n W u q : ℝ} {B : ℕ} (hn : 0 < n)
    (hW : 0 < W) (hq : 0 ≤ q)
    (hjet : W/n^B ≤ |u|+Real.sqrt q/n) :
    n^2*W^2/(2*n^(2*B)) ≤ n^2*u^2+q := by
  have h0 : 0 ≤ n*W/n^B := by positivity
  have hlin : n*W/n^B ≤ n*|u|+Real.sqrt q := by
    calc
      n*W/n^B = n*(W/n^B) := by ring
      _ ≤ n*(|u|+Real.sqrt q/n) := mul_le_mul_of_nonneg_left hjet hn.le
      _ = n*|u|+Real.sqrt q := by field_simp
  have hs := mul_self_le_mul_self h0 hlin
  have hsqrt := Real.sq_sqrt hq
  have hsqabs := sq_abs u
  have hsplit := sq_nonneg (n*|u|-Real.sqrt q)
  have ht : (n*W/n^B)^2 ≤ 2*(n^2*u^2+q) := by
    nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ u^2 by positivity)]
  have he : n^2*W^2/(2*n^(2*B)) = (n*W/n^B)^2/2 := by
    rw [pow_mul]; field_simp; ring
  rw [he]
  linarith



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SmoothExtension
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

lemma positive_smooth_extension_at {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hfx : 0 < f x) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ (∀ y, 0 < F y) ∧ f =ᶠ[𝓝 x] F := by
  have hp : {y | 0 < f y} ∈ 𝓝 x :=
    (hf.continuousOn.continuousAt (hO.mem_nhds hx)).eventually (isOpen_Ioi.mem_nhds hfx)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hp
  obtain ⟨F,hF,he⟩ := smooth_extension_at (hO.inter hVo) ⟨hx,hxV⟩
    ((hf.mono inter_subset_left).log (fun y hy => (hV hy.2).ne'))
  refine ⟨fun y => Real.exp (F y), hF.exp,fun _ => Real.exp_pos _,?_⟩
  filter_upwards [he, hp] with y hy hpy
  rw [← hy,Real.exp_log hpy]

omit [FiniteDimensional ℝ E] in
lemma coordinateDivergence_eventuallyEq (e : ι → E) {ρ σ : E → ℝ}
    {X Y : ι → E → ℝ} {x : E} (hρ : ρ =ᶠ[𝓝 x] σ)
    (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    coordinateDivergence e ρ X =ᶠ[𝓝 x] coordinateDivergence e σ Y := by
  have hd (i : ι) := (hρ.mul (hX i)).fderiv (𝕜:=ℝ)
  filter_upwards [hρ,eventually_all.mpr hd] with y hy hdy
  simp only [coordinateDivergence,hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e i)) (hdy i)

omit [FiniteDimensional ℝ E] in
lemma scalarCorrectionDenominator_eventuallyEq (e : ι → E) (n : ℝ)
    {U V : E → ℝ} {X Y : ι → E → ℝ} {x : E}
    (hU : U =ᶠ[𝓝 x] V) (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    scalarCorrectionDenominator e n U X =ᶠ[𝓝 x] scalarCorrectionDenominator e n V Y := by
  filter_upwards [hU,hU.fderiv (𝕜:=ℝ),eventually_all.mpr hX] with y hy hdy hxy
  simp only [scalarCorrectionDenominator,hy,hdy,hxy]

lemma contDiffOn_coordinateDivergence (e : ι → E) {O : Set E} (hO : IsOpen O)
    {ρ : E → ℝ} {X : ι → E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hρp : ∀ y ∈ O, 0 < ρ y) :
    ContDiffOn ℝ ∞ (coordinateDivergence e ρ X) O := by
  intro x hx
  obtain ⟨σ,hσ,hσp,hσe⟩ := positive_smooth_extension_at hO hx hρ (hρp x hx)
  choose Y hY hYe using fun i => smooth_extension_at hO hx (hX i)
  exact ((contDiff_coordinateDivergence e σ Y hσ hY (fun y => (hσp y).ne')).contDiffAt.congr_of_eventuallyEq
    (coordinateDivergence_eventuallyEq e hσe hYe)).contDiffWithinAt

lemma contDiffOn_scalarCorrectionDenominator (e : ι → E) (n : ℝ)
    {O : Set E} (hO : IsOpen O) {U : E → ℝ} {X : ι → E → ℝ}
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) :
    ContDiffOn ℝ ∞ (scalarCorrectionDenominator e n U X) O := by
  intro x hx
  obtain ⟨V,hV,hVe⟩ := smooth_extension_at hO hx hU
  choose Y hY hYe using fun i => smooth_extension_at hO hx (hX i)
  exact ((contDiff_scalarCorrectionDenominator e n V Y hV hY).contDiffAt.congr_of_eventuallyEq
    (scalarCorrectionDenominator_eventuallyEq e n hVe hYe)).contDiffWithinAt

lemma contDiffOn_scalarCorrectionRatio (e : ι → E) (n Λ : ℝ)
    {O : Set E} (hO : IsOpen O) {ρ U : E → ℝ} {X : ι → E → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ O) (hU : ContDiffOn ℝ ∞ U O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hden : ∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0) :
    ContDiffOn ℝ ∞ (scalarCorrectionRatio e ρ n Λ U X) O := by
  exact ((contDiffOn_coordinateDivergence e hO hρ hX hρp).add
    (contDiffOn_const.mul hU)).div (contDiffOn_scalarCorrectionDenominator e n hO hU hX) hden

theorem frequency_weighted_quotient_uniform_on
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f d : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hd : ContDiffOn ℝ ∞ d O)
    (h B a D : ℕ) {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨d',hd',hdp,hde⟩ := positive_smooth_extension_at hO hxO hd
    ((show 0 < W^2/(2*n^(2*B)) by positivity).trans_le hx)
  have hq := frequency_weighted_quotient_uniform hf' hd' (fun y => (hdp y).ne') x h B a D
    hn hW hF (hde.self_of_nhds ▸ hx)
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj hjh => (hde.iteratedFDeriv ℝ j).self_of_nhds ▸ hdj j hj hjh)
  intro j hj
  change ‖iteratedFDeriv ℝ j (f/d) x‖ ≤ _
  rw [(hfe.div hde).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem frequency_weighted_product_bound_on
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h a b D : ℕ) {n W F G : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*n^(b+j)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤
      (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hxO hg
  have hq := frequency_weighted_product_bound hf' hg' x h a b D hn hW hF hG
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  intro j hj
  change ‖iteratedFDeriv ℝ j (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem scalar_denominator_jet_bound_on (e : ι → E) (U : E → ℝ) (X : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O)
    (h : ℕ) {n W C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C)
    (hUj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (scalarCorrectionDenominator e n U X) x‖ ≤
      (2^h*C*C*(1+∑ i, ‖e i‖))*n^(j+10)*W^2 := by
  obtain ⟨V,hV,hVe⟩ := smooth_extension_at hO hxO hU
  choose Y hY hYe using fun i => smooth_extension_at hO hxO (hX i)
  have hq := scalar_denominator_jet_bound e V Y hV hY x h hn hW hC
    (fun j hj => (hVe.iteratedFDeriv ℝ j).self_of_nhds ▸ hUj j hj)
    (fun i j hj => ((hYe i).iteratedFDeriv ℝ j).self_of_nhds ▸ hXj i j hj)
  intro j hj
  rw [(scalarCorrectionDenominator_eventuallyEq e n hVe hYe).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem coordinate_divergence_jet_bound_on (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) O)
    (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  obtain ⟨σ,hσ,hσp,hσe⟩ := positive_smooth_extension_at hO hxO hρ (hρp x hxO)
  choose Y hY hYe using fun i => smooth_extension_at hO hxO (hZ i)
  have hq := coordinate_divergence_jet_bound e σ Y hσ (fun y => (hσp y).ne') hY x h hC hF
    (fun j hj => (hσe.iteratedFDeriv ℝ j).self_of_nhds ▸ hρj j hj)
    (fun j hj => (hσe.inv.iteratedFDeriv ℝ j).self_of_nhds ▸ hρij j hj)
    (fun i j hj => ((hYe i).iteratedFDeriv ℝ j).self_of_nhds ▸ hZj i j hj)
  intro j hj
  rw [(coordinateDivergence_eventuallyEq e hσe hYe).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem scalar_correction_error_from_quotients_on
    (e : ι → E) (ρ U : E → ℝ) (X : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O)
    {n : ℝ} (hn : 1 ≤ n)
    (hden : ∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0)
    (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hqU : ∀ j ≤ h, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F)
    (hqX : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F) :
    ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      (2+2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  let f := scalarCorrectionRatio e ρ n (n*(n+2)) U X
  have hf : ContDiffOn ℝ ∞ f O := contDiffOn_scalarCorrectionRatio e n (n*(n+2)) hO
    hρ hU hX hρp hden
  let Z : ι → E → ℝ := fun i y => f y*X i y
  have hZ (i : ι) : ContDiffOn ℝ ∞ (Z i) O := hf.mul (hX i)
  have hd := contDiffOn_coordinateDivergence e hO hρ hZ hρp
  have hq := hf.mul hU
  have hdiv := coordinate_divergence_jet_bound_on e ρ Z hO hxO hρ hρp hZ h hC hF hρj hρij hqX
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hΛ : 0 < n*(n+2) := by positivity
  have hΛ1 : 1 ≤ n*(n+2) := by nlinarith
  have hnratio : (n*(n+2))⁻¹*n^2 ≤ 1 := by
    rw [← div_eq_inv_mul,div_le_one hΛ]
    nlinarith
  have hΛinv : (n*(n+2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
  have hCb : 0 ≤ 2^(2*h+1)*C*C*(∑ i, ‖e i‖) := by positivity
  intro j hj
  have hj' : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have heb : (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) =
      fun y => -(f y*U y) := by funext y; dsimp only [scalarCorrectionB,f]; ring
  have hes : (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) =
      fun y => -((n*(n+2))⁻¹ • (n^2 • (f y*U y)-coordinateDivergence e ρ Z y)) := by
    funext y; dsimp only [scalarCorrectionS,f,Z,smul_eq_mul]; ring
  have hb : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ ≤ F := by
    rw [heb]
    change ‖iteratedFDeriv ℝ j (-(fun y => f y*U y)) x‖ ≤ F
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hqU j hj
  have hs : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
    have hz : ContDiffOn ℝ ∞ (fun y => n^2 • (f y*U y)-coordinateDivergence e ρ Z y) O :=
      (hq.const_smul (n^2)).sub hd
    rw [hes]
    change ‖iteratedFDeriv ℝ j (-(fun y => (n*(n+2))⁻¹ •
      (n^2 • (f y*U y)-coordinateDivergence e ρ Z y))) x‖ ≤ _
    rw [iteratedFDeriv_neg_apply,norm_neg,iteratedFDeriv_const_smul_apply' ((hz.contDiffAt (hO.mem_nhds hxO)).of_le hj'),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΛ),
      fun_iteratedFDeriv_sub_apply (((hq.const_smul (n^2)).contDiffAt (hO.mem_nhds hxO)).of_le hj') ((hd.contDiffAt (hO.mem_nhds hxO)).of_le hj')]
    calc
      _ ≤ (n*(n+2))⁻¹*(‖iteratedFDeriv ℝ j (fun y => n^2 • (f y*U y)) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hΛ.le)
      _ = (n*(n+2))⁻¹*(n^2*‖iteratedFDeriv ℝ j (fun y => f y*U y) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) := by
        rw [iteratedFDeriv_const_smul_apply' ((hq.contDiffAt (hO.mem_nhds hxO)).of_le hj'),norm_smul,
          Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ (n*(n+2))⁻¹*(n^2*F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hqU j hj) (sq_nonneg _)) (hdiv j hj))
          (inv_nonneg.mpr hΛ.le)
      _ = ((n*(n+2))⁻¹*n^2)*F + (n*(n+2))⁻¹*((2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by ring
      _ ≤ _ := add_le_add
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnratio hF)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hΛinv (mul_nonneg hCb hF))
  calc
    _ ≤ F+(F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := add_le_add hb hs
    _ = _ := by ring

theorem quantitative_scalar_correction_jets_on
    (e : ι → E) (ρ : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ K > 0, ∀ (n : ℝ), 1 ≤ n → ∀ (D : ℕ) (U : E → ℝ) (X : ι → E → ℝ),
      ContDiffOn ℝ ∞ U O → (∀ i, ContDiffOn ℝ ∞ (X i) O) →
      (∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0) →
      ∀ x ∈ O, ∀ (W : ℝ), 0 < W →
      W^2/(2*n^(2*B)) ≤ scalarCorrectionDenominator e n U X x →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W) →
      (∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
        (fun y => coordinateDivergence e ρ X y+n*(n+2)*U y) x‖ ≤ C*n^4/(n^D)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C) →
      ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
        K*n^((2*B+21)*(h+2)+10)/(n^D) := by
  let Cd : ℝ := 2^(h+1)*C*C*(1+∑ i, ‖e i‖)
  let A : ℝ := 2^(h+1)*C*C
  let Kq : ℝ := 2*A*((h+1).factorial:ℝ)^2*(1+max 1 (2*Cd))^(h+1)
  let Kv : ℝ := 2+2^(2*h+1)*C*C*(∑ i, ‖e i‖)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hKq : 0 < Kq := by
    have hc : 0 < (1+max 1 (2*Cd)) := by have := le_max_left (1:ℝ) (2*Cd); linarith
    dsimp only [Kq]
    positivity
  have hKv : 0 < Kv := by dsimp only [Kv]; positivity
  refine ⟨Kv*Kq, mul_pos hKv hKq, ?_⟩
  intro n hn D U X hU hX hden x hxO W hW hx hUj hXj hRj hρj hρij j hj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let R : E → ℝ := fun y => coordinateDivergence e ρ X y+n*(n+2)*U y
  let d := scalarCorrectionDenominator e n U X
  have hR : ContDiffOn ℝ ∞ R O :=
    (contDiffOn_coordinateDivergence e hO hρ hX hρp).add (contDiffOn_const.mul hU)
  have hd : ContDiffOn ℝ ∞ d O := contDiffOn_scalarCorrectionDenominator e n hO hU hX
  have hRj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k R x‖ ≤ C*n^(4+k)/(n^D)*W := by
    intro k hk
    apply (hRj k hk).trans
    gcongr
    omega
  have hUj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k U x‖ ≤ C*n^(4+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hUj k (by omega)
  have hXj' (i : ι) : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (X i) x‖ ≤ C*n^(5+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hXj i k hk
  have hdj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k d x‖ ≤ Cd*n^(k+10)*W^2 :=
    scalar_denominator_jet_bound_on e U X hO hxO hU hX (h+1) hn hW hC.le
      (fun k hk => hUj k (by omega)) hXj
  have hRU := frequency_weighted_product_bound_on hO hxO hR hU (h+1) 4 4 D hn hW hC.le hC.le hRj' hUj'
  have hRX (i : ι) := frequency_weighted_product_bound_on hO hxO hR (hX i) (h+1) 4 5 D hn hW hC.le hC.le hRj' (hXj' i)
  have hqU := frequency_weighted_quotient_uniform_on hO hxO (hR.mul hU) hd (h+1) B 8 D hn hW hA.le hx hRU
    (fun k _ hk => hdj k hk)
  have hqX (i : ι) := frequency_weighted_quotient_uniform_on hO hxO (hR.mul (hX i)) hd (h+1) B 9 D hn hW hA.le hx (hRX i)
    (fun k _ hk => hdj k hk)
  let T : ℕ := 9+2*B+(2*B+11)*(h+1)
  let F : ℝ := Kq*n^T/(n^D)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hqu : ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F := by
    intro k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) =
        fun y => (R y*U y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    apply (hqU k (by omega)).trans
    change Kq*n^(8+2*B+(2*B+11)*(h+1))/(n^D) ≤ Kq*n^T/(n^D)
    gcongr
    dsimp only [T]; omega
  have hqx : ∀ i, ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F := by
    intro i k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) =
        fun y => (R y*X i y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    exact hqX i k hk
  have hb := scalar_correction_error_from_quotients_on e ρ U X hO hxO hρ hρp hU hX hn hden h hC.le hF hρj hρij hqu hqx j hj
  apply hb.trans
  change Kv*(Kq*n^T/(n^D)) ≤ Kv*Kq*n^((2*B+21)*(h+2)+10)/(n^D)
  rw [show Kv*(Kq*n^T/(n^D))=Kv*Kq*n^T/(n^D) by ring]
  gcongr
  dsimp only [T]; nlinarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ConstantComplexProductJetBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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

lemma constant_complex_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*F*G := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _) hF) (hgj (h-i) (Nat.sub_le _ _))
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hG
    _ = 2^h*F*G := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose h

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem localized_real_chart_jet_bound (p : M) (η : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η) (N : ℕ) :
    ∃ C > 0, ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f →
      ∀ R : ℝ, 0 ≤ R →
      (∀ y ∈ (chartAt E p) '' tsupport η, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (f ∘ (chartAt E p).symm) y‖ ≤ R) →
      ∀ y : E, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (chartLocalize (E:=E) p η (fun x => (f x : ℂ))) y‖ ≤ C*R := by
  let K := (chartAt E p) '' tsupport η
  have hK : IsCompact K := isCompact_chartSupport (E:=E) p η hηc hηs
  let e := chartLocalize (E:=E) p η (fun _ => (1 : ℂ))
  have he : ContDiff ℝ ∞ e := contDiff_chartLocalize p η _ hηc hηs hη contMDiff_const
  obtain ⟨B,hB,hBj⟩ := compact_derivative_bound hK he N
  refine ⟨2^N*B,by positivity,?_⟩
  intro f hf R hR hfj y j hj
  let fL := chartLocalize (E:=E) p η (fun x => (f x : ℂ))
  have hsupp : tsupport fL ⊆ K :=
    closure_minimal (support_chartLocalize (E:=E) p η _) hK.isClosed
  by_cases hy : y ∈ K
  · have hyt : y ∈ (chartAt E p).target := by
      obtain ⟨x,hx,rfl⟩ := hy
      exact (chartAt E p).map_source (hηs hx)
    have hfc : ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) (chartAt E p).target :=
      fun z hz => (contDiffAt_inChart hf p hz).contDiffWithinAt
    obtain ⟨F,hF,hFe⟩ := smooth_extension_at (chartAt E p).open_target hyt hfc
    have hfLe : fL =ᶠ[𝓝 y] (fun z => e z*(F z : ℂ)) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds hyt,hFe] with z hz hFz
      simp only [fL,e,chartLocalize_eq p η _ hz,mul_one]
      rw [← hFz]
      rfl
    rw [(hfLe.iteratedFDeriv ℝ j).self_of_nhds]
    have hFj (l : ℕ) (hl : l ≤ j) :
        ‖iteratedFDeriv ℝ l (fun z => (F z : ℂ)) y‖ ≤ R := by
      change ‖iteratedFDeriv ℝ l (Complex.ofRealLI ∘ F) y‖ ≤ R
      rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hF.contDiffAt
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top l))),
        ← (hFe.iteratedFDeriv ℝ l).self_of_nhds]
      exact hfj y hy l (hl.trans hj)
    apply (constant_complex_product_jet_bound he (Complex.ofRealCLM.contDiff.comp hF)
      y j (zero_le_one.trans hB) hR
      (fun l hl => hBj l (hl.trans hj) y hy) hFj).trans
    gcongr; norm_num
  · have hn : y ∉ tsupport (iteratedFDeriv ℝ j fL) :=
      fun h => hy (hsupp (tsupport_iteratedFDeriv_subset j h))
    rw [image_eq_zero_of_notMem_tsupport hn,norm_zero]
    positivity


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring

lemma weightedLaplacian_expansion {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x = b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  let e := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hb' := contDiffAt_inChart_C2 hb x hx
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hρ := Real.sqrt_pos.mpr (metricCoefficients_det_pos g x hx)
  have hρd := ((contDiffOn_metricDensity g x).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hflux (i : CoordIndex E) : DifferentiableAt ℝ
      (fun y => ρ y * ∑ j, (a y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (e j)) (c x) := by
    apply hρd.mul
    apply DifferentiableAt.fun_sum
    intro j _
    apply (((contDiffOn_metricInverse g x i j).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)).mul
    exact ((hu'.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  change (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) = _
  have hd (i : CoordIndex E) : fderiv ℝ
      (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) =
      b x * fderiv ℝ (fun y => ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j)) (c x) (e i) +
      (ρ (c x) * ∑ j, (a (c x))⁻¹ i j * fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i) := by
    erw [fderiv_fun_mul (hb'.differentiableAt (by norm_num)) (hflux i)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  simp_rw [hd, Finset.sum_add_distrib]
  change (ρ (c x))⁻¹ * ((∑ i, b x * _) +
    ∑ i, (ρ (c x) * ∑ j, (a (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i)) = _
  unfold laplaceBeltrami coordinateGradientPair
  dsimp only
  simp only [Finset.mul_sum, mul_add, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ρ, a, c, e] at hρ ⊢
    field_simp [ne_of_gt hρ]


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_zero_off_support (g : SmoothMetric E M) (u v : M → ℝ)
    {x : M} (hx : x ∉ tsupport u) : coordinateGradientPair g u v x = 0 := by
  have hzero : u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hc : Tendsto (chartAt E x).symm (𝓝 ((chartAt E x) x)) (𝓝 x) := by
    have hh := (chartAt E x).continuousOn_symm.continuousAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))
    simpa only [ContinuousAt, (chartAt E x).left_inv (mem_chart_source E x)] using hh
  have he : (u ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] (fun _ => (0 : ℝ)) :=
    hzero.comp_tendsto hc
  simp only [coordinateGradientPair, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero]

end GradientPairCalculus

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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_scalar_correction {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => 1 - f y * u y) u x =
      - f x * coordinateGradientPair g u u x - u x * coordinateGradientPair g f u x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => 1 - f y * u y) ∘ c.symm) =
      fun y => 1 - (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => 1 - f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_sub (f := fun _ => (1 : ℝ))
    (g := fun y => (f ∘ c.symm) y * (u ∘ c.symm) y)
    (differentiableAt_const _) (hf'.mul hu'),
    fderiv_fun_mul hf' hu', fderiv_const]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  simp only [_root_.zero_apply, (chartAt E x).left_inv (mem_chart_source E x)]
  ring

lemma contMDiff_weightedLaplacian {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (weightedLaplacian g b u) := by
  have he : weightedLaplacian g b u = fun x =>
      b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
    funext x
    exact weightedLaplacian_expansion (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) g x
  rw [he]
  exact (hb.mul (contMDiff_laplaceBeltrami hu g)).add
    (contMDiff_coordinateGradientPair hb hu g)

lemma contMDiff_intrinsicCorrectionF {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionF g n Λ u) := by
  exact ((contMDiff_laplaceBeltrami hu g).add (contMDiff_const.mul hu)).div₀
    ((contMDiff_const.mul (hu.pow 2)).add (contMDiff_coordinateGradientPair hu hu g)) hD

theorem intrinsic_scalar_correction {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hΛ : Λ ≠ 0) (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionB g n Λ u) ∧
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionS g n Λ u) ∧
    ∀ x, weightedLaplacian g (intrinsicCorrectionB g n Λ u) u x +
      Λ * intrinsicCorrectionS g n Λ u x * u x = 0 := by
  let f := intrinsicCorrectionF g n Λ u
  have hf := contMDiff_intrinsicCorrectionF hu g n Λ hD
  have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionB g n Λ u) :=
    contMDiff_const.sub (hf.mul hu)
  have hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionS g n Λ u) :=
    contMDiff_const.sub (contMDiff_const.mul
      (((contMDiff_const.mul hf).mul hu).sub (contMDiff_weightedLaplacian hf hu g)))
  refine ⟨hb, hs, fun x => ?_⟩
  rw [weightedLaplacian_expansion (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  change (1 - f x * u x) * laplaceBeltrami g u x +
    coordinateGradientPair g (fun y => 1 - f y * u y) u x +
    Λ * (1 - Λ⁻¹ * (n ^ 2 * f x * u x - weightedLaplacian g f u x)) * u x = 0
  rw [coordinateGradientPair_scalar_correction hf hu,
    weightedLaplacian_expansion (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have hprod : f x * (n ^ 2 * u x ^ 2 + coordinateGradientPair g u u x) =
      laplaceBeltrami g u x + Λ * u x := div_mul_cancel₀ _ (hD x)
  field_simp
  nlinarith [hprod]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma chartGradientField_smooth {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    (i : CoordIndex E) :
    ContDiffOn ℝ ∞ (chartGradientField g u p i) (chartAt E p).target := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  unfold chartGradientField coordinateFlux
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).mul
    (((contDiffAt_inChart hu p hy).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

lemma scalarCorrectionDenominator_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionD g n u ((chartAt E p).symm y) =
      scalarCorrectionDenominator (Module.finBasis ℝ E) n
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionD
  rw [coordinateGradientPair_inChart hu hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  rfl

lemma scalarCorrectionRatio_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionF g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionRatio (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionF scalarCorrectionRatio
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy, scalarCorrectionDenominator_inChart hu g n p hy]
  rfl

lemma weightedLaplacian_chartGradient {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    weightedLaplacian g f u ((chartAt E p).symm y) =
      coordinateDivergence (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det)
        (fun i z => f ((chartAt E p).symm z)*chartGradientField g u p i z) y := by
  have hρ := (contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)
  have hρp := Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)
  rw [coordinateDivergence_mul (Module.finBasis ℝ E)
    (fun z => Real.sqrt (metricCoefficients g p z).det)
    (fun z => f ((chartAt E p).symm z)) (chartGradientField g u p) y
    (hρ.differentiableAt (by simp)) ((contDiffAt_inChart hf p hy).differentiableAt (by simp))
    (fun i => ((chartGradientField_smooth hu g p i).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)) hρp.ne']
  rw [weightedLaplacian_expansion
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    coordinateGradientPair_inChart hf hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  rfl

lemma scalarCorrectionB_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionB g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionB (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionB scalarCorrectionB
  rw [scalarCorrectionRatio_inChart hu g n Λ p hy]
  rfl

lemma scalarCorrectionS_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionS g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionS (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  have he : (fun z => intrinsicCorrectionF g n Λ u ((chartAt E p).symm z)) =ᶠ[𝓝 y]
      scalarCorrectionRatio (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
    exact scalarCorrectionRatio_inChart hu g n Λ p hz
  have hed := coordinateDivergence_eventuallyEq (Module.finBasis ℝ E)
    (Filter.EventuallyEq.refl (𝓝 y) (fun z => Real.sqrt (metricCoefficients g p z).det))
    (fun i => he.mul (Filter.EventuallyEq.refl _ (chartGradientField g u p i)))
  unfold intrinsicCorrectionS scalarCorrectionS
  rw [weightedLaplacian_chartGradient (contMDiff_intrinsicCorrectionF hu g n Λ hD) hu g p hy]
  erw [hed.eq_of_nhds]
  rw [scalarCorrectionRatio_inChart hu g n Λ p hy]
  rfl

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma intrinsicCorrectionD_lower (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    {n W : ℝ} {B : ℕ} (hn : 0 < n) (hW : 0 < W)
    (hjet : W/n^B ≤ |u x| + Real.sqrt (coordinateGradientPair g u u x)/n) :
    n^2*W^2/(2*n^(2*B)) ≤ intrinsicCorrectionD g n u x :=
  scalar_denominator_lower hn hW (coordinateGradientPair_nonneg g u x) hjet

lemma intrinsicCorrectionD_pos (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    {n W : ℝ} {B : ℕ} (hn : 0 < n) (hW : 0 < W)
    (hjet : W/n^B ≤ |u x| + Real.sqrt (coordinateGradientPair g u u x)/n) :
    0 < intrinsicCorrectionD g n u x :=
  (by positivity : 0 < n^2*W^2/(2*n^(2*B))).trans_le
    (intrinsicCorrectionD_lower g u x hn hW hjet)

lemma compact_derivative_bound_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact hK hO hKO hf
  obtain ⟨C,hC,hFC⟩ := compact_derivative_bound hK hF N
  refine ⟨C,hC,fun j hj x hx => ?_⟩
  have hex := he.filter_mono (nhds_le_nhdsSet hx)
  rw [(hex.iteratedFDeriv ℝ j).self_of_nhds]
  exact hFC j hj x hx

lemma geometric_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hx hg
  have hb := geometric_product_jet_bound hf' hg' x h hF hG hR hS
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  change ‖iteratedFDeriv ℝ h (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hb

lemma norm_iteratedFDeriv_scalar_direction_on {O : Set E} (hO : IsOpen O)
    {x : E} (hx : x ∈ O) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (v : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) f x‖ := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hx hf
  have hd : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y v) :=
    (he.fderiv (𝕜:=ℝ)).mono (fun y hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy)
  rw [(hd.iteratedFDeriv ℝ k).self_of_nhds, (he.iteratedFDeriv ℝ (k+1)).self_of_nhds]
  exact norm_iteratedFDeriv_scalar_direction hF v k x

lemma chartGradientField_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^(k+4)*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^(k+5)*W := by
  let U := u ∘ (chartAt E p).symm
  have hU : ContDiffOn ℝ ∞ U (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hdi (j : CoordIndex E) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  intro i k hk
  have hprod (j : CoordIndex E) :
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j *
        fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
      (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by
    have hder (l : ℕ) (hl : l ≤ k) :
        ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
          ‖Module.finBasis ℝ E j‖*C*n^5*W*n^l := by
      calc
        _ ≤ ‖Module.finBasis ℝ E j‖*‖iteratedFDeriv ℝ (l+1) U y‖ :=
          norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
        _ ≤ ‖Module.finBasis ℝ E j‖*(C*n^((l+1)+4)*W) :=
          mul_le_mul_of_nonneg_left (huj (l+1) (by omega)) (norm_nonneg _)
        _ = _ := by rw [show l+1+4=5+l by omega,pow_add]; ring
    apply (geometric_product_jet_bound_on (chartAt E p).open_target hy
      (contDiffOn_metricInverse g p i j) (hdi j) k hA
      (show 0 ≤ ‖Module.finBasis ℝ E j‖*C*n^5*W by positivity) hn0 hn0
      (fun l hl => (haj i j l (hl.trans hk)).trans (by
        exact le_mul_of_one_le_right hA (one_le_pow₀ hn))) hder).trans
    rw [show n+n=2*n by ring,mul_pow]
    calc
      A*(‖Module.finBasis ℝ E j‖*C*n^5*W)*(2^k*n^k) =
          (2^k*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by rw [pow_add]; ring
      _ ≤ _ := by gcongr; norm_num
  unfold chartGradientField coordinateFlux
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    (((contDiffOn_metricInverse g p i j).mul (hdi j)).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W :=
      Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul]

lemma compact_metric_scalar_coefficient_bounds (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      (∀ i j, ∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A) ∧
      (∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => Real.sqrt (metricCoefficients g p z).det) y‖ ≤ A) ∧
      (∀ k ≤ h, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (Real.sqrt (metricCoefficients g p z).det)⁻¹) y‖ ≤ A) := by
  classical
  choose a ha haj using fun i j => compact_derivative_bound_on hK
    (chartAt E p).open_target hKt (contDiffOn_metricInverse g p i j) (h+1)
  obtain ⟨b,hb,hbj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    (contDiffOn_metricDensity g p) (h+1)
  obtain ⟨c,hc,hcj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    ((contDiffOn_metricDensity g p).inv (fun z hz =>
      (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hz)).ne')) h
  let A := 1+b+c+∑ i, ∑ j, a i j
  have ha0 (i j : CoordIndex E) : 0 ≤ a i j := zero_le_one.trans (ha i j)
  have hs0 : 0 ≤ ∑ i, ∑ j, a i j := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => ha0 i j))
  refine ⟨A,by dsimp only [A]; linarith,?_,?_,?_⟩
  · intro i j k hk y hy
    apply (haj i j k hk y hy).trans
    have hai : a i j ≤ ∑ j, a i j :=
      Finset.single_le_sum (fun j _ => ha0 i j) (Finset.mem_univ j)
    have haj' : (∑ j, a i j) ≤ ∑ i, ∑ j, a i j :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => ha0 i j)) (Finset.mem_univ i)
    dsimp only [A]
    linarith
  · intro k hk y hy
    exact (hbj k hk y hy).trans (by dsimp only [A]; linarith)
  · intro k hk y hy
    exact (hcj k hk y hy).trans (by dsimp only [A]; linarith)

theorem quantitative_intrinsic_correction_on_compact_chart
    (g : SmoothMetric E M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target)
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ L > 0, ∀ n : ℝ, 1 ≤ n → ∀ D : ℕ, ∀ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u → ∀ W : M → ℝ,
      (∀ x, 0 < W x) →
      (∀ x, W x/n^B ≤ |u x|+Real.sqrt (coordinateGradientPair g u u x)/n) →
      (∀ y ∈ K, ∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) y‖ ≤
        C*n^(j+4)*W ((chartAt E p).symm y)) →
      (∀ y ∈ K, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
        ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E p).symm) y‖ ≤
        C*n^4/(n^D)*W ((chartAt E p).symm y)) →
      ∀ y ∈ K, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j
          ((fun x => intrinsicCorrectionB g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) y‖+
        ‖iteratedFDeriv ℝ j
          ((fun x => intrinsicCorrectionS g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) y‖ ≤
        L*n^((2*B+21)*(h+2)+10)/(n^D) := by
  obtain ⟨A,hA,haj,hρj,hρij⟩ := compact_metric_scalar_coefficient_bounds g p hK hKt h
  let CX : ℝ := 2^(h+1)*A*C*(∑ j, ‖Module.finBasis ℝ E j‖)
  have hCX : 0 ≤ CX := by dsimp only [CX]; positivity
  let C' := C+A+CX+1
  have hC' : 0 < C' := by dsimp only [C']; linarith
  have hCC : C ≤ C' := by dsimp only [C']; linarith
  have hAC : A ≤ C' := by dsimp only [C']; linarith
  have hXC : CX ≤ C' := by dsimp only [C']; linarith
  obtain ⟨L,hL,hLj⟩ := quantitative_scalar_correction_jets_on (Module.finBasis ℝ E)
    (fun z => Real.sqrt (metricCoefficients g p z).det) (chartAt E p).open_target
    (contDiffOn_metricDensity g p) (fun z hz => Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hz)) h B hC'
  refine ⟨L,hL,?_⟩
  intro n hn D u hu W hW hnc huj hRj y hy j hj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hWy : 0 ≤ W ((chartAt E p).symm y) := (hW _).le
  have hD (x : M) : intrinsicCorrectionD g n u x ≠ 0 :=
    (intrinsicCorrectionD_pos g u x hn0 (hW x) (hnc x)).ne'
  have hU : ContDiffOn ℝ ∞ (u ∘ (chartAt E p).symm) (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hb := hLj n hn D (u ∘ (chartAt E p).symm) (chartGradientField g u p) hU
    (chartGradientField_smooth hu g p)
    (fun z hz => (scalarCorrectionDenominator_inChart hu g n p hz) ▸ hD ((chartAt E p).symm z))
    y (hKt hy) (W ((chartAt E p).symm y)) (hW _) ?_ ?_ ?_ ?_
    (fun k hk => (hρj k hk y hy).trans hAC) (fun k hk => (hρij k hk y hy).trans hAC) j hj
  · have heB : ((fun x => intrinsicCorrectionB g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) =ᶠ[𝓝 y]
        (fun z => scalarCorrectionB (Module.finBasis ℝ E)
          (fun z => Real.sqrt (metricCoefficients g p z).det) n (n*(n+2))
          (u ∘ (chartAt E p).symm) (chartGradientField g u p) z-1) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      exact congrArg (fun t : ℝ => t-1) (scalarCorrectionB_inChart hu g n (n*(n+2)) p hz)
    have heS : ((fun x => intrinsicCorrectionS g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) =ᶠ[𝓝 y]
        (fun z => scalarCorrectionS (Module.finBasis ℝ E)
          (fun z => Real.sqrt (metricCoefficients g p z).det) n (n*(n+2))
          (u ∘ (chartAt E p).symm) (chartGradientField g u p) z-1) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      exact congrArg (fun t : ℝ => t-1) (scalarCorrectionS_inChart hu g n (n*(n+2)) hD p hz)
    rw [(heB.iteratedFDeriv ℝ j).self_of_nhds,(heS.iteratedFDeriv ℝ j).self_of_nhds]
    exact hb
  · rw [← scalarCorrectionDenominator_inChart hu g n p (hKt hy)]
    apply le_trans ?_ (intrinsicCorrectionD_lower g u ((chartAt E p).symm y) hn0 (hW _) (hnc _))
    calc
      _ = 1*(W ((chartAt E p).symm y))^2/(2*n^(2*B)) := by ring
      _ ≤ _ := by gcongr; exact one_le_pow₀ hn
  · intro k hk
    exact (huj y hy k hk).trans (by gcongr)
  · intro i k hk
    exact (chartGradientField_jet_bound hu g p (hKt hy) (h+1) hn (hW _) hC.le
      (zero_le_one.trans hA) (fun i j k hk => haj i j k hk y hy)
      (fun k hk => huj y hy k (by omega)) i k hk).trans (by change CX*_ * _ ≤ _; gcongr)
  · intro k hk
    have he : (fun z => coordinateDivergence (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) (chartGradientField g u p) z+
        n*(n+2)*(u ∘ (chartAt E p).symm) z) =ᶠ[𝓝 y]
        ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E p).symm) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      dsimp only [Function.comp_apply]
      rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hz), (chartAt E p).right_inv hz]
      rfl
    rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
    exact (hRj y hy k hk).trans (by gcongr)


end

section
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
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem quantitative_intrinsic_correction_jets
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ L > 0, ∀ n : ℝ, 1 ≤ n → ∀ D : ℕ, ∀ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u → ∀ W : M → ℝ,
      (∀ x, 0 < W x) →
      (∀ x, W x/n^B ≤ |u x|+Real.sqrt (coordinateGradientPair g u u x)/n) →
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (u ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*n^(j+4)*W ((chartAt E (A.p i)).symm y)) →
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*n^4/(n^D)*W ((chartAt E (A.p i)).symm y)) →
      A.ChartJetBound h (fun x => ((intrinsicCorrectionB g n (n*(n+2)) u x-1 : ℝ) : ℂ))
        (L*n^((2*B+21)*(h+2)+10)/(n^D)) ∧
      A.ChartJetBound h (fun x => ((intrinsicCorrectionS g n (n*(n+2)) u x-1 : ℝ) : ℂ))
        (L*n^((2*B+21)*(h+2)+10)/(n^D)) ∧
      (∀ x, |intrinsicCorrectionB g n (n*(n+2)) u x-1|+
        |intrinsicCorrectionS g n (n*(n+2)) u x-1| ≤
        L*n^((2*B+21)*(h+2)+10)/(n^D)) := by
  classical
  choose L hL hLjet using fun i : A.t =>
    quantitative_intrinsic_correction_on_compact_chart g (A.p i)
      (A.scalarChartSupport_compact i) (A.scalarChartSupport_target i) h B hC
  choose T hT hTjet using fun i : A.t =>
    localized_real_chart_jet_bound (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
      (A.chart_η i) (A.smooth_η i) h
  let L₀ : ℝ := 1+∑ i : A.t, (T i+1)*L i
  have hL₀ : 0 < L₀ := by
    have hsum : 0 ≤ ∑ i : A.t, (T i+1)*L i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by linarith [hT i]) (hL i).le)
    dsimp only [L₀]
    linarith
  have hiL' (i : A.t) : (T i+1)*L i ≤ L₀ := by
    apply (Finset.single_le_sum (fun j _ => mul_nonneg (by linarith [hT j]) (hL j).le)
      (Finset.mem_univ i)).trans
    dsimp only [L₀]
    linarith
  have hiL (i : A.t) : T i*L i ≤ L₀ := (by nlinarith [hL i] : T i*L i ≤ (T i+1)*L i).trans (hiL' i)
  have hiLraw (i : A.t) : L i ≤ L₀ := (by nlinarith [hT i,hL i] : L i ≤ (T i+1)*L i).trans (hiL' i)
  refine ⟨L₀,hL₀,?_⟩
  intro n hn D u hu W hW hnc huj hRj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hD (x : M) : intrinsicCorrectionD g n u x ≠ 0 :=
    (intrinsicCorrectionD_pos g u x hn0 (hW x) (hnc x)).ne'
  obtain ⟨hb,hsmooth,heq⟩ := intrinsic_scalar_correction hu g n (n*(n+2))
    (by positivity) hD
  have hraw := fun i => hLjet i n hn D u hu W hW hnc (huj i) (hRj i)
  have hloc (i : A.t) (f : M → ℝ)
      (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
      (hjf : ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (f ∘ (chartAt E (A.p i)).symm) y‖ ≤
          L i*n^((2*B+21)*(h+2)+10)/n^D) :
      ∀ j ≤ h, ∀ y : E,
        ‖iteratedFDeriv ℝ j (chartLocalize (E:=E) (A.p i) (A.η i) (fun x => (f x : ℂ))) y‖ ≤
          L₀*n^((2*B+21)*(h+2)+10)/n^D := by
    intro j hj y
    apply (hTjet i f hf _ (div_nonneg (mul_nonneg (hL i).le (pow_nonneg hn0.le _))
      (pow_nonneg hn0.le _)) hjf y j hj).trans
    calc
      T i*(L i*n^((2*B+21)*(h+2)+10)/n^D) =
        (T i*L i)*n^((2*B+21)*(h+2)+10)/n^D := by ring
      _ ≤ _ := by gcongr; exact hiL i
  refine ⟨?_,?_,?_⟩
  · intro i j hj y
    exact hloc i _ (hb.sub contMDiff_const)
      (fun z hz l hl => (le_add_of_nonneg_right (norm_nonneg _)).trans (hraw i z hz l hl)) j hj y
  · intro i j hj y
    exact hloc i _ (hsmooth.sub contMDiff_const)
      (fun z hz l hl => (le_add_of_nonneg_left (norm_nonneg _)).trans (hraw i z hz l hl)) j hj y
  · intro x
    have hi : ∃ i : A.t, A.η i x ≠ 0 := by
      by_contra hno
      push Not at hno
      have hz : (∑ i : A.t, A.η i x)=0 := Finset.sum_eq_zero (fun i _ => hno i)
      rw [A.sum_η x] at hz
      exact one_ne_zero hz
    obtain ⟨i,hi⟩ := hi
    have hxη : x ∈ tsupport (A.η i) := subset_tsupport _ hi
    have hxs : x ∈ (chartAt E (A.p i)).source := A.chart_η i hxη
    have hbnd := hraw i ((chartAt E (A.p i)) x) ⟨x,hxη,rfl⟩ 0 (Nat.zero_le h)
    simp only [norm_iteratedFDeriv_zero,Function.comp_apply,
      (chartAt E (A.p i)).left_inv hxs,Real.norm_eq_abs] at hbnd
    exact hbnd.trans (by gcongr; exact hiLraw i)
end CompactMetricAtlas

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
open scoped Topology ContDiff Manifold Matrix


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
open Filter
open scoped Topology

lemma inverseFrequency_zero : Tendsto inverseFrequency atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma inverseFrequency_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => inverseFrequency n ^ m) atTop (𝓝 0) := by
  simpa only [zero_pow hm] using inverseFrequency_zero.pow m

end


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_equation (k : ℕ) :
    productWaveFrequency k*(productWaveFrequency k+2)=productFrequency k := by
  have h := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  unfold productWaveFrequency
  nlinarith
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
lemma productWaveFrequency_tendsto : Tendsto productWaveFrequency atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) _ _)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  exact (productWaveFrequency_bounds hk).1
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_EventualProductScalarCorrectionRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma tsupport_intrinsicCorrectionF (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) :
    tsupport (intrinsicCorrectionF g n Λ u) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) := by
  apply closure_mono
  intro x hx hzero
  apply hx
  simp only [intrinsicCorrectionF,hzero,zero_div]

lemma intrinsic_corrections_eq_one_off_residual
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) {x : M}
    (hx : x ∉ tsupport (fun x => laplaceBeltrami g u x+Λ*u x)) :
    intrinsicCorrectionB g n Λ u x=1 ∧ intrinsicCorrectionS g n Λ u x=1 := by
  have hxF : x ∉ tsupport (intrinsicCorrectionF g n Λ u) :=
    fun h => hx (tsupport_intrinsicCorrectionF g n Λ u h)
  have hF := image_eq_zero_of_notMem_tsupport hxF
  have hgrad := coordinateGradientPair_zero_off_support g (intrinsicCorrectionF g n Λ u) u hxF
  have hf := contMDiff_intrinsicCorrectionF hu g n Λ hD
  have hw := weightedLaplacian_expansion
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) g x
  simp only [hF,hgrad,zero_mul,zero_add] at hw
  simp only [intrinsicCorrectionB,intrinsicCorrectionS,hF,hw,zero_mul,mul_zero,
    sub_zero,and_self]

lemma tsupport_intrinsic_corrections_sub_one
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    tsupport (fun x => intrinsicCorrectionB g n Λ u x-1) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) ∧
    tsupport (fun x => intrinsicCorrectionS g n Λ u x-1) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) := by
  constructor <;> apply closure_minimal _ isClosed_closure <;> intro x hx <;> by_contra hn
  · exact hx (sub_eq_zero.mpr (intrinsic_corrections_eq_one_off_residual hu g n Λ hD hn).1)
  · exact hx (sub_eq_zero.mpr (intrinsic_corrections_eq_one_off_residual hu g n Λ hD hn).2)

end

open Set Filter Function Manifold
open scoped Topology ContDiff
lemma eventual_product_scalar_correction_rate (L : ℝ) (P Q D : ℕ)
    (hD : P+Q+2 ≤ D) :
    ∀ᶠ n : ℕ in atTop, L*productWaveFrequency n^Q/productWaveFrequency n^D ≤  inverseFrequency n^P := by
  have hb := productWaveFrequency_tendsto.eventually (eventually_ge_atTop (max 1 L))
  filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hν1 : 1 ≤ productWaveFrequency n := (le_max_left _ _).trans hn
  have hν0 : 0<productWaveFrequency n := zero_lt_one.trans_le hν1
  have hLν : L ≤ productWaveFrequency n := (le_max_right _ _).trans hn
  have hratio : L*productWaveFrequency n^Q/productWaveFrequency n^D ≤ (productWaveFrequency n)⁻¹^P := by
    rw [inv_pow,←one_div,div_le_div_iff₀ (pow_pos hν0 D) (pow_pos hν0 P),one_mul]
    calc
      _ = L*productWaveFrequency n^(P+Q) := by rw [pow_add]; ring
      _  ≤  productWaveFrequency n*productWaveFrequency n^(P+Q) :=
        mul_le_mul_of_nonneg_right hLν (pow_nonneg hν0.le _)
      _ = productWaveFrequency n^(P+Q+1) := by rw [pow_succ]; ring
      _  ≤  _ := pow_le_pow_right₀ hν1 (by omega)
  exact hratio.trans (pow_le_pow_left₀ (inv_nonneg.mpr hν0.le)
    (inv_anti₀ (by exact_mod_cast (show 0<n by omega)) (productWaveFrequency_bounds hn1).1) P)
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E<2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)
omit [T2Space M] in
theorem eventually_product_scalar_exactification_oai
    (h B P D : ℕ) (hP : 0 < P) (hD : P+((2*B+21)*(h+2)+10)+2  ≤  D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(productWaveFrequency n)^B  ≤  |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(productWaveFrequency n)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j  ≤  h+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖  ≤
          C*(productWaveFrequency n)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j  ≤  h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖  ≤
          C*(productWaveFrequency n)^4/(productWaveFrequency n)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n)
      let s := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+productFrequency n*s x*U n x=0) ∧
      A.ChartJetBound h (fun x => ((b x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      A.ChartJetBound h (fun x => ((s x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      (∀ x, |b x-1|+|s x-1|  ≤  inverseFrequency n^P) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) := by
  obtain ⟨L,hL,hbound⟩ := A.quantitative_intrinsic_correction_jets h B hC
  have hrate := eventual_product_scalar_correction_rate L P ((2*B+21)*(h+2)+10) D hD
  have hsmall := (inverseFrequency_pow_zero P (Nat.ne_of_gt hP)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdata,hrate,hsmall,eventually_ge_atTop 1] with n hn hr hsmall hn1
  have hn1' : 1  ≤  productWaveFrequency n :=
    (show (1:ℝ) ≤ n by exact_mod_cast hn1).trans (productWaveFrequency_bounds hn1).1
  have hn0 : 0 < (productWaveFrequency n) := zero_lt_one.trans_le hn1'
  have hΛ : productFrequency n ≠ 0 := by unfold productFrequency; positivity
  have hden (x : M) : intrinsicCorrectionD g (productWaveFrequency n) (U n) x ≠ 0 :=
    (intrinsicCorrectionD_pos g (U n) x hn0 (hW n x) (hn.1 x)).ne'
  obtain ⟨hb,hsmooth,heq⟩ := intrinsic_scalar_correction (hU n) g (productWaveFrequency n)
    (productFrequency n) hΛ hden
  have hrj := hn.2.2
  rw [←productWaveFrequency_equation n] at hrj
  have hbounds := hbound (productWaveFrequency n) hn1' D (U n) (hU n) (W n) (hW n)
    hn.1 hn.2.1 hrj
  rw [productWaveFrequency_equation] at hbounds
  obtain ⟨hbj,hsj,habs⟩ := hbounds
  have hsupp := tsupport_intrinsic_corrections_sub_one (hU n) g (productWaveFrequency n)
    (productFrequency n) hden
  refine ⟨hb,hsmooth,?_,heq,
    fun chart order horder point => (hbj chart order horder point).trans hr,
    fun chart order horder point => (hsj chart order horder point).trans hr,?_,hsupp⟩
  · intro x
    have hx := (habs x).trans hr
    have hbx : |intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_right h).trans_lt (hx.trans_lt hsmall)
    have hsx : |intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_left h).trans_lt (hx.trans_lt hsmall)
    constructor <;> linarith [(abs_lt.mp hbx).1,(abs_lt.mp hsx).1]
  · intro x
    exact (habs x).trans hr

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification_oai.{u_1, u_2}
