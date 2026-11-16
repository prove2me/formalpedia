-- Prove2me | solution 1 for WildeQIT.Recover.theorem_12_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T00:30:53.996248+00:00
-- url     : https://prove2.me/submissions/68a7e863-91c2-4db7-818f-5468a62b128e

import Theorems.Thm_Complex_JensenFatou_lintegral_circle_limit_neglog_le
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.IsLUB
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanDensities
import Mathlib.Analysis.Complex.ReImTopology

noncomputable section
open Set Filter Metric MeasureTheory Real MeromorphicOn
open scoped Topology ENNReal NNReal
set_option autoImplicit false
namespace HirschmanDisk

/-- Nonnegative extended negative logarithm, with the essential value `+∞` at zero. -/
def negLog (z : ℂ) : ℝ≥0∞ := (- ENNReal.log (ENNReal.ofReal ‖z‖)).toENNReal

lemma negLog_zero : negLog 0 = ⊤ := by simp [negLog]

lemma negLog_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    negLog z = ENNReal.ofReal (-Real.log ‖z‖) := by
  rw [negLog,ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz),← EReal.coe_neg,
    EReal.real_coe_toENNReal]

lemma continuous_negLog : Continuous negLog := by
  exact EReal.continuous_toENNReal.comp
    (ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp continuous_norm)).neg

lemma lintegral_negLog_boundary_le {f : ℂ → ℂ} {g : ℝ → ℂ} {r : ℕ → ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hc : f 0 ≠ 0)
    (hr : ∀ n, 0 < r n ∧ r n < 1)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioc 0 (2*Real.pi)),
      Tendsto (fun n => f (circleMap 0 (r n) t)) atTop (𝓝 (g t))) :
    (∫⁻ t in Ioc 0 (2*Real.pi), negLog (g t)) ≤
      ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f 0‖)) := by
  simpa only [negLog] using Complex.JensenFatou.lintegral_circle_limit_neglog_le hf hc hr hb hlim
end HirschmanDisk

noncomputable section
open Set Filter Metric MeasureTheory Real Complex
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
namespace HirschmanConformal

def cayley (c s : ℝ) (w : ℂ) : ℂ := (c : ℂ) + (s : ℂ)*I*((1+w)/(1-w))
def stripMap (c s : ℝ) (w : ℂ) : ℂ := -I*Complex.log (cayley c s w)/(Real.pi : ℂ)

lemma cayley_im (c s : ℝ) (w : ℂ) :
    (cayley c s w).im = s*(1-Complex.normSq w)/Complex.normSq (1-w) := by
  simp only [cayley,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_mul,add_zero,
    Complex.div_re,Complex.add_re,Complex.one_re,Complex.sub_re,Complex.sub_im,
    Complex.one_im,Complex.normSq_apply]
  ring

lemma one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1-w ≠ 0 := by
  intro h
  have hh : w=1 := (sub_eq_zero.mp h).symm
  simpa [hh] using hw

lemma cayley_im_pos (c : ℝ) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayley c s w).im := by
  rw [cayley_im]
  apply div_pos
  · apply mul_pos hs
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero hw)

lemma cayley_differentiableAt (c s : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableAt ℂ (cayley c s) w := by
  unfold cayley
  exact (differentiableAt_const (c : ℂ)).add ((differentiableAt_const ((s : ℂ)*I)).mul
    (((differentiableAt_const (1 : ℂ)).add differentiableAt_id).div
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) (one_sub_ne_zero hw)))

lemma cayley_continuousAt (c s : ℝ) {w : ℂ} (hw : w ≠ 1) :
    ContinuousAt (cayley c s) w := by
  unfold cayley
  exact continuousAt_const.add (continuousAt_const.mul
    ((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr (Ne.symm hw))))

lemma cayley_boundary_im (c s : ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    (cayley c s w).im=0 := by
  rw [cayley_im,Complex.normSq_eq_norm_sq,hw]
  simp

/-- At a nonexceptional boundary point, the logarithm is continuous from the upper side. -/
lemma stripMap_tendsto_boundary {α : Type*} {l : Filter α} {v : α → ℂ}
    (c : ℝ) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 1)
    (hi : (cayley c s w).im=0) (hz : cayley c s w ≠ 0)
    (hv : Tendsto v l (𝓝 w)) (hvin : ∀ᶠ n in l, ‖v n‖ < 1) :
    Tendsto (fun n => stripMap c s (v n)) l (𝓝 (stripMap c s w)) := by
  have hcv : Tendsto (fun n => cayley c s (v n)) l (𝓝 (cayley c s w)) :=
    (cayley_continuousAt c s hw).tendsto.comp hv
  have hl : Tendsto (fun n => Complex.log (cayley c s (v n))) l
      (𝓝 (Complex.log (cayley c s w))) := by
    by_cases hre : (cayley c s w).re < 0
    · apply (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hi).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hcv,hvin.mono fun n hn => (cayley_im_pos c hs hn).le⟩
    · have hpos : 0 < (cayley c s w).re := by
        have hne : (cayley c s w).re ≠ 0 := by
          intro h
          exact hz (Complex.ext h hi)
        exact lt_of_le_of_ne (le_of_not_gt hre) (Ne.symm hne)
      exact (Complex.differentiableAt_log (Or.inl hpos)).continuousAt.tendsto.comp hcv
  simpa only [stripMap] using (tendsto_const_nhds.mul hl).div_const (Real.pi : ℂ)

lemma stripMap_re (c s : ℝ) (w : ℂ) :
    (stripMap c s w).re = Complex.arg (cayley c s w)/Real.pi := by
  unfold stripMap
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  simp [Complex.mul_re,div_eq_mul_inv,Complex.log_im]

lemma stripMap_mem_strip (c : ℝ) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (stripMap c s w).re ∧ (stripMap c s w).re < 1 := by
  rw [stripMap_re]
  have hi := cayley_im_pos c hs hw
  have harg0 : 0 < Complex.arg (cayley c s w) := by
    have ha := Complex.arg_nonneg_iff.mpr hi.le
    have hn : Complex.arg (cayley c s w) ≠ 0 := by
      intro h
      exact hi.ne' (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne ha (Ne.symm hn)
  have harg1 : Complex.arg (cayley c s w) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
  exact ⟨div_pos harg0 Real.pi_pos,(div_lt_one Real.pi_pos).mpr harg1⟩

lemma stripMap_differentiableOn (c : ℝ) {s : ℝ} (hs : 0 < s) :
    DifferentiableOn ℂ (stripMap c s) (ball 0 1) := by
  intro w hw
  have hn : ‖w‖ < 1 := by simpa [mem_ball,dist_eq_norm] using hw
  have hcut : cayley c s w ∈ Complex.slitPlane := by
    exact Or.inr (cayley_im_pos c hs hn).ne'
  exact (((differentiableAt_const (-I)).mul
    ((Complex.differentiableAt_log hcut).comp w (cayley_differentiableAt c s hn))).div_const _).differentiableWithinAt

lemma cayley_zero (c s : ℝ) : cayley c s 0 = (c : ℂ)+(s : ℂ)*I := by simp [cayley]

lemma stripMap_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    stripMap (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) 0 = (θ : ℂ) := by
  have hθpi0 : -(Real.pi) < Real.pi*θ := by nlinarith [Real.pi_pos]
  have hθpi1 : Real.pi*θ ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hexp : (Real.cos (Real.pi*θ) : ℂ)+(Real.sin (Real.pi*θ) : ℂ)*I =
      Complex.exp ((Real.pi*θ : ℝ)*I) := by rw [Complex.exp_mul_I]; simp
  rw [stripMap,cayley_zero,hexp,Complex.log_exp]
  · field_simp
    simp [Complex.I_sq,Complex.ofReal_mul]
  · simpa using hθpi0
  · simpa using hθpi1

end HirschmanConformal

noncomputable section
open Set Filter Metric MeasureTheory Real Complex HirschmanConformal
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HirschmanBoundary

def angle (c s y : ℝ) : ℝ := Real.pi+2*Real.arctan ((y-c)/s)
def cauchyWeight (c s y : ℝ) : ℝ := 2*s/((y-c)^2+s^2)

lemma angle_mem (c s y : ℝ) : angle c s y ∈ Ioo 0 (2*Real.pi) := by
  have h0 := Real.neg_pi_div_two_lt_arctan ((y-c)/s)
  have h1 := Real.arctan_lt_pi_div_two ((y-c)/s)
  dsimp [angle]
  constructor <;> linarith

lemma angle_strictMono (c : ℝ) {s : ℝ} (hs : 0 < s) : StrictMono (angle c s) := by
  intro x y hxy
  have ha := Real.arctan_strictMono ((div_lt_div_iff_of_pos_right hs).mpr (sub_lt_sub_right hxy c))
  dsimp [angle]
  linarith

lemma angle_image (c : ℝ) {s : ℝ} (hs : 0 < s) :
    angle c s '' univ = Ioo 0 (2*Real.pi) := by
  apply subset_antisymm
  · rintro y ⟨x,_,rfl⟩
    exact angle_mem c s x
  · intro x hx
    refine ⟨c+s*Real.tan ((x-Real.pi)/2),mem_univ _,?_⟩
    unfold angle
    have he : (c+s*Real.tan ((x-Real.pi)/2)-c)/s = Real.tan ((x-Real.pi)/2) := by field_simp [hs.ne']; ring
    rw [he,Real.arctan_tan (by linarith [hx.1]) (by linarith [hx.2])]
    ring

lemma angle_hasDerivAt (c : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    HasDerivAt (angle c s) (cauchyWeight c s y) y := by
  have hd := (((Real.hasDerivAt_arctan ((y-c)/s)).comp y
    (((hasDerivAt_id y).sub_const c).div_const s)).const_mul 2).const_add Real.pi
  have he : 2 * (1 / (1 + ((y-c)/s)^2) * (1/s)) = cauchyWeight c s y := by
    unfold cauchyWeight
    field_simp [hs.ne']
    ring
  rw [he] at hd
  exact hd

lemma lintegral_angle (c : ℝ) {s : ℝ} (hs : 0 < s) (g : ℝ → ℝ≥0∞) :
    (∫⁻ φ in Ioo 0 (2*Real.pi), g φ) =
      ∫⁻ y, ENNReal.ofReal (cauchyWeight c s y)*g (angle c s y) := by
  rw [← angle_image c hs]
  have hp (y : ℝ) : 0 < cauchyWeight c s y := by unfold cauchyWeight; positivity
  simpa only [Measure.restrict_univ,abs_of_pos (hp _)] using
    lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun y _ => (angle_hasDerivAt c hs y).hasDerivWithinAt)
      (angle_strictMono c hs).injective.injOn g

lemma circleMap_angle (x : ℝ) :
    circleMap 0 1 (Real.pi+2*Real.arctan x) =
      ((x : ℂ)-I)/((x : ℂ)+I) := by
  have hn : (x : ℂ)+I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [circleMap]
  simp only [Complex.ofReal_one,one_mul,zero_add,Complex.exp_ofReal_mul_I,
    Real.cos_add,Real.sin_add,Real.cos_pi,Real.sin_pi,mul_zero,zero_mul,add_zero,zero_add,
    Real.cos_two_mul,Real.sin_two_mul,Real.cos_sq_arctan,Real.sin_arctan,Real.cos_arctan]
  have hpos : 0 < 1+x^2 := by positivity
  have hsqrt := Real.sq_sqrt hpos.le
  apply (eq_div_iff hn).mpr
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,Complex.sub_im,
    Complex.I_re,Complex.I_im] <;> field_simp <;> nlinarith

lemma cayley_angle (c : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    cayley c s (circleMap 0 1 (angle c s y)) = (y : ℂ) := by
  rw [angle,circleMap_angle]
  have hden : (((y-c)/s : ℝ) : ℂ)+I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  unfold cayley
  have he : 1-((((y-c)/s : ℝ) : ℂ)-I)/((((y-c)/s : ℝ) : ℂ)+I) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := congrArg Complex.im ((eq_div_iff hden).mp h)
    norm_num at this
  have hr : (1+((((y-c)/s : ℝ) : ℂ)-I)/((((y-c)/s : ℝ) : ℂ)+I)) /
      (1-((((y-c)/s : ℝ) : ℂ)-I)/((((y-c)/s : ℝ) : ℂ)+I)) = -(((y-c)/s : ℝ) : ℂ)*I := by
    field_simp [hden,he]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hr]
  simp only [Complex.ofReal_div,Complex.ofReal_sub]
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
  simp [Complex.I_sq]

lemma circleMap_angle_ne_one (c : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    circleMap 0 1 (angle c s y) ≠ 1 := by
  rw [angle,circleMap_angle]
  intro h
  have hden : (((y-c)/s : ℝ) : ℂ)+I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have he := (div_eq_iff hden).mp h
  have := congrArg Complex.im he
  norm_num at this

end HirschmanBoundary

noncomputable section
open Set Filter Metric MeasureTheory Real Complex HirschmanConformal HirschmanBoundary
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HirschmanStrip

def boundaryLog (y : ℝ) : ℂ := -I*Complex.log (y : ℂ)/(Real.pi : ℂ)

lemma cauchy_boundary_bound (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hc : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (hb : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθ : f θ ≠ 0) :
    (∫⁻ y, ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) y)*
      HirschmanDisk.negLog (f (boundaryLog y))) ≤
        ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f θ‖)) := by
  let c := Real.cos (Real.pi*θ)
  let s := Real.sin (Real.pi*θ)
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])
  obtain ⟨r,_,hr,hlimr⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hmem (w : ℂ) (hw : ‖w‖ < 1) : stripMap c s w ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := by
    have hh := stripMap_mem_strip c hs hw
    exact ⟨hh.1.le,hh.2.le⟩
  have hF : DifferentiableOn ℂ (fun w => f (stripMap c s w)) (ball 0 1) :=
    hd.comp (stripMap_differentiableOn c hs) (fun w hw =>
      stripMap_mem_strip c hs (by simpa [mem_ball,dist_eq_norm] using hw))
  have hF0 : f (stripMap c s 0) ≠ 0 := by
    simpa only [c,s,stripMap_zero hθ0 hθ1] using hθ
  have hFb : ∀ w ∈ ball (0 : ℂ) 1, ‖f (stripMap c s w)‖ ≤ 1 := by
    intro w hw
    have hm := hmem w (by simpa [mem_ball,dist_eq_norm] using hw)
    exact hb _ hm.1 hm.2
  have hboundary : ∀ᵐ φ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      Tendsto (fun n => f (stripMap c s (circleMap 0 (r n) φ))) atTop
        (𝓝 (f (stripMap c s (circleMap 0 1 φ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc 0 (2*Real.pi))).ae_ne (2*Real.pi),
      (volume.restrict (Ioc 0 (2*Real.pi))).ae_ne (angle c s 0)] with φ hφ hφ1 hφ0
    have hφ' : φ ∈ Ioo 0 (2*Real.pi) := ⟨hφ.1,lt_of_le_of_ne hφ.2 hφ1⟩
    obtain ⟨y,_,rfl⟩ := (angle_image c hs).symm ▸ hφ'
    have hy : y ≠ 0 := by intro h; subst y; exact hφ0 rfl
    have hv : Tendsto (fun n => circleMap 0 (r n) (angle c s y)) atTop
        (𝓝 (circleMap 0 1 (angle c s y))) :=
      (show Continuous (fun r : ℝ => circleMap 0 r (angle c s y)) by fun_prop).continuousAt.tendsto.comp hlimr
    have hvin : ∀ᶠ n : ℕ in atTop, ‖circleMap 0 (r n) (angle c s y)‖ < 1 :=
      Eventually.of_forall fun n => by simpa [abs_of_pos (hr n).1] using (hr n).2
    have hi : (cayley c s (circleMap 0 1 (angle c s y))).im=0 := by rw [cayley_angle c hs]; simp
    have hz : cayley c s (circleMap 0 1 (angle c s y)) ≠ 0 := by
      rw [cayley_angle c hs]
      exact Complex.ofReal_ne_zero.mpr hy
    have ht := stripMap_tendsto_boundary c hs (circleMap_angle_ne_one c hs y) hi hz hv hvin
    have hin : ∀ᶠ n : ℕ in atTop, stripMap c s (circleMap 0 (r n) (angle c s y)) ∈
        {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := hvin.mono fun n hn => hmem _ hn
    exact (hc.continuousWithinAt (hclosed.mem_of_tendsto ht hin)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht,hin⟩)
  have hh := HirschmanDisk.lintegral_negLog_boundary_le hF hF0 hr hFb hboundary
  rw [show stripMap c s 0 = (θ : ℂ) from stripMap_zero hθ0 hθ1] at hh
  rw [← restrict_Ioo_eq_restrict_Ioc] at hh
  rw [lintegral_angle c hs] at hh
  simpa only [stripMap,cayley_angle c hs,boundaryLog,c,s,stripMap_zero hθ0 hθ1] using hh

end HirschmanStrip

noncomputable section
open Set Filter Metric MeasureTheory Real Complex HirschmanConformal HirschmanBoundary HirschmanStrip
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HirschmanWeights

def leftWeight (θ t : ℝ) : ℝ := Real.sin (Real.pi*θ)/(2*(Real.cosh (Real.pi*t)-Real.cos (Real.pi*θ)))
def rightWeight (θ t : ℝ) : ℝ := Real.sin (Real.pi*θ)/(2*(Real.cosh (Real.pi*t)+Real.cos (Real.pi*θ)))
def expParam (t : ℝ) : ℝ := Real.exp (-Real.pi*t)

lemma expParam_pos (t : ℝ) : 0 < expParam t := Real.exp_pos _
lemma expParam_hasDerivAt (t : ℝ) : HasDerivAt expParam (-Real.pi*expParam t) t := by
  unfold expParam
  simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using
    (Real.hasDerivAt_exp (-Real.pi*t)).comp t ((hasDerivAt_id t).const_mul (-Real.pi))
lemma expParam_injective : Function.Injective expParam := by
  intro x y h
  have he := Real.exp_injective h
  nlinarith [Real.pi_pos]
lemma expParam_image : expParam '' univ = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t,_,rfl⟩
    exact expParam_pos t
  · intro hy
    refine ⟨-Real.log y/Real.pi,mem_univ _,?_⟩
    unfold expParam
    rw [show -Real.pi*(-Real.log y/Real.pi)=Real.log y by field_simp]
    exact Real.exp_log hy

lemma neg_expParam_image : (fun t => -expParam t) '' univ = Iio 0 := by
  ext y
  constructor
  · rintro ⟨t,_,rfl⟩
    exact neg_neg_of_pos (expParam_pos t)
  · intro hy
    have hh : -y ∈ expParam '' univ := by
      rw [expParam_image]
      change 0 < -y
      exact neg_pos.mpr hy
    obtain ⟨t,_,ht⟩ := hh
    exact ⟨t,mem_univ _,by simpa using congrArg Neg.neg ht⟩

lemma boundaryLog_expParam (t : ℝ) : boundaryLog (expParam t) = (t : ℂ)*I := by
  rw [boundaryLog,← Complex.ofReal_log (expParam_pos t).le]
  simp only [expParam,Real.log_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  field_simp

lemma boundaryLog_neg_expParam (t : ℝ) : boundaryLog (-expParam t) = 1+(t : ℂ)*I := by
  have hl : Complex.log ((-expParam t : ℝ) : ℂ) = ((-Real.pi*t : ℝ) : ℂ)+(Real.pi : ℂ)*I := by
    have he : ((-expParam t : ℝ) : ℂ) = (expParam t : ℂ)*(-1) := by simp
    rw [he,Complex.log_ofReal_mul (expParam_pos t) (neg_ne_zero.mpr one_ne_zero),Complex.log_neg_one]
    simp only [expParam,Real.log_exp]
  rw [boundaryLog,hl]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma denominator_exp (c s x : ℝ) (hcs : c^2+s^2=1) :
    (Real.exp x-c)^2+s^2 = 2*Real.exp x*(Real.cosh x-c) := by
  rw [Real.cosh_eq,Real.exp_neg]
  have he := mul_inv_cancel₀ (Real.exp_ne_zero x)
  nlinarith

lemma leftWeight_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) : 0 < leftWeight θ t := by
  have hs : 0 < Real.sin (Real.pi*θ) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcs := Real.cos_sq_add_sin_sq (Real.pi*θ)
  have hc : Real.cos (Real.pi*θ) < 1 := by nlinarith [Real.cos_le_one (Real.pi*θ)]
  unfold leftWeight
  exact div_pos hs (mul_pos (by norm_num) (sub_pos.mpr (hc.trans_le (Real.one_le_cosh _))))

lemma rightWeight_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) : 0 < rightWeight θ t := by
  have hs : 0 < Real.sin (Real.pi*θ) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcs := Real.cos_sq_add_sin_sq (Real.pi*θ)
  have hc : -1 < Real.cos (Real.pi*θ) := by nlinarith [Real.neg_one_le_cos (Real.pi*θ)]
  unfold rightWeight
  exact div_pos hs (mul_pos (by norm_num) (by linarith [Real.one_le_cosh (Real.pi*t)]))

lemma left_jacobian {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    Real.pi*expParam t*cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (expParam t) =
      (2*Real.pi)*leftWeight θ t := by
  have hd := denominator_exp (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (-Real.pi*t)
    (Real.cos_sq_add_sin_sq (Real.pi*θ))
  simp only [neg_mul,Real.cosh_neg] at hd
  unfold cauchyWeight leftWeight expParam
  simp only [neg_mul]
  rw [hd]
  have hden : Real.cosh (Real.pi*t)-Real.cos (Real.pi*θ) ≠ 0 := by
    intro he
    have hp := leftWeight_pos h0 h1 t
    simpa [leftWeight,he] using hp
  field_simp [Real.exp_ne_zero,hden] <;> ring

lemma right_jacobian {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ) :
    Real.pi*expParam t*cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (-expParam t) =
      (2*Real.pi)*rightWeight θ t := by
  have hd := denominator_exp (-Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (-Real.pi*t)
    (by simpa using Real.cos_sq_add_sin_sq (Real.pi*θ))
  simp only [neg_mul,Real.cosh_neg,sub_neg_eq_add] at hd
  unfold cauchyWeight rightWeight expParam
  rw [show (-Real.exp (-Real.pi*t)-Real.cos (Real.pi*θ))^2 =
    (Real.exp (-Real.pi*t)- -Real.cos (Real.pi*θ))^2 by ring]
  simp only [neg_mul,sub_neg_eq_add]
  rw [hd]
  have hden : Real.cosh (Real.pi*t)+Real.cos (Real.pi*θ) ≠ 0 := by
    intro he
    have hp := rightWeight_pos h0 h1 t
    simpa [rightWeight,he] using hp
  field_simp [Real.exp_ne_zero,hden] <;> ring

lemma left_weight_alpha {θ : ℝ} (h1 : θ < 1) (t : ℝ) : leftWeight θ t=(1-θ)*alphaDensity θ t := by
  unfold leftWeight alphaDensity
  field_simp [sub_ne_zero.mpr h1.ne']

lemma right_weight_beta {θ : ℝ} (h0 : 0 < θ) (t : ℝ) : rightWeight θ t=θ*betaDensity θ t := by
  unfold rightWeight betaDensity
  field_simp [h0.ne']

end HirschmanWeights

noncomputable section
open Set Filter Metric MeasureTheory Real Complex HirschmanBoundary HirschmanStrip HirschmanWeights
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HirschmanNormalized

lemma lintegral_split_zero (k : ℝ → ℝ≥0∞) :
    (∫⁻ y, k y) = (∫⁻ y in Ioi 0, k y)+(∫⁻ y in Iio 0, k y) := by
  have h := lintegral_add_compl (μ := volume) (A := Ioi (0 : ℝ)) k measurableSet_Ioi
  simpa only [compl_Ioi,← restrict_Iio_eq_restrict_Iic] using h.symm

lemma left_change {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (g : ℂ → ℝ≥0∞) :
    (∫⁻ y in Ioi 0, ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) y)*g (boundaryLog y)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ t, ENNReal.ofReal (leftWeight θ t)*g ((t : ℂ)*I) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun t _ => (expParam_hasDerivAt t).hasDerivWithinAt) expParam_injective.injOn
    (fun y => ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) y)*g (boundaryLog y))
  rw [expParam_image,Measure.restrict_univ] at h
  rw [h]
  have he (t : ℝ) :
      ENNReal.ofReal |-(Real.pi)*expParam t| *
        (ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (expParam t))*g (boundaryLog (expParam t))) =
      ENNReal.ofReal (2*Real.pi)*(ENNReal.ofReal (leftWeight θ t)*g ((t : ℂ)*I)) := by
    rw [abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos (expParam_pos t),boundaryLog_expParam,
      ← mul_assoc,← ENNReal.ofReal_mul (mul_pos Real.pi_pos (expParam_pos t)).le,left_jacobian h0 h1,
      ENNReal.ofReal_mul (by positivity),mul_assoc]
  simp_rw [he]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma right_change {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (g : ℂ → ℝ≥0∞) :
    (∫⁻ y in Iio 0, ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) y)*g (boundaryLog y)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ t, ENNReal.ofReal (rightWeight θ t)*g (1+(t : ℂ)*I) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun t _ => (expParam_hasDerivAt t).neg.hasDerivWithinAt)
    (show Function.Injective (fun t => -expParam t) from neg_injective.comp expParam_injective).injOn
    (fun y => ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) y)*g (boundaryLog y))
  rw [show (-expParam : ℝ → ℝ) = (fun t => -expParam t) from rfl,
    neg_expParam_image,Measure.restrict_univ] at h
  rw [h]
  have he (t : ℝ) :
      ENNReal.ofReal |-(-(Real.pi)*expParam t)| *
        (ENNReal.ofReal (cauchyWeight (Real.cos (Real.pi*θ)) (Real.sin (Real.pi*θ)) (-expParam t))*g (boundaryLog (-expParam t))) =
      ENNReal.ofReal (2*Real.pi)*(ENNReal.ofReal (rightWeight θ t)*g (1+(t : ℂ)*I)) := by
    rw [abs_neg,abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos (expParam_pos t),boundaryLog_neg_expParam,
      ← mul_assoc,← ENNReal.ofReal_mul (mul_pos Real.pi_pos (expParam_pos t)).le,right_jacobian h0 h1,
      ENNReal.ofReal_mul (by positivity),mul_assoc]
  simp_rw [he]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Hirschman's inequality for strip functions bounded by one, in nonnegative form. -/
theorem normalized_bound (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hc : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (hb : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ 1)
    {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hθ : f θ ≠ 0) :
    (∫⁻ t, ENNReal.ofReal (leftWeight θ t)*HirschmanDisk.negLog (f ((t : ℂ)*I))) +
    (∫⁻ t, ENNReal.ofReal (rightWeight θ t)*HirschmanDisk.negLog (f (1+(t : ℂ)*I))) ≤
      ENNReal.ofReal (-Real.log ‖f θ‖) := by
  have hh := cauchy_boundary_bound f hd hc hb h0 h1 hθ
  rw [lintegral_split_zero,left_change h0 h1 (fun z => HirschmanDisk.negLog (f z)),
    right_change h0 h1 (fun z => HirschmanDisk.negLog (f z)),← mul_add] at hh
  rw [ENNReal.ofReal_mul (show 0 ≤ 2*Real.pi by positivity)] at hh
  exact (ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top).mp hh

end HirschmanNormalized

noncomputable section
open Set Filter Metric MeasureTheory Real Complex HirschmanBoundary HirschmanStrip HirschmanWeights
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HirschmanLog

lemma upperLogIntegral_of_ae_coe {u : ℝ → ℝ} {v : ℝ → EReal} (hu : Integrable u)
    (hv : ∀ᵐ t, v t=(u t : EReal)) : upperLogIntegral v=(∫ t, u t : ℝ) := by
  have hp : (∫⁻ t, ENNReal.ofReal (u t)) ≠ ⊤ :=
    ne_top_of_le_ne_top hu.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm u)
  have hn : (∫⁻ t, ENNReal.ofReal (-u t)) ≠ ⊤ :=
    ne_top_of_le_ne_top hu.neg.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm (fun t => -u t))
  have hpe : (∫⁻ t, (v t).toENNReal) = ∫⁻ t, ENNReal.ofReal (u t) :=
    lintegral_congr_ae (hv.mono fun t ht => by
      change (v t).toENNReal=ENNReal.ofReal (u t)
      rw [ht,EReal.real_coe_toENNReal])
  have hne : (∫⁻ t, (-v t).toENNReal) = ∫⁻ t, ENNReal.ofReal (-u t) :=
    lintegral_congr_ae (hv.mono fun t ht => by
      change (-v t).toENNReal=ENNReal.ofReal (-u t)
      rw [ht,← EReal.coe_neg,EReal.real_coe_toENNReal])
  unfold upperLogIntegral
  rw [hpe,hne,
    ← EReal.coe_ennreal_toReal hp,← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub,integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu]

lemma integrand_eq_coe {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (t : ℝ)
    {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    (alphaDensity θ t : EReal)*extendedLog (‖z‖^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog (‖w‖^θ) =
    (leftWeight θ t*Real.log ‖z‖+rightWeight θ t*Real.log ‖w‖ : ℝ) := by
  have hzpow : 0 < ‖z‖^(1-θ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  have hwpow : 0 < ‖w‖^θ := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _
  rw [extendedLog,if_neg (not_le_of_gt hzpow),extendedLog,if_neg (not_le_of_gt hwpow),
    Real.log_rpow (norm_pos_iff.mpr hz),Real.log_rpow (norm_pos_iff.mpr hw)]
  simp only [← EReal.coe_mul,← EReal.coe_add]
  congr 1
  rw [left_weight_alpha h1,right_weight_beta h0]
  ring

lemma weight_sum_integrable {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Integrable (fun t => leftWeight θ t+rightWeight θ t) ∧
      (∫ t, leftWeight θ t+rightWeight θ t)=1 := by
  obtain ⟨_,ha,hb,hia,hib⟩ := hirschmanDensities.1 θ h0 h1
  have hfa : leftWeight θ = fun t => (1-θ)*alphaDensity θ t := funext (left_weight_alpha h1)
  have hfb : rightWeight θ = fun t => θ*betaDensity θ t := funext (right_weight_beta h0)
  rw [hfa,hfb]
  refine ⟨(ha.const_mul _).add (hb.const_mul _),?_⟩
  rw [integral_add (ha.const_mul _) (hb.const_mul _),integral_const_mul,integral_const_mul,hia,hib]
  ring

/-- Remove the unit bound without losing boundary zeros or the signed-integral convention. -/
theorem bounded_hirschman (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hc : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (M : ℝ) (hM : 0 < M)
    (hb : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ M)
    {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hθ : f θ ≠ 0) :
    (Real.log ‖f θ‖ : EReal) ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog (‖f ((t : ℂ)*I)‖^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog (‖f (1+(t : ℂ)*I)‖^θ)) := by
  let F : ℂ → ℂ := fun z => f z/(M : ℂ)
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re ∧ z.re < 1} := hd.div_const _
  have hFc : ContinuousOn F {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := hc.div_const _
  have hFb : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ 1 := by
    intro z hz0 hz1
    dsimp [F]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    exact (div_le_one hM).mpr (hb z hz0 hz1)
  have hFθ : F θ ≠ 0 := div_ne_zero hθ (Complex.ofReal_ne_zero.mpr hM.ne')
  let H : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (leftWeight θ t)*HirschmanDisk.negLog (F ((t : ℂ)*I)) +
    ENNReal.ofReal (rightWeight θ t)*HirschmanDisk.negLog (F (1+(t : ℂ)*I))
  have hcontL : Continuous (fun t : ℝ => F ((t : ℂ)*I)) := by
    apply hFc.comp_continuous (by fun_prop)
    intro t
    simp
  have hcontR : Continuous (fun t : ℝ => F (1+(t : ℂ)*I)) := by
    apply hFc.comp_continuous (by fun_prop)
    intro t
    simp
  have hLm : Measurable (fun t => ENNReal.ofReal (leftWeight θ t)*HirschmanDisk.negLog (F ((t : ℂ)*I))) :=
    (ENNReal.measurable_ofReal.comp (by unfold leftWeight; fun_prop)).mul
      (HirschmanDisk.continuous_negLog.comp hcontL).measurable
  have hRm : Measurable (fun t => ENNReal.ofReal (rightWeight θ t)*HirschmanDisk.negLog (F (1+(t : ℂ)*I))) :=
    (ENNReal.measurable_ofReal.comp (by unfold rightWeight; fun_prop)).mul
      (HirschmanDisk.continuous_negLog.comp hcontR).measurable
  have hHmeas : Measurable H := hLm.add hRm
  have hneg : 0 ≤ -Real.log ‖F θ‖ := neg_nonneg.mpr
    (Real.log_nonpos (norm_nonneg _) (hFb _ h0.le h1.le))
  have hbound : (∫⁻ t, H t) ≤ ENNReal.ofReal (-Real.log ‖F θ‖) := by
    rw [show (∫⁻ t, H t) =
      (∫⁻ t, ENNReal.ofReal (leftWeight θ t)*HirschmanDisk.negLog (F ((t : ℂ)*I))) +
      (∫⁻ t, ENNReal.ofReal (rightWeight θ t)*HirschmanDisk.negLog (F (1+(t : ℂ)*I))) by
        exact lintegral_add_left hLm _]
    exact HirschmanNormalized.normalized_bound F hF hFc hFb h0 h1 hFθ
  have hHfin : (∫⁻ t, H t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hHae : ∀ᵐ t, H t ≠ ⊤ := (ae_lt_top hHmeas hHfin).mono fun t ht => ht.ne
  have hHint : Integrable (fun t => (H t).toReal) := integrable_toReal_of_lintegral_ne_top hHmeas.aemeasurable hHfin
  have hHmean : (∫ t, (H t).toReal) ≤ -Real.log ‖F θ‖ := by
    rw [integral_toReal hHmeas.aemeasurable (ae_lt_top hHmeas hHfin)]
    exact ENNReal.toReal_le_of_le_ofReal hneg hbound
  have hweights := weight_sum_integrable h0 h1
  let u : ℝ → ℝ := fun t => (leftWeight θ t+rightWeight θ t)*Real.log M-(H t).toReal
  have hu : Integrable u := (hweights.1.mul_const _).sub hHint
  have hlog (z : ℂ) (hz : F z ≠ 0) : Real.log ‖F z‖ = Real.log ‖f z‖-Real.log M := by
    rw [show F z=f z/(M : ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    apply Real.log_div
    · exact norm_ne_zero_iff.mpr (fun h => hz (by simp [F,h]))
    · exact hM.ne'
  have hae : ∀ᵐ t,
      (alphaDensity θ t : EReal)*extendedLog (‖f ((t : ℂ)*I)‖^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog (‖f (1+(t : ℂ)*I)‖^θ) = (u t : EReal) := by
    filter_upwards [hHae] with t ht
    have hL : F ((t : ℂ)*I) ≠ 0 := by
      intro he
      have hpos := ENNReal.ofReal_pos.mpr (leftWeight_pos h0 h1 t)
      simp [H,he,HirschmanDisk.negLog_zero,ne_of_gt hpos] at ht
    have hR : F (1+(t : ℂ)*I) ≠ 0 := by
      intro he
      have hpos := ENNReal.ofReal_pos.mpr (rightWeight_pos h0 h1 t)
      simp [H,he,HirschmanDisk.negLog_zero,ne_of_gt hpos] at ht
    have hLf : f ((t : ℂ)*I) ≠ 0 := fun h => hL (by simp [F,h])
    have hRf : f (1+(t : ℂ)*I) ≠ 0 := fun h => hR (by simp [F,h])
    rw [integrand_eq_coe h0 h1 t hLf hRf]
    congr 1
    have hlb : 0 ≤ -Real.log ‖F ((t : ℂ)*I)‖ := neg_nonneg.mpr
      (Real.log_nonpos (norm_nonneg _) (hFb _ (by simp) (by simp)))
    have hrb : 0 ≤ -Real.log ‖F (1+(t : ℂ)*I)‖ := neg_nonneg.mpr
      (Real.log_nonpos (norm_nonneg _) (hFb _ (by simp) (by simp)))
    have hHreal : (H t).toReal = leftWeight θ t*(-Real.log ‖F ((t : ℂ)*I)‖)+
        rightWeight θ t*(-Real.log ‖F (1+(t : ℂ)*I)‖) := by
      dsimp [H]
      rw [HirschmanDisk.negLog_of_ne_zero hL,HirschmanDisk.negLog_of_ne_zero hR,
        ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),ENNReal.toReal_mul,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (leftWeight_pos h0 h1 t).le,ENNReal.toReal_ofReal (rightWeight_pos h0 h1 t).le,
        ENNReal.toReal_ofReal hlb,ENNReal.toReal_ofReal hrb]
    dsimp [u]
    rw [hHreal,hlog _ hL,hlog _ hR]
    ring
  rw [upperLogIntegral_of_ae_coe hu hae]
  apply EReal.coe_le_coe_iff.mpr
  dsimp [u]
  rw [integral_sub (hweights.1.mul_const _) hHint,integral_mul_const,hweights.2,one_mul]
  rw [hlog _ hFθ] at hHmean
  linarith

end HirschmanLog

noncomputable section
open Set Filter Metric MeasureTheory Real Complex
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped Topology ENNReal NNReal ComplexConjugate
set_option autoImplicit false
namespace HirschmanFinal

theorem hirschman (f : ℂ → ℂ)
    (hbdd : Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog ‖f θ‖ ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog (‖f ((t : ℂ)*I)‖^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog (‖f (1+(t : ℂ)*I)‖^θ)) := by
  by_cases hzero : f θ=0
  · simp only [hzero,norm_zero,extendedLog,le_refl,if_true]
    exact bot_le
  · have hcl : closure {z : ℂ | 0 < z.re ∧ z.re < 1} = {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := by
      change closure (Complex.re ⁻¹' Ioo 0 1) = Complex.re ⁻¹' Icc 0 1
      rw [Complex.closure_preimage_re,closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    have hc : ContinuousOn f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := hcl ▸ hf.continuousOn
    obtain ⟨B,hB⟩ := hbdd.exists_norm_le
    let M := max 1 B
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hbound : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ M := by
      intro z hz0 hz1
      exact (hB _ ⟨z,⟨hz0,hz1⟩,rfl⟩).trans (le_max_right _ _)
    rw [extendedLog,if_neg (not_le_of_gt (norm_pos_iff.mpr hzero))]
    exact HirschmanLog.bounded_hirschman f hf.differentiableOn hc M hM hbound hθ0 hθ1 hzero

end HirschmanFinal

set_option autoImplicit false



/-- **Theorem 12.2.2 (Hirschman)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 12.2.2, (12.14)–(12.16), p. 369). Let `S = {z : 0 < Re z < 1}` and
`f : S̄ → ℂ` be bounded on `S̄`, holomorphic on `S` and continuous on `S̄`. Then for `θ ∈ (0, 1)`,
`ln |f(θ)| ≤ ∫ dt (α_θ(t) ln[|f(it)|^{1−θ}] + β_θ(t) ln[|f(1 + it)|^θ])`, with
`α_θ(t) = sin(πθ) / (2(1 − θ)[cosh(πt) − cos(πθ)])` and
`β_θ(t) = sin(πθ) / (2θ[cosh(πt) + cos(πθ)])`.

**Formalization Note** `f` is a function on `ℂ`; only its values on `S̄` enter. "Continuous on the
boundary" is read as continuity on the closed strip (`DiffContOnCl`), the standard hypothesis; the
literal reading is false (see the item's differences). `ln 0 = −∞` (`extendedLog`), and the
integral is the signed extended integral `∫⁺ − ∫⁻` (`upperLogIntegral`), whose positive part is
finite because `f` is bounded; it may equal `−∞`. These and the densities are the published
definitions of Junge–Renner–Sutter–Wilde–Winter (2018). -/
theorem solution (f : ℂ → ℂ)
    (hbdd : Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog ‖f θ‖ ≤
      upperLogIntegral (fun t =>
        (alphaDensity θ t : EReal) * extendedLog (‖f ((t : ℂ) * Complex.I)‖ ^ (1 - θ)) +
        (betaDensity θ t : EReal) * extendedLog (‖f (1 + (t : ℂ) * Complex.I)‖ ^ θ)) := by
  exact HirschmanFinal.hirschman f hbdd hf θ hθ0 hθ1