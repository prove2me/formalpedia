-- Prove2me | solution 1 for Viterbo.Cap.exists_critical_cerami
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:41.989585+00:00
-- url     : https://prove2.me/submissions/974c2fd6-671c-4441-9eba-4a1645edb5d1

import Mathlib
import Definitions.Def_OAIQWSP000
import Theorems.Thm_AGT_brouwer_fixed_point
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap
universe u3 u4 u5 u6 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99 u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115 u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127

section
section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl

@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothDegree
noncomputable section

 theorem exists_zero {E : Type u78} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContDiff ℝ ∞ f)
    {R : ℝ} (hR : 0 < R) (hId : ∀ x, R ≤ ‖x‖ → f x = x) : ∃ x, f x = 0 := by
  -- from the published Brouwer theorem AGT.brouwer_fixed_point: x ↦ x - f x vanishes outside
  -- the ball of radius R, so it maps a large closed ball into itself; a fixed point is a zero of f
  have hc : Continuous (fun x => x - f x) := continuous_id.sub hf.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hc.continuousOn
  have hbd (x : E) : ‖x - f x‖ ≤ max M 0 := by
    by_cases hx : ‖x‖ ≤ R
    · exact (hM x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)
    · rw [hId x (not_le.mp hx).le, sub_self, norm_zero]
      exact le_max_right _ _
  obtain ⟨x, -, hx⟩ := AGT.brouwer_fixed_point (convex_closedBall (0:E) (max M 0))
    (isCompact_closedBall _ _) (Metric.nonempty_closedBall.mpr (le_max_right _ _))
    (fun x => x - f x) hc.continuousOn (fun x _ => mem_closedBall_zero_iff.mpr (hbd x))
  exact ⟨x, sub_eq_self.mp hx⟩

end
end SmoothDegree

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FiniteDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem degreeMap_eq_self {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ)
    (hη : η (z.1, (z.2+ρ) • e) = (z.1, (z.2+ρ) • e)) :
    degreeMap η e ρ z = z := by
  simp only [degreeMap, ite_eq_left hz, hη, norm_smul, he, mul_one,
    Real.norm_eq_abs, sq_abs]
  apply Prod.ext
  · rfl
  change ((z.2+ρ)^2-ρ^2)/(z.2+2*ρ) = z.2
  apply (div_eq_iff (by linarith : z.2+2*ρ ≠ 0)).mpr
  ring

theorem contDiffAt_degreeMap_pos {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    (e : F) {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ) :
    ContDiffAt ℝ ∞ (degreeMap η e ρ) z := by
  have hinput : ContDiff ℝ ∞ (fun w : E × ℝ => (w.1, (w.2+ρ) • e)) :=
    contDiff_fst.prodMk ((contDiff_snd.add contDiff_const).smul contDiff_const)
  have hout := hη.comp hinput
  have hn : z.2+2*ρ ≠ 0 := by linarith
  have hd : ContDiffAt ℝ ∞ (fun w : E × ℝ =>
      ((η (w.1, (w.2+ρ) • e)).1, (‖(η (w.1, (w.2+ρ) • e)).2‖^2-ρ^2)/(w.2+2*ρ))) z := by
    exact (contDiff_fst.comp hout).contDiffAt.prodMk
      (((contDiff_norm_sq ℝ).comp (contDiff_snd.comp hout)).contDiffAt.sub contDiffAt_const |>.div
        (contDiffAt_snd.add contDiffAt_const) hn)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const (continuous_snd.add continuous_const)).mem_nhds hz] with w hw
  change 0 < w.2+ρ at hw
  simp only [degreeMap, ite_eq_left hw]

theorem contDiff_degreeMap {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    {e : F} (he : ‖e‖ = 1) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e)) :
    ContDiff ℝ ∞ (degreeMap η e ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : 0 < z.2+ρ
  · exact contDiffAt_degreeMap_pos hη e hρ hz
  have hz' : z.2+ρ < ε := lt_of_le_of_lt (le_of_not_gt hz) hε
  apply (contDiffAt_id : ContDiffAt ℝ ∞ (id : E × ℝ → E × ℝ) z).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_snd.add continuous_const) continuous_const).mem_nhds hz'] with w hw
  by_cases hp : 0 < w.2+ρ
  · exact degreeMap_eq_self he hρ hp (hfixed w.1 (w.2+ρ) hp hw)
  · simp only [degreeMap, ite_eq_right hp, id_eq]

omit [NormedSpace ℝ E] in
theorem norm_translate_le (z : E × ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖z‖ ≤ ‖(z.1, z.2+ρ)‖ + ρ := by
  have he : z = (z.1, z.2+ρ) - (0,ρ) := by ext <;> simp
  calc
    ‖z‖ = ‖(z.1, z.2+ρ) - (0,ρ)‖ := congrArg norm he
    _ ≤ ‖(z.1, z.2+ρ)‖+‖((0,ρ) : E × ℝ)‖ := norm_sub_le _ _
    _ = _ := by simp [Prod.norm_def, abs_of_nonneg hρ, hρ]

omit [NormedSpace ℝ E] in
theorem degreeMap_identity_outside {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ R : ℝ} (hρ : 0 < ρ)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e))
    (z : E × ℝ) (hz : R+ρ ≤ ‖z‖) : degreeMap η e ρ z = z := by
  by_cases hp : 0 < z.2+ρ
  · apply degreeMap_eq_self he hρ hp
    apply hfixed _ _ hp
    have hn := norm_translate_le z hρ.le
    linarith
  · simp only [degreeMap, ite_eq_right hp]

theorem sphere_linking [FiniteDimensional ℝ E]
    {η : E × F → E × F} (hη : ContDiff ℝ ∞ η) {e : F} (he : ‖e‖ = 1)
    {ρ ε R : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e))
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e)) :
    ∃ (y : E) (s : ℝ), 0 < s ∧ ‖(y,s)‖ < R ∧ (η (y, s • e)).1 = 0 ∧ ‖(η (y, s • e)).2‖ = ρ := by
  obtain ⟨z, hz⟩ := SmoothDegree.exists_zero (contDiff_degreeMap hη he hρ hε hnear)
    (show 0 < R+ρ by linarith) (degreeMap_identity_outside he hρ hfar)
  have hp : 0 < z.2+ρ := by
    by_contra h
    have heq : z = 0 := by simpa only [degreeMap, ite_eq_right h] using hz
    simp only [heq, Prod.snd_zero, zero_add] at h
    exact h hρ
  have hfst : (η (z.1, (z.2+ρ) • e)).1 = 0 := by
    simpa only [degreeMap, ite_eq_left hp, Prod.fst_zero, Prod.fst] using congrArg Prod.fst hz
  have hsnd : ‖(η (z.1, (z.2+ρ) • e)).2‖ = ρ := by
    have h := congrArg Prod.snd hz
    simp only [degreeMap, ite_eq_left hp, Prod.snd_zero] at h
    have hd : z.2+2*ρ ≠ 0 := by linarith
    have hsq : ‖(η (z.1, (z.2+ρ) • e)).2‖^2 = ρ^2 :=
      sub_eq_zero.mp ((div_eq_zero_iff).mp h |>.resolve_right hd)
    nlinarith [norm_nonneg (η (z.1, (z.2+ρ) • e)).2]
  refine ⟨z.1, z.2+ρ, hp, ?_, hfst, hsnd⟩
  by_contra! hn
  have hid := hfar z.1 (z.2+ρ) hp hn
  rw [hid] at hfst hsnd
  simp only [norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_pos hp] at hfst hsnd
  rw [hfst, hsnd] at hn
  have : ‖((0 : E),ρ)‖ = ρ := by simp [Prod.norm_def, abs_of_pos hρ, hρ.le]
  rw [this] at hn
  exact hR.not_ge hn

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u82} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem curve_displacement {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {L : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L) (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖SmoothODE.curve hV h hh x t - x‖ ≤ h*L*t := by
  have hb (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
      ‖h • V (SmoothODE.curve hV h hh x s)‖ ≤ h*L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hL _) h0
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (SmoothODE.hasDerivAt_curve hV h hh x ⟨s,hs⟩).hasDerivWithinAt)
    hb (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ht
  simpa only [SmoothODE.curve_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm

 theorem curve_energy_deriv {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Φ (SmoothODE.curve hV h hh x s))
      (h * fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t))) t := by
  have hd := (hΦ (SmoothODE.curve hV h hh x t)).hasFDerivAt.comp_hasDerivAt t
    (SmoothODE.hasDerivAt_curve hV h hh x ⟨t,ht⟩)
  simpa only [Function.comp_def, map_smul, smul_eq_mul] using hd

 theorem curve_energy_antitone {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    (hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).continuousOn
    (fun t ht => (curve_energy_deriv hV hh hΦ x (interior_subset ht)).hasDerivWithinAt)
  intro t _
  exact mul_nonpos_of_nonneg_of_nonpos h0 (hdec _)

 theorem step_energy_le {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    Φ (SmoothODE.step hV h hh x) ≤ Φ x := by
  simpa only [SmoothODE.curve_one, SmoothODE.curve_zero] using
    (curve_energy_antitone hV hh h0 hΦ hdec x (by simp) (by simp) zero_le_one)

 theorem step_energy_drop {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) {L M a b : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1)
    (x : E) (hx : ‖x‖+h*L ≤ M) (hxb : Φ x ≤ b) :
    Φ (SmoothODE.step hV h hh x) ≤ max a (Φ x-h) := by
  by_cases hxa : Φ (SmoothODE.step hV h hh x) ≤ a
  · exact hxa.trans (le_max_left _ _)
  have ha := le_of_lt (lt_of_not_ge hxa)
  have ham := curve_energy_antitone hV hh h0 hΦ hdec x
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t)) ≤ -1 := by
    apply hrate
    · have hdn := curve_displacement hV hh h0 hL x ht
      have hLn : 0 ≤ L := le_trans (norm_nonneg (V x)) (hL x)
      have hn := norm_le_norm_sub_add (SmoothODE.curve hV h hh x t) x
      have htime := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg h0 hLn)
      linarith
    · exact ha.trans (by simpa only [SmoothODE.curve_one] using ham ht (by simp) ht.2)
    · exact (show Φ (SmoothODE.curve hV h hh x t) ≤ Φ x from by
        simpa only [SmoothODE.curve_zero] using ham (by simp) ht ht.1).trans hxb
  have hm : AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)+h*t) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
      (((hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).add
        (continuous_const.mul continuous_id)).continuousOn)
      (fun t ht => ((curve_energy_deriv hV hh hΦ x (interior_subset ht)).add
        ((hasDerivAt_id t).const_mul h)).hasDerivWithinAt)
    intro t ht
    have := mul_le_mul_of_nonneg_left (hb t (interior_subset ht)) h0
    linarith
  have hend := hm (by simp) (by simp) zero_le_one
  simp only [SmoothODE.curve_one, SmoothODE.curve_zero, mul_one, mul_zero, add_zero] at hend
  exact (by linarith : Φ (SmoothODE.step hV h hh x) ≤ Φ x-h).trans (le_max_right _ _)

end
end FlowDescent

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u83} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_energy_le {f : E → E} {Φ : E → ℝ} (hf : ∀ x, Φ (f x) ≤ Φ x)
    (j : ℕ) (x : E) : Φ (f^[j] x) ≤ Φ x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hf (f^[j] x)).trans ih

 omit [CompleteSpace E] in
 theorem contDiff_iterate {f : E → E} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (f^[j]) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih =>
    convert! hf.comp ih using 1
    ext x
    exact Function.iterate_succ_apply' f j x

end
end FlowDescent

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GradientLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 theorem contDiff_gradient {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (gradient Φ) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hΦ.fderiv_right (by simp))

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem energyCutoff_contDiff {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (a : ℝ) :
    ContDiff ℝ ∞ (energyCutoff Φ a) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul hΦ).sub contDiff_const).div_const a)

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_mem (Φ : E → ℝ) (a : ℝ) (x : E) :
    energyCutoff Φ a x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_one (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : a ≤ Φ x) :
    energyCutoff Φ a x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ ha]
  linarith

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_zero (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : Φ x ≤ a/2) :
    energyCutoff Φ a x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le

end
end GradientDescent

namespace FiniteLinking
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {H : Type u86} {E : Type u87} {F : Type u88} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end
end FiniteLinking

end

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions

end
end FourierPolynomial

namespace WeightedSchur
noncomputable section
open Finset

end
end WeightedSchur

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 local instance instFactLtRealOfNat_solutions_1_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
 local instance instFactLtRealOfNat_solutions_2_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_3_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u106} {κ : Type u107} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_4
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_5_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_6
variable {ι κ : Type} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.QuadraticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace DiagonalQuadratic
noncomputable section
open Finset
open scoped ComplexConjugate ContDiff
variable {α : Type u112} [Fintype α]

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_8_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_9_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GalerkinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_10_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_11_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_12
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_13_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] OAI.L2Paths.instFactLtRealOfNat_solutions

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
open FourierPolynomial (integrable_continuous)

 attribute [local instance] OAI.PeriodicFourier.instFactLtRealOfNat_solutions

end
end PeriodicFourier

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_14
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open DiagonalQuadratic FourierPolynomial

 local instance instFactLtRealOfNat_solutions_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

 variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianODE
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open FourierPolynomial DiagonalQuadratic
local instance instFactLtRealOfNat_solutions_rc74a79_2 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {κ : Type u116} [Fintype κ]

end
end HamiltonianODE

namespace HamiltonianODE
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u118} [Fintype κ]

end
end HamiltonianODE

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianGrowth
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u119} [Fintype κ]

end
end HamiltonianGrowth

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type u120} [Fintype κ]

end
end HamiltonianPeriodic

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE
variable {κ : Type u122} [Fintype κ]

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

end
end SmoothProfiles

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.ExteriorHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth SmoothProfiles
variable {κ : Type u124} [Fintype κ]

end
end ExteriorHamiltonian

namespace ExteriorHamiltonian
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
variable {κ : Type u125} [Fintype κ]

end
end ExteriorHamiltonian

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles ExteriorHamiltonian
variable {κ : Type u126} [Fintype κ]

end
end PushedBall

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Nonsqueezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

end
end CylinderParameters

namespace CylinderNonsqueezing
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
open ExteriorHamiltonian PushedBall CylinderParameters
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end

end OAI
end
end

section
/-!
Blueprint, Part M: elementary properties of `cEHZ` on convex domains, and monotonicity under
inclusion from Clarke's dual action principle in length form
(`Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`).
-/

open MeasureTheory Set OAI.SymmetricPolar
open scoped ENNReal Pointwise

namespace Viterbo.CM

variable {n : ℕ}

/-! ## Helpers -/

/-! ### Absolutely continuous loops -/

/-! ### Support functions -/

/-! ### Translation -/

/-! ### Scaling -/

/-! ### Positivity of the action -/

end Viterbo.CM
end

section
set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/


/-! ## Non-squeezing in phase-space form -/

/-! ## The two capacities -/

end Viterbo.Capacities
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE1
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
open Metric
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
/-!
# Part E1: the finite-dimensional linking lemma under a Cerami condition

Same scheme as `OAI.FiniteLinking.exists_critical`, with a descent field weighted by
`1 + ‖x‖²`, so that `Φ` drops at unit rate on the strip while `‖x‖` grows at most
exponentially along the descent.
-/
/-! ## The weighted field -/
/-- The weighted descent field `-(2σW/(W‖∇Φ‖² + ε²)) ∇Φ`, `W = 1 + ‖x‖²`. -/
def wfield (Φ σ : X → ℝ) (ε : ℝ) (x : X) : X :=
  (-(2 * σ x * (1 + ‖x‖ ^ 2) / ((1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 + ε ^ 2))) • gradient Φ x

theorem wden_pos (Φ : X → ℝ) {ε : ℝ} (hε : 0 < ε) (x : X) :
    0 < (1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 + ε ^ 2 := by positivity

theorem contDiff_wfield {Φ σ : X → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hσ : ContDiff ℝ ∞ σ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (wfield Φ σ ε) := by
  have hg := GradientDescent.contDiff_gradient hΦ
  have hW : ContDiff ℝ ∞ (fun x : X => 1 + ‖x‖ ^ 2) := contDiff_const.add (contDiff_norm_sq ℝ)
  exact (((contDiff_const.mul hσ).mul hW).div
    ((hW.mul ((contDiff_norm_sq ℝ).comp hg)).add contDiff_const)
    (fun x => (wden_pos Φ hε x).ne')).neg.smul hg

theorem wfield_eq_zero {Φ σ : X → ℝ} {ε : ℝ} {x : X} (hσ : σ x = 0) :
    wfield Φ σ ε x = 0 := by simp [wfield, hσ]

theorem wfield_rate (Φ σ : X → ℝ) (ε : ℝ) (x : X) :
    fderiv ℝ Φ x (wfield Φ σ ε x) =
      -(2 * σ x * (1 + ‖x‖ ^ 2) / ((1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 + ε ^ 2)) *
        ‖gradient Φ x‖ ^ 2 := by
  rw [wfield, map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [real_inner_self_eq_norm_sq]

theorem wfield_nonincrease (Φ : X → ℝ) {σ : X → ℝ} (hσ : ∀ x, 0 ≤ σ x)
    {ε : ℝ} (hε : 0 < ε) (x : X) : fderiv ℝ Φ x (wfield Φ σ ε x) ≤ 0 := by
  rw [wfield_rate]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hσ x))
      (by positivity)) (wden_pos Φ hε x).le)
  · exact sq_nonneg _

theorem wfield_decrease (Φ : X → ℝ) {σ : X → ℝ} {ε : ℝ} (hε : 0 < ε)
    {x : X} (hσ : σ x = 1) (hx : ε ^ 2 ≤ (1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2) :
    fderiv ℝ Φ x (wfield Φ σ ε x) ≤ -1 := by
  rw [wfield_rate, hσ, mul_one]
  have hd := wden_pos Φ hε x
  have he : -(2 * (1 + ‖x‖ ^ 2) / ((1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 + ε ^ 2)) *
      ‖gradient Φ x‖ ^ 2 =
      -(2 * ((1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2) /
        ((1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 + ε ^ 2)) := by ring
  rw [he, neg_le_neg_iff, le_div_iff₀ hd]
  linarith

theorem wfield_norm_le (Φ : X → ℝ) {σ : X → ℝ} (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (x : X) : ‖wfield Φ σ ε x‖ ≤ (1 + ‖x‖) / ε := by
  have hden := wden_pos Φ hε x
  set W := 1 + ‖x‖ ^ 2 with hWdef
  set g := ‖gradient Φ x‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have hW0 : 0 < W := by positivity
  set D := W * g ^ 2 + ε ^ 2 with hD
  rw [wfield, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hσ x).1) hW0.le) hden.le)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hε]
  -- key: `2 W g ε ≤ (1 + ‖x‖) D`
  have hkey : 2 * W * g * ε ≤ (1 + ‖x‖) * D := by
    have h1 : (2 * W * g * ε) ^ 2 ≤ W * D ^ 2 := by
      have : 4 * (W * g ^ 2) * ε ^ 2 ≤ D ^ 2 := by
        rw [hD]; nlinarith [sq_nonneg (W * g ^ 2 - ε ^ 2)]
      nlinarith
    have h2 : W * D ^ 2 ≤ ((1 + ‖x‖) * D) ^ 2 := by
      have : W ≤ (1 + ‖x‖) ^ 2 := by rw [hWdef]; nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg D]
    have h3 : 0 ≤ (1 + ‖x‖) * D := by positivity
    exact abs_le_of_sq_le_sq' (h1.trans h2) h3 |>.2
  have hs : 2 * σ x * W * g * ε ≤ 2 * W * g * ε := by
    have : 0 ≤ 2 * W * g * ε := by positivity
    nlinarith [(hσ x).2]
  nlinarith

theorem wfield_hasCompactSupport {Φ σ : X → ℝ} (hσ : HasCompactSupport σ) (ε : ℝ) :
    HasCompactSupport (wfield Φ σ ε) := by
  apply HasCompactSupport.of_support_subset_isCompact hσ.isCompact
  intro x hx
  by_contra hn
  apply hx
  exact wfield_eq_zero (image_eq_zero_of_notMem_tsupport hn)

/-- Uniform weighted lower bound on the strip, from the Cerami bound and compactness. -/
theorem exists_weighted_lower [FiniteDimensional ℝ X] {Φ : X → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b : ℝ} (hnocrit : ∀ x, a ≤ Φ x → Φ x ≤ b → gradient Φ x ≠ 0)
    {R₁ c₁ : ℝ} (hc₁ : 0 < c₁)
    (hcer : ∀ x, a ≤ Φ x → Φ x ≤ b → R₁ ≤ ‖x‖ → c₁ ≤ (1 + ‖x‖) * ‖gradient Φ x‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, a ≤ Φ x → Φ x ≤ b →
      ε ^ 2 ≤ (1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2 := by
  have hout : ∀ y, a ≤ Φ y → Φ y ≤ b → R₁ ≤ ‖y‖ →
      (c₁ / 2) ^ 2 ≤ (1 + ‖y‖ ^ 2) * ‖gradient Φ y‖ ^ 2 := by
    intro y ha hb hy
    have hc := hcer y ha hb hy
    have hg0 := norm_nonneg (gradient Φ y)
    have hy0 := norm_nonneg y
    have h1 : c₁ ^ 2 ≤ ((1 + ‖y‖) * ‖gradient Φ y‖) ^ 2 := pow_le_pow_left₀ hc₁.le hc 2
    have h2 : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖y‖)]
    have h3 : ((1 + ‖y‖) * ‖gradient Φ y‖) ^ 2 ≤ 2 * ((1 + ‖y‖ ^ 2) * ‖gradient Φ y‖ ^ 2) := by
      rw [mul_pow]; nlinarith [sq_nonneg ‖gradient Φ y‖]
    nlinarith
  let S := closedBall (0 : X) R₁ ∩ Φ ⁻¹' Icc a b
  have hS : IsCompact S := (isCompact_closedBall (0 : X) R₁).inter_right
    (isClosed_Icc.preimage hΦ.continuous)
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx, hm⟩ :=
      hS.exists_isMinOn hne (GradientDescent.contDiff_gradient hΦ).continuous.norm.continuousOn
    have hxg : 0 < ‖gradient Φ x‖ := norm_pos_iff.mpr (hnocrit x hx.2.1 hx.2.2)
    refine ⟨min (c₁ / 2) ‖gradient Φ x‖, lt_min (by linarith) hxg, ?_⟩
    intro y ha hb
    have hm0 : 0 ≤ min (c₁ / 2) ‖gradient Φ x‖ := (lt_min (by linarith) hxg).le
    by_cases hy : ‖y‖ ≤ R₁
    · have hle : min (c₁ / 2) ‖gradient Φ x‖ ≤ ‖gradient Φ y‖ :=
        (min_le_right _ _).trans (hm ⟨by simpa using hy, ha, hb⟩)
      have h1 := pow_le_pow_left₀ hm0 hle 2
      have : ‖gradient Φ y‖ ^ 2 ≤ (1 + ‖y‖ ^ 2) * ‖gradient Φ y‖ ^ 2 := by
        nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖gradient Φ y‖]
      linarith
    · have h1 := pow_le_pow_left₀ hm0 (min_le_left (c₁ / 2) ‖gradient Φ x‖) 2
      exact h1.trans (hout y ha hb (le_of_lt (lt_of_not_ge hy)))
  · refine ⟨c₁ / 2, by linarith, ?_⟩
    intro y ha hb
    apply hout y ha hb
    by_contra h
    exact hne ⟨y, by simpa using (le_of_lt (lt_of_not_ge h)), ha, hb⟩

/-- The cut-off weighted field. -/
theorem exists_wcutoff_field [FiniteDimensional ℝ X] {Φ : X → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b ε M : ℝ} (ha : 0 < a) (hε : 0 < ε) (hM : 0 < M)
    (hgrad : ∀ x, a ≤ Φ x → Φ x ≤ b → ε ^ 2 ≤ (1 + ‖x‖ ^ 2) * ‖gradient Φ x‖ ^ 2) :
    ∃ (V : X → X) (K : ℝ≥0) (L : ℝ), ContDiff ℝ ∞ V ∧ LipschitzWith K V ∧
      (∀ x, ‖V x‖ ≤ L) ∧ (∀ x, ‖V x‖ ≤ (1 + ‖x‖) / ε) ∧
      (∀ x, fderiv ℝ Φ x (V x) ≤ 0) ∧
      (∀ x, Φ x ≤ a / 2 → V x = 0) ∧
      (∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) := by
  let χ : ContDiffBump (0 : X) := ⟨M, M + 1, hM, by linarith⟩
  let σ : X → ℝ := fun x => χ x * GradientDescent.energyCutoff Φ a x
  have hσ : ContDiff ℝ ∞ σ := χ.contDiff.mul (GradientDescent.energyCutoff_contDiff hΦ a)
  have hσc : HasCompactSupport σ := χ.hasCompactSupport.mul_right
  have hσm (x : X) : σ x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg χ.nonneg (GradientDescent.energyCutoff_mem Φ a x).1, ?_⟩
    exact (mul_le_of_le_one_left (GradientDescent.energyCutoff_mem Φ a x).1 χ.le_one).trans
      (GradientDescent.energyCutoff_mem Φ a x).2
  let V := wfield Φ σ ε
  have hV : ContDiff ℝ ∞ V := contDiff_wfield hΦ hσ hε
  have hVc : HasCompactSupport V := wfield_hasCompactSupport hσc ε
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  obtain ⟨L, hL⟩ := hV.continuous.bounded_above_of_compact_support hVc
  refine ⟨V, K, L, hV, hK, hL, wfield_norm_le Φ hσm hε,
    wfield_nonincrease Φ (fun x => (hσm x).1) hε, ?_, ?_⟩
  · intro x hx
    apply wfield_eq_zero
    simp only [σ, GradientDescent.energyCutoff_zero Φ ha hx, mul_zero]
  · intro x hx hxa hxb
    apply wfield_decrease Φ hε _ (hgrad x hxa hxb)
    have hχ : χ x = 1 := χ.one_of_mem_closedBall (by simpa using hx)
    simp only [σ, hχ, GradientDescent.energyCutoff_one Φ ha hxa, mul_one]

end Viterbo.Cap.PartE1
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE1
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
open Metric
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
/-! ## Descent with linear growth -/
theorem step_norm_le {V : X → X} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {L ε : ℝ} (hε : 0 < ε)
    (hL : ∀ x, ‖V x‖ ≤ L) (hhL : h * L ≤ 1) (hlin : ∀ x, ‖V x‖ ≤ (1 + ‖x‖) / ε) (x : X) :
    1 + ‖OAI.SmoothODE.step hV h hh x‖ ≤ (1 + ‖x‖) * (1 + 2 * h / ε) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖h • V (OAI.SmoothODE.curve hV h hh x s)‖ ≤ h * ((2 + ‖x‖) / ε) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    apply mul_le_mul_of_nonneg_left _ h0
    have hd := OAI.FlowDescent.curve_displacement hV hh h0 hL x hs
    have hn := norm_le_norm_sub_add (OAI.SmoothODE.curve hV h hh x s) x
    have hLn : 0 ≤ L := le_trans (norm_nonneg (V x)) (hL x)
    have hs1 : h * L * s ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hs.2 (mul_nonneg h0 hLn)
      linarith
    refine (hlin _).trans ?_
    apply div_le_div_of_nonneg_right _ hε.le
    linarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (OAI.SmoothODE.hasDerivAt_curve hV h hh x ⟨s, hs⟩).hasDerivWithinAt)
    hb (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  simp only [OAI.SmoothODE.curve_zero, OAI.SmoothODE.curve_one, sub_zero, norm_one,
    mul_one] at hm
  have hn := norm_le_norm_sub_add (OAI.SmoothODE.step hV h hh x) x
  have hx0 := norm_nonneg x
  have : h * ((2 + ‖x‖) / ε) ≤ (1 + ‖x‖) * (2 * h / ε) := by
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hε]
    nlinarith
  nlinarith

theorem iterate_norm_le {V : X → X} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {L ε : ℝ} (hε : 0 < ε)
    (hL : ∀ x, ‖V x‖ ≤ L) (hhL : h * L ≤ 1) (hlin : ∀ x, ‖V x‖ ≤ (1 + ‖x‖) / ε)
    (j : ℕ) (x : X) :
    1 + ‖(OAI.SmoothODE.step hV h hh)^[j] x‖ ≤ (1 + ‖x‖) * (1 + 2 * h / ε) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ, ← mul_assoc]
    have hq : 0 ≤ 1 + 2 * h / ε := by positivity
    exact (step_norm_le hV hh h0 hε hL hhL hlin _).trans
      (mul_le_mul_of_nonneg_right (by linarith) hq)

theorem exists_wdescent_map [ProperSpace X] {V : X → X} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {Φ : X → ℝ}
    (hΦ : Differentiable ℝ Φ) (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0)
    {L ε a b B T M : ℝ} (hε : 0 < ε) (hT : 0 < T) (hba : b - T ≤ a)
    (hL : ∀ x, ‖V x‖ ≤ L) (hlin : ∀ x, ‖V x‖ ≤ (1 + ‖x‖) / ε)
    (hM : (1 + B) * Real.exp (2 * T / ε) + 1 ≤ M)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) :
    ∃ η : X → X, ContDiff ℝ ∞ η ∧ (∀ x, V x = 0 → η x = x) ∧
      ∀ x, ‖x‖ ≤ B → Φ x ≤ b → Φ (η x) ≤ a := by
  have hL0 : 0 ≤ L := (norm_nonneg (V 0)).trans (hL 0)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (T * (K : ℝ)) (T * L))
  have hN0 : (0 : ℝ) < N :=
    lt_of_le_of_lt (le_max_of_le_right (mul_nonneg hT.le hL0)) hN
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  let h := T / N
  have h0 : 0 ≤ h := (div_pos hT hN0).le
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖ * (K : ℝ) < (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  have hhL : h * L ≤ 1 := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact ((div_lt_one hN0).mpr ((le_max_right _ _).trans_lt hN)).le
  have hNh : (N : ℝ) * h = T := by dsimp [h]; field_simp
  let f := OAI.SmoothODE.step hV h hh
  have hf : ContDiff ℝ ∞ f := OAI.SmoothODE.contDiff_step hV hVs h hh
  have hfd (x : X) : Φ (f x) ≤ Φ x := OAI.FlowDescent.step_energy_le hV hh h0 hΦ hdec x
  refine ⟨f^[N], OAI.FlowDescent.contDiff_iterate hf N, ?_, ?_⟩
  · intro x hx
    have hfix : f x = x := by
      simpa only [OAI.SmoothODE.curve_one] using
        (OAI.SmoothODE.curve_of_eq_zero hV h hh x hx (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1))
    exact Function.iterate_fixed hfix N
  · intro x hx hb
    have hq : 0 ≤ 2 * h / ε := by positivity
    have hpow (j : ℕ) (hj : j ≤ N) : (1 + 2 * h / ε) ^ j ≤ Real.exp (2 * T / ε) := by
      calc (1 + 2 * h / ε) ^ j ≤ (1 + 2 * h / ε) ^ N :=
            pow_le_pow_right₀ (by linarith) hj
        _ ≤ Real.exp (2 * h / ε) ^ N := by
            apply pow_le_pow_left₀ (by linarith)
            linarith [Real.add_one_le_exp (2 * h / ε)]
        _ = Real.exp (2 * T / ε) := by
            rw [← Real.exp_nat_mul]
            congr 1
            rw [← hNh]
            ring
    have hx0 := norm_nonneg x
    have hB : 0 ≤ 1 + B := by linarith
    have hnorm (j : ℕ) (hj : j ≤ N) : ‖f^[j] x‖ + h * L ≤ M := by
      have h1 := iterate_norm_le hV hh h0 hε hL hhL hlin j x
      have h2 : (1 + ‖x‖) * (1 + 2 * h / ε) ^ j ≤ (1 + B) * Real.exp (2 * T / ε) := by
        apply mul_le_mul (by linarith) (hpow j hj) (by positivity) hB
      linarith
    suffices hs : ∀ j, j ≤ N → Φ (f^[j] x) ≤ max a (Φ x - j * h) by
      have hd := hs N le_rfl
      rw [hNh] at hd
      exact hd.trans (max_le le_rfl (by linarith))
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hij := ih (Nat.le_trans (Nat.le_succ j) hj)
      have hb' := (OAI.FlowDescent.iterate_energy_le hfd j x).trans hb
      have hd := OAI.FlowDescent.step_energy_drop hV hh h0 hΦ hdec hL hrate (f^[j] x)
        (hnorm j (Nat.le_trans (Nat.le_succ j) hj)) hb'
      rw [Function.iterate_succ_apply']
      apply hd.trans
      apply max_le (le_max_left _ _)
      apply (sub_le_sub_right hij h).trans
      rw [← max_sub_sub_right]
      apply max_le
      · exact (sub_le_self a h0).trans (le_max_left _ _)
      · apply le_trans _ (le_max_right _ _)
        push_cast
        linarith

end Viterbo.Cap.PartE1
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE1
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
open Metric
variable {H : Type} {E : Type} {F : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-! ## The theorem -/
theorem exists_critical_cerami (l : H ≃L[ℝ] E × F) {Φ : H → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {e : F} (he : ‖e‖ = 1) {a b ρ ε R : ℝ}
    (ha : 0 < a) (hba : a ≤ b) (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hpos : ∀ z : F, ‖z‖ = ρ → 2 * a ≤ Φ (l.symm (0, z)))
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → Φ (l.symm (y, s • e)) ≤ a / 2)
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y, s)‖ → Φ (l.symm (y, s • e)) ≤ a / 2)
    (hupper : ∀ (y : E) (s : ℝ), 0 < s → ‖(y, s)‖ < R → Φ (l.symm (y, s • e)) ≤ b)
    (hcerami : ∃ R₁ c₁ : ℝ, 0 < c₁ ∧ ∀ x, a ≤ Φ x → Φ x ≤ b → R₁ ≤ ‖x‖ →
      c₁ ≤ (1 + ‖x‖) * ‖gradient Φ x‖) :
    ∃ x : H, a ≤ Φ x ∧ Φ x ≤ b ∧ gradient Φ x = 0 := by
  by_contra! hn
  obtain ⟨R₁, c₁, hc₁, hcer⟩ := hcerami
  obtain ⟨δ, hδ, hgrad⟩ := exists_weighted_lower hΦ hn hc₁ hcer
  let B := ‖l.symm.toContinuousLinearMap‖ * R
  let T := b - a + 1
  let M := (1 + B) * Real.exp (2 * T / δ) + 1
  have hR0 : 0 < R := hρ.trans hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨V, K, L, hVs, hV, hL, hlin, hdec, hfix, hrate⟩ :=
    exists_wcutoff_field hΦ ha hδ hM hgrad
  obtain ⟨η, hη, hηfix, hηlow⟩ := exists_wdescent_map hV hVs
    (hΦ.differentiable (by simp)) hdec hδ hT (show b - T ≤ a by dsimp [T]; linarith)
    hL hlin (le_refl M) hrate
  let ψ : E × F → E × F := l ∘ η ∘ l.symm
  have hψ : ContDiff ℝ ∞ ψ := l.contDiff.comp (hη.comp l.symm.contDiff)
  have hψeq (y : E) (s : ℝ) (hx : Φ (l.symm (y, s • e)) ≤ a / 2) :
      ψ (y, s • e) = (y, s • e) := by
    simp only [ψ, Function.comp_apply, hηfix _ (hfix _ hx), l.apply_symm_apply]
  obtain ⟨y, s, hs, hys, hfst, hsnd⟩ := OAI.SmoothLinking.sphere_linking hψ he hρ hε hR
    (fun y s hs heps => hψeq y s (hnear y s hs heps))
    (fun y s hs hnorm => hψeq y s (hfar y s hs hnorm))
  have hncone : ‖(y, s • e)‖ = ‖(y, s)‖ := by
    simp only [Prod.norm_def, norm_smul, he, mul_one, Real.norm_eq_abs]
  have hxB : ‖l.symm (y, s • e)‖ ≤ B :=
    (l.symm.toContinuousLinearMap.le_opNorm _).trans (by
      rw [hncone]
      exact mul_le_mul_of_nonneg_left hys.le (norm_nonneg l.symm.toContinuousLinearMap))
  have hlow := hηlow (l.symm (y, s • e)) hxB (hupper y s hs hys)
  have hhigh := hpos (ψ (y, s • e)).2 hsnd
  have heq : l.symm (0, (ψ (y, s • e)).2) = η (l.symm (y, s • e)) := by
    rw [← hfst]
    change l.symm (ψ (y, s • e)) = _
    simp only [ψ, Function.comp_apply, l.symm_apply_apply]
  rw [heq] at hhigh
  linarith

end Viterbo.Cap.PartE1
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {H : Type} {E : Type} {F : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-!
# Blueprint: `c_EHZ` extends to a symplectic capacity (HKO p. 2)

Target: `Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ`.

Route (see `proofs/capacity/BRIEF.md` in the mission repo):
* the capacity is the envelope `c(U) = ⨆ {cEHZ K : K convex domain, K ↪ U}`;
* everything reduces to (A) `cEHZ_le_of_hse`: `K ↪ L` between convex domains gives
  `cEHZ K ≤ cEHZ L`, proved by a Hofer–Zehnder argument on OpenAI's Galerkin engine
  (`OAI.FourierPolynomial`, `OAI.HamiltonianPeriodic`), with
  - linking along a trigonometric approximation of a minimal characteristic of `L` (Parts W, C),
  - compactness from the identity `Φ = ∫ (⟨∇H x, x⟩/2 - H x)` and a homogeneous limit (Parts E1, E2a),
  - mollified gauges for smoothness (Part M) and slow profiles on `K` (Part K).
-/
/-! ## Shared definitions -/
/-! ## Part E1: the linking lemma under a Cerami condition (finite dimension) -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
/-! ## Parts E2a, E2b: the Galerkin engine -/


/-! ## Part C: the cone estimate from a lower bound `H ≥ α gauge_L² - C₀` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part W: a trigonometric loop beating `α > c_EHZ(L)` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
/-! ## Part M: mollified gauges -/














end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part K: profiles of a mollified gauge on `K` have only constant `1`-periodic orbits -/

/-! ## Part A1: the bridge from a symplectic embedding of convex domains -/

/-! ## Part A2: one-variable profiles -/


/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

/-! ## Part P: the envelope capacity and the target -/

end Viterbo.Cap
end
end

theorem solution : type_of% @Viterbo.Cap.PartE1.exists_critical_cerami := @Viterbo.Cap.PartE1.exists_critical_cerami
