-- Prove2me | solution 1 for WeilTypeCycles.periodic_closed_form_exact_iff_average_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:56:05.159567+00:00
-- url     : https://prove2.me/submissions/aca904d9-ed6c-403f-8612-d32e7ba9c431

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped ContDiff

noncomputable section
set_option autoImplicit false

section
set_option backward.isDefEq.respectTransparency true

open ContinuousAlternatingMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CartanConstantVectorAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

def contraction (v : E) : (E [⋀^Fin (k+1)]→L[ℝ] ℂ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ (E [⋀^Fin k]→L[ℝ] ℂ) v).comp
    curryLeftLI.toContinuousLinearMap

lemma contraction_apply (v : E) (w : E [⋀^Fin (k+1)]→L[ℝ] ℂ) :
    contraction v w=w.curryLeft v := rfl

lemma remove_cons (v : E) (u : Fin (k+1) → E) (i : Fin (k+1)) :
    Fin.removeNth i.succ (Fin.cons v u : Fin (k+2) → E)=
      (Fin.cons v (Fin.removeNth i u) : Fin (k+1) → E) := by
  funext j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [Fin.removeNth]
  · simp [Fin.removeNth,Fin.succ_succAbove_succ]

lemma algebraic_cartan (F : E →L[ℝ] E [⋀^Fin (k+1)]→L[ℝ] ℂ) (v : E) :
    alternatizeUncurryFin ((contraction v).comp F)+
      (alternatizeUncurryFin F).curryLeft v=F v := by
  ext u
  change alternatizeUncurryFin ((contraction v).comp F) u+
    alternatizeUncurryFin F (Fin.cons v u)=F v u
  rw [alternatizeUncurryFin_apply,alternatizeUncurryFin_apply,
    Fin.sum_univ_succ (n := k+1)]
  simp only [Fin.val_zero,pow_zero,one_smul,Fin.cons_zero,Fin.removeNth_zero,Fin.tail_cons,
    Fin.val_succ,Fin.cons_succ,remove_cons,ContinuousLinearMap.comp_apply,contraction_apply,
    curryLeft_apply_apply,pow_succ,mul_neg_one,neg_smul]
  rw [Finset.sum_neg_distrib]
  simp only [Matrix.vecCons,neg_one_smul]
  abel

lemma cartan (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ) (x v : E)
    (hw : DifferentiableAt ℝ w x) :
    extDeriv (fun y => (w y).curryLeft v) x+(extDeriv w x).curryLeft v=
      fderiv ℝ w x v := by
  have hd : fderiv ℝ (fun y => (w y).curryLeft v) x=
      (contraction v).comp (fderiv ℝ w x) :=
    ((contraction v).hasFDerivAt.comp x hw.hasFDerivAt).fderiv
  unfold extDeriv
  rw [hd]
  exact algebraic_cartan (fderiv ℝ w x) v

lemma closed_directional_derivative_exact (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : Differentiable ℝ w) (hc : ∀ x,extDeriv w x=0) (v : E) :
    extDeriv (fun y => (w y).curryLeft v) = fun x => fderiv ℝ w x v := by
  funext x
  have h := cartan w x v (hw x)
  simpa only [hc,curryLeft_zero,ContinuousLinearMap.zero_apply,add_zero] using h

end CartanConstantVectorAux
end

section
set_option backward.isDefEq.respectTransparency true

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CompactParametricIntegralAux
variable {E : Type} {B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

lemma hasFDerivAt_integral (F : E → ℝ → B) (F' : E → ℝ → E →L[ℝ] B)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x t,HasFDerivAt (fun y => F y t) (F' x t) x) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1,F y t)
      (∫ t in (0 : ℝ)..1,F' x t) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn hF'.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x 1) (bound := fun _ => C) (ball_mem_nhds x zero_lt_one)
  · apply Filter.Eventually.of_forall
    intro y
    exact ((hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with t ht
    intro y hy
    apply hC (y,t)
    refine ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy)),?_⟩
    have ht' : 0 < t ∧ t ≤ 1 := by simpa [uIoc_of_le zero_le_one] using ht
    exact ⟨ht'.1.le,ht'.2⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with t _
    intro y _
    exact hd y t

def integral (F : E × ℝ → B) (x : E) : B := ∫ t in (0 : ℝ)..1,F (x,t)

def partialFDeriv (F : E × ℝ → B) (p : E × ℝ) : E →L[ℝ] B :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

lemma partial_smooth (F : E × ℝ → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialFDeriv F) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const

lemma partial_derivative (F : E × ℝ → B) (hF : ContDiff ℝ ∞ F) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => F (y,t)) (partialFDeriv F (x,t)) x := by
  have hi : HasFDerivAt (fun y : E => (y,t)) (ContinuousLinearMap.inl ℝ E ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact (hF.differentiable (by simp) (x,t)).hasFDerivAt.comp x hi

lemma integral_derivative (F : E × ℝ → B) (hF : ContDiff ℝ ∞ F) (x : E) :
    HasFDerivAt (integral F) (integral (partialFDeriv F) x) x :=
  hasFDerivAt_integral (fun y t => F (y,t)) (fun y t => partialFDeriv F (y,t))
    hF.continuous (partial_smooth F hF).continuous (partial_derivative F hF) x

lemma integral_contDiff_nat (n : ℕ) (F : E × ℝ → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (integral F) := by
  induction n generalizing B with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact Differentiable.continuous (𝕜 := ℝ) (fun x => (integral_derivative F hF x).differentiableAt)
  | succ n ih =>
    rw [show ((n+1 : ℕ) : WithTop ℕ∞)=(n : WithTop ℕ∞)+1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (integral_derivative F hF x).differentiableAt,?_,?_⟩
    · simp
    · have he : fderiv ℝ (integral F)=integral (partialFDeriv F) :=
        funext (fun x => (integral_derivative F hF x).fderiv)
      rw [he]
      exact ih (partialFDeriv F) (partial_smooth F hF)

lemma integral_smooth (F : E × ℝ → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (integral F) := contDiff_infty.mpr (fun n => integral_contDiff_nat n F hF)

end CompactParametricIntegralAux
end

section
set_option backward.isDefEq.respectTransparency true

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CompactSetParametricIntegralAux
variable {E T : Type} {B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [MeasurableSpace T] [BorelSpace T]
  [SecondCountableTopology T]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  (μ : Measure T) [IsFiniteMeasureOnCompacts μ] (K : Set T)

lemma hasFDerivAt_integral (hK : IsCompact K) (F : E → T → B) (F' : E → T → E →L[ℝ] B)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x t,HasFDerivAt (fun y => F y t) (F' x t) x) (x : E) :
    HasFDerivAt (fun y => ∫ t in K,F y t ∂μ) (∫ t in K,F' x t ∂μ) x := by
  letI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn hF'.continuousOn
  apply _root_.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x 1) (bound := fun _ => C) (ball_mem_nhds x zero_lt_one)
  · apply Filter.Eventually.of_forall
    intro y
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ContinuousOn.integrableOn_compact hK
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact hC (y,t) ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy)),ht⟩
  · exact integrable_const C
  · filter_upwards [] with t
    intro y _
    exact hd y t

def integral (F : E × T → B) (x : E) : B := ∫ t in K,F (x,t) ∂μ

def partialFDeriv (F : E × T → B) (p : E × T) : E →L[ℝ] B :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E T)

lemma partial_smooth (F : E × T → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialFDeriv F) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const

lemma partial_derivative (F : E × T → B) (hF : ContDiff ℝ ∞ F) (x : E) (t : T) :
    HasFDerivAt (fun y => F (y,t)) (partialFDeriv F (x,t)) x := by
  have hi : HasFDerivAt (fun y : E => (y,t)) (ContinuousLinearMap.inl ℝ E T) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact (hF.differentiable (by simp) (x,t)).hasFDerivAt.comp x hi

lemma integral_derivative (hK : IsCompact K) (F : E × T → B) (hF : ContDiff ℝ ∞ F) (x : E) :
    HasFDerivAt (integral μ K F) (integral μ K (partialFDeriv F) x) x :=
  hasFDerivAt_integral μ K hK (fun y t => F (y,t)) (fun y t => partialFDeriv F (y,t))
    hF.continuous (partial_smooth F hF).continuous (partial_derivative F hF) x

lemma integral_contDiff_nat (hK : IsCompact K) (n : ℕ) (F : E × T → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (integral μ K F) := by
  induction n generalizing B with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact Differentiable.continuous (𝕜 := ℝ) (fun x => (integral_derivative μ K hK F hF x).differentiableAt)
  | succ n ih =>
    rw [show ((n+1 : ℕ) : WithTop ℕ∞)=(n : WithTop ℕ∞)+1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (integral_derivative μ K hK F hF x).differentiableAt,?_,?_⟩
    · simp
    · have he : fderiv ℝ (integral μ K F)=integral μ K (partialFDeriv F) :=
        funext (fun x => (integral_derivative μ K hK F hF x).fderiv)
      rw [he]
      exact ih (partialFDeriv F) (partial_smooth F hF)

lemma integral_smooth (hK : IsCompact K) (F : E × T → B) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (integral μ K F) :=
  contDiff_infty.mpr (fun n => integral_contDiff_nat μ K hK n F hF)

end CompactSetParametricIntegralAux
end

section
set_option backward.isDefEq.respectTransparency true

open ContinuousAlternatingMap MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TranslationHomotopyAux
open CartanConstantVectorAux
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {k : ℕ}

def homotopy (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ) (v x : E) : E [⋀^Fin k]→L[ℝ] ℂ :=
  ∫ t in (0 : ℝ)..1,(w (x+t • v)).curryLeft v

lemma smooth_integrand (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (v : E) :
    ContDiff ℝ ∞ (fun p : E × ℝ => (w (p.1+p.2 • v)).curryLeft v) :=
  (contraction v).contDiff.comp (hw.comp (contDiff_fst.add (contDiff_snd.smul contDiff_const)))

lemma homotopy_smooth (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (v : E) : ContDiff ℝ ∞ (homotopy w v) :=
  CompactParametricIntegralAux.integral_smooth _ (smooth_integrand w hw v)

lemma derivative_integrand_continuous (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (v : E) :
    Continuous (fun p : E × ℝ => (contraction v).comp (fderiv ℝ w (p.1+p.2 • v))) :=
  continuous_const.clm_comp ((hw.continuous_fderiv (by simp)).comp
    (continuous_fst.add (continuous_snd.smul continuous_const)))

lemma homotopy_fderiv (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (v x : E) :
    fderiv ℝ (homotopy w v) x=
      ∫ t in (0 : ℝ)..1,(contraction v).comp (fderiv ℝ w (x+t • v)) := by
  apply HasFDerivAt.fderiv
  apply CompactParametricIntegralAux.hasFDerivAt_integral
    (fun y t => (w (y+t • v)).curryLeft v)
    (fun y t => (contraction v).comp (fderiv ℝ w (y+t • v)))
    (smooth_integrand w hw v).continuous (derivative_integrand_continuous w hw v)
  intro y t
  have hd : HasFDerivAt (fun z => w (z+t • v)) (fderiv ℝ w (y+t • v)) y := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using!
      ((hw.differentiable (by simp) (y+t • v)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).add_const (t • v)))
  exact (contraction v).hasFDerivAt.comp y hd

lemma translation_formula (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (v x : E) :
    extDeriv (homotopy w v) x+homotopy (extDeriv w) v x=w (x+v)-w x := by
  letI : NormedAddCommGroup (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℂ) := inferInstance
  have hi : IntervalIntegrable
      (fun t : ℝ => ((contraction (k := k) v).comp (fderiv ℝ w (x+t • v)) :
        E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℂ)) volume 0 1 :=
    ((derivative_integrand_continuous w hw v).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hd : extDeriv (homotopy w v) x=
      ∫ t in (0 : ℝ)..1,alternatizeUncurryFin ((contraction v).comp (fderiv ℝ w (x+t • v))) := by
    rw [extDeriv,homotopy_fderiv w hw]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (𝕜 := ℝ) (E := E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℂ)
      (F := E [⋀^Fin (k+1)]→L[ℝ] ℂ)
      (alternatizeUncurryFinCLM (n := k) ℝ E ℂ) hi).symm
  have hdi : IntervalIntegrable
      (fun t : ℝ => alternatizeUncurryFin ((contraction v).comp (fderiv ℝ w (x+t • v)))) volume 0 1 :=
    ((alternatizeUncurryFinCLM ℝ E ℂ).continuous.comp
      ((derivative_integrand_continuous w hw v).comp
        (continuous_const.prodMk continuous_id))).intervalIntegrable 0 1
  have hdc : Continuous (fun t : ℝ => (extDeriv w (x+t • v)).curryLeft v) := by
    exact (contraction (k := k+1) v).continuous.comp
      ((alternatizeUncurryFinCLM ℝ E ℂ).continuous.comp
        ((hw.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))))
  rw [hd,homotopy,← intervalIntegral.integral_add hdi (hdc.intervalIntegrable 0 1)]
  simp_rw [show ∀ t : ℝ,
    alternatizeUncurryFin ((contraction v).comp (fderiv ℝ w (x+t • v)))+
      (extDeriv w (x+t • v)).curryLeft v=fderiv ℝ w (x+t • v) v from
        fun t => algebraic_cartan (fderiv ℝ w (x+t • v)) v]
  have ht : (∫ t in (0 : ℝ)..1,fderiv ℝ w (x+t • v) v)=w (x+(1 : ℝ) • v)-w (x+(0 : ℝ) • v) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => w (x+t • v))
    · intro t _
      apply (hw.differentiable (by simp) (x+t • v)).hasFDerivAt.comp_hasDerivAt t
      simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const v |>.const_add x)
    · exact (((hw.continuous_fderiv (by simp)).comp
        (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const).intervalIntegrable 0 1
  simpa only [one_smul,zero_smul,add_zero] using ht

lemma closed_translation_exact (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) (hc : ∀ x,extDeriv w x=0) (v : E) :
    extDeriv (homotopy w v)=fun x => w (x+v)-w x := by
  funext x
  have h := translation_formula w hw v x
  simpa [homotopy,hc] using h

lemma homotopy_periodic (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ) (v z : E)
    (hz : ∀ x,w (x+z)=w x) (x : E) : homotopy w v (x+z)=homotopy w v x := by
  unfold homotopy
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show x+z+t • v=(x+t • v)+z by abel,hz]

end TranslationHomotopyAux
end

section
set_option backward.isDefEq.respectTransparency true

open ContinuousAlternatingMap
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace JointTranslationHomotopyAux
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {k : ℕ}

lemma integrand_smooth (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun p : (E × E) × ℝ =>
      (w (p.1.1+p.2 • p.1.2)).curryLeft p.1.2) := by
  have ha : ContDiff ℝ ∞ (fun p : (E × E) × ℝ => p.1.1+p.2 • p.1.2) :=
    (contDiff_fst.comp contDiff_fst).add
      (contDiff_snd.smul (contDiff_snd.comp contDiff_fst))
  exact (curryLeftLI.toContinuousLinearMap.contDiff.comp (hw.comp ha)).clm_apply
    (contDiff_snd.comp contDiff_fst)

lemma homotopy_joint_smooth (w : E → E [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun p : E × E => TranslationHomotopyAux.homotopy w p.2 p.1) :=
  CompactParametricIntegralAux.integral_smooth _ (integrand_smooth w hw)

end JointTranslationHomotopyAux
end

section
set_option backward.isDefEq.respectTransparency true

open Set MeasureTheory ContinuousAlternatingMap
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ParametricExteriorDerivativeAux
variable {E T : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [MeasurableSpace T] [BorelSpace T]
  [SecondCountableTopology T]
  {k : ℕ} (μ : Measure T) [IsFiniteMeasureOnCompacts μ] (K : Set T)

lemma extDeriv_integral (hK : IsCompact K)
    (F : E × T → E [⋀^Fin k]→L[ℝ] ℂ) (hF : ContDiff ℝ ∞ F) (x : E) :
    extDeriv (fun y => ∫ t in K,F (y,t) ∂μ) x =
      ∫ t in K,extDeriv (fun y => F (y,t)) x ∂μ := by
  have hi : IntegrableOn
      (fun t => CompactSetParametricIntegralAux.partialFDeriv F (x,t)) K μ :=
    ContinuousOn.integrableOn_compact hK
      (((CompactSetParametricIntegralAux.partial_smooth F hF).continuous).comp
        (continuous_const.prodMk continuous_id)).continuousOn
  unfold extDeriv
  have hd := (CompactSetParametricIntegralAux.integral_derivative μ K hK F hF x).fderiv
  unfold CompactSetParametricIntegralAux.integral at hd
  rw [hd]
  trans ∫ t in K,alternatizeUncurryFin (CompactSetParametricIntegralAux.partialFDeriv F (x,t)) ∂μ
  · exact ((alternatizeUncurryFinCLM (n := k) ℝ E ℂ).integral_comp_comm hi).symm
  apply integral_congr_ae
  filter_upwards [] with t
  rw [(CompactSetParametricIntegralAux.partial_derivative F hF x t).fderiv]

end ParametricExteriorDerivativeAux
end

section
set_option backward.isDefEq.respectTransparency true

open Set Function MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LatticeCellAverageAux
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Lattice (m : ℕ) := Fin m → AddSubgroup.zmultiples (1 : ℝ)

def cell (a : Fin m → ℝ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ (fun i => Ioc (a i) (a i+1))

lemma component_unique (x a : ℝ) :
    ∃! c : AddSubgroup.zmultiples (1 : ℝ), c +ᵥ x ∈ Ioc a (a+1) := by
  have hbij : Bijective (codRestrict (fun n : ℤ => n • (1 : ℝ))
      (AddSubgroup.zmultiples (1 : ℝ)) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • (1 : ℝ))
      (zsmul_left_strictMono (zero_lt_one : (0 : ℝ)<1)).injective).bijective
  apply hbij.existsUnique_iff.mpr
  simpa only [add_comm x] using!
    existsUnique_add_zsmul_mem_Ioc (zero_lt_one : (0 : ℝ)<1) x a

lemma cell_fundamental (a : Fin m → ℝ) : IsAddFundamentalDomain (Lattice m) (cell a) volume := by
  apply IsAddFundamentalDomain.mk'
  · exact (MeasurableSet.univ_pi (fun i => measurableSet_Ioc)).nullMeasurableSet
  · intro x
    choose f hf using fun i : Fin m => (component_unique (x i) (a i)).exists
    refine ⟨f,?_,?_⟩
    · exact fun i _ => hf i
    · intro g hg
      funext i
      exact (component_unique (x i) (a i)).unique (hg i (mem_univ i)) (hf i)

lemma lattice_cast (c : Lattice m) : ∃ z : Fin m → ℤ, (fun i => ((c i : ℝ)))=fun i => (z i : ℝ) := by
  have h (i : Fin m) : ∃ z : ℤ, (z : ℝ)=(c i : ℝ) := by
    obtain ⟨z,hz⟩ := (AddSubgroup.mem_zmultiples_iff).mp (c i).property
    exact ⟨z,by simpa using hz⟩
  choose z hz using h
  exact ⟨z,funext (fun i => (hz i).symm)⟩

lemma cell_integral_eq (f : (Fin m → ℝ) → E)
    (hper : ∀ x (z : Fin m → ℤ), f (x+fun i => (z i : ℝ))=f x)
    (a b : Fin m → ℝ) : (∫ x in cell a, f x) = ∫ x in cell b, f x := by
  letI : VAddInvariantMeasure (Lattice m) (Fin m → ℝ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (fun i => (c i : ℝ)) s⟩
  apply (cell_fundamental a).setIntegral_eq (cell_fundamental b)
  intro c x
  obtain ⟨z,hz⟩ := lattice_cast c
  change f ((fun i => (c i : ℝ))+x)=f x
  rw [hz,add_comm]
  exact hper x z

lemma cell_translate_preimage (a : Fin m → ℝ) :
    (fun x => a+x) ⁻¹' cell a = cell (0 : Fin m → ℝ) := by
  ext x
  simp [cell,Pi.add_apply,add_lt_add_iff_left,add_le_add_iff_left]

lemma cell_zero_ae_cube : cell (0 : Fin m → ℝ) =ᵐ[volume] Icc (0 : Fin m → ℝ) 1 := by
  simpa only [cell,Pi.zero_apply,Pi.one_apply,zero_add,volume_pi] using
    (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := (0 : Fin m → ℝ)) (g := 1))

lemma integral_periodic_translate (f : (Fin m → ℝ) → E)
    (hper : ∀ x (z : Fin m → ℤ), f (x+fun i => (z i : ℝ))=f x)
    (a : Fin m → ℝ) :
    (∫ x in Icc (0 : Fin m → ℝ) 1, f (a+x)) =
      ∫ x in Icc (0 : Fin m → ℝ) 1, f x := by
  rw [← setIntegral_congr_set cell_zero_ae_cube,← setIntegral_congr_set cell_zero_ae_cube]
  have h := (measurePreserving_add_left (volume : Measure (Fin m → ℝ)) a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) f (cell a)
  rw [cell_translate_preimage] at h
  exact h.trans (cell_integral_eq f hper a 0)

end LatticeCellAverageAux
end

section
set_option backward.isDefEq.respectTransparency true

open ContinuousAlternatingMap MeasureTheory Set
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PeriodicDeRhamExactnessAux
variable {m k : ℕ}
abbrev Space (m : ℕ) := Fin m → ℝ
abbrev Form (m k : ℕ) := Space m [⋀^Fin k]→L[ℝ] ℂ

def Periodic (w : Space m → Form m k) : Prop :=
  ∀ x (z : Fin m → ℤ),w (x+fun i => (z i : ℝ))=w x

def average (w : Space m → Form m k) : Form m k :=
  ∫ x in Icc (0 : Space m) 1,w x

def averagedHomotopy (w : Space m → Form m (k+1)) (x : Space m) : Form m k :=
  ∫ v in Icc (0 : Space m) 1,TranslationHomotopyAux.homotopy w v x

lemma averagedHomotopy_smooth (w : Space m → Form m (k+1)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (averagedHomotopy w) :=
  CompactSetParametricIntegralAux.integral_smooth volume _ isCompact_Icc _
    (JointTranslationHomotopyAux.homotopy_joint_smooth w hw)

lemma averagedHomotopy_periodic (w : Space m → Form m (k+1)) (hp : Periodic w) :
    Periodic (averagedHomotopy w) := by
  intro x z
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  exact TranslationHomotopyAux.homotopy_periodic w v _ (fun y => hp y z) x

lemma integral_const_cell (c : Form m k) : (∫ _ in Icc (0 : Space m) 1,c)=c := by
  simp [Measure.real,Real.volume_Icc_pi]

lemma averagedHomotopy_derivative (w : Space m → Form m (k+1))
    (hw : ContDiff ℝ ∞ w) (hp : Periodic w) (hc : ∀ x,extDeriv w x=0) (x : Space m) :
    extDeriv (averagedHomotopy w) x=average w-w x := by
  unfold averagedHomotopy
  rw [ParametricExteriorDerivativeAux.extDeriv_integral volume _ isCompact_Icc _
    (JointTranslationHomotopyAux.homotopy_joint_smooth w hw)]
  simp_rw [TranslationHomotopyAux.closed_translation_exact w hw hc]
  have hi : IntegrableOn (fun v => w (x+v)) (Icc (0 : Space m) 1) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (hw.continuous.comp (continuous_const.add continuous_id)).continuousOn
  have hj : IntegrableOn (fun _ : Space m => w x) (Icc (0 : Space m) 1) :=
    ContinuousOn.integrableOn_compact isCompact_Icc continuous_const.continuousOn
  rw [integral_sub hi hj,LatticeCellAverageAux.integral_periodic_translate w hp,
    integral_const_cell]
  rfl

lemma average_extDeriv_zero (w : Space m → Form m k) (hw : ContDiff ℝ ∞ w)
    (hp : Periodic w) : average (extDeriv w)=0 := by
  have hF : ContDiff ℝ ∞ (fun p : Space m × Space m => w (p.1+p.2)) :=
    hw.comp (contDiff_fst.add contDiff_snd)
  have hconst : (fun x : Space m => ∫ t in Icc (0 : Space m) 1,w (x+t))=
      fun _ => average w :=
    funext (fun x => LatticeCellAverageAux.integral_periodic_translate w hp x)
  have h := ParametricExteriorDerivativeAux.extDeriv_integral volume
    (Icc (0 : Space m) 1) isCompact_Icc _ hF (0 : Space m)
  rw [hconst] at h
  simpa only [extDeriv,fderiv_const_apply,alternatizeUncurryFin,_root_.map_zero,
    fderiv_comp_add_right,zero_add,average] using h.symm

theorem exact_iff_average_zero (w : Space m → Form m (k+1))
    (hw : ContDiff ℝ ∞ w) (hp : Periodic w) (hc : ∀ x,extDeriv w x=0) :
    (∃ b : Space m → Form m k,ContDiff ℝ ∞ b ∧ Periodic b ∧ extDeriv b=w) ↔
      average w=0 := by
  constructor
  · rintro ⟨b,hb,hpb,rfl⟩
    exact average_extDeriv_zero b hb hpb
  · intro ha
    refine ⟨fun x => -averagedHomotopy w x,(averagedHomotopy_smooth w hw).neg,?_,?_⟩
    · intro x z
      dsimp only
      rw [averagedHomotopy_periodic w hp x z]
    · funext x
      have hn : extDeriv (fun x => -averagedHomotopy w x) x=
          -extDeriv (averagedHomotopy w) x := by
        simpa only [neg_one_smul,Pi.neg_def] using! (extDeriv_fun_smul (-1 : ℝ) (averagedHomotopy w) (x := x))
      rw [hn,averagedHomotopy_derivative w hw hp hc,ha]
      simp

end PeriodicDeRhamExactnessAux
end

theorem solution {m k : ℕ}
    (w : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x (z : Fin m → ℤ),w (x+fun i => (z i : ℝ))=w x)
    (hc : ∀ x,extDeriv w x=0) :
    (∃ b : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin k]→L[ℝ] ℂ,
      ContDiff ℝ ∞ b ∧ (∀ x (z : Fin m → ℤ),b (x+fun i => (z i : ℝ))=b x) ∧ extDeriv b=w) ↔
      (∫ x in Set.Icc (0 : Fin m → ℝ) 1,w x)=0 :=
  PeriodicDeRhamExactnessAux.exact_iff_average_zero w hw hp hc

#print axioms solution
