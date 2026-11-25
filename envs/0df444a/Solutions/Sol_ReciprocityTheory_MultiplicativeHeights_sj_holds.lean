-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sj_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:14.435803+00:00
-- url     : https://prove2.me/submissions/b7b25341-2cde-4e41-ae18-d744bc7c2260

import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormEvalZeroLeCircleAverage
import Definitions.Def_ReciprocityTheory_SemistableReduction_SjHolds
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coe_rotS
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_rotS
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_smul_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_eval_zero_le_circleAverage
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_rotS
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_inner_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hLin : SphereLinLogStatement) : SJStatement := by
  intro n a f u hf hu hfu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := nontrivial_of_ne u 0 hu0
  haveI hprob : IsProbabilityMeasure (sphereProb n) := by
    unfold sphereProb
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
      exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    · rw [Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  have hT : (0:ℝ) < 2 * π := by positivity

  have hsp : Continuous (fun z : UnitSphereC n => spherePoint z) := by
    unfold spherePoint; fun_prop
  have hcont : Continuous (fun z : UnitSphereC n => MvPolynomial.eval (spherePoint z) f) :=
    (MvPolynomial.continuous_eval f).comp hsp
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨L, hL⟩ : ∃ L : UnitSphereC n → ℝ,
      L = fun z => Real.log ‖MvPolynomial.eval (spherePoint z) f‖ := ⟨_, rfl⟩
  have hLM : ∀ z, L z ≤ M := fun z => by
    rw [hL]
    exact (Real.log_le_self (norm_nonneg _)).trans (hM z (Set.mem_univ _))
  have hLmeas : Measurable L := by
    rw [hL]; exact hcont.norm.measurable.log

  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℂ (Fin n),
      c = WithLp.toLp 2 (fun i => starRingEnd ℂ (WithLp.ofLp u i)) := ⟨_, rfl⟩
  have hcn : ‖c‖ = 1 := by
    rw [← hu, hc, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcn; exact zero_ne_one hcn
  obtain ⟨hGint, hGeq⟩ := hLin n c hc0
  obtain ⟨G, hG⟩ : ∃ G : UnitSphereC n → ℝ,
      G = fun z => Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ := ⟨_, rfl⟩
  have hGint' : Integrable G (sphereProb n) := by rw [hG]; exact hGint
  have hGeq' : ∫ z, G z ∂(sphereProb n) = Real.log ‖c‖ - (harmonic (n - 1) : ℝ) / 2 := by
    rw [hG]; exact hGeq
  have hip : ∀ z : UnitSphereC n,
      ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖ = ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ := by
    intro z
    rw [hc]
    simp [PiLp.inner_apply, spherePoint, mul_comm]

  have hpoly : ∀ (w v : Fin n → ℂ) (ζ : ℂ) (p : MvPolynomial (Fin n) ℂ),
      (MvPolynomial.aeval (fun i => Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X) p).eval ζ =
        MvPolynomial.eval (fun i => w i + ζ * v i) p := by
    intro w v ζ p
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
      simp [hp]
      exact Or.inl (mul_comm _ _)

  have hcirc : ∀ z : UnitSphereC n, inner ℂ u (z : EuclideanSpace ℂ (Fin n)) ≠ 0 →
      IntegrableOn (fun θ => L (rotS hu θ z)) (Set.Ioc 0 (2 * π)) ∧
      2 * π * (Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ +
          (a : ℝ) * Real.log ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖) ≤
        ∫ θ in Set.Ioc 0 (2 * π), L (rotS hu θ z) := by
    intro z hz
    set s := inner ℂ u (z : EuclideanSpace ℂ (Fin n)) with hs
    set q : Polynomial ℂ := MvPolynomial.aeval (fun i => Polynomial.C (s * WithLp.ofLp u i) +
      Polynomial.C (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i) * Polynomial.X) f
      with hqdef
    have hq : ∀ ζ, q.eval ζ = MvPolynomial.eval (fun i => s * WithLp.ofLp u i +
        ζ * (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i)) f := fun ζ => by
      rw [hqdef]; exact hpoly _ _ _ _
    have hq0 : q.eval 0 = s ^ a * MvPolynomial.eval (WithLp.ofLp u) f := by
      rw [hq]; simp only [zero_mul, add_zero]
      exact eval_smul_of_isHomogeneous hf s _
    have hrot : ∀ θ : ℝ, spherePoint (rotS hu θ z) = fun i => s * WithLp.ofLp u i +
        circleMap 0 1 θ * (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i) := by
      intro θ
      funext i
      simp [spherePoint, coe_rotS, hs]
    have hqc : ∀ θ : ℝ, Real.log ‖q.eval (circleMap 0 1 θ)‖ = L (rotS hu θ z) := by
      intro θ
      simp only [hL]
      rw [hq, hrot]
    have hne : q.eval 0 ≠ 0 := by
      rw [hq0]; exact mul_ne_zero (pow_ne_zero _ hz) hfu
    have hJ := log_norm_eval_zero_le_circleAverage q hne
    have hci : CircleIntegrable (fun ζ => Real.log ‖q.eval ζ‖) 0 1 :=
      circleIntegrable_log_norm_meromorphicOn
        (fun x _ => (q.differentiable.analyticAt x).meromorphicAt)
    have hii : IntervalIntegrable (fun θ => L (rotS hu θ z)) MeasureTheory.volume 0 (2 * π) := by
      have := hci
      unfold CircleIntegrable at this
      simpa only [hqc] using this
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hii, ?_⟩
    rw [hq0, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hz))
      (norm_ne_zero_iff.2 hfu), Real.log_pow] at hJ
    unfold Real.circleAverage at hJ
    simp only [hqc, smul_eq_mul] at hJ
    rw [intervalIntegral.integral_of_le hT.le] at hJ
    have h2 := mul_le_mul_of_nonneg_left hJ hT.le
    rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at h2
    linarith

  obtain ⟨h, hh⟩ : ∃ h : UnitSphereC n → ℝ,
      h = fun z => M - Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ - (a : ℝ) * G z := ⟨_, rfl⟩
  have hae : ∀ᵐ (z : UnitSphereC n) ∂(sphereProb n), inner ℂ u (z : EuclideanSpace ℂ (Fin n)) ≠ 0 := by
    have := sphereProb_inner_eq_zero hu0
    exact ae_iff.2 (by simpa using this)
  have hC : ∀ᵐ (z : UnitSphereC n) ∂(sphereProb n), 0 ≤ h z ∧
      ∫⁻ θ in Set.Ioc 0 (2 * π), ENNReal.ofReal (M - L (rotS hu θ z)) ≤
        ENNReal.ofReal (2 * π) * ENNReal.ofReal (h z) := by
    filter_upwards [hae] with z hz
    obtain ⟨hint, hJ⟩ := hcirc z hz
    have hGz : Real.log ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖ = G z := by rw [hG, hip]
    rw [hGz] at hJ
    have hint2 : IntegrableOn (fun θ => M - L (rotS hu θ z)) (Set.Ioc 0 (2 * π)) :=
      (integrable_const M).sub hint
    have hI : ∫ θ in Set.Ioc 0 (2 * π), (M - L (rotS hu θ z)) =
        2 * π * M - ∫ θ in Set.Ioc 0 (2 * π), L (rotS hu θ z) := by
      rw [integral_sub (integrable_const M) hint, integral_const]
      simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT.le, smul_eq_mul, Real.pi_pos.le]
    have hnn : 0 ≤ ∫ θ in Set.Ioc 0 (2 * π), (M - L (rotS hu θ z)) :=
      setIntegral_nonneg measurableSet_Ioc (fun θ _ => sub_nonneg.2 (hLM _))
    have hhz : 2 * π * h z = 2 * π * M - 2 * π * (Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ +
        (a : ℝ) * G z) := by
      rw [hh]; ring
    refine ⟨?_, ?_⟩
    · have : 0 ≤ 2 * π * h z := by linarith
      exact (mul_nonneg_iff_of_pos_left hT).1 this
    · rw [← ofReal_integral_eq_lintegral_ofReal hint2
        (ae_of_all _ fun θ => sub_nonneg.2 (hLM _)), ← ENNReal.ofReal_mul hT.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)

  obtain ⟨g, hg⟩ : ∃ g : UnitSphereC n → ENNReal, g = fun z => ENNReal.ofReal (M - L z) :=
    ⟨_, rfl⟩
  have hgmeas : Measurable g := by
    rw [hg]; exact (measurable_const.sub hLmeas).ennreal_ofReal
  have hrotInv : ∀ θ, ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) = ∫⁻ z, g z ∂(sphereProb n) :=
    fun θ => (measurePreserving_rotS hu θ).lintegral_comp hgmeas
  have hmeas2 : Measurable (fun p : ℝ × UnitSphereC n => g (rotS hu p.1 p.2)) :=
    hgmeas.comp (continuous_rotS hu).measurable
  have hswap : ∫⁻ θ in Set.Ioc 0 (2 * π), ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) =
      ∫⁻ z, (∫⁻ θ in Set.Ioc 0 (2 * π), g (rotS hu θ z)) ∂(sphereProb n) :=
    lintegral_lintegral_swap hmeas2.aemeasurable
  have hleft : ∫⁻ θ in Set.Ioc 0 (2 * π), ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) =
      ENNReal.ofReal (2 * π) * ∫⁻ z, g z ∂(sphereProb n) := by
    simp_rw [hrotInv]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hmain : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ∂(sphereProb n) ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z, ENNReal.ofReal (h z) ∂(sphereProb n) := by
    rw [← hleft, hswap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hC] with z hz
    simp only [hg]
    exact hz.2
  have hglint : ∫⁻ z, g z ∂(sphereProb n) ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂(sphereProb n) :=
    by
      have h0 : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 hT).ne'
      have h1 : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
      first
        | exact (ENNReal.mul_le_mul_iff_right h0 h1).1 hmain
        | exact (ENNReal.mul_le_mul_iff_left h0 h1).1 hmain
        | exact (ENNReal.mul_le_mul_left h0 h1).1 hmain
        | exact ENNReal.le_of_mul_le_mul_left hmain h0 h1
  have hhint : Integrable h (sphereProb n) := by
    rw [hh]; exact ((integrable_const _).sub (integrable_const _)).sub (hGint'.const_mul _)
  have hfin : ∫⁻ z, g z ∂(sphereProb n) ≠ ⊤ := (hglint.trans_lt hhint.lintegral_lt_top).ne
  have hg0 : ∀ z, 0 ≤ M - L z := fun z => sub_nonneg.2 (hLM z)
  have hgint : Integrable (fun z => M - L z) (sphereProb n) := by
    have := integrable_toReal_of_lintegral_ne_top hgmeas.aemeasurable hfin
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [hg]
    exact ENNReal.toReal_ofReal (hg0 z)
  have hLint : Integrable L (sphereProb n) := by
    have := (integrable_const M).sub hgint
    refine this.congr (ae_of_all _ fun z => ?_)
    simp

  have hh0 : 0 ≤ᵐ[sphereProb n] h := by
    filter_upwards [hC] with z hz
    exact hz.1
  have hint_g : ∫ z, (M - L z) ∂(sphereProb n) ≤ ∫ z, h z ∂(sphereProb n) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgint.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hh0 hhint.aestronglyMeasurable]
    apply ENNReal.toReal_mono hhint.lintegral_lt_top.ne
    simpa only [hg] using hglint
  have hIh : ∫ z, h z ∂(sphereProb n) = M - Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ -
      (a : ℝ) * ∫ z, G z ∂(sphereProb n) := by
    simp only [hh]
    rw [integral_sub (integrable_const _) (hGint'.const_mul _), integral_const, integral_const_mul]
    simp
  rw [hGeq', hcn, Real.log_one] at hIh
  have hIg : ∫ z, (M - L z) ∂(sphereProb n) = M - ∫ z, L z ∂(sphereProb n) := by
    rw [integral_sub (integrable_const _) hLint, integral_const]
    simp
  refine ⟨by rw [hL] at hLint; exact hLint, ?_⟩
  have hfin2 : ∫ z, L z ∂(sphereProb n) =
      ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) f‖ ∂(sphereProb n) := by rw [hL]
  rw [← hfin2]
  linarith
end ReciprocityTheory.MultiplicativeHeights
