-- Prove2me | solution 1 for ProbEffIS.GE.ge_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:24:05.203109+00:00
-- url     : https://prove2.me/submissions/bc4105c7-2807-4a48-8d21-6d2d555dae2e

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.UB

variable {d : ℕ}

/-- An eventual bound on the moment generating function from a bound on `μ`. -/
lemma mgf_bound (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (θ : Rd d) (M : ℝ) (hM : μ θ < (M : EReal)) :
    ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) ∧
      ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) ≤ Real.exp (γ * M) := by
  have h := (h1.tendsto θ).eventually (gt_mem_nhds hM)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with γ hγ hγ0
  unfold scaledLogMGF at hγ
  set J := ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ θ y)) ∂(ν γ) with hJ_def
  have hγ' : (0:ℝ) < γ⁻¹ := inv_pos.2 hγ0
  have hJtop : J ≠ ⊤ := by
    intro hJ
    rw [hJ, ENNReal.log_top, EReal.coe_mul_top_of_pos hγ'] at hγ
    exact absurd hγ (not_lt.2 le_top)
  have hint : Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) := by
    refine ⟨(Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simpa [Real.enorm_eq_ofReal (Real.exp_pos _).le] using hJtop.lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le) hint.1]
  rw [← hJ_def]
  rcases eq_or_ne J 0 with h0 | h0
  · rw [h0]; simp only [ENNReal.toReal_zero]; positivity
  have hr : 0 < J.toReal := ENNReal.toReal_pos h0 hJtop
  rw [← ENNReal.ofReal_toReal hJtop, ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_lt_coe_iff] at hγ
  have : Real.log J.toReal < γ * M := by rw [inv_mul_lt_iff₀ hγ0] at hγ; exact hγ
  exact (Real.log_lt_iff_lt_exp hr |>.1 this).le

/-- Chernoff's bound for a scaled half-space. -/
lemma chernoff (P : Measure (Rd d)) [IsFiniteMeasure P] (γ : ℝ) (hγ : 0 < γ) (θ : Rd d) (c : ℝ)
    (hint : Integrable (fun y => Real.exp (inner ℝ θ y)) P) :
    (P {x | c ≤ inner ℝ θ (γ⁻¹ • x)}).toReal ≤
      (∫ y, Real.exp (inner ℝ θ y) ∂P) * Real.exp (-(γ * c)) := by
  have hA : MeasurableSet {x : Rd d | c ≤ inner ℝ θ (γ⁻¹ • x)} :=
    measurableSet_le measurable_const
      ((continuous_const.inner (continuous_const_smul γ⁻¹)).measurable)
  rw [← integral_mul_const, ← measureReal_def, ← integral_indicator_one hA]
  refine integral_mono ((integrable_const 1).indicator hA) (hint.mul_const _) fun x => ?_
  by_cases hx : x ∈ {x : Rd d | c ≤ inner ℝ θ (γ⁻¹ • x)}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← Real.exp_add]
    apply Real.one_le_exp
    have h0 : c ≤ inner ℝ θ (γ⁻¹ • x) := hx
    rw [inner_smul_right] at h0
    have := mul_le_mul_of_nonneg_left h0 hγ.le
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at this
    linarith
  · rw [Set.indicator_of_notMem hx]; positivity

lemma chernoff_ev (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (θ : Rd d) (M : ℝ) (hM : μ θ < (M : EReal))
    (c : ℝ) :
    ∀ᶠ γ in atTop, (ν γ {x | c ≤ inner ℝ θ (γ⁻¹ • x)}).toReal ≤ Real.exp (γ * (M - c)) := by
  filter_upwards [mgf_bound ν μ h1 θ M hM, hν, eventually_gt_atTop (0:ℝ)]
    with γ ⟨hint, hle⟩ hP hγ
  calc _ ≤ (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * Real.exp (-(γ * c)) :=
        chernoff (ν γ) γ hγ θ c hint
    _ ≤ Real.exp (γ * M) * Real.exp (-(γ * c)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf


lemma dir_bound (μ : Rd d → EReal) (h1z : (0 : Rd d) ∈ interior (dom μ)) :
    ∃ τ > 0, ∀ (k : Fin d) (σ : ℝ), |σ| = 1 →
      μ (EuclideanSpace.single k (σ * τ)) < ⊤ := by
  obtain ⟨t, ht, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h1z
  refine ⟨t / 2, by positivity, fun k σ hσ => ?_⟩
  have hmem : EuclideanSpace.single k (σ * (t / 2)) ∈ Metric.ball (0 : Rd d) t := by
    rw [Metric.mem_ball, dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_mul, hσ,
      one_mul, abs_of_pos (by positivity)]
    linarith
  exact (interior_subset (hball hmem) : _ ∈ dom μ)

/-- Exponential tightness. -/
lemma tight (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (z : ℝ) :
    ∃ R : ℝ, ∀ᶠ γ in atTop,
      (ν γ {x | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) R}).toReal ≤
        (2 * d : ℝ) * Real.exp (-(γ * z)) := by
  obtain ⟨τ, hτ, hdir⟩ := dir_bound μ h1.zero_mem
  have hp : ∀ k : Fin d, ∃ M : ℝ, μ (EuclideanSpace.single k (1 * τ)) < (M : EReal) := fun k =>
    let ⟨M, hM, _⟩ := EReal.lt_iff_exists_real_btwn.1 (hdir k 1 (by norm_num)); ⟨M, hM⟩
  have hn : ∀ k : Fin d, ∃ M : ℝ, μ (EuclideanSpace.single k (-1 * τ)) < (M : EReal) := fun k =>
    let ⟨M, hM, _⟩ := EReal.lt_iff_exists_real_btwn.1 (hdir k (-1) (by norm_num)); ⟨M, hM⟩
  choose Mp hMp using hp
  choose Mn hMn using hn
  set Mmax : ℝ := ∑ k, (|Mp k| + |Mn k|) with hMmax
  have hMp_le : ∀ k, Mp k ≤ Mmax := fun k => by
    have := Finset.single_le_sum (f := fun k => |Mp k| + |Mn k|)
      (fun k _ => by positivity) (Finset.mem_univ k)
    linarith [le_abs_self (Mp k), abs_nonneg (Mn k)]
  have hMn_le : ∀ k, Mn k ≤ Mmax := fun k => by
    have := Finset.single_le_sum (f := fun k => |Mp k| + |Mn k|)
      (fun k _ => by positivity) (Finset.mem_univ k)
    linarith [le_abs_self (Mn k), abs_nonneg (Mp k)]
  set ρ : ℝ := max 0 ((Mmax + z) / τ) with hρ
  have hρ0 : 0 ≤ ρ := le_max_left _ _
  have hτρ : Mmax + z ≤ τ * ρ := by
    have := le_max_right 0 ((Mmax + z) / τ)
    rw [← hρ, div_le_iff₀ hτ] at this; linarith
  refine ⟨(d + 1) * ρ, ?_⟩
  have hk : ∀ k : Fin d, ∀ᶠ γ in atTop,
      (ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (1 * τ)) (γ⁻¹ • x)}).toReal ≤
        Real.exp (-(γ * z)) ∧
      (ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (-1 * τ)) (γ⁻¹ • x)}).toReal ≤
        Real.exp (-(γ * z)) := by
    intro k
    filter_upwards [chernoff_ev ν hν μ h1 _ (Mp k) (hMp k) (τ * ρ),
      chernoff_ev ν hν μ h1 _ (Mn k) (hMn k) (τ * ρ), eventually_gt_atTop (0:ℝ)]
      with γ h1' h2' hγ
    constructor
    · refine h1'.trans (Real.exp_le_exp.2 ?_)
      nlinarith [hMp_le k]
    · refine h2'.trans (Real.exp_le_exp.2 ?_)
      nlinarith [hMn_le k]
  filter_upwards [(eventually_all_finset Finset.univ).2 (fun k _ => hk k), hν] with γ hγ hP
  have hsub : {x : Rd d | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) ((d + 1) * ρ)} ⊆
      ⋃ k ∈ (Finset.univ : Finset (Fin d)),
        ({x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (1 * τ)) (γ⁻¹ • x)} ∪
         {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (-1 * τ)) (γ⁻¹ • x)}) := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or,
      not_le, Finset.mem_univ] at hcon
    have hcoord : ∀ k, |(γ⁻¹ • x) k| ≤ ρ := by
      intro k
      obtain ⟨ha, hb⟩ := hcon k trivial
      rw [EuclideanSpace.inner_single_left] at ha hb
      simp only [map_mul, map_one, map_neg, RCLike.conj_to_real] at ha hb
      rw [abs_le]; constructor <;> nlinarith
    have hnorm : ‖γ⁻¹ • x‖ ≤ (d + 1) * ρ := by
      have h2 : ‖γ⁻¹ • x‖ ^ 2 ≤ ((d + 1) * ρ) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc ∑ i, ((γ⁻¹ • x) i) ^ 2 ≤ ∑ _i : Fin d, ρ ^ 2 :=
              Finset.sum_le_sum fun i _ => by
                have := hcoord i
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = d * ρ ^ 2 := by simp
          _ ≤ ((d + 1) * ρ) ^ 2 := by nlinarith [sq_nonneg ρ, sq_nonneg ((d:ℝ) * ρ)]
      exact le_of_sq_le_sq (by simpa using h2) (by positivity)
    linarith
  calc (ν γ {x | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) ((d + 1) * ρ)}).toReal
      ≤ (∑ k ∈ (Finset.univ : Finset (Fin d)),
          (ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (1 * τ)) (γ⁻¹ • x)} +
           ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (-1 * τ)) (γ⁻¹ • x)})).toReal := by
        apply ENNReal.toReal_mono
        · exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
        · exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun k _ => measure_union_le _ _))
    _ = ∑ k ∈ (Finset.univ : Finset (Fin d)),
          ((ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (1 * τ)) (γ⁻¹ • x)}).toReal +
           (ν γ {x | τ * ρ ≤ inner ℝ (EuclideanSpace.single k (-1 * τ)) (γ⁻¹ • x)}).toReal) := by
        rw [ENNReal.toReal_sum fun _ _ => ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩]
        exact Finset.sum_congr rfl fun k _ => ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin d)), (Real.exp (-(γ * z)) + Real.exp (-(γ * z))) :=
        Finset.sum_le_sum fun k hk => add_le_add (hγ k hk).1 (hγ k hk).2
    _ = (2 * d : ℝ) * Real.exp (-(γ * z)) := by simp; ring


/-- The local exponential bound near a point of positive rate. -/
lemma local_ub (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (x : Rd d) (z : ℝ) (hz : (z : EReal) < rate μ x) :
    ∃ δ > 0, ∀ᶠ γ in atTop,
      (ν γ {x' | γ⁻¹ • x' ∈ Metric.ball x δ}).toReal ≤ Real.exp (-(γ * z)) := by
  obtain ⟨θ, hθ⟩ := lt_iSup_iff.1 hz
  have hμlt : μ θ < ((inner ℝ θ x - z : ℝ) : EReal) := by
    induction h : μ θ using EReal.rec with
    | bot => exact EReal.bot_lt_coe _
    | top => rw [h, EReal.sub_top] at hθ; exact absurd hθ (not_lt.2 bot_le)
    | coe m =>
      rw [h, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hθ
      rw [EReal.coe_lt_coe_iff]; linarith
  obtain ⟨M, hM1, hM2⟩ := EReal.lt_iff_exists_real_btwn.1 hμlt
  rw [EReal.coe_lt_coe_iff] at hM2
  set g := inner ℝ θ x - z - M with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨g / (2 * (‖θ‖ + 1)), by positivity, ?_⟩
  filter_upwards [chernoff_ev ν hν μ h1 θ M hM1 (inner ℝ θ x - g / 2), hν,
    eventually_gt_atTop (0:ℝ)] with γ hγ hP hγ0
  have hsub : {x' : Rd d | γ⁻¹ • x' ∈ Metric.ball x (g / (2 * (‖θ‖ + 1)))} ⊆
      {x' | inner ℝ θ x - g / 2 ≤ inner ℝ θ (γ⁻¹ • x')} := by
    intro x' hx'
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] at hx' ⊢
    have h1' : inner ℝ θ (γ⁻¹ • x') = inner ℝ θ x + inner ℝ θ (γ⁻¹ • x' - x) := by
      rw [inner_sub_right]; ring
    have h2' : |inner ℝ θ (γ⁻¹ • x' - x)| ≤ ‖θ‖ * ‖γ⁻¹ • x' - x‖ := abs_real_inner_le_norm _ _
    have h3' : ‖θ‖ * ‖γ⁻¹ • x' - x‖ ≤ ‖θ‖ * (g / (2 * (‖θ‖ + 1))) :=
      mul_le_mul_of_nonneg_left hx'.le (norm_nonneg _)
    have h4' : ‖θ‖ * (g / (2 * (‖θ‖ + 1))) ≤ g / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg θ]
    have := neg_abs_le (inner ℝ θ (γ⁻¹ • x' - x))
    linarith
  calc (ν γ {x' | γ⁻¹ • x' ∈ Metric.ball x (g / (2 * (‖θ‖ + 1)))}).toReal
      ≤ (ν γ {x' | inner ℝ θ x - g / 2 ≤ inner ℝ θ (γ⁻¹ • x')}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ Real.exp (γ * (M - (inner ℝ θ x - g / 2))) := hγ
    _ ≤ Real.exp (-(γ * z)) := by
        apply Real.exp_le_exp.2
        have : M - (inner ℝ θ x - g / 2) = -z - g / 2 := by rw [hg]; ring
        rw [this]; nlinarith

/-- The upper bound for a closed set, in exponential form. -/
lemma key_ub (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (F : Set (Rd d)) (hF : IsClosed F) (z : ℝ)
    (hz : (z : EReal) < rateOn μ F) :
    ∀ η > 0, ∀ᶠ γ in atTop, (ν γ {x | γ⁻¹ • x ∈ F}).toReal ≤ Real.exp (γ * (-z + η)) := by
  intro η hη
  obtain ⟨R, hR⟩ := tight ν hν μ h1 z
  set K := Metric.closedBall (0 : Rd d) R ∩ F with hK_def
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right hF
  have hloc : ∀ x ∈ K, ∃ δ > 0, ∀ᶠ γ in atTop,
      (ν γ {x' | γ⁻¹ • x' ∈ Metric.ball x δ}).toReal ≤ Real.exp (-(γ * z)) :=
    fun x hx => local_ub ν hν μ h1 x z (lt_of_lt_of_le hz (iInf₂_le x hx.2))
  choose! δ hδpos hδ using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (δ x))
    (fun x hx => Metric.ball_mem_nhds x (hδpos x hx))
  have hC : ∀ᶠ γ in atTop, (2 * d + t.card : ℝ) ≤ Real.exp (γ * η) :=
    (Real.tendsto_exp_atTop.comp (Tendsto.atTop_mul_const hη tendsto_id)).eventually_ge_atTop _
  filter_upwards [hR, (eventually_all_finset t).2 (fun x hx => hδ x (htK x hx)), hC, hν]
    with γ hRγ hballs hCγ hP
  have hsub : {x : Rd d | γ⁻¹ • x ∈ F} ⊆ {x | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) R} ∪
      ⋃ y ∈ t, {x | γ⁻¹ • x ∈ Metric.ball y (δ y)} := by
    intro x hx
    by_cases hxb : γ⁻¹ • x ∈ Metric.closedBall (0 : Rd d) R
    · right
      have := hcover ⟨hxb, hx⟩
      simp only [Set.mem_iUnion] at this ⊢
      exact this
    · left; exact hxb
  calc (ν γ {x | γ⁻¹ • x ∈ F}).toReal
      ≤ (ν γ {x | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) R} +
          ∑ y ∈ t, ν γ {x | γ⁻¹ • x ∈ Metric.ball y (δ y)}).toReal := by
        apply ENNReal.toReal_mono
        · exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
            ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _⟩
        · exact (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_biUnion_finset_le _ _)))
    _ = (ν γ {x | γ⁻¹ • x ∉ Metric.closedBall (0 : Rd d) R}).toReal +
          ∑ y ∈ t, (ν γ {x | γ⁻¹ • x ∈ Metric.ball y (δ y)}).toReal := by
        rw [ENNReal.toReal_add (measure_ne_top _ _)
          (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _),
          ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    _ ≤ (2 * d : ℝ) * Real.exp (-(γ * z)) + ∑ _y ∈ t, Real.exp (-(γ * z)) :=
        add_le_add hRγ (Finset.sum_le_sum hballs)
    _ = (2 * d + t.card : ℝ) * Real.exp (-(γ * z)) := by simp; ring
    _ ≤ Real.exp (γ * η) * Real.exp (-(γ * z)) :=
        mul_le_mul_of_nonneg_right hCγ (Real.exp_pos _).le
    _ = Real.exp (γ * (-z + η)) := by rw [← Real.exp_add]; ring_nf

/-- Converting eventual exponential bounds into an `EReal` limsup bound. -/
lemma limsup_le_of_exp (m : ℝ → ENNReal) (hm : ∀ᶠ γ in atTop, m γ ≠ ⊤) (L : ℝ)
    (h : ∀ η > 0, ∀ᶠ γ in atTop, (m γ).toReal ≤ Real.exp (γ * (L + η))) :
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ)) atTop ≤ (L : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  rw [EReal.coe_lt_coe_iff] at hz
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [h (z - L) (by linarith), eventually_gt_atTop (0:ℝ), hm] with γ hγ hγ0 hmγ
  have hγ' : (0:ℝ) < γ⁻¹ := inv_pos.2 hγ0
  rcases eq_or_ne (m γ) 0 with h0 | h0
  · rw [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hγ']; exact bot_le
  have hr : 0 < (m γ).toReal := ENNReal.toReal_pos h0 hmγ
  rw [← ENNReal.ofReal_toReal hmγ, ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_le_coe_iff]
  have hl : Real.log (m γ).toReal ≤ γ * (L + (z - L)) := by
    have := Real.log_le_log hr hγ
    rwa [Real.log_exp] at this
  rw [inv_mul_le_iff₀ hγ0]
  linarith

end ProbEffIS.GE.UB

open ProbEffIS.GE ProbEffIS.GE.UB in
theorem solution {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ≤
        -(rateOn μ (closure B)) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro w hw
  have hz : ((-w : ℝ) : EReal) < rateOn μ (closure B) := by
    rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hw
  have hkey := key_ub ν hν μ h1 (closure B) isClosed_closure (-w) hz
  have hfin : ∀ᶠ γ in atTop, ν γ {x | γ⁻¹ • x ∈ B} ≠ ⊤ := by
    filter_upwards [hν] with γ hP using measure_ne_top _ _
  have := limsup_le_of_exp (fun γ => ν γ {x | γ⁻¹ • x ∈ B}) hfin (-(-w)) (fun η hη => by
    filter_upwards [hkey η hη, hν] with γ hγ hP
    refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) hγ
    intro x hx; exact subset_closure hx)
  simpa using this
