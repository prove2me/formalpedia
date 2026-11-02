-- Prove2me | solution 1 for StochArbitrage.Pricing.theorem_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:15:42.975205+00:00
-- url     : https://prove2.me/submissions/ef499ca9-a8af-4e99-ab00-0ea4c8357e7f

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model
import Theorems.Thm_NonsmoothNewton_Shared_isCompact_convexHull_of_isCompact_finiteDimensional
import Theorems.Thm_LinearOptimization_farkas_inequality_form
import Theorems.Thm_StochArbitrage_Pricing_if_direction

open MeasureTheory Matrix Filter Topology

namespace StochArbSol
open StochArbitrage.Pricing

variable {N R : ℕ}

lemma integrable_of_cont (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {F : (Fin N → ℝ) → ℝ} (hF : Continuous F) : Integrable F M.μ := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin N => Set.Icc M.lo M.hi)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [hbox] with x hx
  exact hC x (Set.mem_univ_pi.2 hx)

lemma cont_dot (κ : Fin N → ℝ) : Continuous fun x : Fin N → ℝ => x ⬝ᵥ κ :=
  continuous_id.dotProduct continuous_const

lemma integrable_comp_dot (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {w : ℝ → ℝ} (hw : Continuous w) (z : Fin N → ℝ) :
    Integrable (fun x => w (x ⬝ᵥ z)) M.μ :=
  integrable_of_cont M hbox (hw.comp (cont_dot z))

lemma concave_tangent {u : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ u) (hd : Differentiable ℝ u)
    (y h : ℝ) : u (y + h) - u y ≤ deriv u y * h := by
  rcases lt_trichotomy h 0 with hh | hh | hh
  · have := hc.deriv_le_slope (Set.mem_univ (y+h)) (Set.mem_univ y) (by linarith) (hd y)
    rw [slope_def_field] at this
    have h' : y - (y + h) = -h := by ring
    rw [h', le_div_iff₀ (by linarith)] at this
    linarith
  · simp [hh]
  · have := hc.slope_le_deriv (Set.mem_univ y) (Set.mem_univ (y+h)) (by linarith) (hd y)
    rw [slope_def_field] at this
    have h' : y + h - y = h := by ring
    rw [h', div_le_iff₀ hh] at this
    linarith

lemma pv_dot (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {m : (Fin N → ℝ) → ℝ} (hm : Continuous m) (δ : Fin N → ℝ) :
    M.presentValue m ⬝ᵥ δ = ∫ x, m x * (x ⬝ᵥ δ) ∂M.μ := by
  have h : ∀ i, Integrable (fun x => m x * x i * δ i) M.μ := fun i =>
    integrable_of_cont M hbox ((hm.mul (continuous_apply i)).mul continuous_const)
  calc M.presentValue m ⬝ᵥ δ = ∑ i, ∫ x, m x * x i * δ i ∂M.μ := by
        simp only [dotProduct, Market.presentValue]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_mul_const]
    _ = ∫ x, ∑ i, m x * x i * δ i ∂M.μ := (integral_finsetSum _ (fun i _ => h i)).symm
    _ = _ := by
        congr 1; ext x; simp only [dotProduct, Finset.mul_sum, mul_assoc]

lemma pv_smul_fun (M : Market N R) (d : ℝ) (g : (Fin N → ℝ) → ℝ) :
    M.presentValue (fun x => d * g x) = d • M.presentValue g := by
  ext i
  simp only [Market.presentValue, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext x; ring

lemma pv_comb (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {m₁ m₂ : (Fin N → ℝ) → ℝ} (h₁ : Continuous m₁) (h₂ : Continuous m₂) (a b : ℝ) :
    M.presentValue (a • m₁ + b • m₂) = a • M.presentValue m₁ + b • M.presentValue m₂ := by
  ext i
  simp only [Market.presentValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1; ext x; ring
  · exact integrable_of_cont M hbox (continuous_const.mul (h₁.mul (continuous_apply i)))
  · exact integrable_of_cont M hbox (continuous_const.mul (h₂.mul (continuous_apply i)))

lemma D_comb (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) (a b : ℝ) (κ δ : Fin N → ℝ) :
    M.D (a • u + b • v) κ δ = a * M.D u κ δ + b * M.D v κ δ := by
  have I : ∀ (w : ℝ → ℝ), Continuous w → ∀ z : Fin N → ℝ,
      Integrable (fun x => w (x ⬝ᵥ z)) M.μ := fun w hw z =>
    integrable_of_cont M hbox (hw.comp (cont_dot z))
  simp only [Market.D, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add ((I u hu _).const_mul a) ((I v hv _).const_mul b),
    integral_add ((I u hu _).const_mul a) ((I v hv _).const_mul b)]
  simp only [integral_const_mul]
  ring

/-- Pointwise concavity bound, integrated. -/
lemma D_le_pv (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {u : ℝ → ℝ} (hu1 : ContDiff ℝ 1 u) (hcc : ConcaveOn ℝ Set.univ u) (κ δ : Fin N → ℝ) :
    M.D u κ δ ≤ M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) ⬝ᵥ δ := by
  have hd : Differentiable ℝ u := hu1.differentiable (by norm_num)
  have hg : Continuous (deriv u) := hu1.continuous_deriv (by norm_num)
  rw [pv_dot M hbox (m := fun x => deriv u (x ⬝ᵥ κ)) (hg.comp (cont_dot κ)) δ, Market.D,
    ← integral_sub (integrable_comp_dot M hbox hu1.continuous _)
      (integrable_comp_dot M hbox hu1.continuous _)]
  refine integral_mono ((integrable_comp_dot M hbox hu1.continuous _).sub
      (integrable_comp_dot M hbox hu1.continuous _))
    (integrable_of_cont M hbox ((hg.comp (cont_dot κ)).mul (cont_dot δ))) (fun x => ?_)
  simp only [dotProduct_add]
  exact concave_tangent hcc hd _ _

/-- Convex hull of a family of continuous SDFs pricing `δ` strictly positively. -/
lemma pos_of_mem_convexHull (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi) (δ : Fin N → ℝ)
    (S : Set ((Fin N → ℝ) → ℝ)) (hS : ∀ m ∈ S, Continuous m ∧ 0 < M.presentValue m ⬝ᵥ δ) :
    ∀ m ∈ convexHull ℝ S, Continuous m ∧ 0 < M.presentValue m ⬝ᵥ δ := by
  intro m hm
  refine (convexHull_min (t := {m | Continuous m ∧ 0 < M.presentValue m ⬝ᵥ δ}) hS ?_) hm
  intro m₁ h₁ m₂ h₂ a b ha hb hab
  refine ⟨(h₁.1.const_smul a).add (h₂.1.const_smul b), ?_⟩
  rw [pv_comb M hbox h₁.1 h₂.1, add_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h₁.2) (mul_nonneg hb h₂.2.le)
  · subst ha'; simp at hab; subst hab; simpa using h₂.2

lemma sdf_cont {U : Set (ℝ → ℝ)} {K : Set (Fin N → ℝ)}
    (hU : ∀ u ∈ U, ContDiff ℝ 1 u) {m : (Fin N → ℝ) → ℝ} (hm : m ∈ sdfSet U K) :
    Continuous m := by
  obtain ⟨u, hu, κ, _, d, _, rfl⟩ := hm
  exact continuous_const.mul (((hU u hu).continuous_deriv (by norm_num)).comp (cont_dot κ))

lemma pos_comb {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * x + b * y := by
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  · subst ha'; simp at hab; subst hab; simpa using hy

lemma box_compact (M : Market N R) :
    IsCompact (Set.pi Set.univ (fun _ : Fin N => Set.Icc M.lo M.hi)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

lemma eventually_D_pos (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    (K : Set (Fin N → ℝ)) (hKb : Bornology.IsBounded K)
    {u : ℝ → ℝ} (hu1 : ContDiff ℝ 1 u) (δ : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hpv : ∀ κ ∈ K, ε ≤ M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) ⬝ᵥ δ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ κ ∈ K, 0 < M.D u κ (t • δ) := by
  set B := Set.pi Set.univ (fun _ : Fin N => Set.Icc M.lo M.hi) with hBdef
  have hB : IsCompact B := box_compact M
  have hd : Differentiable ℝ u := hu1.differentiable (by norm_num)
  set g := deriv u with hgdef
  have hg : Continuous g := hu1.continuous_deriv (by norm_num)
  obtain ⟨r, hr⟩ := hKb.subset_closedBall 0
  obtain ⟨Rb, hRb⟩ := (hB.prod (isCompact_closedBall (0 : Fin N → ℝ) r)).exists_bound_of_continuousOn
    (f := fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1 ⬝ᵥ p.2)
    (continuous_fst.dotProduct continuous_snd).continuousOn
  obtain ⟨Z, hZ⟩ := hB.exists_bound_of_continuousOn (cont_dot δ).continuousOn
  set Z' := |Z| with hZ'
  have hZ0 : 0 ≤ Z' := abs_nonneg Z
  have hUC := (isCompact_Icc (a := -|Rb| - 1) (b := |Rb| + 1)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  set η := ε / (2 * (Z' + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨ρ, hρ, hρg⟩ := hUC η hη
  have ht1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * (Z' + 1) < min ρ 1 := by
    have hT : Tendsto (fun t : ℝ => t * (Z' + 1)) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_nhdsWithin_of_tendsto_nhds (a := (0:ℝ)) (s := Set.Ioi 0)
        tendsto_id).mul_const (Z' + 1)
      rwa [zero_mul] at this
    exact hT.eventually (eventually_lt_nhds (lt_min hρ one_pos))
  filter_upwards [ht1, self_mem_nhdsWithin] with t ht htpos
  intro κ hκ
  have htpos : (0:ℝ) < t := htpos
  have htZ : t * Z' < min ρ 1 := lt_of_le_of_lt (by nlinarith) ht
  have hpt : ∀ x ∈ B, |u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ) - g (x ⬝ᵥ κ) * (t * (x ⬝ᵥ δ))|
      ≤ η * (t * Z') := by
    intro x hx
    set y := x ⬝ᵥ κ with hydef
    set h := t * (x ⬝ᵥ δ) with hhdef
    have hy : |y| ≤ |Rb| := by
      have := hRb (x, κ) ⟨hx, hr hκ⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have hz : |x ⬝ᵥ δ| ≤ Z' := by
      have := hZ x hx
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have hh : |h| ≤ t * Z' := by
      rw [hhdef, abs_mul, abs_of_pos htpos]; exact mul_le_mul_of_nonneg_left hz htpos.le
    have hhρ : |h| < ρ := lt_of_le_of_lt hh (lt_of_lt_of_le htZ (min_le_left _ _))
    have hh1 : |h| < 1 := lt_of_le_of_lt hh (lt_of_lt_of_le htZ (min_le_right _ _))
    have heq : x ⬝ᵥ (κ + t • δ) = y + h := by
      simp [dotProduct_add, dotProduct_smul, hydef, hhdef]
    rw [heq]
    have hyI : y ∈ Set.Icc (-|Rb| - 1) (|Rb| + 1) := by
      have := abs_le.mp hy; constructor <;> linarith
    have key := (convex_uIcc y (y + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => u s - g y * s) (f' := fun s => g s - g y) (C := η)
      (fun s _ => by
        exact (((hd s).hasDerivAt.sub ((hasDerivAt_id' s).const_mul (g y))).congr_deriv
          (by simp [hgdef])).hasDerivWithinAt)
      (fun s hs => by
        have hs' : |s - y| ≤ |y + h - y| := Set.abs_sub_left_of_mem_uIcc hs
        rw [show y + h - y = h by ring] at hs'
        have hsI : s ∈ Set.Icc (-|Rb| - 1) (|Rb| + 1) := by
          have h1 := abs_le.mp hs'; have h2 := abs_le.mp hy; have h3 := abs_le.mp hh1.le
          constructor <;> linarith
        have := hρg s hsI y hyI (by rw [Real.dist_eq]; linarith)
        rw [Real.dist_eq] at this; rw [Real.norm_eq_abs]; exact this.le)
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [Real.norm_eq_abs] at key
    have e1 : u (y + h) - g y * (y + h) - (u y - g y * y) = u (y + h) - u y - g y * h := by ring
    rw [e1, show y + h - y = h by ring] at key
    calc _ ≤ η * |h| := key
      _ ≤ η * (t * Z') := mul_le_mul_of_nonneg_left hh hη.le
  have hint1 := integrable_comp_dot M hbox hu1.continuous (κ + t • δ)
  have hint0 := integrable_comp_dot M hbox hu1.continuous κ
  have hint2 : Integrable (fun x => g (x ⬝ᵥ κ) * (x ⬝ᵥ δ)) M.μ :=
    integrable_of_cont M hbox ((hg.comp (cont_dot κ)).mul (cont_dot δ))
  have hE : M.D u κ (t • δ) - t * (M.presentValue (fun x => g (x ⬝ᵥ κ)) ⬝ᵥ δ) =
      ∫ x, (u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ) - g (x ⬝ᵥ κ) * (t * (x ⬝ᵥ δ))) ∂M.μ := by
    have hint3 : Integrable (fun x => u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ)) M.μ := hint1.sub hint0
    have e : (fun x => u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ) - g (x ⬝ᵥ κ) * (t * (x ⬝ᵥ δ))) =
        fun x => (u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ)) - t * (g (x ⬝ᵥ κ) * (x ⬝ᵥ δ)) := by
      ext x; ring
    rw [e, integral_sub hint3 (hint2.const_mul t), integral_sub hint1 hint0, integral_const_mul,
      pv_dot M hbox (m := fun x => g (x ⬝ᵥ κ)) (hg.comp (cont_dot κ)), Market.D]
  have hbound : |∫ x, (u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ) - g (x ⬝ᵥ κ) * (t * (x ⬝ᵥ δ))) ∂M.μ|
      ≤ η * (t * Z') := by
    have := norm_integral_le_of_norm_le_const (μ := M.μ) (C := η * (t * Z'))
      (f := fun x => u (x ⬝ᵥ (κ + t • δ)) - u (x ⬝ᵥ κ) - g (x ⬝ᵥ κ) * (t * (x ⬝ᵥ δ)))
      (by filter_upwards [hbox] with x hx
          rw [Real.norm_eq_abs]; exact hpt x (Set.mem_univ_pi.2 hx))
    simpa using this
  have hpvκ := hpv κ hκ
  have hηZ : η * Z' ≤ ε / 2 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 := (abs_le.mp hbound).1
  have h2 : t * ε ≤ t * (M.presentValue (fun x => g (x ⬝ᵥ κ)) ⬝ᵥ δ) :=
    mul_le_mul_of_nonneg_left hpvκ htpos.le
  have h3 : t * (η * Z') ≤ t * (ε / 2) := mul_le_mul_of_nonneg_left hηZ htpos.le
  nlinarith

lemma pv_contOn (M : Market N R) [IsProbabilityMeasure M.μ]
    (hbox : ∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun κ => M.presentValue (fun x => g (x ⬝ᵥ κ))) K := by
  refine continuousOn_pi.2 (fun i => ?_)
  simp only [Market.presentValue]
  have hF : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => g (p.1 ⬝ᵥ p.2) * p.1 i) :=
    (hg.comp (continuous_fst.dotProduct continuous_snd)).mul
      ((continuous_apply i).comp continuous_fst)
  obtain ⟨C, hC⟩ := ((box_compact M).prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine continuousOn_of_dominated (bound := fun _ => C) (fun κ _ => ?_) (fun κ hκ => ?_)
    (integrable_const C) ?_
  · exact ((hg.comp (cont_dot κ)).mul (continuous_apply i)).aestronglyMeasurable
  · filter_upwards [hbox] with x hx
    exact hC (x, κ) ⟨Set.mem_univ_pi.2 hx, hκ⟩
  · exact Eventually.of_forall (fun x =>
      ((hg.comp (continuous_const.dotProduct continuous_id)).mul continuous_const).continuousOn)

theorem only_if (M : Market N R) (U : Set (ℝ → ℝ)) (K : Set (Fin N → ℝ))
    (hS : M.Standing U K)
    (hU : ∃ U₀ : Set (ℝ → ℝ), U₀.Finite ∧ U = convexHull ℝ U₀)
    (h : M.strictSAOSet U K = ∅) :
    ∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ∈ M.polarCone := by
  obtain ⟨hP, -, hbox, hUreg, -, -, hKc, hKb, -, -, -, ha⟩ := hS
  haveI := hP
  obtain ⟨U₀, hfin, rfl⟩ := hU
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have hU₀ : ∀ u ∈ U₀, ContDiff ℝ 1 u := fun u hu => (hUreg u (subset_convexHull ℝ U₀ hu)).1
  set P₀ : Set (Fin N → ℝ) :=
    ⋃ u ∈ U₀, (fun κ => M.presentValue (fun x => deriv u (x ⬝ᵥ κ))) '' K with hP₀
  set Pol : Set (Fin N → ℝ) := {q | ∀ δ ∈ M.overlaySet, q ⬝ᵥ δ ≤ 0} with hPol
  have hP₀c : IsCompact P₀ := hfin.isCompact_biUnion (fun u hu =>
    hK.image_of_continuousOn (pv_contOn M hbox hK ((hU₀ u hu).continuous_deriv (by norm_num))))
  have hHc : IsCompact (convexHull ℝ P₀) :=
    NonsmoothNewton.Shared.isCompact_convexHull_of_isCompact_finiteDimensional hP₀c
  have hPolc : IsClosed Pol := by
    have : Pol = ⋂ δ ∈ M.overlaySet, {q : Fin N → ℝ | q ⬝ᵥ δ ≤ 0} := by
      ext q; simp [hPol]
    rw [this]
    exact isClosed_biInter (fun δ _ =>
      isClosed_le (continuous_id.dotProduct continuous_const) continuous_const)
  have hPolv : Convex ℝ Pol := by
    intro q₁ h₁ q₂ h₂ a b ha hb _ δ hδ
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (h₁ δ hδ))
      (mul_nonpos_of_nonneg_of_nonpos hb (h₂ δ hδ))
  have h0Pol : (0 : Fin N → ℝ) ∈ Pol := fun δ _ => by simp
  by_cases hint : (convexHull ℝ P₀ ∩ Pol).Nonempty
  · obtain ⟨q, hqH, hqP⟩ := hint
    have hW : convexHull ℝ P₀ ⊆ {q | ∃ m ∈ convexHull ℝ (sdfSet (convexHull ℝ U₀) K),
        Continuous m ∧ M.presentValue m = q} := by
      refine convexHull_min ?_ ?_
      · intro q hq
        simp only [hP₀, Set.mem_iUnion, Set.mem_image] at hq
        obtain ⟨u, hu, κ, hκ, rfl⟩ := hq
        refine ⟨fun x => 1 * deriv u (x ⬝ᵥ κ), subset_convexHull ℝ _
          ⟨u, subset_convexHull ℝ U₀ hu, κ, hκ, 1, one_pos, rfl⟩, ?_, ?_⟩
        · exact continuous_const.mul (((hU₀ u hu).continuous_deriv (by norm_num)).comp
            (cont_dot κ))
        · simp
      · rintro _ ⟨m₁, hm₁, hc₁, rfl⟩ _ ⟨m₂, hm₂, hc₂, rfl⟩ a b ha hb hab
        exact ⟨a • m₁ + b • m₂, convex_convexHull ℝ _ hm₁ hm₂ ha hb hab,
          (hc₁.const_smul a).add (hc₂.const_smul b), pv_comb M hbox hc₁ hc₂ a b⟩
    obtain ⟨m, hm, -, rfl⟩ := hW hqH
    refine ⟨m, hm, ?_⟩
    have hfeas : ∃ x : Fin N → ℝ, M.A.mulVec x ≤ M.aVec := ⟨0, by simpa using ha⟩
    obtain ⟨σ, hσ, hAσ, hσa⟩ := (LinearOptimization.farkas_inequality_form M.A M.aVec
      (M.presentValue m) 0 hfeas).1 (fun δ hδ => hqP δ hδ)
    exact ⟨σ, hσ, hAσ.symm, by rw [dotProduct_comm]; exact hσa⟩
  · exfalso
    have hdisj : Disjoint (convexHull ℝ P₀) Pol :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hint)
    obtain ⟨f, u0, v0, hfu, huv, hfv⟩ :=
      geometric_hahn_banach_compact_closed (convex_convexHull ℝ P₀) hHc hPolv hPolc hdisj
    have hv0 : v0 < 0 := by simpa using hfv 0 h0Pol
    set δ : Fin N → ℝ := fun i => - f (fun j => if i = j then 1 else 0) with hδdef
    have hfδ : ∀ q, f q = - (q ⬝ᵥ δ) := by
      intro q
      have := (f : (Fin N → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ q
      simp only [dotProduct, hδdef, mul_neg, Finset.sum_neg_distrib, neg_neg]
      simpa [smul_eq_mul] using this
    have hpos : ∀ u ∈ U₀, ∀ κ ∈ K,
        -u0 ≤ M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) ⬝ᵥ δ := by
      intro u hu κ hκ
      have := hfu _ (subset_convexHull ℝ _ (by
        simp only [hP₀, Set.mem_iUnion, Set.mem_image]; exact ⟨u, hu, κ, hκ, rfl⟩))
      rw [hfδ] at this; linarith
    have hpol : ∀ y ∈ Pol, y ⬝ᵥ δ ≤ 0 := by
      intro y hy
      by_contra hcon; push_neg at hcon
      set s := v0 / (-(y ⬝ᵥ δ)) with hsdef
      have hs : 0 < s := div_pos_of_neg_of_neg hv0 (by linarith)
      have hsy : s • y ∈ Pol := fun δ' hδ' => by
        rw [smul_dotProduct, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos hs.le (hy δ' hδ')
      have h1 := hfv _ hsy
      rw [hfδ, smul_dotProduct, smul_eq_mul] at h1
      have h2 : -(s * (y ⬝ᵥ δ)) = v0 := by
        rw [hsdef]; field_simp
      linarith
    have hrow : ∀ i, M.aVec i = 0 → (M.A *ᵥ δ) i ≤ 0 := by
      intro i hi
      have hmem : (fun k => M.A i k) ∈ Pol := by
        intro δ' hδ'
        have := hδ' i
        simpa [Matrix.mulVec, hi] using this
      have := hpol _ hmem
      simpa [Matrix.mulVec] using this
    have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, t * (M.A *ᵥ δ) i ≤ M.aVec i := by
      refine Filter.eventually_all.2 (fun i => ?_)
      by_cases hAi : (M.A *ᵥ δ) i ≤ 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact (mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) hAi).trans (ha i)
      · have hai : 0 < M.aVec i := lt_of_le_of_ne (ha i) (fun h0 => hAi (hrow i h0.symm))
        have hT : Tendsto (fun t : ℝ => t * (M.A *ᵥ δ) i) (𝓝[>] 0) (𝓝 0) := by
          have := (tendsto_nhdsWithin_of_tendsto_nhds (a := (0:ℝ)) (s := Set.Ioi 0)
            tendsto_id).mul_const ((M.A *ᵥ δ) i)
          rwa [zero_mul] at this
        exact (hT.eventually (eventually_lt_nhds hai)).mono (fun t ht => ht.le)
    have hu0 : 0 < -u0 := by linarith
    have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ u ∈ U₀, ∀ κ ∈ K, 0 < M.D u κ (t • δ) :=
      (Filter.eventually_all_finite hfin).2 (fun u hu =>
        eventually_D_pos M hbox K hKb (hU₀ u hu) δ hu0 (hpos u hu))
    obtain ⟨t, ht1, ht2⟩ := (hev1.and hev2).exists
    have hmem : t • δ ∈ M.strictSAOSet (convexHull ℝ U₀) K := by
      refine ⟨?_, ?_⟩
      · intro i; simpa [Matrix.mulVec_smul] using ht1 i
      · intro u hu κ hκ
        have hT := convexHull_min
          (t := {u : ℝ → ℝ | Continuous u ∧ ∀ κ ∈ K, 0 < M.D u κ (t • δ)})
          (fun u hu => ⟨(hU₀ u hu).continuous, ht2 u hu⟩) ?_ hu
        · exact hT.2 κ hκ
        · intro u₁ h₁ u₂ h₂ a b ha hb hab
          refine ⟨(h₁.1.const_smul a).add (h₂.1.const_smul b), fun κ hκ => ?_⟩
          rw [D_comb M hbox h₁.1 h₂.1]
          exact pos_comb (h₁.2 κ hκ) (h₂.2 κ hκ) ha hb hab
    rw [h] at hmem; exact hmem

end StochArbSol

open StochArbitrage.Pricing StochArbSol

theorem solution {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K)
    (hU : ∃ U₀ : Set (ℝ → ℝ), U₀.Finite ∧ U = convexHull ℝ U₀) :
    M.strictSAOSet U K = ∅ ↔
      ∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ∈ M.polarCone :=
  ⟨only_if M U K hS hU, if_direction M U K hS⟩
