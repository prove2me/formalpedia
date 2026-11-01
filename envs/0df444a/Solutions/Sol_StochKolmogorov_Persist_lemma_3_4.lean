-- Prove2me | solution 1 for StochKolmogorov.Persist.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T07:57:41.922845+00:00
-- url     : https://prove2.me/submissions/dcdb35a6-ebf9-432a-854b-4fcdf79fd410

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_1
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false

namespace L34Lib
open StochKolmogorov.Persist EthierKurtz

variable {n : ℕ}

theorem pp_apply (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem pp_mem (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [pp_apply]; exact le_max_right _ _

theorem pp_of_mem {x : SDEState n} (hx : x ∈ orthant n) : posPart x = x := by
  ext i; rw [pp_apply]; exact max_eq_left (hx i)

theorem pp_cont : Continuous (posPart (n := n)) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (PiLp.continuous_apply 2 _ i).max continuous_const)

theorem orth_closed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

/-- The weight `(1 + cᵀx)^δ₀ (1 + ∑ᵢ(|fᵢ(x)| + |gᵢ(x)|²))` of (3.8). -/
noncomputable def Wt (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (x : SDEState n) : ℝ :=
  (1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))

theorem one_le_W {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    1 ≤ 1 + ∑ i, c i * x i := by
  have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx i)
  linarith

theorem one_le_U (C : Coeffs n) (x : SDEState n) :
    1 ≤ 1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2) := by
  have : 0 ≤ ∑ i, (|C.f i x| + |C.g i x| ^ 2) :=
    Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) 2)
  linarith

theorem Wt_nonneg (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n)
    (hx : x ∈ orthant n) (δ₀ : ℝ) : 0 ≤ Wt C c δ₀ x :=
  mul_nonneg (Real.rpow_nonneg (by linarith [one_le_W hc hx]) _) (by linarith [one_le_U C x])

theorem Wt_pp_cont (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (hδ : 0 ≤ δ₀)
    (hf : ∀ i, ContinuousOn (C.f i) (orthant n)) (hg : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    Continuous (fun x => Wt C c δ₀ (posPart x)) := by
  have fc : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hf i).comp_continuous pp_cont pp_mem
  have gc : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hg i).comp_continuous pp_cont pp_mem
  unfold Wt
  refine Continuous.mul ?_ ?_
  · exact (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((PiLp.continuous_apply 2 _ i).comp pp_cont))).rpow_const (fun _ => Or.inr hδ)
  · exact continuous_const.add (continuous_finsetSum _ fun i _ =>
      (fc i).abs.add ((gc i).abs.pow 2))

/-- Clamp at level `L`. -/
noncomputable def clampL (L v : ℝ) : ℝ := max (-L) (min v L)

theorem clampL_eq {L v : ℝ} (h : |v| ≤ L) : clampL L v = v := by
  unfold clampL
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem clampL_sub_le {L : ℝ} (hL : 0 ≤ L) (v : ℝ) : |v - clampL L v| ≤ |v| := by
  unfold clampL
  rcases le_total v L with h1 | h1 <;> rcases le_total (-L) v with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2, sub_self, abs_zero]; exact abs_nonneg _
  · rw [min_eq_left h1, max_eq_left h2]
    rw [abs_le]; constructor <;> cases abs_cases v <;> linarith
  · rw [min_eq_right h1, max_eq_right (by linarith)]
    rw [abs_le]; constructor <;> cases abs_cases v <;> linarith
  · rw [min_eq_right h1, max_eq_left (by linarith)]
    rw [abs_le]; constructor <;> cases abs_cases v <;> linarith

theorem clampL_abs_le {L : ℝ} (hL : 0 ≤ L) (v : ℝ) : |clampL L v| ≤ L := by
  unfold clampL
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem clampL_cont (L : ℝ) : Continuous (clampL L) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- Integration against the mean occupation measure. -/
theorem occ_lint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ) (g : SDEState n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(occMean P X x T) =
      (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, g (X x s.toNNReal ω)) ∂P := by
  have hF : Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
      (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  unfold occMean
  rw [lintegral_smul_measure, lintegral_map hg hF,
    lintegral_prod_symm (fun q : ℝ × Ω => g (X x q.1.toNNReal q.2)) ((hg.comp hF).aemeasurable),
    smul_eq_mul]

theorem occ_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (occMean P X x T) := by
  constructor
  have := occ_lint P X x hm hc T (fun _ => 1) measurable_const
  simp only [lintegral_one, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero] at this
  rw [this]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hT).ne' ENNReal.ofReal_ne_top

theorem occ_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ)
    (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) :
    ∀ᵐ y ∂(occMean P X x T), y ∈ orthant n := by
  have hS : MeasurableSet (orthant n)ᶜ := orth_closed.measurableSet.compl
  have := occ_lint P X x hm hc T ((orthant n)ᶜ.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at this
  rw [ae_iff]
  change occMean P X x T (orthant n)ᶜ = 0
  rw [this]
  have h0 : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (orthant n)ᶜ.indicator 1 (X x s.toNNReal ω)) =ᵐ[P] 0 := by
    filter_upwards [hinv] with ω hω
    simp [Set.indicator_apply, hω]
  rw [lintegral_congr_ae h0]
  simp

theorem occ_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 1 < T)
    (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (hWm : Measurable fun y => Wt C c δ₀ (posPart y)) (H₂ a A : ℝ) (hH₂ : 0 < H₂)
    (ha0 : 0 ≤ a) (haA : a ≤ A)
    (h38 : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) ∂P ≤ ENNReal.ofReal (H₂ * (a + T))) :
    ∫⁻ y, ENNReal.ofReal (Wt C c δ₀ (posPart y)) ∂(occMean P X x T) ≤
      ENNReal.ofReal (H₂ * (A + 1)) := by
  have hT0 : 0 < T := by linarith
  rw [occ_lint P X x hm hc T _ hWm.ennreal_ofReal]
  have heq : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (Wt C c δ₀ (posPart (X x s.toNNReal ω)))) =ᵐ[P]
      (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) := by
    filter_upwards [hinv] with ω hω
    simp only [pp_of_mem (hω _)]
  rw [lintegral_congr_ae heq]
  calc (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) ∂P
      ≤ (ENNReal.ofReal T)⁻¹ * ENNReal.ofReal (H₂ * (a + T)) := by gcongr
    _ = ENNReal.ofReal (H₂ * (a + T) / T) := by
        rw [ENNReal.ofReal_div_of_pos hT0, ENNReal.div_eq_inv_mul]
    _ ≤ ENNReal.ofReal (H₂ * (A + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ hT0]
        have h1 : a ≤ A * T := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hH₂.le]

/-- Bochner integrability of a weight with a finite lintegral bound. -/
theorem wt_integrable {ν : Measure (SDEState n)} {Φ : SDEState n → ℝ} (hΦm : Measurable Φ)
    (hΦ0 : 0 ≤ᵐ[ν] Φ) {Bd : ℝ} (hb : ∫⁻ x, ENNReal.ofReal (Φ x) ∂ν ≤ ENNReal.ofReal Bd) :
    Integrable Φ ν :=
  ⟨hΦm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hΦ0).2
    (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩

theorem wt_integral_le {ν : Measure (SDEState n)} {Φ : SDEState n → ℝ} (hΦm : Measurable Φ)
    (hΦ0 : 0 ≤ᵐ[ν] Φ) {Bd : ℝ} (hBd : 0 ≤ Bd)
    (hb : ∫⁻ x, ENNReal.ofReal (Φ x) ∂ν ≤ ENNReal.ofReal Bd) :
    ∫ x, Φ x ∂ν ≤ Bd := by
  rw [integral_eq_lintegral_of_nonneg_ae hΦ0 hΦm.aestronglyMeasurable]
  calc (∫⁻ x, ENNReal.ofReal (Φ x) ∂ν).toReal ≤ (ENNReal.ofReal Bd).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = Bd := ENNReal.toReal_ofReal hBd

theorem est {ν : Measure (SDEState n)} {u v Φ : SDEState n → ℝ} (hu : Integrable u ν)
    (hv : Integrable v ν) (hΦm : Measurable Φ) {S : Set (SDEState n)} (hS : ∀ᵐ x ∂ν, x ∈ S)
    (hΦ0 : ∀ x ∈ S, 0 ≤ Φ x) {Bd η : ℝ} (hBd : 0 ≤ Bd) (hη : 0 ≤ η)
    (hb : ∫⁻ x, ENNReal.ofReal (Φ x) ∂ν ≤ ENNReal.ofReal Bd)
    (hd : ∀ x ∈ S, |u x - v x| ≤ η * Φ x) :
    |∫ x, u x ∂ν - ∫ x, v x ∂ν| ≤ η * Bd := by
  have hΦ0' : 0 ≤ᵐ[ν] Φ := hS.mono fun x hx => hΦ0 x hx
  have hΦi := wt_integrable hΦm hΦ0' hb
  rw [← integral_sub hu hv]
  have h1 : ‖∫ x, (u x - v x) ∂ν‖ ≤ ∫ x, η * Φ x ∂ν :=
    norm_integral_le_of_norm_le (hΦi.const_mul η)
      (hS.mono fun x hx => by rw [Real.norm_eq_abs]; exact hd x hx)
  rw [Real.norm_eq_abs, integral_const_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (wt_integral_le hΦm hΦ0' hBd hb) hη)

/-- Uniform integrability gives convergence of integrals of unbounded continuous functions. -/
theorem ui_limit (μ : ℕ → Measure (SDEState n)) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (π : Measure (SDEState n)) [IsProbabilityMeasure π] (u Φ : SDEState n → ℝ)
    (hu : Continuous u) (hΦm : Measurable Φ) (S : Set (SDEState n))
    (hΦ0 : ∀ x ∈ S, 0 ≤ Φ x) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hb : ∀ k, ∫⁻ x, ENNReal.ofReal (Φ x) ∂μ k ≤ ENNReal.ofReal Bd)
    (hbπ : ∫⁻ x, ENNReal.ofReal (Φ x) ∂π ≤ ENNReal.ofReal Bd)
    (hSk : ∀ k, ∀ᵐ x ∂μ k, x ∈ S) (hSπ : ∀ᵐ x ∂π, x ∈ S)
    (htail : ∀ η > 0, ∃ L ≥ 0, ∀ x ∈ S, |u x - clampL L (u x)| ≤ η * Φ x)
    (hweak : ∀ g : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, g y ∂μ k) atTop (𝓝 (∫ y, g y ∂π)))
    (hint : ∀ k, Integrable u (μ k)) (hintπ : Integrable u π) :
    Tendsto (fun k => ∫ y, u y ∂μ k) atTop (𝓝 (∫ y, u y ∂π)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * (Bd + 1)) with hηdef
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨L, hL, hLt⟩ := htail η hη
  let g : SDEState n →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => clampL L (u x)) ((clampL_cont L).comp hu) L
    (fun x => by rw [Real.norm_eq_abs]; exact clampL_abs_le hL _)
  have hg : ∀ x, g x = clampL L (u x) := fun x => rfl
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hweak g) (ε / 2) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  haveI := hμ k
  have e1 := est (hint k) (g.integrable (μ k)) hΦm (hSk k) hΦ0 hBd hη.le (hb k)
    (fun x hx => by rw [hg]; exact hLt x hx)
  have e2 := est hintπ (g.integrable π) hΦm hSπ hΦ0 hBd hη.le hbπ
    (fun x hx => by rw [hg]; exact hLt x hx)
  have e3 := hN k hk
  rw [Real.dist_eq] at e3 ⊢
  have hηB : η * Bd < ε / 4 := by
    rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  calc |∫ y, u y ∂μ k - ∫ y, u y ∂π|
      ≤ |∫ y, u y ∂μ k - ∫ y, g y ∂μ k| + |∫ y, g y ∂μ k - ∫ y, g y ∂π|
          + |∫ y, u y ∂π - ∫ y, g y ∂π| := by
        have := abs_sub_le (∫ y, u y ∂μ k) (∫ y, g y ∂μ k) (∫ y, u y ∂π)
        have := abs_sub_le (∫ y, g y ∂μ k) (∫ y, g y ∂π) (∫ y, u y ∂π)
        rw [abs_sub_comm (∫ y, g y ∂π) (∫ y, u y ∂π)] at this
        linarith
    _ < ε := by linarith

theorem euc_norm_le_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

/-- Continuous functions are bounded on `{x ∈ ℝⁿ₊ : cᵀx ≤ R}` (`c > 0`). -/
theorem bdd_ell {c : SDEState n} (hc : c ∈ openOrthant n) {g : SDEState n → ℝ}
    (hg : Continuous g) (R : ℝ) : ∃ K, ∀ x ∈ orthant n, ∑ k, c k * x k ≤ R → |g x| ≤ K := by
  set S : Set (SDEState n) := orthant n ∩ {x | ∑ k, c k * x k ≤ R} with hS
  have hcl : IsClosed S := orth_closed.inter (isClosed_le (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (PiLp.continuous_apply 2 _ k)) continuous_const)
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨∑ k, |R| / c k, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (euc_norm_le_sum x).trans (Finset.sum_le_sum fun k _ => ?_)
    have hxk := hx.1 k
    have hck := hc k
    have hsum : c k * x k ≤ ∑ j, c j * x j := Finset.single_le_sum
      (f := fun j => c j * x j) (fun j _ => mul_nonneg (hc j).le (hx.1 j)) (Finset.mem_univ k)
    rw [abs_of_nonneg hxk, le_div_iff₀ hck]
    have := hx.2; simp only [Set.mem_setOf_eq] at this
    nlinarith [le_abs_self R]
  obtain ⟨K, hK⟩ := (Metric.isCompact_of_isClosed_isBounded hcl hbd).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨K, fun x hx hR => by have := hK x ⟨hx, hR⟩; rwa [Real.norm_eq_abs] at this⟩

theorem ofReal_iSup_min (z : ℝ) : ENNReal.ofReal z = ⨆ L : ℕ, ENNReal.ofReal (min z L) := by
  apply le_antisymm
  · exact le_iSup_of_le (⌈z⌉₊) (by rw [min_eq_left (Nat.le_ceil z)])
  · exact iSup_le fun L => ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- Fatou for weak convergence: a uniform lintegral bound passes to the weak limit. -/
theorem fatou_weak (μ : ℕ → Measure (SDEState n)) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (π : Measure (SDEState n)) [IsProbabilityMeasure π] (Φ : SDEState n → ℝ)
    (hΦ : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hb : ∀ k, ∫⁻ x, ENNReal.ofReal (Φ x) ∂μ k ≤ ENNReal.ofReal Bd)
    (hweak : ∀ g : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, g y ∂μ k) atTop (𝓝 (∫ y, g y ∂π))) :
    ∫⁻ x, ENNReal.ofReal (Φ x) ∂π ≤ ENNReal.ofReal Bd := by
  have hmono : Monotone fun (L : ℕ) x => ENNReal.ofReal (min (Φ x) L) := fun a b hab x =>
    ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
  have hmeas : ∀ L : ℕ, Measurable fun x => ENNReal.ofReal (min (Φ x) L) := fun L =>
    (hΦ.measurable.min measurable_const).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (Φ x) ∂π = ∫⁻ x, ⨆ L : ℕ, ENNReal.ofReal (min (Φ x) L) ∂π := by
        congr 1; funext x; exact ofReal_iSup_min _
    _ = ⨆ L : ℕ, ∫⁻ x, ENNReal.ofReal (min (Φ x) L) ∂π := lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal Bd := by
        refine iSup_le fun L => ?_
        have h0 : ∀ y, 0 ≤ min (Φ y) (L : ℝ) := fun y => le_min (hΦ0 y) (Nat.cast_nonneg L)
        let g : SDEState n →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
          (fun x => min (Φ x) (L : ℝ)) (hΦ.min continuous_const) L
          (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact min_le_right _ _)
        have hgk : ∀ k, ∫ y, g y ∂μ k ≤ Bd := fun k => by
          haveI := hμ k
          exact wt_integral_le (ν := μ k) (Φ := fun y => g y) g.continuous.measurable
            (ae_of_all _ h0) hBd ((lintegral_mono fun y =>
              ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hb k))
        have hπle : ∫ y, g y ∂π ≤ Bd := le_of_tendsto' (hweak g) hgk
        calc ∫⁻ x, ENNReal.ofReal (min (Φ x) L) ∂π = ENNReal.ofReal (∫ y, g y ∂π) :=
              (ofReal_integral_eq_lintegral_ofReal (g.integrable π) (ae_of_all _ h0)).symm
          _ ≤ ENNReal.ofReal Bd := ENNReal.ofReal_le_ofReal hπle

/-- The tail estimate: outside a sublevel set of `cᵀx`, `|h|` is a small multiple of the (3.8) weight. -/
theorem tail_est (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ δ₀ Kh : ℝ}
    (hδ : δ < δ₀) (hKh : 0 ≤ Kh) (h : SDEState n → ℝ) (hhc : Continuous fun x => h (posPart x))
    (hgrowth : ∀ x ∈ orthant n, |h x| <
      Kh * (1 + ∑ i, c i * x i) ^ δ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) :
    ∀ η > 0, ∃ L ≥ 0, ∀ x ∈ orthant n,
      |h (posPart x) - clampL L (h (posPart x))| ≤ η * Wt C c δ₀ (posPart x) := by
  intro η hη
  have hev : ∀ᶠ R : ℝ in atTop, R ^ (-(δ₀ - δ)) < η / (Kh + 1) ∧ 1 ≤ R :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < δ₀ - δ)).eventually
      (gt_mem_nhds (div_pos hη (by linarith)))).and (eventually_ge_atTop 1)
  obtain ⟨R, hR, hR1⟩ := hev.exists
  obtain ⟨K, hK⟩ := bdd_ell hc hhc (R - 1)
  refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
  have hKx := hK x hx
  rw [pp_of_mem hx] at hKx ⊢
  have hWt := Wt_nonneg C hc hx δ₀
  have hW1 := one_le_W hc hx
  have hU1 := one_le_U C x
  unfold Wt
  by_cases hWR : 1 + ∑ i, c i * x i ≤ R
  · have : |h x| ≤ max K 0 := (hKx (by linarith)).trans (le_max_left _ _)
    rw [clampL_eq this, sub_self, abs_zero]
    exact mul_nonneg hη.le hWt
  · push_neg at hWR
    refine (clampL_sub_le (le_max_right _ _) _).trans ?_
    have hg := (hgrowth x hx).le
    have hW0 : 0 < 1 + ∑ i, c i * x i := by linarith
    have hsplit : (1 + ∑ i, c i * x i) ^ δ =
        (1 + ∑ i, c i * x i) ^ (-(δ₀ - δ)) * (1 + ∑ i, c i * x i) ^ δ₀ := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hmono : (1 + ∑ i, c i * x i) ^ (-(δ₀ - δ)) ≤ R ^ (-(δ₀ - δ)) := by
      rw [Real.rpow_neg hW0.le, Real.rpow_neg (by linarith)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_le_rpow (by linarith) hWR.le (by linarith))
    have hr0 : 0 ≤ R ^ (-(δ₀ - δ)) := Real.rpow_nonneg (by linarith) _
    have hKR : Kh * (1 + ∑ i, c i * x i) ^ (-(δ₀ - δ)) ≤ η := by
      have h1 := (lt_div_iff₀ (by linarith : (0 : ℝ) < Kh + 1)).1 hR
      have h2 : Kh * (1 + ∑ i, c i * x i) ^ (-(δ₀ - δ)) ≤ Kh * R ^ (-(δ₀ - δ)) :=
        mul_le_mul_of_nonneg_left hmono hKh
      nlinarith
    have hP0 : 0 ≤ (1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2)) :=
      mul_nonneg (Real.rpow_nonneg hW0.le _) (by linarith)
    calc |h x| ≤ Kh * (1 + ∑ i, c i * x i) ^ δ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2)) := hg
      _ = (Kh * (1 + ∑ i, c i * x i) ^ (-(δ₀ - δ))) *
          ((1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) := by
          rw [hsplit]; ring
      _ ≤ η * ((1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) :=
          mul_le_mul_of_nonneg_right hKR hP0

end L34Lib

open StochKolmogorov.Persist EthierKurtz L34Lib in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M) (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (xs : ℕ → SDEState n) (hxs : ∀ k, xs k ∈ orthant n ∧ l1 (xs k) ≤ M)
    (Ts : ℕ → ℝ) (hTs : ∀ k, 1 < Ts k) (hTs_lim : Tendsto Ts atTop atTop)
    (π : Measure (SDEState n)) (hπ : IsInvariant P X π)
    (hweak : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 (∫ y, h y ∂π)))
    (h : SDEState n → ℝ) (hcont : ContinuousOn h (orthant n)) (Kh δ : ℝ) (hKh : 0 ≤ Kh)
    (hδ : δ < δ₀)
    (hgrowth : ∀ x ∈ orthant n, |h x| <
      Kh * (1 + ∑ i, c i * x i) ^ δ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) :
    (∀ k, Integrable h (occMean P X (xs k) (Ts k))) ∧ Integrable h π ∧
      Tendsto (fun k => ∫ y, h y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 (∫ y, h y ∂π)) := by
  haveI hP : IsProbabilityMeasure P := hX.1
  obtain ⟨H₁, H₂, hH₁, hH₂, -, h38, -⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P C B X hX c γb hA δ₀ hδ₀
  have L31 := StochKolmogorov.Persist.lemma_3_1 hn P C B hX.2.1 c γb hA
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hδ₀pos : 0 < δ₀ := hδ₀.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hA.2.1 i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hA.2.1 i).2.continuousOn
  have hsol : ∀ x ∈ orthant n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) (X x) := hX.2.2
  have hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
    intro x hx
    have hface : x ∈ faceOpen (Finset.univ.filter fun i => 0 < x i) := by
      refine ⟨hx, fun i hi => ?_, fun i hi => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        exact le_antisymm hi (hx i)
      · simpa using hi
    filter_upwards [L31.2.2.1 _ x hface (X x) (hsol x hx)] with ω hω t using (hω t).1
  have hΦc : Continuous fun y => Wt C c δ₀ (posPart y) := Wt_pp_cont C c δ₀ hδ₀pos.le hfc hgc
  have hΦ0 : ∀ y, 0 ≤ Wt C c δ₀ (posPart y) := fun y => Wt_nonneg C hc (pp_mem y) δ₀
  have hsc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => (hc i).le
  have hA0 : 0 ≤ (1 + (∑ i, c i) * M) ^ δ₀ :=
    Real.rpow_nonneg (by nlinarith) _
  have hBd : 0 ≤ H₂ * ((1 + (∑ i, c i) * M) ^ δ₀ + 1) := mul_nonneg hH₂.le (by linarith)
  have hμp : ∀ k, IsProbabilityMeasure (occMean P X (xs k) (Ts k)) := fun k =>
    occ_prob P X (xs k) (hsol _ (hxs k).1).1 (hsol _ (hxs k).1).2.1 (by linarith [hTs k])
  have hμS : ∀ k, ∀ᵐ y ∂(occMean P X (xs k) (Ts k)), y ∈ orthant n := fun k =>
    occ_ae P X (xs k) (hsol _ (hxs k).1).1 (hsol _ (hxs k).1).2.1 (Ts k) (hinv _ (hxs k).1)
  have hμb : ∀ k, ∫⁻ y, ENNReal.ofReal (Wt C c δ₀ (posPart y)) ∂(occMean P X (xs k) (Ts k)) ≤
      ENNReal.ofReal (H₂ * ((1 + (∑ i, c i) * M) ^ δ₀ + 1)) := by
    intro k
    have hx := (hxs k).1
    have hT := hTs k
    have hT0 : 0 ≤ Ts k := by linarith
    have h38k := h38 (xs k) hx (Ts k).toNNReal (Real.toNNReal_pos.2 (by linarith))
    rw [Real.coe_toNNReal _ hT0] at h38k
    refine occ_bound P C c δ₀ X (xs k) (hsol _ hx).1 (hsol _ hx).2.1 hT (hinv _ hx)
      hΦc.measurable H₂ _ _ hH₂ (Real.rpow_nonneg (by linarith [one_le_W hc hx]) _) ?_ h38k
    apply Real.rpow_le_rpow (by linarith [one_le_W hc hx]) _ hδ₀pos.le
    have : ∑ i, c i * xs k i ≤ (∑ i, c i) * M := by
      calc ∑ i, c i * xs k i ≤ ∑ i, c i * l1 (xs k) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              ((le_abs_self (xs k i)).trans (Finset.single_le_sum (f := fun j => |xs k j|)
                (fun j _ => abs_nonneg _) (Finset.mem_univ i))) (hc i).le
        _ = (∑ i, c i) * l1 (xs k) := by rw [Finset.sum_mul]
        _ ≤ (∑ i, c i) * M := mul_le_mul_of_nonneg_left (hxs k).2 hsc0
    linarith
  haveI hπp : IsProbabilityMeasure π := hπ.1
  have hπS : ∀ᵐ y ∂π, y ∈ orthant n := by rw [ae_iff]; exact hπ.2.1
  have hπb := fatou_weak (fun k => occMean P X (xs k) (Ts k)) hμp π _ hΦc hΦ0 _ hBd hμb hweak
  have hhc : Continuous fun y => h (posPart y) := hcont.comp_continuous pp_cont pp_mem
  have hdom : ∀ y ∈ orthant n, |h (posPart y)| ≤ Kh * Wt C c δ₀ (posPart y) := by
    intro y hy
    rw [pp_of_mem hy]
    refine (hgrowth y hy).le.trans ?_
    unfold Wt
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_W hc hy) hδ.le) hKh) (by linarith [one_le_U C y])
  have hint : ∀ (ν : Measure (SDEState n)), (∀ᵐ y ∂ν, y ∈ orthant n) →
      ∫⁻ y, ENNReal.ofReal (Wt C c δ₀ (posPart y)) ∂ν ≤
        ENNReal.ofReal (H₂ * ((1 + (∑ i, c i) * M) ^ δ₀ + 1)) →
      Integrable (fun y => h (posPart y)) ν ∧ (fun y => h (posPart y)) =ᵐ[ν] h := by
    intro ν hS hb
    refine ⟨Integrable.mono' ((wt_integrable hΦc.measurable (ae_of_all _ hΦ0) hb).const_mul Kh)
      hhc.aestronglyMeasurable (hS.mono fun y hy => by rw [Real.norm_eq_abs]; exact hdom y hy),
      hS.mono fun y hy => by simp only [pp_of_mem hy]⟩
  have hk := fun k => hint _ (hμS k) (hμb k)
  have hπi := hint π hπS hπb
  refine ⟨fun k => (hk k).1.congr (hk k).2, hπi.1.congr hπi.2, ?_⟩
  have hlim := ui_limit (fun k => occMean P X (xs k) (Ts k)) hμp π (fun y => h (posPart y))
    (fun y => Wt C c δ₀ (posPart y)) hhc hΦc.measurable (orthant n) (fun y _ => hΦ0 y) _ hBd
    hμb hπb hμS hπS (tail_est C hc hδ hKh h hhc hgrowth) hweak (fun k => (hk k).1) hπi.1
  rw [integral_congr_ae hπi.2] at hlim
  exact hlim.congr fun k => integral_congr_ae (hk k).2
