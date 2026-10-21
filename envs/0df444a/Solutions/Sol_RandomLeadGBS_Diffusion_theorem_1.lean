-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:58:54.997021+00:00
-- url     : https://prove2.me/submissions/5fb5e8d8-d39c-40b0-a7cd-122f7151058f

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_theorem_1_stability
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_9
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5_centered
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_8_centered
import Theorems.Thm_RandomLeadGBS_Diffusion_eq_36_centered

open Filter Topology MeasureTheory ProbabilityTheory
open RandomLeadGBS.Diffusion

namespace GBSThm1

variable {ι : Type*} [Countable ι]

/-- The law of `u` under the mass function `w`. -/
noncomputable def dmeas (w : ι → ℝ) (u : ι → ℝ) : Measure ℝ :=
  Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (u i))

lemma dmeas_apply (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (S : Set ℝ)
    (hS : MeasurableSet S) [DecidablePred (· ∈ S)] :
    dmeas w u S = ENNReal.ofReal (∑' i, if u i ∈ S then w i else 0) := by
  have hs' : Summable (fun i => if u i ∈ S then w i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
      (fun i => by split_ifs; exact le_rfl; exact hw i) hs
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by split_ifs; exact hw i; exact le_rfl) hs']
  unfold dmeas
  rw [Measure.sum_apply_of_countable]
  congr 1; funext i
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  by_cases h : u i ∈ S
  · simp [h]
  · simp [h]

lemma dmeas_prob (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (h1 : ∑' i, w i = 1) :
    IsProbabilityMeasure (dmeas w u) := by
  constructor
  classical
  rw [dmeas_apply w u hw hs Set.univ MeasurableSet.univ]
  simp [h1]

lemma dmeas_integrable (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (g : ℝ → ℝ) (hg : Continuous g)
    (hsum : Summable (fun i => w i * |g (u i)|)) : Integrable g (dmeas w u) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral dmeas
  rw [lintegral_sum_measure]
  have : ∀ i, ∫⁻ x, ‖g x‖ₑ ∂(ENNReal.ofReal (w i) • Measure.dirac (u i)) =
      ENNReal.ofReal (w i * |g (u i)|) := by
    intro i
    rw [lintegral_smul_measure, lintegral_dirac, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_mul (hw i), smul_eq_mul]
  simp only [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (abs_nonneg _)) hsum]
  exact ENNReal.ofReal_lt_top

lemma dmeas_integral (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (g : ℝ → ℝ)
    (hint : Integrable g (dmeas w u)) : ∫ x, g x ∂(dmeas w u) = ∑' i, w i * g (u i) := by
  unfold dmeas at hint ⊢
  rw [integral_sum_measure hint]
  congr 1; funext i
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

open Real Set
open scoped NNReal
lemma half_mean (v : NNReal) (hv : v ≠ 0) :
    ∫ x, max (-x) 0 ∂(gaussianReal 0 v) = √((v : ℝ) / (2 * π)) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1 : ∫ x, gaussianPDFReal 0 v x * max (-x) 0 = ∫ x, gaussianPDFReal 0 v x * max x 0 := by
    rw [← integral_neg_eq_self (fun x => gaussianPDFReal 0 v x * max (-x) 0)]
    congr 1; funext x
    simp only [neg_neg, gaussianPDFReal, sub_zero, even_two, Even.neg_pow]
  rw [h1]
  have h2 : ∫ x, gaussianPDFReal 0 v x * max x 0 =
      ∫ x in Ioi (0 : ℝ), (√(2 * π * v))⁻¹ * (x ^ (1 : ℝ) * rexp (-(1 / (2 * v)) * x ^ (2 : ℝ))) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (mem_Ioi.mpr hx)]
      simp only [gaussianPDFReal, sub_zero, rpow_one, max_eq_left hx.le]
      rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
      have e : -x ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * x ^ 2 := by ring
      rw [e]; ring
    · rw [indicator_of_notMem (by simpa using hx)]
      simp [max_eq_right (not_lt.mp hx)]
  rw [h2, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity)]
  have e1 : (-((1 : ℝ) + 1) / 2) = -1 := by norm_num
  have e2 : (((1 : ℝ) + 1) / 2) = 1 := by norm_num
  rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one]
  have hπ : 0 < π := Real.pi_pos
  have hs : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [show ((v : ℝ) / (2 * π)) = ((√(2 * π * v))⁻¹ * v) ^ 2 by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; field_simp]
  rw [Real.sqrt_sq (by positivity)]
  field_simp



end GBSThm1

open GBSThm1

theorem solution (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ s₀ : State, ∀ s : State, Relation.ReflTransGen (Step P r) s s₀) ∧
    (∃ r₀ : ℝ, ∀ r ≥ r₀, ∃! p : State → ℝ, IsStationary P r p) ∧
    ∀ p : ℝ → State → ℝ, (∀ᶠ r in atTop, IsStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' s, p r s * g (scaled P r s)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' s, p r s * max (scaled P r s) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' s, p r s * max (-(scaled P r s)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by
  obtain ⟨hst1, hst2⟩ := theorem_1_stability P hP
  refine ⟨hst1, hst2, fun p hp => ?_⟩
  classical
  obtain ⟨hex, hlim⟩ := lemma_5_centered P hP
  set N := gaussianReal 0 (1 / (P.β * P.γ)).toNNReal with hN
  set K : ℝ := (2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)) with hK
  let q : ℝ → ℤ → ℝ := fun r => if h : 0 < r then (hex r h).choose else fun _ => 0
  have hqs : ∀ r, 0 < r → IsArtStationary P r (q r) := by
    intro r hr; simp only [q, dif_pos hr]; exact (hex r hr).choose_spec
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  have hq : ∀ᶠ r in atTop, IsArtStationary P r (q r) := by
    filter_upwards [hpos] with r hr using hqs r hr
  obtain ⟨hw5, hp5, hn5⟩ := hlim q hq
  obtain ⟨hsum36, ht36⟩ := eq_36_centered P hP p hp q hq
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((((hp.and hq).and hsum36).and hpos))
  -- the two laws
  let uq : ℝ → ℤ → ℝ := fun r j => ((j : ℝ) - P.xs r) / Real.sqrt r
  let up : ℝ → State → ℝ := fun r s => scaled P r s
  let μ : ℝ → Measure ℝ := fun r => if R ≤ r then dmeas (q r) (uq r) else N
  let ν : ℝ → Measure ℝ := fun r => if R ≤ r then dmeas (p r) (up r) else N
  have hNp : IsProbabilityMeasure N := by rw [hN]; infer_instance
  have hNid : Integrable (fun x : ℝ => x) N :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  -- facts for r ≥ R
  have facts : ∀ r, R ≤ r →
      (∀ j, 0 ≤ q r j) ∧ Summable (q r) ∧ ∑' j, q r j = 1 ∧
      (∀ s, 0 ≤ p r s) ∧ Summable (p r) ∧ ∑' s, p r s = 1 ∧
      Summable (fun j => q r j * |uq r j|) ∧ Summable (fun s => p r s * |up r s|) := by
    intro r hr
    obtain ⟨⟨⟨hpr, hqr⟩, ⟨hs1, hs2⟩⟩, hr0⟩ := hR r hr
    obtain ⟨q0, qs, q1, -, -⟩ := hqr
    obtain ⟨p0, ps, p1, -, -⟩ := hpr
    refine ⟨q0, qs, q1, p0, ps, p1, ?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (q0 j) (abs_nonneg _)) (fun j => ?_)
        ((hs2.abs.add (qs.mul_right |P.xs r|)).div_const (Real.sqrt r))
      simp only [uq]
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hr0), abs_mul, abs_of_nonneg (q0 j), mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg r)
      have := abs_sub ((j : ℝ)) (P.xs r)
      have := mul_le_mul_of_nonneg_left this (q0 j)
      linarith
    · refine Summable.of_nonneg_of_le (fun s => mul_nonneg (p0 s) (abs_nonneg _)) (fun s => ?_)
        ((hs1.abs.add (ps.mul_right |P.xs r|)).div_const (Real.sqrt r))
      simp only [up, scaled]
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hr0), abs_mul, abs_of_nonneg (p0 s), mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg r)
      have := abs_sub ((s.1 : ℝ)) (P.xs r)
      have := mul_le_mul_of_nonneg_left this (p0 s)
      linarith
  -- integrals against the laws
  have intq : ∀ r, R ≤ r → ∀ g : ℝ → ℝ, Continuous g → ((∀ x, |g x| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C) →
      ∫ x, g x ∂(μ r) = ∑' j, q r j * g (uq r j) := by
    intro r hr g hg hgb
    obtain ⟨q0, qs, -, -, -, -, hqa, -⟩ := facts r hr
    simp only [μ, if_pos hr]
    apply dmeas_integral _ _ q0
    apply dmeas_integrable _ _ q0 _ hg
    rcases hgb with h | ⟨C, hC⟩
    · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (q0 j) (abs_nonneg _))
        (fun j => mul_le_mul_of_nonneg_left (h _) (q0 j)) ?_
      simpa [mul_add] using qs.add hqa
    · exact Summable.of_nonneg_of_le (fun j => mul_nonneg (q0 j) (abs_nonneg _))
        (fun j => mul_le_mul_of_nonneg_left (hC _) (q0 j)) (qs.mul_right C)
  have intp : ∀ r, R ≤ r → ∀ g : ℝ → ℝ, Continuous g → ((∀ x, |g x| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C) →
      ∫ x, g x ∂(ν r) = ∑' s, p r s * g (up r s) := by
    intro r hr g hg hgb
    obtain ⟨-, -, -, p0, ps, -, -, hpa⟩ := facts r hr
    simp only [ν, if_pos hr]
    apply dmeas_integral _ _ p0
    apply dmeas_integrable _ _ p0 _ hg
    rcases hgb with h | ⟨C, hC⟩
    · refine Summable.of_nonneg_of_le (fun s => mul_nonneg (p0 s) (abs_nonneg _))
        (fun s => mul_le_mul_of_nonneg_left (h _) (p0 s)) ?_
      simpa [mul_add] using ps.add hpa
    · exact Summable.of_nonneg_of_le (fun s => mul_nonneg (p0 s) (abs_nonneg _))
        (fun s => mul_le_mul_of_nonneg_left (hC _) (p0 s)) (ps.mul_right C)
  have hev : ∀ᶠ r : ℝ in atTop, R ≤ r := eventually_ge_atTop R
  have bcf_bound : ∀ g : BoundedContinuousFunction ℝ ℝ,
      (∀ x, |g x| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C :=
    fun g => Or.inr ⟨‖g‖, fun y => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm y⟩
  have pos_bound : (∀ x : ℝ, |max x 0| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x : ℝ, |max x 0| ≤ C := Or.inl (fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    have := le_abs_self x; have := abs_nonneg x
    exact max_le (by linarith) (by linarith))
  have neg_bound : (∀ x : ℝ, |max (-x) 0| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x : ℝ, |max (-x) 0| ≤ C :=
    Or.inl (fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    have := neg_le_abs x; have := abs_nonneg x
    exact max_le (by linarith) (by linarith))
  have id_bound : (∀ x : ℝ, |id x| ≤ 1 + |x|) ∨ ∃ C : ℝ, ∀ x : ℝ, |id x| ≤ C :=
    Or.inl (fun x => by simp)
  -- Gaussian half-means
  have hmeanN : ∫ x, x ∂N = 0 := by rw [hN, integral_id_gaussianReal]
  have hβ := hP.1
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hP.2.1
  have hβγ : 0 < P.β * P.γ := by positivity
  have hπ : 0 < Real.pi := Real.pi_pos
  have hvval : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 1 / (P.β * P.γ) :=
    Real.coe_toNNReal _ (by positivity)
  have hv : (1 / (P.β * P.γ)).toNNReal ≠ 0 := by
    intro h0
    have : (((1 / (P.β * P.γ)).toNNReal : NNReal) : ℝ) = 0 := by rw [h0]; rfl
    rw [hvval] at this
    have : 0 < 1 / (P.β * P.γ) := by positivity
    linarith
  have hnegN : ∫ x, max (-x) 0 ∂N = K := by
    rw [hN, half_mean _ hv, hvval, hK]
    rw [show 1 / (P.β * P.γ) / (2 * Real.pi) = (2 * Real.pi * P.β * P.γ)⁻¹ by field_simp]
    rw [Real.sqrt_inv, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  have hposN : ∫ x, max x 0 ∂N = K := by
    have e : ∫ x, x ∂N = ∫ x, max x 0 ∂N - ∫ x, max (-x) 0 ∂N := by
      rw [← integral_sub hNid.pos_part hNid.neg_part]
      congr 1; funext x; exact (max_zero_sub_max_neg_zero_eq_self x).symm
    linarith
  have hμp : ∀ r, 0 < r → IsProbabilityMeasure (μ r) := by
    intro r _
    by_cases h : R ≤ r
    · simp only [μ, if_pos h]
      obtain ⟨q0, qs, q1, -⟩ := facts r h
      exact dmeas_prob _ _ q0 qs q1
    · simp only [μ, if_neg h]; exact hNp
  have hνp : ∀ r, 0 < r → IsProbabilityMeasure (ν r) := by
    intro r _
    by_cases h : R ≤ r
    · simp only [ν, if_pos h]
      obtain ⟨-, -, -, p0, ps, p1, -⟩ := facts r h
      exact dmeas_prob _ _ p0 ps p1
    · simp only [ν, if_neg h]; exact hNp
  have h32 : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun r => ∫ x, g x ∂(μ r)) atTop (𝓝 (∫ x, g x ∂N)) := by
    intro g
    refine (hw5 g).congr' ?_
    filter_upwards [hev] with r hr
    exact (intq r hr g g.continuous (bcf_bound g)).symm
  have h33p : Tendsto (fun r => ∫ x, max x 0 ∂(μ r)) atTop (𝓝 (∫ x, max x 0 ∂N)) := by
    rw [hposN]
    refine hp5.congr' ?_
    filter_upwards [hev] with r hr
    exact (intq r hr _ (continuous_id.max continuous_const) pos_bound).symm
  have h33m : Tendsto (fun r => ∫ x, max (-x) 0 ∂(μ r)) atTop (𝓝 (∫ x, max (-x) 0 ∂N)) := by
    rw [hnegN]
    refine hn5.congr' ?_
    filter_upwards [hev] with r hr
    exact (intq r hr _ (continuous_neg.max continuous_const) neg_bound).symm
  have hst : ∀ r, 0 < r → ∀ x : ℝ, μ r (Set.Ioi x) ≤ ν r (Set.Ioi x) := by
    intro r hr0 x
    by_cases h : R ≤ r
    · obtain ⟨q0, qs, -, p0, ps, -, -⟩ := facts r h
      obtain ⟨⟨⟨hpr, hqr⟩, -⟩, -⟩ := hR r h
      simp only [μ, ν, if_pos h]
      rw [dmeas_apply _ _ q0 qs _ measurableSet_Ioi, dmeas_apply _ _ p0 ps _ measurableSet_Ioi]
      apply ENNReal.ofReal_le_ofReal
      have h8 := (lemma_8_centered P hP r hr0 (p r) hpr (q r) hqr).1 (P.xs r + x * Real.sqrt r)
      have hsq := Real.sqrt_pos.mpr hr0
      have e1 : ∀ j : ℤ, (uq r j ∈ Set.Ioi x) = (P.xs r + x * Real.sqrt r < (j : ℝ)) := by
        intro j; apply propext; simp only [uq, Set.mem_Ioi]; rw [lt_div_iff₀ hsq]
        constructor <;> intro h <;> linarith
      have e2 : ∀ s : State, (up r s ∈ Set.Ioi x) = (P.xs r + x * Real.sqrt r < (s.1 : ℝ)) := by
        intro s; apply propext; simp only [up, scaled, Set.mem_Ioi]; rw [lt_div_iff₀ hsq]
        constructor <;> intro h <;> linarith
      simp only [e1, e2]
      exact h8
    · simp only [μ, ν, if_neg h]; exact le_rfl
  have hint : ∀ r, 0 < r → Integrable (fun x : ℝ => x) (μ r) ∧ Integrable (fun x : ℝ => x) (ν r) := by
    intro r _
    by_cases h : R ≤ r
    · obtain ⟨q0, -, -, p0, -, -, hqa, hpa⟩ := facts r h
      simp only [μ, ν, if_pos h]
      exact ⟨dmeas_integrable _ _ q0 _ continuous_id hqa, dmeas_integrable _ _ p0 _ continuous_id hpa⟩
    · simp only [μ, ν, if_neg h]; exact ⟨hNid, hNid⟩
  have hmean : Tendsto (fun r => ∫ x, x ∂(ν r) - ∫ x, x ∂(μ r)) atTop (𝓝 0) := by
    refine ht36.congr' ?_
    filter_upwards [hev] with r hr
    obtain ⟨-, qs, q1, -, ps, p1, -⟩ := facts r hr
    obtain ⟨⟨-, hs1, hs2⟩, -⟩ := hR r hr
    have i1 := intp r hr _ continuous_id id_bound
    have i2 := intq r hr _ continuous_id id_bound
    simp only [id] at i1 i2
    rw [i1, i2]
    have ep : (fun s : State => p r s * up r s) =
        fun s => p r s * ((s.1 : ℝ) / Real.sqrt r) - p r s * (P.xs r / Real.sqrt r) := by
      funext s; simp only [up, scaled]; ring
    have eq' : (fun j : ℤ => q r j * uq r j) =
        fun j => q r j * ((j : ℝ) / Real.sqrt r) - q r j * (P.xs r / Real.sqrt r) := by
      funext j; simp only [uq]; ring
    have sp : Summable (fun s : State => p r s * ((s.1 : ℝ) / Real.sqrt r)) := by
      simpa [mul_div_assoc'] using hs1.div_const (Real.sqrt r)
    have sq : Summable (fun j : ℤ => q r j * ((j : ℝ) / Real.sqrt r)) := by
      simpa [mul_div_assoc'] using hs2.div_const (Real.sqrt r)
    rw [ep, eq', Summable.tsum_sub sp (ps.mul_right _), Summable.tsum_sub sq (qs.mul_right _),
      tsum_mul_right, tsum_mul_right, p1, q1]
    ring
  obtain ⟨c1, c2, c3⟩ := lemma_9 μ ν N hμp hνp hNp h32 hNid h33p h33m hst hint hmean
  refine ⟨fun g => ?_, ?_, ?_⟩
  · refine (c1 g).congr' ?_
    filter_upwards [hev] with r hr
    exact intp r hr g g.continuous (bcf_bound g)
  · rw [← hposN]
    refine c2.congr' ?_
    filter_upwards [hev] with r hr
    exact intp r hr _ (continuous_id.max continuous_const) pos_bound
  · rw [← hnegN]
    refine c3.congr' ?_
    filter_upwards [hev] with r hr
    exact intp r hr _ (continuous_neg.max continuous_const) neg_bound
