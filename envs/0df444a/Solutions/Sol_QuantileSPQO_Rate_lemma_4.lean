-- Prove2me | solution 1 for QuantileSPQO.Rate.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:48:14.874897+00:00
-- url     : https://prove2.me/submissions/3454ee17-af6e-4313-a1fe-6ae735e97a9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting
import Theorems.Thm_QuantileSPQO_Rate_lemma_1
import Theorems.Thm_QuantileSPQO_Rate_lemma_3

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace SPQOL4Aux
open QuantileSPQO.Rate

lemma proj1d {I : Set ℝ} {Pq : ℝ → ℝ} (h : IsIntervalProj I Pq) {z : ℝ} (hz : z ∈ I) (x : ℝ) :
    |Pq x - z| ≤ |x - z| := by
  obtain ⟨hp, hmin⟩ := h.proj x
  have hmz := hmin z hz
  rcases le_total z x with hzx | hxz
  · -- z ≤ x
    have h1 : z ≤ Pq x ∨ Pq x < z := le_or_gt z (Pq x)
    rcases h1 with h1 | h1
    · by_cases h2 : Pq x ≤ x
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · push Not at h2
        have hx : x ∈ I := h.ordConnected.out hz hp ⟨hzx, h2.le⟩
        have h3 : |x - Pq x| = 0 := le_antisymm (by simpa using hmin x hx) (abs_nonneg _)
        rw [abs_eq_zero] at h3
        linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - z)] at hmz ⊢
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - Pq x)] at hmz
      rw [abs_of_neg (by linarith : Pq x - z < 0)]
      linarith
  · -- x ≤ z
    have h1 : Pq x ≤ z ∨ z < Pq x := le_or_gt (Pq x) z
    rcases h1 with h1 | h1
    · by_cases h2 : x ≤ Pq x
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · push Not at h2
        have hx : x ∈ I := h.ordConnected.out hp hz ⟨h2.le, hxz⟩
        have h3 : |x - Pq x| = 0 := le_antisymm (by simpa using hmin x hx) (abs_nonneg _)
        rw [abs_eq_zero] at h3
        linarith
    · rw [abs_of_nonpos (by linarith : x - z ≤ 0)] at hmz ⊢
      rw [abs_of_nonpos (by linarith : x - Pq x ≤ 0)] at hmz
      rw [abs_of_pos (by linarith : 0 < Pq x - z)]
      linarith

lemma cdf_nonneg {d : ℕ} (M : Model d) (y : ℝ) (θ : E d) : 0 ≤ cdf M y θ := ENNReal.toReal_nonneg

lemma cdf_le_one {d : ℕ} (M : Model d) (hprob : ∀ θ, IsProbabilityMeasure (M.law θ)) (y : ℝ)
    (θ : E d) : cdf M y θ ≤ 1 := by
  unfold cdf
  haveI := hprob θ
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma cond_fixed {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (P : Measure Ω)
    [IsProbabilityMeasure P] (X H Φ : Ω → ℝ) (hX : Integrable X P) (hH : StronglyMeasurable[m] H)
    (Hb : ℝ) (hHb : ∀ ω, |H ω| ≤ Hb) (hce : P[X | m] =ᵐ[P] Φ) :
    ∫ ω, H ω * X ω ∂P = ∫ ω, H ω * Φ ω ∂P := by
  have hHX : Integrable (H * X) P :=
    hX.bdd_mul (c := Hb) (hH.mono hm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hHb ω)
  calc ∫ ω, H ω * X ω ∂P = ∫ ω, (P[H * X | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (H * P[X | m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hH hHX hX)
    _ = ∫ ω, H ω * Φ ω ∂P := integral_congr_ae (hce.mono fun ω h => by simp [h])

lemma cond_threshold {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (M : Model d) (hprob : ∀ θ, IsProbabilityMeasure (M.law θ))
    (hcont : ∀ θ, Continuous (fun y => cdf M y θ))
    (Y : Ω → ℝ) (hY : Measurable[m0] Y) (θ : Ω → E d) (q G : Ω → ℝ)
    (hq : StronglyMeasurable[m] q) (hG : StronglyMeasurable[m] G) (Qb Gb : ℝ)
    (hqb : ∀ ω, |q ω| ≤ Qb) (hGb : ∀ ω, |G ω| ≤ Gb)
    (hs : ∀ v : ℝ, P[fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω) | m] =ᵐ[P]
      fun ω => cdf M v (θ ω)) :
    AEStronglyMeasurable (fun ω => cdf M (q ω) (θ ω)) P ∧
    ∫ ω, G ω * (if Y ω ≤ q ω then 1 else 0) ∂P = ∫ ω, G ω * cdf M (q ω) (θ ω) ∂P := by
  -- measurability of the fixed-level cdf
  have hcdfv : ∀ v : ℝ, AEStronglyMeasurable (fun ω => cdf M v (θ ω)) P := fun v =>
    ((stronglyMeasurable_condExp (m := m) (μ := P)).mono hm).aestronglyMeasurable.congr (hs v)
  have hind : ∀ v : ℝ, (fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω))
      = fun ω => if Y ω ≤ v then (1:ℝ) else 0 := by
    intro v; funext ω; by_cases h : Y ω ≤ v <;> simp [Set.indicator_apply, h]
  have hindI : ∀ v : ℝ, Integrable (fun ω => if Y ω ≤ v then (1:ℝ) else 0) P := by
    intro v
    rw [← hind v]
    have : (fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω))
        = (Y ⁻¹' Set.Iic v).indicator (fun _ => (1:ℝ)) := by
      funext ω; by_cases h : Y ω ≤ v <;> simp [Set.indicator_apply, h]
    rw [this]
    exact (integrable_const (1:ℝ)).indicator (hY measurableSet_Iic)
  -- fixed level identity
  have hfix : ∀ (v : ℝ) (H : Ω → ℝ), StronglyMeasurable[m] H → (∀ ω, |H ω| ≤ Gb) →
      ∫ ω, H ω * (if Y ω ≤ v then 1 else 0) ∂P = ∫ ω, H ω * cdf M v (θ ω) ∂P := by
    intro v H hH hHb
    have hsv := hs v
    rw [hind v] at hsv
    exact cond_fixed hm P (fun ω => if Y ω ≤ v then (1:ℝ) else 0) H (fun ω => cdf M v (θ ω))
      (hindI v) hH Gb hHb hsv
  -- dyadic approximation
  set s : ℕ → ℝ := fun n => (2:ℝ) ^ n with hsdef
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  set qn : ℕ → Ω → ℝ := fun n ω => (⌈q ω * s n⌉ : ℝ) / s n with hqn
  have hqn_ge : ∀ n ω, q ω ≤ qn n ω := by
    intro n ω
    simp only [hqn]
    rw [le_div_iff₀ (hs0 n)]
    exact Int.le_ceil _
  have hqn_lt : ∀ n ω, qn n ω < q ω + 1 / s n := by
    intro n ω
    simp only [hqn]
    rw [div_lt_iff₀ (hs0 n), add_mul, div_mul_cancel₀ _ (hs0 n).ne']
    exact Int.ceil_lt_add_one _
  have hceil_meas : ∀ n, Measurable[m] (fun ω => ⌈q ω * s n⌉) := fun n =>
    Int.measurable_ceil.comp (hq.measurable.mul_const _)
  set N : ℕ → ℤ := fun n => ⌈Qb * s n⌉ + 1 with hN
  have hmemJ : ∀ n ω, ⌈q ω * s n⌉ ∈ Finset.Icc (-N n) (N n) := by
    intro n ω
    rw [Finset.mem_Icc]
    have h1 := hqb ω
    have hsn := hs0 n
    constructor
    · have : -(Qb * s n) ≤ q ω * s n := by
        have := neg_abs_le (q ω); nlinarith
      have h2 : (-(N n) : ℝ) ≤ ⌈q ω * s n⌉ := by
        simp only [hN]; push_cast
        have := Int.le_ceil (Qb * s n)
        have := Int.le_ceil (q ω * s n)
        linarith
      exact_mod_cast h2
    · simp only [hN]
      have : q ω * s n ≤ Qb * s n := by
        have := le_abs_self (q ω); nlinarith
      have := Int.ceil_mono this
      omega
  have hrep : ∀ (n : ℕ) (Φ : ℝ → ℝ) (ω : Ω), Φ (qn n ω) =
      ∑ j ∈ Finset.Icc (-N n) (N n), (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0) * Φ ((j : ℝ) / s n) := by
    intro n Φ ω
    rw [Finset.sum_eq_single_of_mem (⌈q ω * s n⌉) (hmemJ n ω)]
    · simp [hqn]
    · intro j _ hj; simp [Ne.symm hj]
  have hHj : ∀ (n : ℕ) (j : ℤ), StronglyMeasurable[m]
      (fun ω => G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) := by
    intro n j
    refine hG.mul ?_
    exact (Measurable.ite ((hceil_meas n) (measurableSet_singleton j)) measurable_const
      measurable_const).stronglyMeasurable
  have hHjb : ∀ (n : ℕ) (j : ℤ) (ω : Ω),
      |G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)| ≤ Gb := by
    intro n j ω
    split_ifs
    · simpa using hGb ω
    · simpa using (abs_nonneg _).trans (hGb ω)
  have hcdfqn : ∀ n, AEStronglyMeasurable (fun ω => cdf M (qn n ω) (θ ω)) P := by
    intro n
    have : (fun ω => cdf M (qn n ω) (θ ω)) = fun ω => ∑ j ∈ Finset.Icc (-N n) (N n),
        (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0) * cdf M ((j : ℝ) / s n) (θ ω) := by
      funext ω; exact hrep n (fun y => cdf M y (θ ω)) ω
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ?_)
    refine AEStronglyMeasurable.mul ?_ (hcdfv _)
    exact ((Measurable.ite ((hceil_meas n) (measurableSet_singleton j)) measurable_const
      measurable_const).mono hm le_rfl).aestronglyMeasurable
  have hGaesm : AEStronglyMeasurable G P := (hG.mono hm).aestronglyMeasurable
  have hYle : ∀ v : ℝ, Measurable[m0] (fun ω => if Y ω ≤ v then (1:ℝ) else 0) := fun v =>
    Measurable.ite (hY measurableSet_Iic) measurable_const measurable_const
  -- identity at level n
  have hlevel : ∀ n, ∫ ω, G ω * (if Y ω ≤ qn n ω then 1 else 0) ∂P
      = ∫ ω, G ω * cdf M (qn n ω) (θ ω) ∂P := by
    intro n
    have e1 : (fun ω => G ω * (if Y ω ≤ qn n ω then (1:ℝ) else 0)) = fun ω =>
        ∑ j ∈ Finset.Icc (-N n) (N n), (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) *
          (if Y ω ≤ (j : ℝ) / s n then 1 else 0) := by
      funext ω
      rw [hrep n (fun y => if Y ω ≤ y then (1:ℝ) else 0) ω, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have e2 : (fun ω => G ω * cdf M (qn n ω) (θ ω)) = fun ω =>
        ∑ j ∈ Finset.Icc (-N n) (N n), (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) *
          cdf M ((j : ℝ) / s n) (θ ω) := by
      funext ω
      rw [hrep n (fun y => cdf M y (θ ω)) ω, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, e2, integral_finsetSum, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      exact hfix _ _ (hHj n j) (hHjb n j)
    · intro j _
      refine Integrable.of_bound (((hHj n j).mono hm).aestronglyMeasurable.mul (hcdfv _)) Gb
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have := hHjb n j ω
      have h0 := cdf_nonneg M ((j : ℝ) / s n) (θ ω)
      have h1 := cdf_le_one M hprob ((j : ℝ) / s n) (θ ω)
      rw [abs_of_nonneg h0]
      nlinarith [abs_nonneg (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0))]
    · intro j _
      refine Integrable.of_bound (((hHj n j).mono hm).aestronglyMeasurable.mul
        (hYle _).aestronglyMeasurable) Gb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have := hHjb n j ω
      have h1 : |(if Y ω ≤ (j:ℝ) / s n then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [abs_nonneg (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)),
        abs_nonneg (if Y ω ≤ (j:ℝ) / s n then (1:ℝ) else 0)]
  -- limits
  have hqn_t : ∀ ω, Tendsto (fun n => qn n ω) atTop (𝓝 (q ω)) := by
    intro ω
    have hinv : Tendsto (fun n : ℕ => 1 / s n) atTop (𝓝 0) := by
      simp only [hsdef, one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hup : Tendsto (fun n => q ω + 1 / s n) atTop (𝓝 (q ω)) := by
      simpa using hinv.const_add (q ω)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hqn_ge n ω) (fun n => (hqn_lt n ω).le)
  have hcdf_lim : AEStronglyMeasurable (fun ω => cdf M (q ω) (θ ω)) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hcdfqn
      (Eventually.of_forall fun ω => ((hcont (θ ω)).tendsto _).comp (hqn_t ω))
  refine ⟨hcdf_lim, ?_⟩
  have hL : Tendsto (fun n => ∫ ω, G ω * (if Y ω ≤ qn n ω then 1 else 0) ∂P) atTop
      (𝓝 (∫ ω, G ω * (if Y ω ≤ q ω then 1 else 0) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Gb) (fun n => ?_)
      (integrable_const Gb) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · refine hGaesm.mul ?_
      have : Measurable[m0] (fun ω => if Y ω ≤ qn n ω then (1:ℝ) else 0) := by
        refine Measurable.ite ?_ measurable_const measurable_const
        have hc : Measurable[m0] (fun ω => ((⌈q ω * s n⌉ : ℤ) : ℝ)) :=
          measurable_from_top.comp ((hceil_meas n).mono hm le_rfl)
        exact measurableSet_le hY (hc.div_const _)
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(if Y ω ≤ qn n ω then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [hGb ω, abs_nonneg (G ω), abs_nonneg (if Y ω ≤ qn n ω then (1:ℝ) else 0)]
    · by_cases hyq : Y ω ≤ q ω
      · have : ∀ n, (if Y ω ≤ qn n ω then (1:ℝ) else 0) = 1 := fun n =>
          if_pos (hyq.trans (hqn_ge n ω))
        simp only [this, if_pos hyq]
        exact tendsto_const_nhds
      · push Not at hyq
        have hev : ∀ᶠ n in atTop, (if Y ω ≤ qn n ω then (1:ℝ) else 0) = 0 := by
          have := (hqn_t ω).eventually (gt_mem_nhds hyq)
          filter_upwards [this] with n hn
          exact if_neg (not_le.2 hn)
        rw [if_neg (not_le.2 hyq), mul_zero]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [hn, mul_zero]
  have hR : Tendsto (fun n => ∫ ω, G ω * cdf M (qn n ω) (θ ω) ∂P) atTop
      (𝓝 (∫ ω, G ω * cdf M (q ω) (θ ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Gb)
      (fun n => hGaesm.mul (hcdfqn n))
      (integrable_const Gb) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      have h0 := cdf_nonneg M (qn n ω) (θ ω)
      have h1 := cdf_le_one M hprob (qn n ω) (θ ω)
      rw [abs_of_nonneg h0]
      nlinarith [hGb ω, abs_nonneg (G ω)]
    · exact (((hcont (θ ω)).tendsto _).comp (hqn_t ω)).const_mul (G ω)
  have := hL.congr (fun n => hlevel n)
  exact tendsto_nhds_unique this hR

lemma onestep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z z' ind F Dn : Ω → ℝ) (γ ε α L φ : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (iz : Integrable (fun ω => z ω ^ 2) P) (iz1 : Integrable z P)
    (iz' : Integrable (fun ω => z' ω ^ 2) P)
    (izI : Integrable (fun ω => z ω * ind ω) P) (izF : Integrable (fun ω => z ω * F ω) P)
    (iD2 : Integrable (fun ω => Dn ω ^ 2) P) (iD : Integrable Dn P)
    (hcond : ∫ ω, z ω * ind ω ∂P = ∫ ω, z ω * F ω ∂P)
    (P1 : ∀ ω, z' ω ^ 2 ≤ (1 + γ * ε) * z ω ^ 2 + (1 + 1 / (γ * ε)) * (L * α) ^ 2 * Dn ω ^ 2
      + γ ^ 2 + 2 * γ * (φ * z ω - z ω * ind ω) + 2 * γ * (L * α) * Dn ω)
    (P2 : ∀ᵐ ω ∂P, φ * z ω - z ω * F ω ≤ -ε * z ω ^ 2) :
    ∫ ω, z' ω ^ 2 ∂P ≤ (1 - γ * ε) * ∫ ω, z ω ^ 2 ∂P
      + (1 + 1 / (γ * ε)) * (L * α) ^ 2 * ∫ ω, Dn ω ^ 2 ∂P + γ ^ 2
      + 2 * γ * (L * α) * ∫ ω, Dn ω ∂P := by
  set c1 := 1 + γ * ε
  set c2 := (1 + 1 / (γ * ε)) * (L * α) ^ 2
  set c3 := 2 * γ * (L * α)
  have i1 : Integrable (fun ω => c1 * z ω ^ 2) P := iz.const_mul c1
  have i2 : Integrable (fun ω => c2 * Dn ω ^ 2) P := iD2.const_mul c2
  have i3 : Integrable (fun _ : Ω => γ ^ 2) P := integrable_const _
  have i4 : Integrable (fun ω => 2 * γ * (φ * z ω - z ω * ind ω)) P :=
    ((iz1.const_mul φ).sub izI).const_mul (2 * γ)
  have i5 : Integrable (fun ω => c3 * Dn ω) P := iD.const_mul c3
  have hmono := integral_mono iz' ((((i1.add i2).add i3).add i4).add i5) P1
  rw [integral_add' (((i1.add i2).add i3).add i4) i5, integral_add' ((i1.add i2).add i3) i4,
    integral_add' (i1.add i2) i3, integral_add' i1 i2] at hmono
  beta_reduce at hmono
  rw [integral_const_mul, integral_const_mul,
    integral_const, integral_const_mul, integral_sub (iz1.const_mul φ) izI, integral_const_mul,
    integral_const_mul, hcond] at hmono
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at hmono
  have hP2 : φ * ∫ ω, z ω ∂P - ∫ ω, z ω * F ω ∂P ≤ -ε * ∫ ω, z ω ^ 2 ∂P := by
    rw [← integral_const_mul, ← integral_sub (iz1.const_mul φ) izF, ← integral_const_mul]
    exact integral_mono_ae ((iz1.const_mul φ).sub izF) (iz.const_mul _) P2
  have : 2 * γ * (φ * ∫ ω, z ω ∂P - ∫ ω, z ω * F ω ∂P) ≤ 2 * γ * (-ε * ∫ ω, z ω ^ 2 ∂P) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  nlinarith

lemma proj_nonexp {d : ℕ} {Θ : Set (E d)} {Proj : E d → E d} (hc : Convex ℝ Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj) {z : E d} (hz : z ∈ Θ) (x : E d) :
    ‖Proj x - z‖ ≤ ‖x - z‖ := by
  obtain ⟨hp, hmin⟩ := hProj x
  set p := Proj x
  have hvi : ⟪x - p, z - p⟫ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set δ := ⟪x - p, z - p⟫
    set t := min 1 (δ / (‖z - p‖ ^ 2 + 1))
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htδ : t ≤ δ / (‖z - p‖ ^ 2 + 1) := min_le_right _ _
    have hmem : p + t • (z - p) ∈ Θ := by
      have := hc hp hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hle := hmin _ hmem
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - (p + t • (z - p))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    have e : x - (p + t • (z - p)) = (x - p) - t • (z - p) := by abel
    have e2 : ‖(x - p) - t • (z - p)‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * t * δ + t ^ 2 * ‖z - p‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e, e2] at hsq
    have h1 : t * ‖z - p‖ ^ 2 < δ := by
      have hpos' : (0:ℝ) < ‖z - p‖ ^ 2 + 1 := by positivity
      have := mul_le_mul_of_nonneg_right htδ (by positivity : (0:ℝ) ≤ ‖z - p‖ ^ 2 + 1)
      rw [div_mul_cancel₀ _ hpos'.ne'] at this
      nlinarith [sq_nonneg ‖z - p‖]
    nlinarith [mul_pos ht0 hpos]
  have h1 : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * ⟪x - p, z - p⟫ + ‖z - p‖ ^ 2 := by
    have : x - z = (x - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real]
  have h2 : ‖p - z‖ = ‖z - p‖ := norm_sub_rev _ _
  have h3 : ‖p - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    rw [h1, h2]; nlinarith [sq_nonneg ‖x - p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

lemma q_lip {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ} (hc : Convex ℝ Θ) (hK : IsCompact Θ)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 q U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Θ, ∀ y ∈ Θ, |q x - q y| ≤ L * ‖x - y‖ := by
  obtain ⟨U, hU, hΘU, hq⟩ := hq2
  have hcont : ContinuousOn (fun x => fderiv ℝ q x) U :=
    hq.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdiff : ∀ x ∈ Θ, DifferentiableAt ℝ q x := fun x hx =>
    (hq.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hΘU hx))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x => fderiv ℝ q x) (hcont.mono hΘU)
  refine ⟨max C 1, by positivity, fun x hx y hy => ?_⟩
  have hb : ∀ z ∈ Θ, ‖fderiv ℝ q z‖ ≤ max C 1 := fun z hz => (hC z hz).trans (le_max_left _ _)
  have := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb hy hx
  rwa [Real.norm_eq_abs] at this

lemma meas_comp_on {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ} {Θ : Set (E d)} {g : E d → ℝ}
    (hg : ContinuousOn g Θ) {θ : Ω → E d} (hθ : StronglyMeasurable[m] θ) (hmem : ∀ ω, θ ω ∈ Θ) :
    StronglyMeasurable[m] (fun ω => g (θ ω)) := by
  have h1 : Measurable[m] (fun ω => (⟨θ ω, hmem ω⟩ : Θ)) := hθ.measurable.subtype_mk
  have h2 : Measurable (Θ.restrict g) := hg.restrict.measurable
  exact (h2.comp h1).stronglyMeasurable

lemma mvt_cdf {d : ℕ} (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (θ : E d) (y1 y2 : ℝ) :
    ∃ ξ ∈ Set.uIcc y1 y2, cdf M y2 θ - cdf M y1 θ = M.dens ξ θ * (y2 - y1) := by
  have hc : Continuous (fun y => cdf M y θ) :=
    continuous_iff_continuousAt.2 fun y => (hdens y θ).continuousAt
  rcases lt_trichotomy y1 y2 with h | h | h
  · obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun y => cdf M y θ) (fun y => M.dens y θ)
      h hc.continuousOn (fun x _ => hdens x θ)
    refine ⟨ξ, ?_, ?_⟩
    · rw [Set.uIcc_of_le h.le]; exact Set.Ioo_subset_Icc_self hξ
    · rw [he]; field_simp [sub_ne_zero.2 h.ne']
  · subst h; exact ⟨y1, Set.left_mem_uIcc, by ring⟩
  · obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun y => cdf M y θ) (fun y => M.dens y θ)
      h hc.continuousOn (fun x _ => hdens x θ)
    refine ⟨ξ, ?_, ?_⟩
    · rw [Set.uIcc_of_ge h.le]; exact Set.Ioo_subset_Icc_self hξ
    · rw [he]; field_simp [sub_ne_zero.2 h.ne']; ring

lemma D_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (D : Ω → E d) (hD : StronglyMeasurable D) (Sr : ℝ) (hSr : 0 ≤ Sr)
    (h : ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal Sr) :
    Integrable (fun ω => ‖D ω‖ ^ 2) P ∧ ∫ ω, ‖D ω‖ ^ 2 ∂P ≤ Sr ∧
      Integrable (fun ω => ‖D ω‖) P ∧ ∫ ω, ‖D ω‖ ∂P ≤ Sr + 1 := by
  have hm2 : AEStronglyMeasurable (fun ω => ‖D ω‖ ^ 2) P := (hD.norm.pow 2).aestronglyMeasurable
  have heq : ∫⁻ ω, ENNReal.ofReal (‖D ω‖ ^ 2) ∂P = ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂P := by
    congr 1; funext ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have i2 : Integrable (fun ω => ‖D ω‖ ^ 2) P := by
    refine ⟨hm2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply]; positivity), heq]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have v2 : ∫ ω, ‖D ω‖ ^ 2 ∂P ≤ Sr := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => ‖D ω‖ ^ 2)
      (Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; positivity) hm2, heq]
    exact ENNReal.toReal_le_of_le_ofReal hSr h
  have hpt : ∀ ω, ‖D ω‖ ≤ ‖D ω‖ ^ 2 + 1 := fun ω => by
    nlinarith [sq_nonneg (‖D ω‖ - 1), norm_nonneg (D ω)]
  have i1 : Integrable (fun ω => ‖D ω‖) P :=
    Integrable.mono' (i2.add (integrable_const 1)) hD.norm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_norm]
        exact hpt ω)
  refine ⟨i2, v2, i1, ?_⟩
  have := integral_mono i1 (i2.add (integrable_const 1)) (fun ω => by
    simp only [Pi.add_apply]; exact hpt ω)
  rw [integral_add' i2 (integrable_const 1)] at this
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
  linarith

lemma pathwise (z z' δq e Δ γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hz : |z'| ≤ |z + δq + γ * e|) (hδ : |δq| ≤ Δ) (he : |e| ≤ 1) :
    z' ^ 2 ≤ (1 + γ * ε) * z ^ 2 + (1 + 1 / (γ * ε)) * Δ ^ 2 + γ ^ 2 + 2 * γ * (z * e)
      + 2 * γ * Δ := by
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hδ
  have hge : 0 < γ * ε := by positivity
  have hsq : z' ^ 2 ≤ (z + δq + γ * e) ^ 2 := by
    rw [← sq_abs z', ← sq_abs (z + δq + γ * e)]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have amgm : 2 * |z| * Δ ≤ γ * ε * z ^ 2 + Δ ^ 2 / (γ * ε) := by
    have h0 : 0 ≤ (γ * ε * |z| - Δ) ^ 2 / (γ * ε) := by positivity
    have e2 : (γ * ε * |z| - Δ) ^ 2 / (γ * ε)
        = γ * ε * |z| ^ 2 - 2 * |z| * Δ + Δ ^ 2 / (γ * ε) := by
      field_simp; ring
    rw [e2, sq_abs] at h0
    linarith
  have t1 : 2 * z * δq ≤ 2 * |z| * Δ := by
    have h2 : z * δq ≤ |z| * |δq| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : |z| * |δq| ≤ |z| * Δ := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    linarith
  have t2 : δq ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have t3 : δq * e ≤ Δ := by
    calc δq * e ≤ |δq * e| := le_abs_self _
      _ = |δq| * |e| := abs_mul _ _
      _ ≤ Δ * 1 := mul_le_mul hδ he (abs_nonneg _) hΔ0
      _ = Δ := mul_one _
  have t4 : e ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg e]
  have hexp : (z + δq + γ * e) ^ 2 = z ^ 2 + δq ^ 2 + γ ^ 2 * e ^ 2 + 2 * z * δq
      + 2 * γ * (z * e) + 2 * γ * (δq * e) := by ring
  have hfin : Δ ^ 2 / (γ * ε) + Δ ^ 2 = (1 + 1 / (γ * ε)) * Δ ^ 2 := by
    field_simp; ring
  have t5 : γ ^ 2 * e ^ 2 ≤ γ ^ 2 := by nlinarith [sq_nonneg γ]
  have t6 : 2 * γ * (δq * e) ≤ 2 * γ * Δ := by nlinarith
  nlinarith

end SPQOL4Aux

namespace SPQOT3Seq

noncomputable def Ssum (u w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - u j)) * u i * w i

lemma Ssum_succ (u w : ℕ → ℝ) (k : ℕ) :
    Ssum u w (k + 1) = (1 - u (k + 1)) * Ssum u w k + u (k + 1) * w (k + 1) := by
  unfold Ssum
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  simp only [Finset.Ioc_self, Finset.prod_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Finset.prod_Ioc_succ_top (by omega)]
  ring

lemma Ssum_nonneg (u w : ℕ → ℝ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (k : ℕ) : 0 ≤ Ssum u w k := by
  unfold Ssum
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_Icc] at hi
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j hj => ?_) (hu0 i hi.1)) (hw0 i hi.1)
  rw [Finset.mem_Ioc] at hj
  linarith [hu1 j (by omega)]

lemma Ssum_add (u w₁ w₂ : ℕ → ℝ) (k : ℕ) :
    Ssum u (fun i => w₁ i + w₂ i) k = Ssum u w₁ k + Ssum u w₂ k := by
  unfold Ssum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

lemma cmp (u w x : ℕ → ℝ) (N : ℕ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (hbase : x (N + 1) ≤ u (N + 1) * w (N + 1))
    (hstep : ∀ k, N + 1 ≤ k → x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1)) :
    ∀ k, N + 1 ≤ k → x k ≤ Ssum u w k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Ssum_succ]
    have h1 := Ssum_nonneg u w hu0 hu1 hw0 N
    have h2 : 0 ≤ 1 - u (N + 1) := by linarith [hu1 (N + 1) (by omega)]
    nlinarith
  | succ k hk ih =>
    rw [Ssum_succ]
    have h2 : 0 ≤ 1 - u (k + 1) := by linarith [hu1 (k + 1) (by omega)]
    calc x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1) := hstep k hk
      _ ≤ _ := by gcongr

lemma rp_div (A B p q X : ℝ) (hX : 0 < X) (hB : B ≠ 0) :
    (A / X ^ p) / (B / X ^ q) = A / B * X ^ (-(p - q)) := by
  rw [Real.rpow_neg hX.le, Real.rpow_sub hX]
  have h1 : 0 < X ^ p := Real.rpow_pos_of_pos hX p
  have h2 : 0 < X ^ q := Real.rpow_pos_of_pos hX q
  field_simp

lemma rp_sq (A τ X : ℝ) (hX : 0 < X) : (A / X ^ τ) ^ 2 = A ^ 2 * X ^ (-(2 * τ)) := by
  rw [Real.rpow_neg hX.le, mul_comm 2 τ, Real.rpow_mul hX.le, Real.rpow_two]
  have h1 : 0 < X ^ τ := Real.rpow_pos_of_pos hX τ
  field_simp

lemma rp_sqrt (B C e τ X : ℝ) (hX : 0 < X) (hB : 0 ≤ B) (hC : C ≠ 0) :
    Real.sqrt (B / X ^ e) / (C / X ^ τ) = Real.sqrt B / C * X ^ (-(e / 2 - τ)) := by
  rw [Real.sqrt_div' B (Real.rpow_nonneg hX.le _), Real.sqrt_eq_rpow (X ^ e),
    ← Real.rpow_mul hX.le]
  rw [rp_div _ _ _ _ _ hX hC]
  ring_nf

lemma rp_pow_sq (X z : ℝ) (hX : 0 < X) : (X ^ z) ^ 2 = X ^ (2 * z) := by
  rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]

lemma exp_neg_of_tendsto (f : ℕ → ℝ) (A e : ℝ) (hA : 0 < A)
    (hf : ∀ k : ℕ, f k = A * ((k : ℝ) + 1) ^ e) (ht : Tendsto f atTop (𝓝 0)) : e < 0 := by
  by_contra h
  push Not at h
  have hge : ∀ k : ℕ, A ≤ f k := by
    intro k
    rw [hf k]
    have : 1 ≤ ((k : ℝ) + 1) ^ e := Real.one_le_rpow (by linarith [k.cast_nonneg (α := ℝ)]) h
    nlinarith
  have := ge_of_tendsto' ht hge
  linarith

lemma exp_lt_of_summable (A e : ℝ) (hA : 0 < A)
    (hs : Summable (fun k : ℕ => A * ((k : ℝ) + 1) ^ e)) : e < -1 := by
  have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ e) := by
    have := hs.mul_left A⁻¹
    refine this.congr (fun k => ?_)
    field_simp
  have h2 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ e) := by
    refine h1.congr (fun k => ?_)
    push_cast; rfl
  have h3 : Summable (fun n : ℕ => (n : ℝ) ^ e) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ e) 1).1 h2
  exact Real.summable_nat_rpow.1 h3

lemma kpow_le (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (k : ℝ) ^ (-s) ≤ 2 * ((k : ℝ) + 1) ^ (-s) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX : (0 : ℝ) < k := by linarith
  rw [Real.rpow_neg hX.le, Real.rpow_neg (by linarith)]
  have h1 : 0 < (k : ℝ) ^ s := Real.rpow_pos_of_pos hX s
  have h2 : ((k : ℝ) + 1) ^ s ≤ 2 * (k : ℝ) ^ s := by
    calc ((k : ℝ) + 1) ^ s ≤ (2 * (k : ℝ)) ^ s :=
          Real.rpow_le_rpow (by linarith) (by linarith) hs0
      _ = 2 ^ s * (k : ℝ) ^ s := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2 * (k : ℝ) ^ s := by
          gcongr
          calc (2:ℝ) ^ s ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
            _ = 2 := Real.rpow_one 2
  have h3 : 0 < ((k : ℝ) + 1) ^ s := Real.rpow_pos_of_pos (by linarith) s
  rw [inv_le_iff_one_le_mul₀ h1]
  calc (1 : ℝ) = ((k : ℝ) + 1) ^ s * (((k : ℝ) + 1) ^ s)⁻¹ := by field_simp
    _ ≤ (2 * (k : ℝ) ^ s) * (((k : ℝ) + 1) ^ s)⁻¹ := by gcongr
    _ = _ := by ring

lemma fin_ineq (x S1 S2 S3 B1 B2 B3 A1 A2 A3 T1 T2 T3 : ℝ) (hx : x ≤ S1 + S2 + S3)
    (h1 : S1 ≤ B1) (h2 : S2 ≤ B2) (h3 : S3 ≤ B3) (m1 : B1 ≤ 2 * A1 * T1) (m2 : B2 ≤ 2 * A2 * T2)
    (m3 : B3 ≤ 2 * A3 * T3) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hT1 : 0 ≤ T1)
    (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3) : x ≤ 2 * (A1 + A2 + A3) * (T1 + T2 + T3) := by
  nlinarith [mul_nonneg hA1 hT2, mul_nonneg hA1 hT3, mul_nonneg hA2 hT1, mul_nonneg hA2 hT3,
      mul_nonneg hA3 hT1, mul_nonneg hA3 hT2]

end SPQOT3Seq

namespace SPQOL4Det
open QuantileSPQO.Rate SPQOT3Seq

lemma det_rate (Z : ℕ → ℝ) (hZ0 : ∀ k, 0 ≤ Z k) (r ε eα eγ : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (heα0 : 0 < eα) (heα1 : eα < 1) (heγ0 : 0 < eγ) (heγ1 : eγ < 1) (hs1 : eγ < eα)
    (hrε : r * ε ≤ 1 / 2) (K1 K2 K3 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (hrec : ∀ k : ℕ, Z (k + 1) ≤ (1 - r * ε * ((k:ℝ) + 1) ^ (-eγ)) * Z k
      + r * ε * ((k:ℝ) + 1) ^ (-eγ) * (K1 * ((k:ℝ) + 1) ^ (-(2 * (eα - eγ)))
        + K2 * ((k:ℝ) + 1) ^ (-eγ) + K3 * ((k:ℝ) + 1) ^ (-eα))) :
    ∃ A1 A2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ ∀ᶠ k : ℕ in atTop,
      Z k ≤ A1 * ((k:ℝ) + 1) ^ (-(2 * (eα - eγ))) + A2 * ((k:ℝ) + 1) ^ (-eγ) := by
  have hX : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1 := fun k => by positivity
  have hX1 : ∀ k : ℕ, (1:ℝ) ≤ (k:ℝ) + 1 := fun k => by
    have := (k.cast_nonneg : (0:ℝ) ≤ k); linarith
  set s1 := 2 * (eα - eγ) with hs1def
  set s1' := min s1 eγ with hs1'
  have hs1'0 : 0 < s1' := lt_min (by linarith) heγ0
  have hs1'1 : s1' < 1 := lt_of_le_of_lt (min_le_right _ _) heγ1
  have hrε0 : 0 < r * ε := by positivity
  set u : ℕ → ℝ := fun j => r * ε / (j : ℝ) ^ eγ with hudef
  have hu_eq : ∀ k : ℕ, u (k + 1) = r * ε * ((k:ℝ) + 1) ^ (-eγ) := by
    intro k; simp only [hudef]; push_cast
    rw [Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hupos : ∀ j, 1 ≤ j → 0 < u j := by
    intro j hj
    have : (0:ℝ) < j := by exact_mod_cast hj
    simp only [hudef]; exact div_pos hrε0 (Real.rpow_pos_of_pos this _)
  have hu0 : ∀ j, 1 ≤ j → 0 ≤ u j := fun j hj => (hupos j hj).le
  have hu1 : ∀ j, 1 ≤ j → u j ≤ 1 := by
    intro j hj
    have : (1:ℝ) ≤ j := by exact_mod_cast hj
    simp only [hudef]
    calc r * ε / (j:ℝ) ^ eγ ≤ r * ε := div_le_self hrε0.le (Real.one_le_rpow this heγ0.le)
      _ ≤ 1 := by linarith
  set bump : ℕ → ℝ := fun j => if j = 1 then Z 0 / u 1 else 0 with hbump
  have hbump0 : ∀ j, 0 ≤ bump j := by
    intro j; simp only [hbump]; split_ifs
    · exact div_nonneg (hZ0 0) (hu0 _ le_rfl)
    · exact le_rfl
  set w1 : ℕ → ℝ := fun j => K1 * (j : ℝ) ^ (-s1') + bump j with hw1
  set w2 : ℕ → ℝ := fun j => K2 * (j : ℝ) ^ (-eγ) with hw2
  set w3 : ℕ → ℝ := fun j => K3 * (j : ℝ) ^ (-eα) with hw3
  set w : ℕ → ℝ := fun j => (w1 j + w2 j) + w3 j with hw
  have hW : ∀ k : ℕ, K1 * ((k:ℝ) + 1) ^ (-s1) + K2 * ((k:ℝ) + 1) ^ (-eγ)
      + K3 * ((k:ℝ) + 1) ^ (-eα) + bump (k + 1) ≤ w (k + 1) := by
    intro k
    simp only [hw, hw1, hw2, hw3]
    push_cast
    have : ((k:ℝ) + 1) ^ (-s1) ≤ ((k:ℝ) + 1) ^ (-s1') :=
      Real.rpow_le_rpow_of_exponent_le (hX1 k) (by
        have := min_le_left s1 eγ; linarith)
    nlinarith
  have hw0 : ∀ j, 1 ≤ j → 0 ≤ w j := by
    intro j hj
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    simp only [hw, hw1, hw2, hw3]
    have := hbump0 j
    have h1 := Real.rpow_pos_of_pos hj0 (-s1')
    have h2 := Real.rpow_pos_of_pos hj0 (-eγ)
    have h3 := Real.rpow_pos_of_pos hj0 (-eα)
    positivity
  have hcmp := cmp u w Z 0 hu0 hu1 hw0 (by
      have h1 := hrec 0
      have h2 := hW 0
      rw [← hu_eq 0] at h1
      simp only [Nat.cast_zero, zero_add] at h1 h2
      have hb : bump 1 = Z 0 / u 1 := by simp [hbump]
      rw [hb] at h2
      have hu1p := hupos 1 le_rfl
      have e : u 1 * (Z 0 / u 1) = Z 0 := mul_div_cancel₀ _ hu1p.ne'
      have h3 := mul_le_mul_of_nonneg_left h2 hu1p.le
      have h4 : 0 ≤ u 1 * Z 0 := mul_nonneg hu1p.le (hZ0 0)
      have h5 : u 1 * (K1 * 1 ^ (-s1) + K2 * 1 ^ (-eγ) + K3 * 1 ^ (-eα) + Z 0 / u 1)
          = u 1 * (K1 * 1 ^ (-s1) + K2 * 1 ^ (-eγ) + K3 * 1 ^ (-eα)) + Z 0 := by
        rw [mul_add, e]
      nlinarith)
    (by
      intro k hk
      have h1 := hrec k
      rw [← hu_eq k] at h1
      have h2 := hW k
      have h3 := mul_le_mul_of_nonneg_left
        (show K1 * ((k:ℝ) + 1) ^ (-s1) + K2 * ((k:ℝ) + 1) ^ (-eγ) + K3 * ((k:ℝ) + 1) ^ (-eα)
          ≤ w (k + 1) by linarith [hbump0 (k + 1)]) (hu0 (k + 1) (by omega))
      linarith)
  have hpow_eq : ∀ (K s : ℝ) (i : ℕ), 1 ≤ i → K * (i : ℝ) ^ (-s) = K / (i : ℝ) ^ s := by
    intro K s i hi
    have : (0:ℝ) < i := by exact_mod_cast hi
    rw [Real.rpow_neg this.le, div_eq_mul_inv]
  obtain ⟨C1, hC1⟩ := lemma_3 (r * ε) eγ s1' hrε0 ⟨heγ0, heγ1⟩ ⟨hs1'0, hs1'1⟩ w1
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have := hbump0 i
      have h1 := Real.rpow_pos_of_pos hi0 (-s1')
      simp only [hw1]; positivity)
    ⟨K1, by
      filter_upwards [eventually_ge_atTop 2] with i hi
      have hb : bump i = 0 := by simp only [hbump]; rw [if_neg (by omega)]
      simp only [hw1, hb, add_zero]
      rw [hpow_eq _ _ _ (by omega)]⟩
  obtain ⟨C2, hC2⟩ := lemma_3 (r * ε) eγ eγ hrε0 ⟨heγ0, heγ1⟩ ⟨heγ0, heγ1⟩ w2
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have h1 := Real.rpow_pos_of_pos hi0 (-eγ)
      simp only [hw2]; positivity)
    ⟨K2, by
      filter_upwards [eventually_ge_atTop 1] with i hi
      simp only [hw2]; rw [hpow_eq _ _ _ hi]⟩
  obtain ⟨C3, hC3⟩ := lemma_3 (r * ε) eγ eα hrε0 ⟨heγ0, heγ1⟩ ⟨heα0, heα1⟩ w3
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have h1 := Real.rpow_pos_of_pos hi0 (-eα)
      simp only [hw3]; positivity)
    ⟨K3, by
      filter_upwards [eventually_ge_atTop 1] with i hi
      simp only [hw3]; rw [hpow_eq _ _ _ hi]⟩
  refine ⟨2 * max C1 0, 2 * (max C1 0 + max C2 0 + max C3 0), by positivity, by positivity, ?_⟩
  filter_upwards [hC1, hC2, hC3, eventually_ge_atTop 1] with k h1 h2 h3 hk
  have hxk := hcmp k hk
  have hsplit : Ssum u w k = Ssum u w1 k + Ssum u w2 k + Ssum u w3 k := by
    simp only [hw]
    rw [Ssum_add u (fun i => w1 i + w2 i) w3, Ssum_add u w1 w2]
  have h1' : Ssum u w1 k ≤ C1 * (k : ℝ) ^ (-s1') := h1
  have h2' : Ssum u w2 k ≤ C2 * (k : ℝ) ^ (-eγ) := h2
  have h3' : Ssum u w3 k ≤ C3 * (k : ℝ) ^ (-eα) := h3
  have hkp : ∀ s : ℝ, 0 ≤ (k : ℝ) ^ s := fun s => Real.rpow_nonneg (Nat.cast_nonneg k) s
  have m : ∀ (C s : ℝ), 0 ≤ s → s ≤ 1 → C * (k : ℝ) ^ (-s) ≤ max C 0 * (2 * ((k:ℝ) + 1) ^ (-s)) :=
    fun C s hs0 hs1 => (mul_le_mul_of_nonneg_right (le_max_left _ _) (hkp _)).trans
      (mul_le_mul_of_nonneg_left (kpow_le k hk s hs0 hs1) (le_max_right _ _))
  have m1 := m C1 s1' hs1'0.le hs1'1.le
  have m2 := m C2 eγ heγ0.le heγ1.le
  have m3 := m C3 eα heα0.le heα1.le
  have hXs1' : ((k:ℝ) + 1) ^ (-s1') ≤ ((k:ℝ) + 1) ^ (-s1) + ((k:ℝ) + 1) ^ (-eγ) := by
    have ha := Real.rpow_nonneg (hX k).le (-s1)
    have hb := Real.rpow_nonneg (hX k).le (-eγ)
    rcases min_choice s1 eγ with h | h
    · rw [hs1', h]; linarith
    · rw [hs1', h]; linarith
  have hXeα : ((k:ℝ) + 1) ^ (-eα) ≤ ((k:ℝ) + 1) ^ (-eγ) :=
    Real.rpow_le_rpow_of_exponent_le (hX1 k) (by linarith)
  have p1 := le_max_right C1 0
  have p2 := le_max_right C2 0
  have p3 := le_max_right C3 0
  have q1 := Real.rpow_nonneg (hX k).le (-s1)
  have q2 := Real.rpow_nonneg (hX k).le (-eγ)
  have q3 := Real.rpow_nonneg (hX k).le (-eα)
  have q4 := Real.rpow_nonneg (hX k).le (-s1')
  have n1 := mul_le_mul_of_nonneg_left hXs1' p1
  have n3 := mul_le_mul_of_nonneg_left hXeα p3
  nlinarith

lemma coef_ineq (α γ a r ε Lq Sr t : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hγr : γ ≤ r) (ha : 0 < a)
    (hr : 0 < r) (hε : 0 < ε) (hLq : 0 < Lq) (hSr : 0 ≤ Sr) (ht : 0 < t) :
    (1 + 1 / (γ * ε)) * (Lq * α) ^ 2 * Sr + γ ^ 2 + 2 * γ * (Lq * α) * t ≤
      γ * ε * ((Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1) * ((r / a) ^ 2 * (α / γ) ^ 2)
        + r / ε * (γ / r) + (2 * Lq * t * a / ε + 1) * (α / a)) := by
  have e1 : γ * ε * ((Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1) * ((r / a) ^ 2 * (α / γ) ^ 2))
      = Lq ^ 2 * Sr * (r * α ^ 2 / γ) + Lq ^ 2 * Sr * (α ^ 2 / (γ * ε))
        + γ * ε * ((r / a) ^ 2 * (α / γ) ^ 2) := by
    field_simp
  have e2 : γ * ε * (r / ε * (γ / r)) = γ ^ 2 := by field_simp
  have e3 : γ * ε * ((2 * Lq * t * a / ε + 1) * (α / a)) = 2 * γ * (Lq * α) * t + γ * ε * (α / a) := by
    field_simp
  have e4 : (1 + 1 / (γ * ε)) * (Lq * α) ^ 2 * Sr = Lq ^ 2 * Sr * α ^ 2 + Lq ^ 2 * Sr * (α ^ 2 / (γ * ε)) := by
    field_simp
  have h1 : α ^ 2 ≤ r * α ^ 2 / γ := by
    rw [le_div_iff₀ hγ]; nlinarith [sq_nonneg α]
  have h2 : Lq ^ 2 * Sr * α ^ 2 ≤ Lq ^ 2 * Sr * (r * α ^ 2 / γ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 0 ≤ γ * ε * ((r / a) ^ 2 * (α / γ) ^ 2) := by positivity
  have h4 : 0 ≤ γ * ε * (α / a) := by positivity
  rw [mul_add, mul_add, e1, e2, e3, e4]
  linarith

lemma fin_sq (Zk A B x g sg : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hsg0 : 0 ≤ sg)
    (hsg : sg ^ 2 = g) (hk : Zk ≤ A * x ^ 2 + B * g) : Zk ≤ (A + B) * (x + sg) ^ 2 := by
  have h1 : x ^ 2 ≤ (x + sg) ^ 2 := by nlinarith
  have h2 : g ≤ (x + sg) ^ 2 := by rw [← hsg]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB]

end SPQOL4Det

open QuantileSPQO.Rate SPQOL4Aux SPQOT3Seq SPQOL4Det

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∫⁻ ω, ENNReal.ofReal ((R.q k ω - M.qf (R.θ k ω)) ^ 2) ∂P
        ≤ ENNReal.ofReal ((C * (α k / γ k + Real.sqrt (γ k))) ^ 2) := by
  obtain ⟨hsup, -⟩ := lemma_1 hd P ℱ M Θ Proj I Pq α β γ c R hΘ hM hProj hrun hA1 hA2 hA3a
  obtain ⟨ε0, Cf, hε0, hCf, hB1ae⟩ := hB1
  obtain ⟨a, b, r, c₀, eα, eβ, eγ, τ, ha, hb, hr, hc0, ⟨heα0, heα1⟩, ⟨heβ0, heβ1⟩,
    ⟨heγ0, heγ1⟩, ⟨hτ0, hτ1⟩, hsteps⟩ := hpoly
  have hX : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1 := fun k => by positivity
  have hX1 : ∀ k : ℕ, (1:ℝ) ≤ (k:ℝ) + 1 := fun k => by
    have := (k.cast_nonneg : (0:ℝ) ≤ k); linarith
  have hαk : ∀ k, α k = a / ((k:ℝ) + 1) ^ eα := fun k => (hsteps k).1
  have hγk : ∀ k, γ k = r / ((k:ℝ) + 1) ^ eγ := fun k => (hsteps k).2.2.1
  have hαpos : ∀ k, 0 < α k := fun k => by
    rw [hαk]; exact div_pos ha (Real.rpow_pos_of_pos (hX k) _)
  have hγpos : ∀ k, 0 < γ k := fun k => by
    rw [hγk]; exact div_pos hr (Real.rpow_pos_of_pos (hX k) _)
  have hγle : ∀ k, γ k ≤ r := fun k => by
    rw [hγk]; exact div_le_self hr.le (Real.one_le_rpow (hX1 k) heγ0.le)
  have iαγ : ∀ k : ℕ, α k / γ k = a / r * ((k:ℝ) + 1) ^ (-(eα - eγ)) := fun k => by
    rw [hαk, hγk]; exact rp_div _ _ _ _ _ (hX k) hr.ne'
  have iα : ∀ k : ℕ, α k = a * ((k:ℝ) + 1) ^ (-eα) := fun k => by
    rw [hαk, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have iγ : ∀ k : ℕ, γ k = r * ((k:ℝ) + 1) ^ (-eγ) := fun k => by
    rw [hγk, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hs1 : eγ < eα := by
    have := exp_neg_of_tendsto (fun k => α k / γ k) (a / r) (-(eα - eγ)) (by positivity) iαγ hA3d.1
    linarith
  -- geometry
  obtain ⟨θ₀, hθ₀, q₀, hq₀, D₀, hinit⟩ := hrun.init
  have hθΘ : ∀ k ω, R.θ k ω ∈ Θ := by
    intro k ω
    induction k with
    | zero => rw [(hinit ω).1]; exact hθ₀
    | succ k _ => rw [hrun.eq22]; exact (hProj _).1
  have hqI : ∀ k ω, R.q k ω ∈ I := by
    intro k ω
    induction k with
    | zero => rw [(hinit ω).2.1]; exact hq₀
    | succ k _ => rw [hrun.eq20]; exact (hrun.pqProj.proj _).1
  have hqfI : ∀ k ω, M.qf (R.θ k ω) ∈ I := fun k ω =>
    hrun.quantiles_mem ⟨_, hθΘ k ω, rfl⟩
  obtain ⟨Lq, hLq, hLip⟩ := q_lip hΘ.convex hΘ.isCompact hq2
  obtain ⟨U, hU, hΘU, hqC⟩ := hq2
  have hqcont : ContinuousOn M.qf Θ := hqC.continuousOn.mono hΘU
  obtain ⟨Qθ, hQθ⟩ := hΘ.isCompact.exists_bound_of_continuousOn hqcont
  have hφ0 := hM.φ_pos
  have hφ1 := hM.φ_lt_one
  have hind01 : ∀ (P' : Prop) [Decidable P'], |M.φ - (if P' then (1:ℝ) else 0)| ≤ 1 := by
    intro P' _
    split_ifs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [sub_zero, abs_of_pos hφ0]; linarith
  -- bounds on q_k
  set Qk : ℕ → ℝ := fun k => |q₀| + ∑ i ∈ Finset.range k, γ i with hQk
  have hqb : ∀ k ω, |R.q k ω| ≤ Qk k := by
    intro k ω
    induction k with
    | zero => rw [(hinit ω).2.1]; simp [hQk]
    | succ k ih =>
      have h1 : |R.q (k + 1) ω - R.q k ω| ≤ γ k := by
        rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqI k ω) _).trans ?_
        rw [add_sub_cancel_left, abs_mul, abs_of_pos (hγpos k)]
        have := hind01 (R.Y0 k ω ≤ R.q k ω)
        nlinarith [hγpos k]
      simp only [hQk, Finset.sum_range_succ] at ih ⊢
      have := abs_sub_abs_le_abs_sub (R.q (k + 1) ω) (R.q k ω)
      linarith
  have hθstep : ∀ k ω, ‖R.θ (k + 1) ω - R.θ k ω‖ ≤ α k * ‖R.D k ω‖ := by
    intro k ω
    rw [hrun.eq22]
    have := proj_nonexp hΘ.convex hProj (hθΘ k ω) (R.θ k ω - α k • R.D k ω)
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hαpos k).le] at this
    exact this
  -- measurability
  have hmqf : ∀ k, StronglyMeasurable[ℱ k] (fun ω => M.qf (R.θ k ω)) := fun k =>
    meas_comp_on hqcont (hrun.adapted_θ k) (hθΘ k)
  set ζ : ℕ → Ω → ℝ := fun k ω => R.q k ω - M.qf (R.θ k ω) with hζ
  have hζm : ∀ k, StronglyMeasurable[ℱ k] (ζ k) := fun k => (hrun.adapted_q k).sub (hmqf k)
  have hζm0 : ∀ k, StronglyMeasurable (ζ k) := fun k => (hζm k).mono (ℱ.le k)
  have hζb : ∀ k ω, |ζ k ω| ≤ Qk k + Qθ := by
    intro k ω
    have h1 := hqb k ω
    have h2 := hQθ _ (hθΘ k ω)
    rw [Real.norm_eq_abs] at h2
    calc |ζ k ω| ≤ |R.q k ω| + |M.qf (R.θ k ω)| := abs_sub _ _
      _ ≤ _ := by linarith
  have hζ2int : ∀ k, Integrable (fun ω => ζ k ω ^ 2) P := fun k =>
    Integrable.of_bound ((hζm0 k).aestronglyMeasurable.pow 2) ((Qk k + Qθ) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hζb k ω) 2)
  have hζint : ∀ k, Integrable (ζ k) P := fun k =>
    Integrable.of_bound (hζm0 k).aestronglyMeasurable (Qk k + Qθ)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hζb k ω)
  -- D moments
  set S := ⨆ k, ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P with hS
  set Sr := S.toReal with hSr
  set t := Sr + 1 with ht
  have hSr0 : 0 ≤ Sr := ENNReal.toReal_nonneg
  have ht0 : 0 < t := by positivity
  have hmD : ∀ k, StronglyMeasurable (R.D k) := fun k => (hrun.adapted_D k).mono (ℱ.le k)
  have hD2le : ∀ k, ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal Sr := by
    intro k
    rw [hSr, ENNReal.ofReal_toReal hsup.ne]
    exact le_iSup (fun k => ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P) k
  have hDm := fun k => D_moments P (R.D k) (hmD k) Sr hSr0 (hD2le k)
  -- one-step recursion
  set ε := min ε0 (1 / (2 * r)) with hεdef
  have hε : 0 < ε := lt_min hε0 (by positivity)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hγε : ∀ k, γ k * ε ≤ 1 / 2 := by
    intro k
    have : ε ≤ 1 / (2 * r) := min_le_right _ _
    calc γ k * ε ≤ r * (1 / (2 * r)) := mul_le_mul (hγle k) this hε.le hr.le
      _ = 1 / 2 := by field_simp
  set Z : ℕ → ℝ := fun k => ∫ ω, ζ k ω ^ 2 ∂P with hZ
  have hcontcdf : ∀ θ, Continuous (fun y => cdf M y θ) := fun θ =>
    continuous_iff_continuousAt.2 fun y => (hM.hasDens y θ).continuousAt
  have hrecZ : ∀ k, Z (k + 1) ≤ (1 - γ k * ε) * Z k
      + (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 * Sr + γ k ^ 2 + 2 * γ k * (Lq * α k) * t := by
    intro k
    have hY : Measurable (R.Y0 k) := ((hrun.meas_Y0 k).mono (ℱ.le (k + 1))).measurable
    obtain ⟨hFm, hcond⟩ := cond_threshold (ℱ.le k) P M hM.isProb hcontcdf (R.Y0 k) hY
      (R.θ k) (R.q k) (ζ k) (hrun.adapted_q k) (hζm k) (Qk k) (Qk k + Qθ) (hqb k) (hζb k)
      (fun v => hrun.sample0 k (Set.Iic v) measurableSet_Iic)
    have hindm : Measurable (fun ω => if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_le hY ((hrun.adapted_q k).mono (ℱ.le k)).measurable)
        measurable_const measurable_const
    have izI : Integrable (fun ω => ζ k ω * (if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0)) P :=
      Integrable.of_bound ((hζm0 k).aestronglyMeasurable.mul hindm.aestronglyMeasurable)
        (Qk k + Qθ) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |(if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
          nlinarith [hζb k ω, abs_nonneg (ζ k ω),
            abs_nonneg (if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0)])
    have izF : Integrable (fun ω => ζ k ω * cdf M (R.q k ω) (R.θ k ω)) P :=
      Integrable.of_bound ((hζm0 k).aestronglyMeasurable.mul hFm) (Qk k + Qθ)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h0 := cdf_nonneg M (R.q k ω) (R.θ k ω)
          have h1 := cdf_le_one M hM.isProb (R.q k ω) (R.θ k ω)
          rw [abs_of_nonneg h0]
          nlinarith [hζb k ω, abs_nonneg (ζ k ω)])
    have hP1 : ∀ ω, ζ (k + 1) ω ^ 2 ≤ (1 + γ k * ε) * ζ k ω ^ 2
        + (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 * ‖R.D k ω‖ ^ 2 + γ k ^ 2
        + 2 * γ k * (M.φ * ζ k ω - ζ k ω * (if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0))
        + 2 * γ k * (Lq * α k) * ‖R.D k ω‖ := by
      intro ω
      set e := M.φ - (if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0) with he
      have he1 : |e| ≤ 1 := hind01 _
      set δq := M.qf (R.θ k ω) - M.qf (R.θ (k + 1) ω) with hδq
      have hδ : |δq| ≤ Lq * α k * ‖R.D k ω‖ := by
        have := hLip _ (hθΘ k ω) _ (hθΘ (k + 1) ω)
        rw [norm_sub_rev] at this
        calc |δq| ≤ Lq * ‖R.θ (k + 1) ω - R.θ k ω‖ := this
          _ ≤ Lq * (α k * ‖R.D k ω‖) := mul_le_mul_of_nonneg_left (hθstep k ω) hLq.le
          _ = _ := by ring
      have hz1 : |ζ (k + 1) ω| ≤ |ζ k ω + δq + γ k * e| := by
        simp only [hζ]
        rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqfI (k + 1) ω) _).trans (le_of_eq ?_)
        congr 1; simp only [hδq, he]; ring
      have hpw := pathwise (ζ k ω) (ζ (k + 1) ω) δq e (Lq * α k * ‖R.D k ω‖) (γ k) ε
        (hγpos k) hε hz1 hδ he1
      have e1 : (Lq * α k * ‖R.D k ω‖) ^ 2 = (Lq * α k) ^ 2 * ‖R.D k ω‖ ^ 2 := by ring
      have e2 : ζ k ω * e = M.φ * ζ k ω - ζ k ω *
          (if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0) := by rw [he]; ring
      rw [e1, e2] at hpw
      linarith
    have hP2 : ∀ᵐ ω ∂P, M.φ * ζ k ω - ζ k ω * cdf M (R.q k ω) (R.θ k ω) ≤ -ε * ζ k ω ^ 2 := by
      filter_upwards [hB1ae] with ω hω
      obtain ⟨ξ, hξ, hmvt⟩ := mvt_cdf M hM.hasDens (R.θ k ω) (R.q k ω) (M.qf (R.θ k ω))
      have hfξ := ((hω k) ξ hξ).1
      have hφq : cdf M (M.qf (R.θ k ω)) (R.θ k ω) = M.φ := hM.quantile _
      have e : M.φ * ζ k ω - ζ k ω * cdf M (R.q k ω) (R.θ k ω)
          = -(M.dens ξ (R.θ k ω)) * ζ k ω ^ 2 := by
        rw [← hφq]
        have : ζ k ω = R.q k ω - M.qf (R.θ k ω) := rfl
        rw [this]
        linear_combination (R.q k ω - M.qf (R.θ k ω)) * hmvt
      rw [e]
      have := sq_nonneg (ζ k ω)
      nlinarith
    have hos := onestep P (ζ k) (ζ (k + 1)) (fun ω => if R.Y0 k ω ≤ R.q k ω then (1:ℝ) else 0)
      (fun ω => cdf M (R.q k ω) (R.θ k ω)) (fun ω => ‖R.D k ω‖) (γ k) ε (α k) Lq M.φ
      (hγpos k) hε (hζ2int k) (hζint k) (hζ2int (k + 1)) izI izF (hDm k).1 (hDm k).2.2.1 hcond
      hP1 hP2
    have c1 : 0 ≤ (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 := by
      have := hγpos k; positivity
    have c2 : 0 ≤ 2 * γ k * (Lq * α k) := by
      have := hγpos k; have := hαpos k; positivity
    refine le_trans hos ?_
    have := mul_le_mul_of_nonneg_left (hDm k).2.1 c1
    have := mul_le_mul_of_nonneg_left (hDm k).2.2.2 c2
    linarith
  -- deterministic analysis
  have hrε : r * ε ≤ 1 / 2 := by
    have : ε ≤ 1 / (2 * r) := min_le_right _ _
    calc r * ε ≤ r * (1 / (2 * r)) := mul_le_mul_of_nonneg_left this hr.le
      _ = 1 / 2 := by field_simp
  have hZ0 : ∀ k, 0 ≤ Z k := fun k => integral_nonneg (fun ω => sq_nonneg _)
  set K1 := Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1 with hK1
  set K2 := r / ε with hK2
  set K3 := 2 * Lq * t * a / ε + 1 with hK3
  have hX2 : ∀ k : ℕ, ((k:ℝ) + 1) ^ (-(2 * (eα - eγ))) = (r / a) ^ 2 * (α k / γ k) ^ 2 := by
    intro k
    rw [iαγ k, mul_pow, rp_pow_sq _ _ (hX k)]
    field_simp
    try ring_nf
  have hXg : ∀ k : ℕ, ((k:ℝ) + 1) ^ (-eγ) = γ k / r := by
    intro k; rw [iγ k]; field_simp
  have hXa : ∀ k : ℕ, ((k:ℝ) + 1) ^ (-eα) = α k / a := by
    intro k; rw [iα k]; field_simp
  obtain ⟨A1, A2, hA1, hA2, hev⟩ := det_rate Z hZ0 r ε eα eγ hr hε heα0 heα1 heγ0 heγ1 hs1 hrε
    K1 K2 K3 (by positivity) (by positivity) (by positivity) (by
      intro k
      rw [hX2 k, hXg k, hXa k]
      have hci := coef_ineq (α k) (γ k) a r ε Lq Sr t (hαpos k) (hγpos k) (hγle k) ha hr hε hLq
        hSr0 ht0
      have hre : r * ε * (γ k / r) = γ k * ε := by field_simp
      rw [hre]
      have := hrecZ k
      linarith)
  set C := Real.sqrt (A1 * (r / a) ^ 2 + A2 / r) with hC
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hev] with k hk
  rw [hX2 k, hXg k] at hk
  have hCsq : C ^ 2 = A1 * (r / a) ^ 2 + A2 / r := Real.sq_sqrt (by positivity)
  have hsg : Real.sqrt (γ k) ^ 2 = γ k := Real.sq_sqrt (hγpos k).le
  have hq1 : 0 ≤ α k / γ k := (div_pos (hαpos k) (hγpos k)).le
  have hq2' : 0 ≤ Real.sqrt (γ k) := Real.sqrt_nonneg _
  have hfin : Z k ≤ (C * (α k / γ k + Real.sqrt (γ k))) ^ 2 := by
    rw [mul_pow, hCsq]
    have e : A1 * ((r / a) ^ 2 * (α k / γ k) ^ 2) + A2 * (γ k / r)
        = A1 * (r / a) ^ 2 * (α k / γ k) ^ 2 + A2 / r * γ k := by ring
    rw [e] at hk
    exact fin_sq (Z k) _ _ _ _ _ (by positivity) (by positivity) hq1 hq2' hsg hk
  have hlin : ∫⁻ ω, ENNReal.ofReal ((R.q k ω - M.qf (R.θ k ω)) ^ 2) ∂P = ENNReal.ofReal (Z k) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hζ2int k)
      (Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; positivity)]
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hfin
