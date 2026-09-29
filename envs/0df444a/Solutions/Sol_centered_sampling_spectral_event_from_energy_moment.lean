-- Prove2me | solution 1 for centered_sampling_spectral_event_from_energy_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T09:14:39.433481+00:00
-- url     : https://prove2.me/submissions/d985172a-09d3-47ab-a856-6f4487630aa9

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_centered_sampling_symmetrization_moment_bound_of_sample_ratio
import Theorems.Thm_rademacher_pointwise_khintchine_spectral_energy
import Theorems.Thm_bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
import Theorems.Thm_fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
import Theorems.Thm_sampled_row_energy_max_nonnegative
import Theorems.Thm_sampled_column_energy_max_nonnegative
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
# Tight row/column-energy Theorem-6.3 spectral EVENT keystone (energy-MOMENT form)

Source: Candès--Recht 2008, PDF p. 26, Theorem 6.3 and equation (6.7),
with the row/column-energy input replacing the fixed entry-sup scale used in
the paper's square-matrix statement.

The genuinely tight keystone both §6.3 outer-fold lanes are blocked on.  A
deterministic `sampledRowEnergyMax Ω X ≤ E` hypothesis is provably too weak: the
worst-case Ω samples the entire heaviest row, forcing `E ≈ rowEnergy(X)` (no `p`),
which overcounts by `≈ n₁n₂/m`.  This version instead takes the *probabilistic*
energy `q`-MOMENT hypothesis

  `bExp[max(rowEnergy, colEnergy)^q] ≤ EnergyBound^q`

so the `p`-concentration of the sampled energy lives inside the expectation.  When
the caller supplies the tight energy moment `EnergyBound ≈ C·p·μ₀μ₁²r` (paper
Lemma 6.2 with the tangent structure `‖coef‖∞ ≤ μ₁√(r/N)`), the spectral event
lands at the paper Lemma 6.6 scale `K₀ = C·μ₁·√(μ₀ N r β log n/m)` — NOT the loose
`√(βN log N/p)·‖X‖∞` (verified numerically: threshold/K₀ ≡ 1, no n-growth).

Derivation (all children Proved on platform / banked):
* symmetrization `bExp[‖S‖^q] ≤ Csym^q · bExp[Eε‖S_sym‖^q]`;
* pointwise conditional Khintchine `Eε‖S_sym‖^q ≤ (Ckh·√q·p⁻¹·√maxEnergy)^q`
  lifted to the Bernoulli expectation;
* Jensen power-mean `bExp[maxEnergy^{q/2}] ≤ (bExp[maxEnergy^q])^{1/2} ≤ EnergyBound^{q/2}`
  (built inline over the Bernoulli weights, mirroring `rademacher_expectation_power_mean`);
* `t = e` Markov absorption `N^{-β} ≥ e^{-q}` (since `q ≥ β log N`);
* the scale-agnostic Markov tail step.
-/

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma sum_bernoulliObservationWeight_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} (_hp : 0 ≤ p) (_hp_one : p ≤ 1) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma sqrt_pow_eq_rpow_half {x : ℝ} (hx : 0 ≤ x) (q : ℕ) :
    (Real.sqrt x) ^ q = Real.rpow x ((q : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1:ℝ)/2)) q, ← Real.rpow_mul hx]
  congr 1; ring

private lemma bernoulliExpectation_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F : Finset (Fin n₁ × Fin n₂) → ℝ} (hF : ∀ Omega, 0 ≤ F Omega) :
    0 ≤ bernoulliExpectation p F := by
  unfold bernoulliExpectation
  apply Finset.sum_nonneg
  intro Omega _
  exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega) (hF Omega)

/-- Bernoulli-expectation power-mean (Jensen for the concave `t ↦ t^{r/s}`),
mirroring the Proved `rademacher_expectation_power_mean`.  For `0 < r ≤ s` and a
nonnegative statistic `F`, `bExp[F^r] ≤ (bExp[F^s])^{r/s}` (rpow exponents). -/
private lemma bernoulli_expectation_power_mean
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega) :
    bernoulliExpectation p (fun Omega => (F Omega) ^ r)
      ≤ Real.rpow (bernoulliExpectation p (fun Omega => (F Omega) ^ s)) (r / s) := by
  classical
  set w : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => bernoulliObservationWeight p Omega with hw
  have hwnn : ∀ Omega, 0 ≤ w Omega := fun Omega =>
    bernoulliObservationWeight_nonneg hp hp_one Omega
  have hwsum : ∑ Omega : Finset (Fin n₁ × Fin n₂), w Omega = 1 :=
    sum_bernoulliObservationWeight_eq_one hp hp_one
  have hp_exp : (1 : ℝ) ≤ s / r := by
    rw [le_div_iff₀ hr]; linarith
  have hznn : ∀ Omega : Finset (Fin n₁ × Fin n₂), 0 ≤ (F Omega) ^ r := by
    intro Omega; exact Real.rpow_nonneg (hF Omega) r
  have key := Real.arith_mean_le_rpow_mean (Finset.univ)
    w (fun Omega => (F Omega) ^ r)
    (fun i _ => hwnn i) hwsum (fun i _ => hznn i) hp_exp
  have hpow : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      ((F Omega) ^ r) ^ (s / r) = (F Omega) ^ s := by
    intro Omega
    rw [← Real.rpow_mul (hF Omega)]
    congr 1
    field_simp
  have hexp : (1 : ℝ) / (s / r) = r / s := by
    rw [one_div_div]
  simp only [bernoulliExpectation]
  calc ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * (F Omega) ^ r
      = ∑ Omega : Finset (Fin n₁ × Fin n₂), w Omega * (F Omega) ^ r := by rfl
    _ ≤ (∑ Omega : Finset (Fin n₁ × Fin n₂),
          w Omega * ((F Omega) ^ r) ^ (s / r)) ^ (1 / (s / r)) := key
    _ = (∑ Omega : Finset (Fin n₁ × Fin n₂), w Omega * (F Omega) ^ s) ^ (r / s) := by
          rw [hexp]
          congr 1
          apply Finset.sum_congr rfl
          intro Omega _
          rw [hpow Omega]
    _ = Real.rpow (∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega * (F Omega) ^ s) (r / s) := by rfl

theorem solution :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) (EnergyBound : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        0 ≤ EnergyBound →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤ EnergyBound ^ q →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (Ctail * Real.sqrt (q : ℝ) *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                  Real.sqrt EnergyBound)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Csym, hCsym, hSymmBound⟩ :=
    centered_sampling_symmetrization_moment_bound_of_sample_ratio
  obtain ⟨Ckh, hCkh, hPointwise⟩ := rademacher_pointwise_khintchine_spectral_energy
  refine ⟨Real.exp 1 * Csym * Ckh, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q X EnergyBound hn₁ hn₂ hm hq hqLog hSample hEB hEnergyMoment
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN_def
  have hp_bounds : (0 : ℝ) ≤ p ∧ p ≤ 1 := by
    refine ⟨by rw [hp_def]; positivity, ?_⟩
    rw [hp_def, div_le_one (by positivity)]
    exact_mod_cast hm
  have hp_nonneg := hp_bounds.1
  have hpinv_nonneg : 0 ≤ p⁻¹ := by positivity
  set scale : ℝ := Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound with hscale_def
  have hscale_nonneg : 0 ≤ scale := by
    rw [hscale_def]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpinv_nonneg) (Real.sqrt_nonneg _)
  set threshold : ℝ := (Real.exp 1 * Csym * Ckh) * scale with hthr_def
  have hthr_nonneg : 0 ≤ threshold := by
    rw [hthr_def]; exact mul_nonneg (by positivity) hscale_nonneg
  -- (1) Symmetrization.
  have hSymm := hSymmBound n₁ n₂ m q X hn₁ hn₂ hm hq
  -- (2) Pointwise Khintchine, lifted to the Bernoulli expectation.
  have hRadBExp :
      bernoulliExpectation p
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps p X) ^ q)) ≤
        bernoulliExpectation p
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
    have := bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
      Ckh n₁ n₂ m q X hn₁ hn₂ hm (fun Omega => hPointwise β hβ n₁ n₂ m q X Omega hn₁ hn₂ hq hqLog)
    simpa [hp_def] using this
  -- (3) Power-mean: bExp[(Ckh√q p⁻¹ √maxEnergy)^q]
  --     = (Ckh√q p⁻¹)^q · bExp[maxEnergy^{q/2}] ≤ (Ckh√q p⁻¹ √EnergyBound)^q.
  set maxE : Finset (Fin n₁ × Fin n₂) → ℝ := fun Omega =>
    max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with hmaxE_def
  have hmaxE_nonneg : ∀ Omega, 0 ≤ maxE Omega := by
    intro Omega
    rw [hmaxE_def]
    exact le_max_of_le_left (sampled_row_energy_max_nonnegative Omega X)
  -- Power-mean with F = maxE, r = q/2, s = q (as reals).
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hPowerMean :
      bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) ((q : ℝ) / 2)) ≤
        Real.rpow EnergyBound ((q : ℝ) / 2) := by
    -- Jensen: bExp[maxE^{q/2}] ≤ (bExp[maxE^q])^{1/2}
    have hjensen :=
      bernoulli_expectation_power_mean hp_bounds.1 hp_bounds.2
        ((q : ℝ) / 2) (q : ℝ) (by positivity) (by linarith [hqR_pos]) maxE hmaxE_nonneg
    -- bExp[maxE^q] ≤ EnergyBound^q ; note maxE^(q:ℝ) = maxE^(q:ℕ) (rpow_natCast)
    have hmoment_rpow :
        bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) (q : ℝ)) ≤
          Real.rpow EnergyBound (q : ℝ) := by
      have hfun : (fun Omega => Real.rpow (maxE Omega) (q : ℝ)) =
          (fun Omega => (maxE Omega) ^ q) := by
        funext Omega; exact Real.rpow_natCast (maxE Omega) q
      rw [hfun]
      have hRHS : Real.rpow EnergyBound (q : ℝ) = EnergyBound ^ q :=
        Real.rpow_natCast EnergyBound q
      rw [hRHS]
      simpa [hmaxE_def] using hEnergyMoment
    -- combine
    have hbexp_nonneg :
        0 ≤ bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) (q : ℝ)) :=
      bernoulliExpectation_nonneg hp_bounds.1 hp_bounds.2
        (fun Omega => Real.rpow_nonneg (hmaxE_nonneg Omega) _)
    have hstep : (Real.rpow (bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) (q : ℝ)))
          (((q : ℝ) / 2) / (q : ℝ))) ≤
        Real.rpow (Real.rpow EnergyBound (q : ℝ)) (((q : ℝ) / 2) / (q : ℝ)) :=
      Real.rpow_le_rpow hbexp_nonneg hmoment_rpow (by positivity)
    -- simplify exponents:  (EnergyBound^q)^{((q/2)/q)} = EnergyBound^{q · ((q/2)/q)} = EnergyBound^{q/2}
    have hEB_simp : Real.rpow (Real.rpow EnergyBound (q : ℝ)) (((q : ℝ) / 2) / (q : ℝ)) =
        Real.rpow EnergyBound ((q : ℝ) / 2) := by
      show (EnergyBound ^ (q : ℝ)) ^ (((q : ℝ) / 2) / (q : ℝ)) =
        EnergyBound ^ ((q : ℝ) / 2)
      rw [← Real.rpow_mul hEB]
      congr 1
      have : (q : ℝ) ≠ 0 := ne_of_gt hqR_pos
      field_simp
    calc
      bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) ((q : ℝ) / 2))
          ≤ Real.rpow (bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) (q : ℝ)))
              (((q : ℝ) / 2) / (q : ℝ)) := hjensen
      _ ≤ Real.rpow (Real.rpow EnergyBound (q : ℝ)) (((q : ℝ) / 2) / (q : ℝ)) := hstep
      _ = Real.rpow EnergyBound ((q : ℝ) / 2) := hEB_simp
  -- (3b) Turn the power-mean into a bound on bExp[(Ckh√q p⁻¹ √maxE)^q].
  --      (Ckh√q p⁻¹ √maxE)^q = (Ckh√q p⁻¹)^q · maxE^{q/2}, and √maxE = maxE^{1/2}.
  have hCkhcoef_nonneg : 0 ≤ Ckh * Real.sqrt (q : ℝ) * (p⁻¹) :=
    mul_nonneg (mul_nonneg (le_of_lt hCkh) (Real.sqrt_nonneg _)) hpinv_nonneg
  have hEnergyConst :
      bernoulliExpectation p
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) *
              Real.sqrt (maxE Omega)) ^ q) ≤
        (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound) ^ q := by
    -- pull the constant out: (c · √maxE)^q = c^q · (√maxE)^q = c^q · maxE^{q/2}
    have hpull : ∀ Omega,
        (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt (maxE Omega)) ^ q =
          (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) ^ q * Real.rpow (maxE Omega) ((q : ℝ) / 2) := by
      intro Omega
      rw [mul_pow, sqrt_pow_eq_rpow_half (hmaxE_nonneg Omega) q]
    -- bExp is linear in the constant multiple
    have hlin :
        bernoulliExpectation p
            (fun Omega =>
              (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt (maxE Omega)) ^ q) =
          (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) ^ q *
            bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) ((q : ℝ) / 2)) := by
      unfold bernoulliExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Omega _
      simp only [hpull Omega]
      ring
    rw [hlin]
    -- multiply the power-mean bound by the nonneg constant
    have hconst_nonneg : 0 ≤ (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) ^ q :=
      pow_nonneg hCkhcoef_nonneg q
    calc
      (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) ^ q *
          bernoulliExpectation p (fun Omega => Real.rpow (maxE Omega) ((q : ℝ) / 2))
          ≤ (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) ^ q * Real.rpow EnergyBound ((q : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hPowerMean hconst_nonneg
      _ = (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound) ^ q := by
            rw [mul_pow (Ckh * Real.sqrt (q : ℝ) * (p⁻¹)) (Real.sqrt EnergyBound) q,
              sqrt_pow_eq_rpow_half hEB q]
  -- (4) Combine: bExp[‖S‖^q] ≤ (Csym·Ckh·√q·p⁻¹·√EnergyBound)^q.
  have hCombine :
      bernoulliExpectation p
          (fun Omega =>
            spectralNorm (centeredSamplingFluctuation Omega p X) ^ q) ≤
        (Csym * Ckh * scale) ^ q := by
    have hstep2 : bernoulliExpectation p
          (fun Omega =>
            spectralNorm (centeredSamplingFluctuation Omega p X) ^ q) ≤
        Csym ^ q * (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound) ^ q := by
      calc
        bernoulliExpectation p
            (fun Omega =>
              spectralNorm (centeredSamplingFluctuation Omega p X) ^ q)
            ≤ Csym ^ q * bernoulliExpectation p
                (fun Omega =>
                  rademacherExpectation
                    (fun eps =>
                      spectralNorm
                        (rademacherSampledMatrix Omega eps p X) ^ q)) := by
              simpa [hp_def] using hSymm
        _ ≤ Csym ^ q *
              bernoulliExpectation p
                (fun Omega =>
                  (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) *
                    Real.sqrt (maxE Omega)) ^ q) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              simpa [hmaxE_def] using hRadBExp
        _ ≤ Csym ^ q * (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound) ^ q :=
              mul_le_mul_of_nonneg_left hEnergyConst (by positivity)
    calc
      bernoulliExpectation p
          (fun Omega =>
            spectralNorm (centeredSamplingFluctuation Omega p X) ^ q)
          ≤ Csym ^ q * (Ckh * Real.sqrt (q : ℝ) * (p⁻¹) * Real.sqrt EnergyBound) ^ q := hstep2
      _ = (Csym * Ckh * scale) ^ q := by
            rw [hscale_def, ← mul_pow]; ring_nf
  -- (5) `t = e` Markov absorption.
  have hNpos : (0 : ℝ) < N := by
    rw [hN_def]
    have : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    exact_mod_cast this
  have hAbsorb :
      (Csym * Ckh * scale) ^ q ≤ threshold ^ q * Real.rpow N (-β) := by
    have hrpow_eq : Real.rpow N (-β) = Real.exp (-β * Real.log N) := by
      rw [show Real.rpow N (-β) = N ^ (-β) from rfl, Real.rpow_def_of_pos hNpos]
      congr 1; ring
    have hexp_le : Real.exp (-(q : ℝ)) ≤ Real.rpow N (-β) := by
      rw [hrpow_eq]
      apply Real.exp_le_exp.mpr
      have : β * Real.log N ≤ (q : ℝ) := by rw [hN_def]; exact hqLog
      linarith
    have hthr_pow :
        threshold ^ q = Real.exp (q : ℝ) * (Csym * Ckh * scale) ^ q := by
      rw [hthr_def]
      have h1 : Real.exp 1 * Csym * Ckh * scale =
          Real.exp 1 * (Csym * Ckh * scale) := by ring
      rw [h1, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]; congr 1; ring
    calc
      (Csym * Ckh * scale) ^ q
          = (Csym * Ckh * scale) ^ q * (Real.exp (q : ℝ) * Real.exp (-(q : ℝ))) := by
            rw [← Real.exp_add]; simp
      _ = (Real.exp (q : ℝ) * (Csym * Ckh * scale) ^ q) * Real.exp (-(q : ℝ)) := by ring
      _ = threshold ^ q * Real.exp (-(q : ℝ)) := by rw [hthr_pow]
      _ ≤ threshold ^ q * Real.rpow N (-β) :=
            mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hthr_nonneg q)
  -- (6) Moment bound at the tight threshold.
  have hMomentThr' :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        threshold ^ q * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have := le_trans hCombine hAbsorb
    simpa [hp_def, hN_def] using this
  -- (7) Scale-agnostic Markov tail step.
  have hResult :=
    fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
      β threshold hβ hthr_nonneg n₁ n₂ m q X hn₁ hn₂ hm hq hMomentThr'
  have hthr_eq : threshold =
      (Real.exp 1 * Csym * Ckh) * Real.sqrt (q : ℝ) *
        (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) * Real.sqrt EnergyBound := by
    rw [hthr_def, hscale_def, hp_def]; ring
  rw [hthr_eq] at hResult
  exact hResult
