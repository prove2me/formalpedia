-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P08.remarkFive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:09:41.53396+00:00
-- url     : https://prove2.me/submissions/1382d31a-0e3f-43ec-87ad-7c5b57705fc4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 5, PDF p.17: appropriate t may depend on energy; all oscillator
parameters and positive epsilon are fixed before the large-coefficientEnergy limit. -/

lemma g66a_core (L : ℝ → ℝ) (hL : Tendsto L atTop atTop) (k a eps : ℝ) (heps : 0 < eps) :
    Asymptotics.IsLittleO atTop
      (fun E => k * eps * (2 * (1 / L E) + continuityRatio eps (1 / L E)) *
        (L E - a * Real.log (eps * (1 / L E))) / eps - k * L E) L := by
  have ht : Tendsto (fun E => 1 / L E) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hL
  have hlog : Tendsto (fun E => Real.log (L E) / L E) atTop (𝓝 0) := by
    have := (Real.isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
    simpa using this
  have hf : Tendsto (fun E => 2 * (1 / L E) + continuityRatio eps (1 / L E)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => 2 * t + (1 + t / 2) / (1 - eps * t)) 0 := by
      apply ContinuousAt.add (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp
    have := hc.tendsto.comp ht
    simpa [continuityRatio, Function.comp_def] using this
  have hlim : Tendsto (fun E => k * (2 * (1 / L E) + continuityRatio eps (1 / L E)) *
      (1 - a * Real.log eps * (1 / L E) + a * (Real.log (L E) / L E)) - k) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := k)).mul hf).mul
      (((tendsto_const_nhds (x := (1:ℝ))).sub ((tendsto_const_nhds (x := a * Real.log eps)).mul ht)).add
        ((tendsto_const_nhds (x := a)).mul hlog))
    have := this.sub (tendsto_const_nhds (x := k))
    simpa using this
  rw [Asymptotics.isLittleO_iff_tendsto']
  · refine hlim.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with E hE
    show _ = (_ / eps - k * L E) / L E
    have hl : Real.log (eps * (1 / L E)) = Real.log eps - Real.log (L E) := by
      rw [one_div, Real.log_mul heps.ne' (inv_ne_zero hE.ne'), Real.log_inv]; ring
    rw [hl]
    field_simp
    ring
  · filter_upwards [hL.eventually_gt_atTop 0] with E hE h0
    exact absurd h0 hE.ne'


lemma g66a_env {ell : ℕ} (hell : 0 < ell) (hbar : ℝ) (hhbar : 0 < hbar)
    (omega : Fin ell → ℝ) (homega : ∀ i, 0 < omega i) :
    Tendsto (oscillatorEnvelope hbar omega) atTop atTop := by
  unfold oscillatorEnvelope
  have hgm : 0 < QAlgorithms.Papers.Independent.Claimed50.P07.oscillatorGeometricMean hbar omega := by
    unfold QAlgorithms.Papers.Independent.Claimed50.P07.oscillatorGeometricMean
    exact Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => mul_pos hhbar (homega i)) _
  have hl : (0:ℝ) < ell := by exact_mod_cast hell
  set c := (ell : ℝ) * QAlgorithms.Papers.Independent.Claimed50.P07.oscillatorGeometricMean hbar omega
  have hc : 0 < c := mul_pos hl hgm
  have h1 : Tendsto (fun E : ℝ => (E + QAlgorithms.Papers.Independent.Claimed50.P07.oscillatorGround hbar omega) / c) atTop atTop := by
    apply Tendsto.atTop_div_const hc
    exact tendsto_atTop_add_const_right _ _ tendsto_id
  have h2 := (Real.tendsto_log_atTop.comp h1).const_mul_atTop hl
  exact tendsto_atTop_add_const_right _ _ h2

theorem solution {ell : ℕ} (hell : 0 < ell) (hbar : ℝ) (hhbar : 0 < hbar)
    (omega : Fin ell → ℝ) (homega : ∀ i, 0 < omega i)
    (epsilon : ℝ) (heps : 0 < epsilon) (hepsone : epsilon ≤ 1) :
    ∃ R : ℝ → ℝ, Asymptotics.IsLittleO atTop R (oscillatorEnvelope hbar omega) ∧
      ∀ᶠ E : ℝ in atTop, ∃ t : ℝ, 0 < t ∧ t ≤ 1/(2*epsilon) ∧
        oscillatorMain 2 hbar omega E epsilon t ≤
          epsilon * (2 * oscillatorEnvelope hbar omega E + R E) := by
  have hL := g66a_env hell hbar hhbar omega homega
  refine ⟨fun E => oscillatorMain 2 hbar omega E epsilon (1 / oscillatorEnvelope hbar omega E) / epsilon -
    2 * oscillatorEnvelope hbar omega E, ?_, ?_⟩
  · have := g66a_core _ hL 2 (ell : ℝ) epsilon heps
    simpa [oscillatorMain] using this
  · filter_upwards [hL.eventually_ge_atTop (2 * epsilon)] with E hE
    have hpos : 0 < oscillatorEnvelope hbar omega E := lt_of_lt_of_le (by linarith) hE
    refine ⟨1 / oscillatorEnvelope hbar omega E, by positivity, one_div_le_one_div_of_le (by linarith) hE, ?_⟩
    field_simp
    ring_nf
    exact le_refl _


end
