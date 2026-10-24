-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P05.remark1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:12:27.528139+00:00
-- url     : https://prove2.me/submissions/bc48df6e-12e9-4cdc-b000-126ee248a2cb

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P05

noncomputable section

open Filter Topology

namespace X7R1

open QAlgorithms.Papers.Independent.Frontier30.P05

lemma g_cont : Continuous entropyCorrection := by
  unfold entropyCorrection
  have h1 : Continuous fun x : ℝ => (x + 1) * Real.log (x + 1) :=
    Real.continuous_mul_log.comp (continuous_id.add continuous_const)
  exact h1.sub Real.continuous_mul_log

lemma g_mono : MonotoneOn entropyCorrection (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) g_cont.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hx
    have hx1 : x + 1 ≠ 0 := by have : (0:ℝ) < x := hx; linarith
    have d1 : HasDerivAt (fun y : ℝ => (y + 1) * Real.log (y + 1)) (Real.log (x + 1) + 1) x := by
      have := (Real.hasDerivAt_mul_log hx1).comp x ((hasDerivAt_id x).add_const 1)
      rw [mul_one] at this
      exact this
    exact (d1.sub (Real.hasDerivAt_mul_log hx0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : (0:ℝ) < x := hx
    have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hx
    have hx1 : x + 1 ≠ 0 := by linarith
    have d1 : HasDerivAt (fun y : ℝ => (y + 1) * Real.log (y + 1)) (Real.log (x + 1) + 1) x := by
      have := (Real.hasDerivAt_mul_log hx1).comp x ((hasDerivAt_id x).add_const 1)
      rw [mul_one] at this
      exact this
    have hd : HasDerivAt entropyCorrection
        (Real.log (x + 1) + 1 - (Real.log x + 1)) x := by
      have := d1.sub (Real.hasDerivAt_mul_log hx0)
      exact this
    rw [hd.deriv]
    have : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx' (by linarith)
    linarith

/-- ε·G(Ē/(εt)²) written through the ratio G(x)/√x. -/
lemma key_id (G : ℝ → ℝ) {Ebar epsilon t : ℝ} (hE : 0 < Ebar) (he : 0 < epsilon) (ht : 0 < t) :
    epsilon * G (Ebar / (epsilon * t) ^ 2) =
      (Real.sqrt Ebar / t) * (G (Ebar / (epsilon * t) ^ 2) /
        Real.sqrt (Ebar / (epsilon * t) ^ 2)) := by
  have hs : Real.sqrt (Ebar / (epsilon * t) ^ 2) = Real.sqrt Ebar / (epsilon * t) := by
    rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hs]
  have : 0 < Real.sqrt Ebar := Real.sqrt_pos.2 hE
  field_simp

end X7R1

open Filter

open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P05 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (h14 : Condition14 S) (G : ℝ → ℝ) (hG : AdmissibleMajorant b S G)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (∀ Ebar t : ℝ, 0 < Ebar → 0 < t →
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → epsilon1 ≤ epsilon2 →
        t ≤ parameterLimit G Ebar epsilon1 → t ≤ parameterLimit G Ebar epsilon2 →
        continuityBound G Ebar epsilon1 C D t ≤ continuityBound G Ebar epsilon2 C D t) ∧
    (∀ epsilon t : ℝ, 0 < epsilon → 0 < t →
      ∀ Ebar1 Ebar2 : ℝ, 0 < Ebar1 → Ebar1 ≤ Ebar2 →
        t ≤ parameterLimit G Ebar1 epsilon → t ≤ parameterLimit G Ebar2 epsilon →
        continuityBound G Ebar1 epsilon C D t ≤ continuityBound G Ebar2 epsilon C D t) ∧
    (∀ Ebar t : ℝ, 0 < Ebar → 0 < t →
      Tendsto (fun epsilon : ℝ => continuityBound G Ebar epsilon C D t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  obtain ⟨-, -, hlim, hmono, hanti⟩ := hG
  set k : ℝ := 1 / (firstDimension G : ℝ) + Real.log 2 with hk
  have hk0 : 0 ≤ k := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hform : ∀ Ebar epsilon t, continuityBound G Ebar epsilon C D t =
      C * (1 + 4 * t) * (epsilon * G (Ebar / (epsilon * t) ^ 2) + epsilon * k) +
      D * (2 * entropyCorrection (epsilon * t) + entropyCorrection (epsilon * (1 + 2 * t))) := by
    intro Ebar epsilon t; simp only [continuityBound, hk]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro Ebar t hE ht e1 e2 he1 h12 _ _
    have he2 : 0 < e2 := lt_of_lt_of_le he1 h12
    rw [hform, hform]
    have hx1 : 0 < Ebar / (e1 * t) ^ 2 := by positivity
    have hx2 : 0 < Ebar / (e2 * t) ^ 2 := by positivity
    have hx21 : Ebar / (e2 * t) ^ 2 ≤ Ebar / (e1 * t) ^ 2 := by
      apply div_le_div_of_nonneg_left hE.le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h12 ht.le) 2
    have hratio := hanti hx2 hx1 hx21
    have hA : e1 * G (Ebar / (e1 * t) ^ 2) ≤ e2 * G (Ebar / (e2 * t) ^ 2) := by
      rw [X7R1.key_id G hE he1 ht, X7R1.key_id G hE he2 ht]
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    have hB : e1 * k ≤ e2 * k := mul_le_mul_of_nonneg_right h12 hk0
    have hg1 : entropyCorrection (e1 * t) ≤ entropyCorrection (e2 * t) :=
      X7R1.g_mono (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity))
        (mul_le_mul_of_nonneg_right h12 ht.le)
    have hg2 : entropyCorrection (e1 * (1 + 2 * t)) ≤ entropyCorrection (e2 * (1 + 2 * t)) :=
      X7R1.g_mono (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity))
        (mul_le_mul_of_nonneg_right h12 (by positivity))
    have hC' : 0 ≤ C * (1 + 4 * t) := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add hA hB) hC'
    have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hg1
      (by norm_num : (0:ℝ) ≤ 2)) hg2) hD
    linarith
  · intro e t he ht E1 E2 hE1 h12 _ _
    rw [hform, hform]
    have hx1 : 0 < E1 / (e * t) ^ 2 := by positivity
    have hx2 : 0 < E2 / (e * t) ^ 2 := by
      have : 0 < E2 := lt_of_lt_of_le hE1 h12
      positivity
    have hx12 : E1 / (e * t) ^ 2 ≤ E2 / (e * t) ^ 2 :=
      div_le_div_of_nonneg_right h12 (by positivity)
    have hGm : G (E1 / (e * t) ^ 2) ≤ G (E2 / (e * t) ^ 2) := hmono.monotoneOn hx1 hx2 hx12
    have hC' : 0 ≤ C * (1 + 4 * t) := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGm he.le) hC'
    nlinarith
  · intro Ebar t hE ht
    have hform' : (fun epsilon => continuityBound G Ebar epsilon C D t) =ᶠ[𝓝[>] 0]
        (fun epsilon => C * (1 + 4 * t) * ((Real.sqrt Ebar / t) *
          (fun x => G x / Real.sqrt x) (Ebar / (epsilon * t) ^ 2) + epsilon * k) +
          D * (2 * entropyCorrection (epsilon * t) +
            entropyCorrection (epsilon * (1 + 2 * t)))) := by
      filter_upwards [self_mem_nhdsWithin] with e he
      rw [hform, X7R1.key_id G hE he ht]
    refine Tendsto.congr' hform'.symm ?_
    have hx : Tendsto (fun epsilon : ℝ => Ebar / (epsilon * t) ^ 2) (𝓝[>] 0) atTop := by
      have h1 : Tendsto (fun epsilon : ℝ => (epsilon * t) ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have : Tendsto (fun epsilon : ℝ => (epsilon * t) ^ 2) (𝓝 0) (𝓝 ((0 * t) ^ 2)) :=
            ((continuous_id.mul continuous_const).pow 2).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with e he
          have : (0:ℝ) < e := he
          show (0:ℝ) < (e * t) ^ 2
          positivity
      have h2 := tendsto_inv_nhdsGT_zero.comp h1
      have h3 := h2.const_mul_atTop hE
      refine h3.congr (fun e => ?_)
      simp [div_eq_mul_inv]
    have hA : Tendsto (fun epsilon : ℝ => (fun x => G x / Real.sqrt x) (Ebar / (epsilon * t) ^ 2))
        (𝓝[>] 0) (𝓝 0) := hlim.comp hx
    have hlin : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hg : ∀ c : ℝ, Tendsto (fun epsilon : ℝ => entropyCorrection (epsilon * c)) (𝓝[>] 0) (𝓝 0) := by
      intro c
      have : Tendsto (fun epsilon : ℝ => entropyCorrection (epsilon * c)) (𝓝 0)
          (𝓝 (entropyCorrection (0 * c))) :=
        (X7R1.g_cont.comp (continuous_id.mul continuous_const)).tendsto 0
      have h0 : entropyCorrection (0 * c) = 0 := by simp [entropyCorrection]
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ((((hA.const_mul (Real.sqrt Ebar / t)).add (hlin.mul_const k)).const_mul
      (C * (1 + 4 * t))).add
      ((((hg t).const_mul 2).add (hg (1 + 2 * t))).const_mul D))
    simpa using this
