-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.theorem_F_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:40:38.529892+00:00
-- url     : https://prove2.me/submissions/42a914d2-974e-4957-a264-b822dab0723b

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_ProcessingNetworks_EntropyIneq_IsConvergent

section MatrixNormAux

open Filter Topology ProcessingNetworks.EntropyIneq
open scoped Matrix.Norms.Operator NNReal ENNReal

private lemma map_pow_complex {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    ∀ k : ℕ, (Q ^ k).map (algebraMap ℝ ℂ) = (Q.map (algebraMap ℝ ℂ)) ^ k
  | 0 => by
      ext i j
      by_cases h : i = j <;> simp [h]
  | k + 1 => by
      rw [pow_succ, pow_succ, ← map_pow_complex Q k]
      ext i j
      simp [Matrix.mul_apply]

private lemma norm_map_complex {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖M.map (algebraMap ℝ ℂ)‖ = ‖M‖ := by
  simp [Matrix.linfty_opNorm_def]

private lemma norm_pow_le_of_nonempty {d : ℕ} [Nonempty (Fin d)]
    (A : Matrix (Fin d) (Fin d) ℝ) : ∀ q : ℕ, ‖A ^ q‖ ≤ ‖A‖ ^ q
  | 0 => by simp
  | q + 1 => by
      rw [pow_succ, pow_succ]
      exact (norm_mul_le (A ^ q) A).trans
        (mul_le_mul_of_nonneg_right (norm_pow_le_of_nonempty A q) (norm_nonneg A))

private lemma geom_sum_one_sub_left {R : Type*} [Ring R] (x : R) :
    ∀ n : ℕ, (1 - x) * (∑ k ∈ Finset.range n, x ^ k) = 1 - x ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, mul_add, geom_sum_one_sub_left x n, sub_mul, one_mul, ← pow_succ']
      abel

private lemma geom_sum_one_sub_right {R : Type*} [Ring R] (x : R) :
    ∀ n : ℕ, (∑ k ∈ Finset.range n, x ^ k) * (1 - x) = 1 - x ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, add_mul, geom_sum_one_sub_right x n, mul_sub, mul_one, ← pow_succ]
      abel

private lemma imp_1_2 {d : ℕ} (hd : 0 < d) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hconv : IsConvergent Q) : RobustToDynamics.specRadius Q < 1 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let Qc : Matrix (Fin d) (Fin d) ℂ := Q.map (algebraMap ℝ ℂ)
  obtain ⟨z₀, hz₀, hz₀_eq⟩ := spectrum.exists_nnnorm_eq_spectralRadius Qc
  have hmax : ∀ z ∈ spectrum ℂ Qc, ‖z‖ ≤ ‖z₀‖ := by
    intro z hz
    have hle : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ Qc :=
      le_iSup₂ (f := fun k _ => (‖k‖₊ : ℝ≥0∞)) z hz
    rw [← hz₀_eq, ENNReal.coe_le_coe] at hle
    exact hle
  have hsr_le : RobustToDynamics.specRadius Q ≤ ‖z₀‖ := by
    unfold RobustToDynamics.specRadius
    exact csSup_le ⟨‖z₀‖, ⟨z₀, hz₀, rfl⟩⟩ (by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz)
  have hlim : Tendsto (fun k : ℕ => ‖Q ^ k‖) atTop (𝓝 0) := by
    simpa using hconv.norm
  have hev : ∀ᶠ k : ℕ in atTop, ‖Q ^ k‖ < 1 :=
    hlim.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let k := max N 1
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one (le_max_right N 1)
  have hQk : ‖Q ^ k‖ < 1 := hN k (le_max_left N 1)
  have hzk_mem : z₀ ^ k ∈ spectrum ℂ (Qc ^ k) := spectrum.pow_mem_pow Qc k hz₀
  have hzk_le : ‖z₀ ^ k‖ ≤ ‖Qc ^ k‖ := spectrum.norm_le_norm_of_mem hzk_mem
  rw [norm_pow, ← map_pow_complex Q k, norm_map_complex] at hzk_le
  have hzk_lt : ‖z₀‖ ^ k < 1 := hzk_le.trans_lt hQk
  have hz₀_lt : ‖z₀‖ < 1 := by
    by_contra hge
    push Not at hge
    have : (1 : ℝ) ≤ ‖z₀‖ ^ k := one_le_pow₀ hge
    linarith
  exact hsr_le.trans_lt hz₀_lt

private lemma imp_2_3 {d : ℕ} (hd : 0 < d) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hρ : RobustToDynamics.specRadius Q < 1) :
    IsUnit (1 - Q) ∧
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 (1 - Q)⁻¹) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let Qc : Matrix (Fin d) (Fin d) ℂ := Q.map (algebraMap ℝ ℂ)
  obtain ⟨z₀, hz₀, hz₀_eq⟩ := spectrum.exists_nnnorm_eq_spectralRadius Qc
  have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' spectrum ℂ Qc) :=
    ((spectrum.isCompact Qc).image continuous_norm).bddAbove
  have hz₀_le : ‖z₀‖ ≤ RobustToDynamics.specRadius Q :=
    le_csSup hbdd ⟨z₀, hz₀, rfl⟩
  have hz₀_lt : ‖z₀‖ < 1 := hz₀_le.trans_lt hρ
  let r : ℝ := (‖z₀‖ + 1) / 2
  have hr0 : 0 < r := by
    have : 0 ≤ ‖z₀‖ := norm_nonneg z₀
    dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hzr : ‖z₀‖ < r := by dsimp [r]; linarith
  have hsr_lt : spectralRadius ℂ Qc < ENNReal.ofReal r := by
    rw [← hz₀_eq]
    have hcoe : (‖z₀‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z₀‖ := by
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    rw [hcoe]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hzr
  have hgelf := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius Qc
  have hev := hgelf.eventually (Iio_mem_nhds hsr_lt)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let m := max N 1
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_right N 1)
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hQm_ofReal : ENNReal.ofReal (‖Qc ^ m‖ ^ (1 / (m : ℝ))) < ENNReal.ofReal r :=
    hN m (le_max_left N 1)
  have hQm_rpow : ‖Q ^ m‖ ^ (1 / (m : ℝ)) ≤ r := by
    have hlt := (ENNReal.ofReal_lt_ofReal_iff hr0).mp hQm_ofReal
    rw [← map_pow_complex Q m, norm_map_complex] at hlt
    exact hlt.le
  have hQm_le : ‖Q ^ m‖ ≤ r ^ m := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hQm_rpow hm_real_pos.le
    rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hm_real_pos.ne',
      Real.rpow_one, Real.rpow_natCast] at h1
    exact h1
  let M : ℝ := ∑ j ∈ Finset.range m, ‖Q ^ j‖ / r ^ j
  have hbound : ∀ k : ℕ, ‖Q ^ k‖ ≤ M * r ^ k := by
    intro k
    let q := k / m
    let rem := k % m
    have hk_eq : m * q + rem = k := Nat.div_add_mod k m
    have hrem_lt : rem < m := Nat.mod_lt k hm_pos
    have hrem_le : ‖Q ^ rem‖ / r ^ rem ≤ M :=
      Finset.single_le_sum (f := fun j => ‖Q ^ j‖ / r ^ j)
        (fun j _ => div_nonneg (norm_nonneg (Q ^ j)) (pow_nonneg hr0.le j))
        (Finset.mem_range.mpr hrem_lt)
    have hQrem : ‖Q ^ rem‖ ≤ M * r ^ rem :=
      (div_le_iff₀ (pow_pos hr0 rem)).mp hrem_le
    calc ‖Q ^ k‖
        = ‖(Q ^ m) ^ q * Q ^ rem‖ := by rw [← pow_mul, ← pow_add, hk_eq]
      _ ≤ ‖(Q ^ m) ^ q‖ * ‖Q ^ rem‖ := norm_mul_le _ _
      _ ≤ ‖Q ^ m‖ ^ q * (M * r ^ rem) :=
          mul_le_mul (norm_pow_le_of_nonempty (Q ^ m) q) hQrem (norm_nonneg _)
            (pow_nonneg (norm_nonneg _) _)
      _ ≤ (r ^ m) ^ q * (M * r ^ rem) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hQm_le q)
            (mul_nonneg (Finset.sum_nonneg fun j _ =>
              div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) (pow_nonneg hr0.le _))
      _ = M * r ^ k := by
          rw [← pow_mul]
          calc r ^ (m * q) * (M * r ^ rem)
              = M * (r ^ (m * q) * r ^ rem) := by ring
            _ = M * r ^ k := by rw [← pow_add, hk_eq]
  have hsum_norm : Summable (fun k : ℕ => ‖Q ^ k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left M)
  have hsum : Summable (fun k : ℕ => Q ^ k) := hsum_norm.of_norm
  let S : Matrix (Fin d) (Fin d) ℝ := ∑' k : ℕ, Q ^ k
  have hTend : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 S) :=
    hsum.hasSum.tendsto_sum_nat
  have hpow0 : Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h1Q_sub : Tendsto (fun n : ℕ => (1 : Matrix (Fin d) (Fin d) ℝ) - Q ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hpow0
  have hL1 : Tendsto (fun n : ℕ => (1 - Q) * ∑ k ∈ Finset.range n, Q ^ k) atTop
      (𝓝 ((1 - Q) * S)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.comp hTend
  have hL2 : Tendsto (fun n : ℕ => (1 - Q) * ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 1) := by
    simpa [Function.comp_def, geom_sum_one_sub_left Q] using h1Q_sub
  have hmulL : (1 - Q) * S = 1 := tendsto_nhds_unique hL1 hL2
  have hR1 : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, Q ^ k) * (1 - Q)) atTop
      (𝓝 (S * (1 - Q))) :=
    (continuous_id.mul continuous_const).continuousAt.tendsto.comp hTend
  have hR2 : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, Q ^ k) * (1 - Q)) atTop (𝓝 1) := by
    simpa [Function.comp_def, geom_sum_one_sub_right Q] using h1Q_sub
  have hmulR : S * (1 - Q) = 1 := tendsto_nhds_unique hR1 hR2
  have hu : IsUnit (1 - Q) := ⟨⟨1 - Q, S, hmulL, hmulR⟩, rfl⟩
  have hinv : (1 - Q)⁻¹ = S := Matrix.inv_eq_right_inv hmulL
  rw [hinv]
  exact ⟨hu, hTend⟩

end MatrixNormAux

open Filter Topology ProcessingNetworks.EntropyIneq

theorem solution {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    List.TFAE [IsConvergent Q, RobustToDynamics.specRadius Q < 1,
      IsUnit (1 - Q) ∧
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 (1 - Q)⁻¹)] := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 : IsConvergent Q := by
      unfold IsConvergent
      convert tendsto_const_nhds (x := (0 : Matrix (Fin 0) (Fin 0) ℝ)) using 1
      ext k i
      exact i.elim0
    have h2 : RobustToDynamics.specRadius Q < 1 := by
      have hemp : spectrum ℂ (Q.map (algebraMap ℝ ℂ)) = ∅ := by
        ext z
        simp only [spectrum.mem_iff, Set.mem_empty_iff_false, iff_false, not_not]
        exact ⟨⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩
      unfold RobustToDynamics.specRadius
      rw [hemp, Set.image_empty, Real.sSup_empty]
      exact zero_lt_one
    have h3 : IsUnit (1 - Q) ∧
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 (1 - Q)⁻¹) := by
      refine ⟨⟨⟨1 - Q, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩, ?_⟩
      convert tendsto_const_nhds (x := (1 - Q)⁻¹) using 1
      ext n i
      exact i.elim0
    tfae_have 1 → 2 := fun _ => h2
    tfae_have 2 → 3 := fun _ => h3
    tfae_have 3 → 1 := fun _ => h1
    tfae_finish
  · tfae_have 1 → 2 := imp_1_2 hd Q
    tfae_have 2 → 3 := imp_2_3 hd Q
    tfae_have 3 → 1 := by
      rintro ⟨_, hTend⟩
      unfold IsConvergent
      have hshift : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range (k + 1), Q ^ j) atTop
          (𝓝 (1 - Q)⁻¹) := hTend.comp (tendsto_add_atTop_nat 1)
      have hdiff := hshift.sub hTend
      rw [sub_self] at hdiff
      convert hdiff using 1
      ext k
      rw [Finset.sum_range_succ, add_sub_cancel_left]
    tfae_finish
