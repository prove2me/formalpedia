-- Prove2me | solution 1 for WassersteinDRO.Gelbrich.gelbrich_risk_bound_false
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:16:00.95711+00:00
-- url     : https://prove2.me/submissions/425b5bce-f67c-4530-a456-26aa64d3cd3d

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_worstCaseRisk
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichRisk
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace S216WD
open WassersteinDRO.Gelbrich

abbrev E := EuclideanSpace ℝ (Fin 2)

noncomputable def c (n : ℕ) : ℝ := 3 / 8 * (1 / 4) ^ n
noncomputable def v (n : ℕ) : E := WithLp.toLp 2 ![1, 2 ^ n]
noncomputable def PN : Measure E :=
  Measure.sum (fun n => ENNReal.ofReal (c n) • (Measure.dirac (v n) + Measure.dirac (-v n)))

lemma c_nonneg (n : ℕ) : 0 ≤ c n := by unfold c; positivity

@[simp] lemma v0 (n : ℕ) : v n 0 = 1 := by simp [v]
@[simp] lemma v1 (n : ℕ) : v n 1 = 2 ^ n := by simp [v]
@[simp] lemma nv0 (n : ℕ) : (-v n) 0 = -1 := by simp [v]
@[simp] lemma nv1 (n : ℕ) : (-v n) 1 = -2 ^ n := by simp [v]

lemma lint (g : E → ℝ≥0∞) :
    ∫⁻ x, g x ∂PN = ∑' n, ENNReal.ofReal (c n) * (g (v n) + g (-v n)) := by
  simp [PN, lintegral_sum_measure, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac, mul_add]

lemma ae_PN (p : E → Prop) (h : ∀ n, p (v n) ∧ p (-v n)) : ∀ᵐ x ∂PN, p x := by
  rw [PN, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq]
  exact ⟨(h n).1, (h n).2⟩

lemma ofReal_pair (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (c n) * (ENNReal.ofReal a + ENNReal.ofReal b) =
      ENNReal.ofReal (c n * (a + b)) := by
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (c_nonneg n)]

lemma tsum_c2 : ∑' n, c n * (1 + 1) = 1 := by
  have : (fun n => c n * (1 + 1)) = fun n => (3 / 4 : ℝ) * (1 / 4) ^ n := by
    funext n; unfold c; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

instance : IsProbabilityMeasure PN := by
  constructor
  rw [← lintegral_one, lint]
  have : ∀ n, ENNReal.ofReal (c n) * ((1 : ℝ≥0∞) + 1) = ENNReal.ofReal (c n * (1 + 1)) := by
    intro n; have := ofReal_pair n 1 1 zero_le_one zero_le_one; simpa using this
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := c_nonneg n; positivity)
    (by
      have : (fun n => c n * (1 + 1)) = fun n => (3 / 4 : ℝ) * (1 / 4) ^ n := by
        funext n; unfold c; ring
      rw [this]; exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _),
    tsum_c2]
  simp

lemma map_neg_PN : PN.map (fun x => -x) = PN := by
  rw [PN, Measure.map_sum (by fun_prop)]
  congr 1
  funext n
  rw [Measure.map_smul, Measure.map_add _ _ (by fun_prop), Measure.map_dirac' (by fun_prop),
    Measure.map_dirac' (by fun_prop), neg_neg, add_comm]

lemma mean_PN : meanVector PN = 0 := by
  have h : meanVector PN = -meanVector PN := by
    unfold meanVector
    conv_lhs => rw [← map_neg_PN]
    rw [integral_map (by fun_prop) (by fun_prop), integral_neg]
  have h2 : (2 : ℝ) • meanVector PN = 0 := by rw [two_smul]; nth_rw 1 [h]; simp
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)


lemma cov_apply (i j : Fin 2) : covarianceMatrix PN i j = ∫ x, x i * x j ∂PN := by
  simp [covarianceMatrix, mean_PN]

lemma ae_sq0 : ∀ᵐ x ∂PN, x 0 * x 0 = 1 := ae_PN _ (fun n => by simp)

lemma integrable_sq0 : Integrable (fun x : E => x 0 * x 0) PN :=
  (integrable_const (1 : ℝ)).congr (ae_sq0.mono fun x hx => hx.symm)

lemma integral_sq0 : ∫ x, x 0 * x 0 ∂PN = 1 := by
  rw [integral_congr_ae ae_sq0]; simp

lemma cov00 : covarianceMatrix PN 0 0 = 1 := by rw [cov_apply, integral_sq0]

lemma cov11 : covarianceMatrix PN 1 1 = 0 := by
  rw [cov_apply]
  apply integral_undef
  intro h
  have h2 := h.2
  unfold HasFiniteIntegral at h2
  rw [lint] at h2
  have : ∀ n, ENNReal.ofReal (c n) * (‖v n 1 * v n 1‖ₑ + ‖(-v n) 1 * (-v n) 1‖ₑ)
      = ENNReal.ofReal (3 / 4) := by
    intro n
    simp only [v1, nv1, Real.enorm_eq_ofReal_abs]
    rw [ofReal_pair n _ _ (abs_nonneg _) (abs_nonneg _)]
    congr 1
    have : (1 / 4 : ℝ) ^ n * 2 ^ n * 2 ^ n = 1 := by
      rw [← mul_pow, ← mul_pow]; norm_num
    unfold c
    rw [neg_mul_neg, abs_of_nonneg (by positivity)]
    linear_combination (3 / 4 : ℝ) * this
  simp_rw [this] at h2
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)] at h2
  exact lt_irrefl _ h2

lemma cov01_pos : 0 < covarianceMatrix PN 0 1 := by
  rw [cov_apply, integral_eq_lintegral_of_nonneg_ae
    (ae_PN _ (fun n => by simp)) (by fun_prop), lint]
  have : ∀ n, ENNReal.ofReal (c n) * (ENNReal.ofReal (v n 0 * v n 1) +
      ENNReal.ofReal ((-v n) 0 * (-v n) 1)) = ENNReal.ofReal ((3 / 4 : ℝ) * (1 / 2) ^ n) := by
    intro n
    simp only [v0, v1, nv0, nv1, neg_mul_neg, one_mul]
    rw [ofReal_pair n _ _ (by positivity) (by positivity)]
    congr 1
    have : (1 / 4 : ℝ) ^ n * 2 ^ n = (1 / 2) ^ n := by
      rw [← mul_pow]; norm_num
    unfold c
    linear_combination (3 / 4 : ℝ) * this
  simp_rw [this]
  have hs : Summable (fun n : ℕ => (3 / 4 : ℝ) * (1 / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun n => by positivity)]
  exact hs.tsum_pos (fun n => by positivity) 0 (by norm_num)

lemma cov10 : covarianceMatrix PN 1 0 = covarianceMatrix PN 0 1 := by
  rw [cov_apply, cov_apply]; simp_rw [mul_comm]

lemma not_psd_cov : ¬ (covarianceMatrix PN).PosSemidef := by
  intro h
  have := h.dotProduct_mulVec_nonneg ![covarianceMatrix PN 0 1, -1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, cov00, cov11, cov10] at this
  nlinarith [cov01_pos]

lemma wass_PN : wassersteinDistance 2 PN PN = 0 := by
  unfold wassersteinDistance
  have : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = PN ∧ π.map Prod.snd = PN),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (2 : ℝ)) ∂π) = 0 := by
    have h1 : (PN.map (fun x => (x, x))).map Prod.fst = PN := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]; exact Measure.map_id
    have h2 : (PN.map (fun x => (x, x))).map Prod.snd = PN := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]; exact Measure.map_id
    refine le_antisymm ((iInf₂_le (PN.map (fun x => (x, x))) ⟨h1, h2⟩).trans ?_) bot_le
    rw [lintegral_map (by fun_prop) (by fun_prop)]; simp
  rw [this]; exact ENNReal.zero_rpow_of_pos (by norm_num)

lemma PN_mem : PN ∈ ambiguitySet 1 2 Set.univ PN :=
  ⟨measure_univ, by simp, by rw [wass_PN]; exact bot_le⟩


lemma psdSqrt_of_not {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : ¬ A.PosSemidef) :
    psdSqrt A = 0 := by
  unfold psdSqrt
  rw [dif_neg]
  rintro ⟨B, hB, rfl⟩
  apply hA
  have := Matrix.posSemidef_conjTranspose_mul_self B
  rwa [hB.isHermitian.eq] at this

lemma psdSqrt_zero {k : ℕ} : psdSqrt (0 : Matrix (Fin k) (Fin k) ℝ) = 0 := by
  unfold psdSqrt
  split_ifs with h
  · obtain ⟨hB, hBB⟩ := h.choose_spec
    have : h.choose.conjTranspose * h.choose = 0 := by rw [hB.isHermitian.eq]; exact hBB
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  · rfl

noncomputable def ell (z : E) : ℝ := z 0 * z 0

lemma worst_ge : ((1 : ℝ) : EReal) ≤ worstCaseRisk 1 2 Set.univ PN ell := by
  unfold worstCaseRisk
  refine le_iSup_of_le PN (le_iSup_of_le PN_mem (le_iSup_of_le integrable_sq0 ?_))
  unfold nominalRisk ell; rw [integral_sq0]

lemma gelbrich_le : gelbrichRisk 1 Set.univ 0 (covarianceMatrix PN) ell ≤ 0 := by
  unfold gelbrichRisk
  refine iSup₂_le fun Q hQ => iSup_le fun _ => ?_
  obtain ⟨_, _, hpsd, hineq⟩ := hQ
  rw [psdSqrt_of_not _ not_psd_cov, Matrix.zero_mul, Matrix.mul_zero, psdSqrt_zero,
    smul_zero, sub_zero, Matrix.trace_add, Matrix.trace_fin_two, Matrix.trace_fin_two,
    cov00, cov11] at hineq
  have hS0 : 0 ≤ covarianceMatrix Q 0 0 := by
    simp only [covarianceMatrix, Matrix.of_apply]
    exact integral_nonneg fun x => mul_self_nonneg _
  have hS1 : 0 ≤ covarianceMatrix Q 1 1 := by
    simp only [covarianceMatrix, Matrix.of_apply]
    exact integral_nonneg fun x => mul_self_nonneg _
  have hn : 0 ≤ ‖(0 : E) - meanVector Q‖ ^ 2 := by positivity
  have hμ : ‖(0 : E) - meanVector Q‖ ^ 2 = 0 := by nlinarith
  have hμ' : meanVector Q = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hμ
    rw [norm_eq_zero, zero_sub, neg_eq_zero] at this
    exact this
  have hS00 : covarianceMatrix Q 0 0 = 0 := by nlinarith
  simp only [covarianceMatrix, Matrix.of_apply, hμ'] at hS00
  have : nominalRisk Q ell = 0 := by
    unfold nominalRisk ell
    simpa using hS00
  rw [this]; rfl
end S216WD

open WassersteinDRO.Gelbrich in
theorem solution :
    ¬∀ {m : ℕ} (ε p : ℝ), 2 ≤ p → (Ξ : Set (EuclideanSpace ℝ (Fin m))) →
      (PN : Measure (EuclideanSpace ℝ (Fin m))) →
      (μhat : EuclideanSpace ℝ (Fin m)) → (SigmaHat : Matrix (Fin m) (Fin m) ℝ) →
      meanVector PN = μhat → covarianceMatrix PN = SigmaHat →
      (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) →
      worstCaseRisk ε p Ξ PN ℓ ≤ gelbrichRisk ε Ξ μhat SigmaHat ℓ := by
  intro h
  have h1 := h (m := 2) 1 2 le_rfl Set.univ S216WD.PN 0 _ S216WD.mean_PN rfl S216WD.ell
  have h2 := (S216WD.worst_ge.trans h1).trans S216WD.gelbrich_le
  exact absurd h2 (by norm_num)
