-- Prove2me | solution 1 for RobustRegLasso.Coupled.corollary_1_dual_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T19:42:26.13734+00:00
-- url     : https://prove2.me/submissions/f00714b0-8120-4c92-bf13-b88fb563b877

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

set_option autoImplicit false

namespace F92Help

open RobustRegLasso.Coupled

lemma N_cont {m : ℕ} (N : Seminorm ℝ (Fin m → ℝ)) : Continuous N :=
  continuousOn_univ.mp (N.convexOn.continuousOn isOpen_univ)

lemma N_lower {m : ℕ} (N : Seminorm ℝ (Fin m → ℝ)) (hN : ∀ z, N z = 0 → z = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ≤ N z := by
  have hS : IsCompact (Metric.sphere (0 : Fin m → ℝ) 1) := isCompact_sphere 0 1
  have key : ∀ z : Fin m → ℝ, z ≠ 0 → ‖z‖⁻¹ • z ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  by_cases hne : (Metric.sphere (0 : Fin m → ℝ) 1).Nonempty
  · obtain ⟨z0, hz0, hmin⟩ := hS.exists_isMinOn hne (N_cont N).continuousOn
    have hz0ne : z0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz0
      norm_num at hz0
    have hpos : 0 < N z0 := by
      rcases (apply_nonneg N z0).lt_or_eq with h | h
      · exact h
      · exact absurd (hN z0 h.symm) hz0ne
    refine ⟨N z0, hpos, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have h1 : N z0 ≤ N (‖z‖⁻¹ • z) := isMinOn_iff.mp hmin _ (key z hz)
      rw [map_smul_eq_mul, norm_inv, norm_norm] at h1
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      calc N z0 * ‖z‖ ≤ ‖z‖⁻¹ * N z * ‖z‖ := by gcongr
        _ = N z := by field_simp
  · refine ⟨1, one_pos, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · exact absurd ⟨_, key z hz⟩ hne

lemma dual_attain {m : ℕ} (N : Seminorm ℝ (Fin m → ℝ)) (hN : ∀ z, N z = 0 → z = 0)
    (y : Fin m → ℝ) :
    ∃ zs : Fin m → ℝ, N zs ≤ 1 ∧ ∀ z, N z ≤ 1 → ∑ i, y i * z i ≤ ∑ i, y i * zs i := by
  obtain ⟨c, hc, hcN⟩ := N_lower N hN
  have hK : IsCompact {z : Fin m → ℝ | N z ≤ 1} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (N_cont N) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1 / c)).subset ?_
      intro z hz
      simp only [Set.mem_setOf_eq] at hz
      rw [mem_closedBall_zero_iff, le_div_iff₀ hc]
      have := hcN z
      nlinarith
  have hcont : Continuous fun z : Fin m → ℝ => ∑ i, y i * z i :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
  obtain ⟨zs, hzs, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ hcont.continuousOn
  exact ⟨zs, hzs, fun z hz => isMaxOn_iff.mp hmax z hz⟩

lemma dualNorm_spec {m : ℕ} (N : Seminorm ℝ (Fin m → ℝ)) (hN : ∀ z, N z = 0 → z = 0)
    (y : Fin m → ℝ) :
    ∃ zs : Fin m → ℝ, N zs ≤ 1 ∧ dualNorm N y = ∑ i, y i * zs i ∧
      ∀ z, N z ≤ 1 → ∑ i, y i * z i ≤ dualNorm N y := by
  obtain ⟨zs, hzs, hmax⟩ := dual_attain N hN y
  have hG : IsGreatest {t : ℝ | ∃ z : Fin m → ℝ, N z ≤ 1 ∧ t = ∑ i, y i * z i}
      (∑ i, y i * zs i) :=
    ⟨⟨zs, hzs, rfl⟩, by rintro t ⟨z, hz, rfl⟩; exact hmax z hz⟩
  have hD : dualNorm N y = ∑ i, y i * zs i := by
    unfold dualNorm
    exact hG.csSup_eq
  exact ⟨zs, hzs, hD, fun z hz => hD ▸ hmax z hz⟩

lemma abs_pair {m : ℕ} (N : Seminorm ℝ (Fin m → ℝ)) (hN : ∀ z, N z = 0 → z = 0)
    (hAbs : IsAbsolute N) (y : Fin m → ℝ)
    (hD : ∀ z, N z ≤ 1 → ∑ i, y i * z i ≤ dualNorm N y) :
    ∀ z, ∑ i, |y i| * |z i| ≤ dualNorm N y * N z := by
  intro z
  obtain ⟨w, hw⟩ : ∃ w : Fin m → ℝ, w = fun i => if 0 ≤ y i then |z i| else -|z i| :=
    ⟨_, rfl⟩
  have hNw : N w = N z := by
    rw [← hAbs w, ← hAbs z]
    congr 1
    funext i
    rw [hw]
    dsimp only
    split_ifs <;> simp [abs_neg]
  have hsum : ∑ i, |y i| * |z i| = ∑ i, y i * w i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw]
    dsimp only
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  rcases (apply_nonneg N z).lt_or_eq with hpos | h0
  · have hle : N ((N z)⁻¹ • w) ≤ 1 := le_of_eq (by
      rw [map_smul_eq_mul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, hNw,
        inv_mul_cancel₀ hpos.ne'])
    have h1 := hD ((N z)⁻¹ • w) hle
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have e : ∑ i, y i * ((N z)⁻¹ * w i) = (N z)⁻¹ * ∑ i, y i * w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, inv_mul_le_iff₀ hpos] at h1
    rw [hsum, mul_comm]
    exact h1
  · have hz := hN z h0.symm
    simp [hz]

lemma exists_unit_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (r : E) : ∃ u : E, ‖u‖ = 1 ∧ r = ‖r‖ • u := by
  by_cases hr : r = 0
  · obtain ⟨e, he⟩ := exists_ne (0 : E)
    refine ⟨‖e‖⁻¹ • e, ?_, by simp [hr]⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)]
  · refine ⟨‖r‖⁻¹ • r, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr), one_smul]

lemma matVec_add' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (a δ : Fin m → E) (x : Fin m → ℝ) : matVec (a + δ) x = matVec a x + matVec δ x := by
  simp only [matVec, Pi.add_apply, smul_add, Finset.sum_add_distrib]

lemma part1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (N : Seminorm ℝ (Fin m → ℝ))
    (hN : ∀ z, N z = 0 → z = 0) (hAbs : IsAbsolute N) (l : ℝ) (hl : 0 ≤ l)
    (x : Fin m → ℝ) :
    IsGreatest (residualValues a b (normBudgetSet N l) x)
        (‖b - matVec a x‖ + l * dualNorm N x) := by
  obtain ⟨zs, hzs, hDeq, hD⟩ := dualNorm_spec N hN x
  have hD0 : 0 ≤ dualNorm N x := by
    have := hD 0 (by simp)
    simpa using this
  have hpair := abs_pair N hN hAbs x hD
  have hres : ∀ δ : Fin m → E,
      perturbedResidual a δ b x = ‖(b - matVec a x) - matVec δ x‖ := by
    intro δ
    rw [perturbedResidual, matVec_add', sub_sub]
  constructor
  · obtain ⟨u, hu1, hru⟩ := exists_unit_dir (b - matVec a x)
    obtain ⟨s, hsdef⟩ : ∃ s : Fin m → ℝ, s = fun i => if 0 ≤ x i then 1 else -1 := ⟨_, rfl⟩
    have hs : ∀ i, x i * s i = |x i| := by
      intro i
      rw [hsdef]
      dsimp only
      split_ifs with h
      · rw [abs_of_nonneg h, mul_one]
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hs1 : ∀ i, |s i| = 1 := by
      intro i
      rw [hsdef]
      dsimp only
      split_ifs <;> simp
    have hW : ∑ i, |x i| * |zs i| = dualNorm N x := by
      apply le_antisymm
      · have := hpair zs
        nlinarith [apply_nonneg N zs]
      · rw [hDeq]
        exact Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _
    refine ⟨(fun i => (-(l * |zs i| * s i)) • u), ?_, ?_⟩
    · show N (colNorms _) ≤ l
      have hc : colNorms (fun i => (-(l * |zs i| * s i)) • u) = l • (fun i => |zs i|) := by
        funext i
        simp only [colNorms, Pi.smul_apply, smul_eq_mul, norm_smul, hu1, mul_one,
          Real.norm_eq_abs, abs_neg, abs_mul, hs1, abs_abs, abs_of_nonneg hl]
      rw [hc, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hl, hAbs zs]
      nlinarith
    · show perturbedResidual a _ b x = _
      rw [hres]
      have hmv : matVec (fun i => (-(l * |zs i| * s i)) • u) x
          = (-(l * dualNorm N x)) • u := by
        simp only [matVec, smul_smul, ← Finset.sum_smul]
        congr 1
        rw [← hW, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hs i]
        ring
      have hsum : (b - matVec a x) - (-(l * dualNorm N x)) • u
          = (‖b - matVec a x‖ + l * dualNorm N x) • u := by
        rw [add_smul, ← hru, neg_smul, sub_neg_eq_add]
      rw [hmv, hsum, norm_smul, hu1, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hl hD0))]
  · rintro t ⟨δ, hδ, rfl⟩
    change N (colNorms δ) ≤ l at hδ
    show perturbedResidual a δ b x ≤ _
    rw [hres]
    have h1 : ‖matVec δ x‖ ≤ ∑ i, |x i| * |colNorms δ i| := by
      unfold matVec
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      simp only [colNorms, abs_norm]
    have h2 := hpair (colNorms δ)
    have h3 : dualNorm N x * N (colNorms δ) ≤ dualNorm N x * l :=
      mul_le_mul_of_nonneg_left hδ hD0
    calc ‖(b - matVec a x) - matVec δ x‖ ≤ ‖b - matVec a x‖ + ‖matVec δ x‖ :=
          norm_sub_le _ _
      _ ≤ ‖b - matVec a x‖ + l * dualNorm N x := by linarith

lemma robust_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (b : E) (U : Set (Fin m → E)) (x : Fin m → ℝ) (v : ℝ)
    (h : IsGreatest (residualValues a b U x) v) : robustObjective a b U x = (v : EReal) := by
  obtain ⟨⟨δ0, hδ0, hv⟩, hub⟩ := h
  unfold robustObjective
  apply le_antisymm
  · exact iSup₂_le fun δ hδ => EReal.coe_le_coe_iff.mpr (hub ⟨δ, hδ, rfl⟩)
  · rw [← hv]
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ U) => ((perturbedResidual a δ b x : ℝ) : EReal))
      δ0 hδ0 le_rfl

end F92Help

open RobustRegLasso.Coupled in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (N : Seminorm ℝ (Fin m → ℝ))
    (hN : ∀ z, N z = 0 → z = 0) (hAbs : IsAbsolute N) (l : ℝ) (hl : 0 ≤ l) :
    (∀ x : Fin m → ℝ,
      IsGreatest (residualValues a b (normBudgetSet N l) x)
        (‖b - matVec a x‖ + l * dualNorm N x)) ∧
    {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        robustObjective a b (normBudgetSet N l) x ≤ robustObjective a b (normBudgetSet N l) x'} =
      {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        ‖b - matVec a x‖ + l * dualNorm N x ≤ ‖b - matVec a x'‖ + l * dualNorm N x'} := by
  have h1 : ∀ x : Fin m → ℝ, IsGreatest (residualValues a b (normBudgetSet N l) x)
      (‖b - matVec a x‖ + l * dualNorm N x) :=
    fun x => F92Help.part1 a b N hN hAbs l hl x
  refine ⟨h1, ?_⟩
  have hr : ∀ x : Fin m → ℝ, robustObjective a b (normBudgetSet N l) x
      = ((‖b - matVec a x‖ + l * dualNorm N x : ℝ) : EReal) :=
    fun x => F92Help.robust_eq a b _ x _ (h1 x)
  ext x
  simp only [Set.mem_setOf_eq, hr, EReal.coe_le_coe_iff]
