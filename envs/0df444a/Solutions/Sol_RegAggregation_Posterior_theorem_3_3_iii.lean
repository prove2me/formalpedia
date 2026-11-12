-- Prove2me | solution 1 for RegAggregation.Posterior.theorem_3_3_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:33:59.395286+00:00
-- url     : https://prove2.me/submissions/6fb093b4-a3c8-4ed2-a049-c9f7e5a25289

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

open Matrix

namespace RegAggMatAux

/-- all-ones matrix -/
noncomputable def J (K : ℕ) : Matrix (Fin K) (Fin K) ℝ := Matrix.of (fun _ _ => (1 : ℝ))

lemma J_mul_J (K : ℕ) : J K * J K = (K : ℝ) • J K := by
  ext i j
  simp [J, Matrix.mul_apply]

lemma cs_mul (K : ℕ) (A B C D : ℝ) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K) * (C • 1 + D • J K) =
      (A * C) • (1 : Matrix (Fin K) (Fin K) ℝ) + (A * D + B * C + B * D * K) • J K := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, J_mul_J, smul_smul, add_smul]
  abel_nf
  module

lemma cs_inv (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hAB : A + K * B ≠ 0) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K)⁻¹ =
      (1 / A) • (1 : Matrix (Fin K) (Fin K) ℝ) + (-(B / (A * (A + K * B)))) • J K := by
  apply Matrix.inv_eq_right_inv
  rw [cs_mul]
  have h1 : A * (1 / A) = 1 := by field_simp
  have h2 : A * -(B / (A * (A + K * B))) + B * (1 / A) +
      B * -(B / (A * (A + K * B))) * K = 0 := by
    have hX : (A + K * B) * (A + K * B)⁻¹ = 1 := mul_inv_cancel₀ hAB
    have hY : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    linear_combination (-B * A⁻¹) * hX
  rw [h1, h2]
  simp

lemma J_eq (K : ℕ) : J K = replicateCol (Fin 1) (fun _ : Fin K => (1 : ℝ)) *
    replicateRow (Fin 1) (fun _ : Fin K => (1 : ℝ)) := by
  ext i j
  simp [J, Matrix.mul_apply]

lemma cs_det (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hK : 1 ≤ K) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K).det = A ^ (K - 1) * (A + K * B) := by
  have : A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K =
      A • (1 + replicateCol (Fin 1) (fun _ : Fin K => B / A) *
        replicateRow (Fin 1) (fun _ : Fin K => (1 : ℝ))) := by
    rw [smul_add, J_eq]
    congr 1
    ext i j
    simp [Matrix.mul_apply]
    field_simp
  rw [this, Matrix.det_smul]
  erw [det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cs_quad (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hAB : A + K * B ≠ 0) (v : Fin K → ℝ) :
    v ⬝ᵥ ((A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K)⁻¹ *ᵥ v) =
      (∑ k, v k ^ 2) / A - B / (A * (A + K * B)) * (∑ k, v k) ^ 2 := by
  rw [cs_inv K A B hA hAB]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  have hJ : J K *ᵥ v = fun _ => ∑ k, v k := by
    ext i; simp [J, Matrix.mulVec, dotProduct]
  rw [hJ]
  have e : v ⬝ᵥ (fun _ => ∑ k, v k) = (∑ k, v k) ^ 2 := by
    simp only [dotProduct, ← Finset.sum_mul, sq]
  have e' : v ⬝ᵥ v = ∑ k, v k ^ 2 := by simp [dotProduct, sq]
  rw [e, e']
  ring

end RegAggMatAux

namespace RegAggregation.Posterior
open RegAggMatAux

lemma pk_facts (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    0 < θ 1 ∧ θ 1 < 1 ∧ 0 ≤ θ 2 ∧ θ 2 < θ 1 ∧ θ 1 ≤ θ 0 ∧
      (K : ℝ) * θ 1 ^ 2 - θ 1 ≤ ((K : ℝ) - 1) * θ 2 := by
  obtain ⟨h1, h2, h3⟩ := hθ
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hK1' : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have h0 : 0 ≤ θ 2 := le_trans (le_max_left _ _) h1
  have hq : ((K : ℝ) * θ 1 ^ 2 - θ 1) / ((K : ℝ) - 1) ≤ θ 2 := le_trans (le_max_right _ _) h1
  have hq' : (K : ℝ) * θ 1 ^ 2 - θ 1 ≤ ((K : ℝ) - 1) * θ 2 := by
    rw [div_le_iff₀ hK1'] at hq; linarith
  have hg : 0 < θ 1 := lt_of_le_of_lt h0 h2
  refine ⟨hg, ?_, h0, h2, h3, hq'⟩
  by_contra hc
  have := mul_pos hK1' (sub_pos.2 h2)
  have hc' : 1 ≤ θ 1 := not_lt.mp hc
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ K) hg.le) (sub_nonneg.2 hc')]

lemma Lam_eq (K : ℕ) (θ : Fin 3 → ℝ) :
    Lam K θ = ((θ 0 - θ 2) / (1 - θ 1)) • (1 : Matrix (Fin K) (Fin K) ℝ) +
      (θ 2 / (1 - θ 1)) • J K := by
  rw [Lam, smul_add, smul_smul, smul_smul]
  simp only [div_eq_inv_mul]
  rfl

lemma eta1_eq (K : ℕ) (θ : Fin 3 → ℝ) :
    eta1 K θ = (θ 0 - θ 2) / (1 - θ 1) + K * (θ 2 / (1 - θ 1)) := by
  rw [eta1]; ring

theorem det_Lam' (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    (Lam K θ).det = eta1 K θ * eta2 θ ^ (K - 1) := by
  obtain ⟨_, hg1, _, hrg, hgd, _⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hA : (θ 0 - θ 2) / (1 - θ 1) ≠ 0 := (div_pos (by linarith) hs).ne'
  rw [Lam_eq, cs_det K _ _ hA (by omega), eta1_eq, eta2]
  ring

theorem quadratic_form' (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    (fun k => P k - μ0 / Real.sqrt (1 - θ 1)) ⬝ᵥ
        ((Lam K θ)⁻¹ *ᵥ (fun k => P k - μ0 / Real.sqrt (1 - θ 1))) =
      (K : ℝ) * (SP P / eta2 θ + (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ) := by
  obtain ⟨_, hg1, h20, hrg, hgd, _⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hApos : 0 < (θ 0 - θ 2) / (1 - θ 1) := div_pos (by linarith) hs
  have hBnn : 0 ≤ θ 2 / (1 - θ 1) := div_nonneg h20 hs.le
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hAB : 0 < (θ 0 - θ 2) / (1 - θ 1) + K * (θ 2 / (1 - θ 1)) := by positivity
  rw [Lam_eq, cs_quad K _ _ hApos.ne' hAB.ne', eta1_eq, ← eta2]
  set A := eta2 θ
  set B := θ 2 / (1 - θ 1)
  set m := μ0 / Real.sqrt (1 - θ 1)
  have hA : A ≠ 0 := hApos.ne'
  have hAB' : A + K * B ≠ 0 := hAB.ne'
  have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
  simp only [SP, Pbar]
  have e1 : ∑ k, (P k - m) ^ 2 = ∑ k, P k ^ 2 - 2 * m * ∑ k, P k + K * m ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro k _; ring
  have e2 : ∑ k, (P k - m) = ∑ k, P k - K * m := by
    simp [Finset.sum_sub_distrib]
  rw [e1, e2]
  field_simp
  ring

end RegAggregation.Posterior


open MeasureTheory Set Filter Topology

namespace RegAggAnAux

lemma key (u κ p : ℝ) (hu : 0 < u) (hκ : 0 < κ) (hp : 0 < p) :
    u ^ p * Real.exp (-(κ * u)) ≤ (p / κ) ^ p := by
  set y := κ * u / p with hy
  have hy0 : 0 < y := by positivity
  have h1 : y ≤ Real.exp (y - 1) := by linarith [Real.add_one_le_exp (y - 1)]
  have h2 : y ^ p ≤ Real.exp (y - 1) ^ p := Real.rpow_le_rpow hy0.le h1 hp.le
  rw [← Real.exp_mul] at h2
  have hu' : u = (p / κ) * y := by rw [hy]; field_simp
  have h3 : Real.exp ((y - 1) * p) ≤ Real.exp (κ * u) := by
    apply Real.exp_le_exp.mpr
    have : (y - 1) * p = κ * u - p := by rw [hy]; field_simp
    rw [this]; linarith
  calc u ^ p * Real.exp (-(κ * u)) = (p / κ) ^ p * y ^ p * Real.exp (-(κ * u)) := by
        rw [← Real.mul_rpow (by positivity) hy0.le, ← hu']
    _ ≤ (p / κ) ^ p * Real.exp (κ * u) * Real.exp (-(κ * u)) := by
        gcongr; exact h2.trans h3
    _ = (p / κ) ^ p := by rw [mul_assoc, ← Real.exp_add]; simp

lemma g_le (x c β : ℝ) (hx : 0 < x) (hc : 0 < c) (hβ : 0 < β) :
    x ^ (-β) * Real.exp (-c / x) ≤ (β / c) ^ β := by
  have := key (1 / x) c β (by positivity) hc hβ
  rw [Real.rpow_neg hx.le, ← Real.inv_rpow hx.le]
  convert this using 3
  · simp
  · ring

/-- integral of the η₂-factor in δ for fixed s. -/
lemma inner_bound (s c β : ℝ) (hs : 0 < s) (hc : 0 < c) (hβ : 1 < β) :
    ∫⁻ t, (Ioi (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal ((t / s) ^ (-β) * Real.exp (-c / (t / s)))) t ≤
      ENNReal.ofReal (s * ((β / c) ^ β + 1 / (β - 1))) := by
  set A := (β / c) ^ β
  have hpt : ∀ t, (Ioi (0 : ℝ)).indicator
        (fun t => ENNReal.ofReal ((t / s) ^ (-β) * Real.exp (-c / (t / s)))) t ≤
      (Ioc 0 s).indicator (fun _ => ENNReal.ofReal A) t +
        (Ioi s).indicator (fun t => ENNReal.ofReal (s ^ β * t ^ (-β))) t := by
    intro t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht)]
      by_cases hts : t ≤ s
      · rw [indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht, hts⟩),
          indicator_of_notMem (show t ∉ Ioi s from fun h => absurd h (not_lt.mpr hts)), add_zero]
        exact ENNReal.ofReal_le_ofReal (g_le _ c β (by positivity) hc (by linarith))
      · push_neg at hts
        rw [indicator_of_notMem (show t ∉ Ioc 0 s from fun h => absurd h.2 (not_le.mpr hts)),
          indicator_of_mem (show t ∈ Ioi s from hts), zero_add]
        apply ENNReal.ofReal_le_ofReal
        have e : (t / s) ^ (-β) = s ^ β * t ^ (-β) := by
          rw [Real.div_rpow ht.le hs.le, Real.rpow_neg hs.le, div_eq_mul_inv, inv_inv, mul_comm]
        rw [e]
        have : Real.exp (-c / (t / s)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 < t / s := by positivity
          have : 0 ≤ c / (t / s) := by positivity
          rw [neg_div]; linarith
        have hnn : 0 ≤ s ^ β * t ^ (-β) := by positivity
        nlinarith
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht)]
      exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc),
    lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc,
    lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun t : ℝ => s ^ β * t ^ (-β)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hs).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hs]
    have e : s ^ β * (-s ^ (-β + 1) / (-β + 1)) = s / (β - 1) := by
      have : s ^ β * s ^ (-β + 1) = s := by
        rw [← Real.rpow_add hs]; simp
      have hb : -β + 1 ≠ 0 := by linarith
      have hb' : β - 1 ≠ 0 := by linarith
      rw [show -s ^ (-β + 1) / (-β + 1) = s ^ (-β + 1) / (β - 1) by
        field_simp; ring]
      rw [← mul_div_assoc, this]
    rw [e, sub_zero, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by have : 0 < β - 1 := by linarith
          positivity)]
    apply le_of_eq; congr 1; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : (0:ℝ) < t := lt_trans hs ht
    positivity

end RegAggAnAux

namespace RegAggregation.Posterior
open RegAggAnAux RegAggMatAux

lemma F_eq (K : ℕ) (hK : 2 ≤ K) (μ0 a b : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    lik K μ0 θ P * prior K a b θ =
      (Real.sqrt ((2 * Real.pi) ^ K))⁻¹ *
        (eta1 K θ ^ (-(a + 1)) *
          Real.exp (-((K : ℝ) * (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / 2) / eta1 K θ)) *
        (eta2 θ ^ (-(b + (K : ℝ) / 2)) * Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ)) *
        (1 - θ 1) ^ (-(a + 5 / 2)) := by
  obtain ⟨hg0, hg1, h20, hrg, hgd, _⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have he2 : 0 < eta2 θ := div_pos (by linarith) hs
  have he1 : 0 < eta1 K θ := by
    rw [eta1_eq]
    have hA : 0 < (θ 0 - θ 2) / (1 - θ 1) := div_pos (by linarith) hs
    have := mul_nonneg hKpos.le (div_nonneg h20 hs.le); linarith
  unfold lik DKFAsymptotics.gaussianPDF prior
  have hv : (P - fun _ => μ0 / Real.sqrt (1 - θ 1)) =
      fun k => P k - μ0 / Real.sqrt (1 - θ 1) := rfl
  rw [hv, quadratic_form' K hK μ0 θ hθ P, det_Lam' K hK θ hθ]
  have hs1 : Real.sqrt ((2 * Real.pi) ^ K * (eta1 K θ * eta2 θ ^ (K - 1))) =
      Real.sqrt ((2 * Real.pi) ^ K) *
        (eta1 K θ ^ (1 / 2 : ℝ) * eta2 θ ^ (((K : ℝ) - 1) / 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul he1.le, Real.sqrt_eq_rpow (eta1 K θ),
      Real.sqrt_eq_rpow (eta2 θ ^ (K - 1)), ← Real.rpow_natCast (eta2 θ) (K - 1),
      ← Real.rpow_mul he2.le]
    congr 3
    push_cast [Nat.cast_sub (show 1 ≤ K by omega)]
    ring
  have e1 : (eta1 K θ ^ (1 / 2 : ℝ))⁻¹ * eta1 K θ ^ (-(a + 1 / 2)) = eta1 K θ ^ (-(a + 1)) := by
    rw [← Real.rpow_neg he1.le, ← Real.rpow_add he1]; ring_nf
  have e2 : (eta2 θ ^ (((K : ℝ) - 1) / 2))⁻¹ * eta2 θ ^ (-(b + 1 / 2)) =
      eta2 θ ^ (-(b + (K : ℝ) / 2)) := by
    rw [← Real.rpow_neg he2.le, ← Real.rpow_add he2]; ring_nf
  have e3 : Real.exp (-((K : ℝ) * (SP P / eta2 θ +
        (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ)) / 2) =
      Real.exp (-((K : ℝ) * (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / 2) / eta1 K θ) *
        Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hs1, e3, mul_inv, mul_inv, ← e1, ← e2]
  ring

lemma eta1_ge (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    (K : ℝ) * θ 1 ^ 2 / (1 - θ 1) ≤ eta1 K θ := by
  obtain ⟨hg0, hg1, h20, hrg, hgd, hq⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  rw [eta1]
  apply div_le_div_of_nonneg_right _ hs.le
  linarith

lemma eta1_part (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) (a : ℝ) (ha : 0 < a)
    (d γ0 d0 : ℝ) (hd : 0 ≤ d) (hγ0 : 0 < γ0) (hγ01 : γ0 < 1) (hd0 : 0 < d0)
    (hcase : θ 1 ≤ γ0 → d0 ≤ d) :
    eta1 K θ ^ (-(a + 1)) * Real.exp (-d / eta1 K θ) ≤
      (((a + 1) / d0) ^ (a + 1) / (1 - γ0) ^ (a + 1) + ((K : ℝ) * γ0 ^ 2) ^ (-(a + 1))) *
        (1 - θ 1) ^ (a + 1) := by
  obtain ⟨hg0, hg1, h20, hrg, hgd, hq⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have he1 : 0 < eta1 K θ := by
    rw [eta1_eq]
    have hA : 0 < (θ 0 - θ 2) / (1 - θ 1) := div_pos (by linarith) hs
    have := mul_nonneg hKpos.le (div_nonneg h20 hs.le); linarith
  have h1g : 0 < 1 - γ0 := by linarith
  have hT1 : 0 ≤ ((a + 1) / d0) ^ (a + 1) / (1 - γ0) ^ (a + 1) :=
    div_nonneg (Real.rpow_nonneg (div_nonneg (by linarith) hd0.le) _)
      (Real.rpow_nonneg h1g.le _)
  have hT2 : 0 ≤ ((K : ℝ) * γ0 ^ 2) ^ (-(a + 1)) := by positivity
  have hsp : 0 < (1 - θ 1) ^ (a + 1) := Real.rpow_pos_of_pos hs _
  by_cases hc : θ 1 ≤ γ0
  · have hdd := hcase hc
    have step1 : eta1 K θ ^ (-(a + 1)) * Real.exp (-d / eta1 K θ) ≤
        eta1 K θ ^ (-(a + 1)) * Real.exp (-d0 / eta1 K θ) := by
      gcongr
    have step2 := g_le (eta1 K θ) d0 (a + 1) he1 hd0 (by linarith)
    have step3 : ((a + 1) / d0) ^ (a + 1) ≤
        ((a + 1) / d0) ^ (a + 1) / (1 - γ0) ^ (a + 1) * (1 - θ 1) ^ (a + 1) := by
      have : (1 - γ0) ^ (a + 1) ≤ (1 - θ 1) ^ (a + 1) :=
        Real.rpow_le_rpow h1g.le (by linarith) (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos h1g _)]
      gcongr
    calc _ ≤ _ := step1
      _ ≤ _ := step2
      _ ≤ _ := step3
      _ ≤ _ := by nlinarith
  · push_neg at hc
    have hexp : Real.exp (-d / eta1 K θ) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]; have := div_nonneg hd he1.le; linarith
    have hlow : (K : ℝ) * γ0 ^ 2 / (1 - θ 1) ≤ eta1 K θ := by
      refine le_trans ?_ (eta1_ge K hK θ hθ)
      gcongr
    have hpow : eta1 K θ ^ (-(a + 1)) ≤ ((K : ℝ) * γ0 ^ 2 / (1 - θ 1)) ^ (-(a + 1)) :=
      Real.rpow_le_rpow_of_nonpos (div_pos (by positivity) hs) hlow (by linarith)
    have heq : ((K : ℝ) * γ0 ^ 2 / (1 - θ 1)) ^ (-(a + 1)) =
        ((K : ℝ) * γ0 ^ 2) ^ (-(a + 1)) * (1 - θ 1) ^ (a + 1) := by
      rw [Real.div_rpow (by positivity) hs.le, Real.rpow_neg hs.le (a + 1), div_inv_eq_mul]
    have hp0 : 0 ≤ eta1 K θ ^ (-(a + 1)) := by positivity
    calc _ ≤ eta1 K θ ^ (-(a + 1)) * 1 := by gcongr
      _ ≤ ((K : ℝ) * γ0 ^ 2) ^ (-(a + 1)) * (1 - θ 1) ^ (a + 1) := by rw [mul_one, ← heq]; exact hpow
      _ ≤ _ := by nlinarith

lemma exists_gamma0 (K : ℕ) (hK : 0 < K) (μ0 Pb : ℝ) (h : Pb ≠ μ0) :
    ∃ γ0 d0 : ℝ, 0 < γ0 ∧ γ0 < 1 ∧ 0 < d0 ∧
      ∀ γ, 0 < γ → γ ≤ γ0 → d0 ≤ (K : ℝ) * (Pb - μ0 / Real.sqrt (1 - γ)) ^ 2 / 2 := by
  set f : ℝ → ℝ := fun γ => (K : ℝ) * (Pb - μ0 / Real.sqrt (1 - γ)) ^ 2 / 2 with hf
  have h1 : ContinuousAt (fun γ : ℝ => Real.sqrt (1 - γ)) 0 :=
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt
  have h2 : ContinuousAt (fun γ : ℝ => μ0 / Real.sqrt (1 - γ)) 0 :=
    continuousAt_const.div h1 (by simp)
  have h3 : ContinuousAt f 0 :=
    (continuousAt_const.mul ((continuousAt_const.sub h2).pow 2)).div_const 2
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hf0 : f 0 = (K : ℝ) * (Pb - μ0) ^ 2 / 2 := by simp [hf]
  have hpos : 0 < f 0 := by
    rw [hf0]; have : 0 < (Pb - μ0) ^ 2 := by
      have : Pb - μ0 ≠ 0 := sub_ne_zero.mpr h
      positivity
    positivity
  have hev : ∀ᶠ γ in 𝓝 (0 : ℝ), f 0 / 2 < f γ :=
    Filter.Tendsto.eventually_const_lt (by linarith) h3
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) (1 / 2), f 0 / 2, by positivity, by
    have := min_le_right (ε / 2) (1 / 2); linarith, by positivity, ?_⟩
  intro γ hγ hγ0
  have : dist γ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hγ]
    have := min_le_left (ε / 2) (1 / 2); linarith
  exact (hball this).le

lemma SP_pos {K : ℕ} (hK : 0 < K) (P : Fin K → ℝ) (hP : ∃ j k, j ≠ k ∧ P j ≠ P k) :
    0 < SP P := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have e : SP P = (∑ k, (P k - Pbar P) ^ 2) / K := by
    simp only [SP, Pbar, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
      ← Finset.mul_sum]
    field_simp
    ring
  rw [e]
  apply div_pos _ hKpos
  obtain ⟨j, k, _, hjk⟩ := hP
  have : P j - Pbar P ≠ 0 ∨ P k - Pbar P ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hjk (by linarith [hc.1, hc.2])
  rcases this with h | h
  · exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ _, by positivity⟩
  · exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨k, Finset.mem_univ _, by positivity⟩

end RegAggregation.Posterior

namespace RegAggregation.Posterior
open RegAggAnAux RegAggMatAux

lemma PK_meas (K : ℕ) : MeasurableSet (PK K) := by
  unfold PK
  simp only [setOf_and]
  refine (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop)))

/-- coordinates `θ ↦ (γ, δ, ρ)` -/
def coordE (θ : Fin 3 → ℝ) : ℝ × ℝ × ℝ := (θ 1, θ 0, θ 2)

lemma coordE_mp : MeasurePreserving coordE volume volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1
  have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)))
      (volume : Measure (ℝ × (Fin 2 → ℝ))) (volume : Measure (ℝ × ℝ × ℝ)) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  have := h2.comp h1
  have e : coordE = Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1) := by
    funext θ
    rfl
  rw [e]
  exact this

end RegAggregation.Posterior

namespace RegAggregation.Posterior
open RegAggAnAux RegAggMatAux

lemma finite_part (K : ℕ) (hK : 2 ≤ K) (μ0 a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (P : Fin K → ℝ) (hP : ∃ j k, j ≠ k ∧ P j ≠ P k) (hPbar : Pbar P ≠ μ0) :
    ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) < ⊤ := by
  have hK0 : 0 < K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨γ0, d0, hγ0, hγ01, hd0, hcase⟩ := exists_gamma0 K hK0 μ0 (Pbar P) hPbar
  set M := ((a + 1) / d0) ^ (a + 1) / (1 - γ0) ^ (a + 1) + ((K : ℝ) * γ0 ^ 2) ^ (-(a + 1))
    with hM
  have h1g : 0 < 1 - γ0 := by linarith
  have hM0 : 0 ≤ M := add_nonneg (div_nonneg (Real.rpow_nonneg (div_nonneg (by linarith)
      hd0.le) _) (Real.rpow_nonneg h1g.le _)) (Real.rpow_nonneg (by positivity) _)
  set C := (Real.sqrt ((2 * Real.pi) ^ K))⁻¹ * M with hC
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) hM0
  set c := (K : ℝ) * SP P / 2 with hc
  have hc0 : 0 < c := by have := SP_pos hK0 P hP; positivity
  set β := b + (K : ℝ) / 2 with hβ
  have hβ1 : 1 < β := by rw [hβ]; linarith
  set C2 := (β / c) ^ β + 1 / (β - 1) with hC2
  set H : ℝ × ℝ × ℝ → ENNReal := fun p =>
    if 0 < p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2.2 ∧ p.2.2 < 1 ∧ p.2.2 < p.2.1 then
      ENNReal.ofReal (C * (1 - p.1) ^ (-(3 / 2 : ℝ)) *
        (((p.2.1 - p.2.2) / (1 - p.1)) ^ (-β) * Real.exp (-c / ((p.2.1 - p.2.2) / (1 - p.1)))))
    else 0 with hH
  have hHm : Measurable H := by
    apply Measurable.ite
    · simp only [setOf_and]
      refine (measurableSet_lt (by fun_prop) (by fun_prop)).inter
        ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
        ((measurableSet_le (by fun_prop) (by fun_prop)).inter
        ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
        (measurableSet_lt (by fun_prop) (by fun_prop)))))
    · apply ENNReal.measurable_ofReal.comp
      fun_prop
    · exact measurable_const
  -- Step 1: pointwise domination on PK
  have hpt : ∀ θ ∈ PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) ≤ H (coordE θ) := by
    intro θ hθ
    obtain ⟨hg0, hg1, h20, hrg, hgd, _⟩ := pk_facts K hK θ hθ
    have hs : 0 < 1 - θ 1 := by linarith
    have hcond : 0 < θ 1 ∧ θ 1 < 1 ∧ 0 ≤ θ 2 ∧ θ 2 < 1 ∧ θ 2 < θ 0 :=
      ⟨hg0, hg1, h20, by linarith, by linarith⟩
    simp only [hH, coordE]
    rw [if_pos hcond]
    apply ENNReal.ofReal_le_ofReal
    rw [F_eq K hK μ0 a b θ hθ P]
    have he2 : 0 < eta2 θ := div_pos (by linarith) hs
    have hE1 := eta1_part K hK θ hθ a ha ((K : ℝ) * (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / 2)
      γ0 d0 (by positivity) hγ0 hγ01 hd0 (fun h => hcase (θ 1) hg0 h)
    have hG2 : 0 ≤ eta2 θ ^ (-(b + (K : ℝ) / 2)) * Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ) :=
      by positivity
    have hs3 : (1 - θ 1) ^ (a + 1) * (1 - θ 1) ^ (-(a + 5 / 2)) = (1 - θ 1) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hs]; ring_nf
    have hsr : 0 ≤ (1 - θ 1) ^ (-(a + 5 / 2)) := Real.rpow_nonneg hs.le _
    calc (Real.sqrt ((2 * Real.pi) ^ K))⁻¹ *
        (eta1 K θ ^ (-(a + 1)) *
          Real.exp (-((K : ℝ) * (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / 2) / eta1 K θ)) *
        (eta2 θ ^ (-(b + (K : ℝ) / 2)) * Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ)) *
        (1 - θ 1) ^ (-(a + 5 / 2))
        ≤ (Real.sqrt ((2 * Real.pi) ^ K))⁻¹ * (M * (1 - θ 1) ^ (a + 1)) *
        (eta2 θ ^ (-(b + (K : ℝ) / 2)) * Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ)) *
        (1 - θ 1) ^ (-(a + 5 / 2)) := by gcongr
      _ = C * ((1 - θ 1) ^ (a + 1) * (1 - θ 1) ^ (-(a + 5 / 2))) *
        (eta2 θ ^ (-(b + (K : ℝ) / 2)) * Real.exp (-((K : ℝ) * SP P / 2) / eta2 θ)) := by
          rw [hC]; ring
      _ = _ := by rw [hs3]; rfl
  -- Step 2: transfer
  have hstep2 : ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) ≤
      ∫⁻ p, H p := by
    calc _ ≤ ∫⁻ θ in PK K, H (coordE θ) := setLIntegral_mono' (PK_meas K) hpt
      _ ≤ ∫⁻ θ, H (coordE θ) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ p, H p := coordE_mp.lintegral_comp hHm
  -- Step 3: iterated integral
  have hstep3 : ∫⁻ p, H p = ∫⁻ γ, ∫⁻ ρ, ∫⁻ δ, H (γ, δ, ρ) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hHm.aemeasurable]
    apply lintegral_congr
    intro γ
    exact lintegral_prod_symm (fun q => H (γ, q)) (hHm.comp measurable_prodMk_left).aemeasurable
  -- Step 4: bound for fixed γ
  have hstep4 : ∀ γ, ∫⁻ ρ, ∫⁻ δ, H (γ, δ, ρ) ≤
      (Ioo (0 : ℝ) 1).indicator (fun γ => ENNReal.ofReal (C * C2 * (1 - γ) ^ (-(1 / 2 : ℝ)))) γ := by
    intro γ
    by_cases hγ : γ ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hγ]
      have hs : 0 < 1 - γ := by linarith [hγ.2]
      have hρ : ∀ ρ, ∫⁻ δ, H (γ, δ, ρ) ≤ (Ico (0 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal (C * C2 * (1 - γ) ^ (-(1 / 2 : ℝ)))) ρ := by
        intro ρ
        by_cases hρ : ρ ∈ Ico (0 : ℝ) 1
        · rw [indicator_of_mem hρ]
          have hfun : ∀ δ, H (γ, δ, ρ) = ENNReal.ofReal (C * (1 - γ) ^ (-(3 / 2 : ℝ))) *
              (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal
                ((t / (1 - γ)) ^ (-β) * Real.exp (-c / (t / (1 - γ))))) (δ - ρ) := by
            intro δ
            by_cases hδ : ρ < δ
            · simp only [hH]
              rw [if_pos ⟨hγ.1, hγ.2, hρ.1, hρ.2, hδ⟩,
                indicator_of_mem (show δ - ρ ∈ Ioi 0 from sub_pos.mpr hδ),
                ← ENNReal.ofReal_mul (mul_nonneg hC0 (Real.rpow_nonneg hs.le _))]
            · simp only [hH]
              rw [if_neg (fun h => hδ h.2.2.2.2),
                indicator_of_notMem (show δ - ρ ∉ Ioi 0 from fun h => hδ (sub_pos.mp h)),
                mul_zero]
          simp_rw [hfun]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun t => (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal
                ((t / (1 - γ)) ^ (-β) * Real.exp (-c / (t / (1 - γ))))) t) ρ]
          refine (mul_le_mul' le_rfl (inner_bound (1 - γ) c β hs hc0 hβ1)).trans ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg hC0 (Real.rpow_nonneg hs.le _))]
          apply le_of_eq
          congr 1
          have : (1 - γ) ^ (-(3 / 2 : ℝ)) * (1 - γ) = (1 - γ) ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_add_one hs.ne']; norm_num
          rw [← this]; ring
        · rw [indicator_of_notMem hρ]
          have h0 : ∀ δ, H (γ, δ, ρ) = 0 := fun δ => by
            simp only [hH]; rw [if_neg (fun h => hρ ⟨h.2.2.1, h.2.2.2.1⟩)]
          simp [h0]
      refine (lintegral_mono hρ).trans ?_
      rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_zero,
        ENNReal.ofReal_one, mul_one]
    · rw [indicator_of_notMem hγ]
      have h0 : ∀ δ ρ, H (γ, δ, ρ) = 0 := fun δ ρ => by
        simp only [hH]; rw [if_neg (fun h => hγ ⟨h.1, h.2.1⟩)]
      simp [h0]
  -- Step 5
  have hI : IntegrableOn (fun γ : ℝ => C * C2 * (1 - γ) ^ (-(1 / 2 : ℝ))) (Ioo 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (a := 1) (b := 0)
      (by norm_num)).comp_sub_left 1
    rw [sub_self, sub_zero] at h
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h).const_mul _
  calc _ ≤ ∫⁻ p, H p := hstep2
    _ = ∫⁻ γ, ∫⁻ ρ, ∫⁻ δ, H (γ, δ, ρ) := hstep3
    _ ≤ ∫⁻ γ, (Ioo (0 : ℝ) 1).indicator
          (fun γ => ENNReal.ofReal (C * C2 * (1 - γ) ^ (-(1 / 2 : ℝ)))) γ := lintegral_mono hstep4
    _ = ∫⁻ γ in Ioo (0 : ℝ) 1, ENNReal.ofReal (C * C2 * (1 - γ) ^ (-(1 / 2 : ℝ))) :=
          lintegral_indicator measurableSet_Ioo _
    _ < ⊤ := hI.lintegral_lt_top

end RegAggregation.Posterior

namespace RegAggregation.Posterior
open RegAggAnAux RegAggMatAux

/-- explicit closed form of likelihood × prior. -/
noncomputable def Eform (K : ℕ) (μ0 a b : ℝ) (P : Fin K → ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ K))⁻¹ *
    (((θ 0 + ((K : ℝ) - 1) * θ 2) / (1 - θ 1)) ^ (-(a + 1)) *
      Real.exp (-((K : ℝ) * (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / 2) /
        ((θ 0 + ((K : ℝ) - 1) * θ 2) / (1 - θ 1)))) *
    (((θ 0 - θ 2) / (1 - θ 1)) ^ (-(b + (K : ℝ) / 2)) *
      Real.exp (-((K : ℝ) * SP P / 2) / ((θ 0 - θ 2) / (1 - θ 1)))) *
    (1 - θ 1) ^ (-(a + 5 / 2))

lemma Eform_meas (K : ℕ) (μ0 a b : ℝ) (P : Fin K → ℝ) : Measurable (Eform K μ0 a b P) := by
  unfold Eform
  fun_prop

lemma PK_vol_pos (K : ℕ) (hK : 2 ≤ K) : 0 < volume (PK K) := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hbox : (Set.pi univ fun i : Fin 3 =>
      Ioo (![99 / 100, 49 / 100, 73 / 200] i) (![101 / 100, 51 / 100, 77 / 200] i)) ⊆ PK K := by
    intro θ hθ
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Ioo] at hθ
    have h0 := hθ 0
    have h1 := hθ 1
    have h2 := hθ 2
    simp at h0 h1 h2
    refine ⟨max_le (by linarith) ?_, by linarith, by linarith⟩
    rw [div_le_iff₀ (by linarith)]
    have hsq : θ 1 ^ 2 ≤ 2601 / 10000 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ K)]
  refine lt_of_lt_of_le ?_ (measure_mono hbox)
  rw [Real.volume_pi_Ioo, Fin.prod_univ_three]
  simp
  norm_num

lemma pos_part (K : ℕ) (hK : 2 ≤ K) (μ0 a b : ℝ) (P : Fin K → ℝ) :
    0 < ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) := by
  have hEq : ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) =
      ∫⁻ θ in PK K, ENNReal.ofReal (Eform K μ0 a b P θ) := by
    apply setLIntegral_congr_fun (PK_meas K)
    intro θ hθ
    dsimp only
    rw [F_eq K hK μ0 a b θ hθ P]
    rfl
  have hpos : ∀ θ ∈ PK K, 0 < Eform K μ0 a b P θ := by
    intro θ hθ
    obtain ⟨hg0, hg1, h20, hrg, hgd, _⟩ := pk_facts K hK θ hθ
    have hs : 0 < 1 - θ 1 := by linarith
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have he1 : 0 < (θ 0 + ((K : ℝ) - 1) * θ 2) / (1 - θ 1) := by
      apply div_pos _ hs
      have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
      have : (0 : ℝ) ≤ ((K : ℝ) - 1) * θ 2 := mul_nonneg (by linarith) h20
      linarith
    have he2 : 0 < (θ 0 - θ 2) / (1 - θ 1) := div_pos (by linarith) hs
    unfold Eform
    have := Real.rpow_pos_of_pos he1 (-(a + 1))
    have := Real.rpow_pos_of_pos he2 (-(b + (K : ℝ) / 2))
    have := Real.rpow_pos_of_pos hs (-(a + 5 / 2))
    positivity
  rw [hEq]
  apply pos_iff_ne_zero.mpr
  intro h0
  replace h0 := (lintegral_eq_zero_iff (f := fun θ => ENNReal.ofReal (Eform K μ0 a b P θ))
    (ENNReal.measurable_ofReal.comp (Eform_meas K μ0 a b P))).mp h0
  have h1 : ∀ᵐ θ ∂volume, θ ∈ PK K → ENNReal.ofReal (Eform K μ0 a b P θ) = 0 :=
    (ae_restrict_iff' (PK_meas K)).mp h0
  have h2 : ∀ᵐ θ ∂volume, θ ∉ PK K := by
    filter_upwards [h1] with θ hθ hmem
    have := hθ hmem
    rw [ENNReal.ofReal_eq_zero] at this
    exact absurd (hpos θ hmem) (not_lt.mpr this)
  have h3 : volume (PK K) = 0 := by
    rw [← ae_iff.mp h2]
    congr 1
    ext θ; simp
  exact absurd h3 (PK_vol_pos K hK).ne'

end RegAggregation.Posterior

open RegAggregation.Posterior in
theorem solution (K : ℕ) (hK : 2 ≤ K) (μ0 a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (P : Fin K → ℝ) (hP : ∃ j k, j ≠ k ∧ P j ≠ P k) (hPbar : Pbar P ≠ μ0) :
    0 < ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) ∧
    ∫⁻ θ in PK K, ENNReal.ofReal (lik K μ0 θ P * prior K a b θ) < ⊤ :=
  ⟨pos_part K hK μ0 a b P, finite_part K hK μ0 a b ha hb P hP hPbar⟩
