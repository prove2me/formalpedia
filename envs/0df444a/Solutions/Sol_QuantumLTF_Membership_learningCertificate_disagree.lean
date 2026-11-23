-- Prove2me | solution 1 for QuantumLTF.Membership.learningCertificate_disagree
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:50:50.905127+00:00
-- url     : https://prove2.me/submissions/01138018-1551-430c-b594-001a7be6e3a8

import Mathlib
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1
import Theorems.Thm_QuantumLTF_Membership_lemma_3_2
import Definitions.Def_QuantumLTF_Membership_LearningCertificate

set_option maxHeartbeats 1000000

namespace QuantumLTF.Membership

private theorem ltf_inv_smul {n : ℕ} (a x : EuclideanSpace ℝ (Fin n)) (b t : ℝ)
    (ht : 0 < t) : ltf (t⁻¹ • a) (t⁻¹ * b) x = ltf a b x := by
  simp only [ltf, inner_smul_left, starRingEnd_apply, star_trivial]
  unfold sgn
  rw [show t⁻¹ * inner ℝ a x - t⁻¹ * b = t⁻¹ * (inner ℝ a x - b) by ring]
  have ht' : 0 < t⁻¹ := inv_pos.mpr ht
  by_cases h : 0 ≤ inner ℝ a x - b
  · rw [if_pos h, if_pos (mul_nonneg ht'.le h)]
  · rw [if_neg h, if_neg]
    exact not_le.mpr (mul_neg_of_pos_of_neg ht' (not_le.mp h))

end QuantumLTF.Membership

open QuantumLTF.Membership

theorem solution {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ : ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (b : ℝ) (cert : LearningCertificate ε w θ a b) :
    disagree (ltf a b) (ltf w θ) ≤ ε := by
  rcases cert with ce | cg
  · have heq : ltf a b = fun _ => ltf w θ 0 := funext ce.1
    rw [heq]
    have hset : {x | (fun _ => ltf w θ 0) x ≠ ltf w θ x} =
        {x | ltf w θ x ≠ (fun _ => ltf w θ 0) x} := by
      ext x
      exact ne_comm
    unfold disagree
    rw [hset]
    exact lemma_3_2 hn w hw θ ε hε (hε2.trans_lt (by norm_num)) ce.2
  · obtain ⟨s, h, ht, g, gt, hs, hL, hglo, hghi, hwg, hθ, hht, hh, hgt, ha, hb⟩ := cg
    have hsR : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hgpos : 0 < ‖g‖ := lt_of_lt_of_le (by norm_num) hglo
    have hgne : ‖g‖ ≠ 0 := ne_of_gt hgpos
    let Δ : ℝ := ε / (100 * (Leps ε + 1))
    have hL0 : 0 ≤ Leps ε := le_trans (by norm_num) hL
    have hΔpos : 0 < Δ := by
      dsimp [Δ]
      positivity
    have hΔbound : Δ ≤ 1 / 400 := by
      dsimp [Δ]
      have hd : 200 ≤ 100 * (Leps ε + 1) := by linarith
      calc
        ε / (100 * (Leps ε + 1)) ≤ ε / 200 := by
          exact div_le_div_of_nonneg_left hε.le (by norm_num) hd
        _ ≤ 1 / 400 := by linarith
    have hnormdiff : |‖gt‖ - ‖g‖| ≤ Δ :=
      (abs_norm_sub_norm_le gt g).trans hgt
    have hgtpos : 1 / 4 < ‖gt‖ := by
      have hlo : ‖gt‖ ≥ ‖g‖ - Δ := by
        have := neg_le_of_abs_le hnormdiff
        linarith
      linarith
    have hgtne : ‖gt‖ ≠ 0 := by linarith
    let U : EuclideanSpace ℝ (Fin n) := ‖g‖⁻¹ • g
    let V : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt
    have hUnorm : ‖U‖ = 1 := by
      dsimp [U]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgne]
    have hVnorm : ‖V‖ = 1 := by
      dsimp [V]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgtne]
    have hwU : w = -(s : ℝ) • U := by
      simpa [U] using hwg
    have hVrel : V = (‖g‖ / ‖gt‖) • U + ‖gt‖⁻¹ • (gt - g) := by
      dsimp [V, U]
      calc
        ‖gt‖⁻¹ • gt = ‖gt‖⁻¹ • (g + (gt - g)) := by rw [show g + (gt - g) = gt by abel]
        _ = ‖gt‖⁻¹ • g + ‖gt‖⁻¹ • (gt - g) := by rw [smul_add]
        _ = (‖g‖ / ‖gt‖) • (‖g‖⁻¹ • g) + ‖gt‖⁻¹ • (gt - g) := by
          rw [smul_smul]
          congr 1
          field_simp
    have hVsub : V - U = ((‖g‖ - ‖gt‖) / ‖gt‖) • U + ‖gt‖⁻¹ • (gt - g) := by
      rw [hVrel]
      have hsc : ‖g‖ / ‖gt‖ = (‖g‖ - ‖gt‖) / ‖gt‖ + 1 := by
        field_simp
        ring
      rw [hsc, add_smul, one_smul]
      abel
    have hnormUle : ‖V - U‖ ≤ (|‖g‖ - ‖gt‖| + Δ) / ‖gt‖ := by
      rw [hVsub]
      have hterm1 : ‖((‖g‖ - ‖gt‖) / ‖gt‖) • U‖ = |‖g‖ - ‖gt‖| / ‖gt‖ := by
        rw [norm_smul, Real.norm_eq_abs, hUnorm, mul_one,
          abs_div, abs_of_pos (by linarith : 0 < ‖gt‖)]
      have hterm2 : ‖‖gt‖⁻¹ • (gt - g)‖ = ‖gt‖⁻¹ * ‖gt - g‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ‖gt‖⁻¹)]
      calc
        ‖((‖g‖ - ‖gt‖) / ‖gt‖) • U + ‖gt‖⁻¹ • (gt - g)‖
            ≤ ‖((‖g‖ - ‖gt‖) / ‖gt‖) • U‖ + ‖‖gt‖⁻¹ • (gt - g)‖ :=
          norm_add_le (((‖g‖ - ‖gt‖) / ‖gt‖) • U) (‖gt‖⁻¹ • (gt - g))
        _ = (|‖g‖ - ‖gt‖| / ‖gt‖) + ‖gt‖⁻¹ * ‖gt - g‖ := by rw [hterm1, hterm2]
        _ ≤ (|‖g‖ - ‖gt‖| / ‖gt‖) + ‖gt‖⁻¹ * Δ := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hgt (inv_nonneg.mpr (norm_nonneg gt))) _
        _ = (|‖g‖ - ‖gt‖| + Δ) / ‖gt‖ := by field_simp
    let wh : EuclideanSpace ℝ (Fin n) := -(s : ℝ) • V
    let th : ℝ := (s : ℝ) * ht / ‖gt‖
    have hwhnorm : ‖wh‖ = 1 := by
      dsimp [wh]
      rw [norm_smul, hVnorm, mul_one]
      rcases hsR with h | h <;> rw [h] <;> norm_num
    have hwhdiff : ‖wh - w‖ = ‖V - U‖ := by
      dsimp [wh]
      rw [hwU, ← smul_sub, norm_smul]
      have hsnorm : ‖(-(s : ℝ))‖ = 1 := by
        rcases hsR with h | h <;> rw [h] <;> norm_num
      rw [hsnorm, one_mul]
    have hwhbound : ‖wh - w‖ ≤ 8 * Δ := by
      rw [hwhdiff]
      have hd : |‖g‖ - ‖gt‖| + Δ ≤ 2 * Δ := by
        rw [abs_sub_comm]
        linarith [hnormdiff]
      calc
        ‖V - U‖ ≤ (|‖g‖ - ‖gt‖| + Δ) / ‖gt‖ := hnormUle
        _ ≤ (2 * Δ) / ‖gt‖ := by gcongr
        _ ≤ (2 * Δ) / (1 / 4 : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (le_of_lt hgtpos)
        _ = 8 * Δ := by ring
    have hthsplit : th - θ = ((s : ℝ) / ‖gt‖) * (ht - h) +
        ((s : ℝ) * h / ‖gt‖) * (1 - ‖gt‖ / ‖g‖) := by
      dsimp [th]
      rw [hθ]
      field_simp
      ring
    have hthbound : |th - θ| ≤ 4 * (ε / 100) + 12 * Leps ε * Δ := by
      have hfirst : |(s : ℝ) / ‖gt‖ * (ht - h)| ≤ 4 * (ε / 100) := by
        rw [abs_mul, abs_div, abs_of_pos (by linarith : 0 < ‖gt‖)]
        have hsabs : |(s : ℝ)| = 1 := by rcases hsR with h | h <;> rw [h] <;> norm_num
        rw [hsabs]
        calc
          1 / ‖gt‖ * |ht - h| ≤ 1 / ‖gt‖ * (ε / 100) := by gcongr
          _ ≤ 4 * (ε / 100) := by
            rw [div_mul_eq_mul_div, one_mul]
            apply (div_le_iff₀ (by linarith : 0 < ‖gt‖)).2
            nlinarith [hε, hgtpos]
      have hsecond : |(s : ℝ) * h / ‖gt‖ * (1 - ‖gt‖ / ‖g‖)| ≤ 12 * Leps ε * Δ := by
        have hRratio : |1 - ‖gt‖ / ‖g‖| = |‖g‖ - ‖gt‖| / ‖g‖ := by
          rw [show 1 - ‖gt‖ / ‖g‖ = (‖g‖ - ‖gt‖) / ‖g‖ by field_simp,
            abs_div, abs_of_pos hgpos]
        rw [abs_mul, abs_div, abs_mul, hRratio]
        have hsabs : |(s : ℝ)| = 1 := by rcases hsR with h | h <;> rw [h] <;> norm_num
        rw [hsabs, one_mul, abs_of_pos (by linarith : 0 < ‖gt‖)]
        calc
          |h| / ‖gt‖ * (|‖g‖ - ‖gt‖| / ‖g‖)
              ≤ Leps ε / ‖gt‖ * (Δ / ‖g‖) := by
                gcongr
                exact abs_sub_comm ‖gt‖ ‖g‖ ▸ hnormdiff
          _ ≤ Leps ε / (1 / 4 : ℝ) * (Δ / (1 / 3 : ℝ)) := by
                gcongr
          _ = 12 * Leps ε * Δ := by ring
      calc
        |th - θ| = |(s : ℝ) / ‖gt‖ * (ht - h) +
            (s : ℝ) * h / ‖gt‖ * (1 - ‖gt‖ / ‖g‖)| := by rw [← hthsplit]
        _ ≤ |(s : ℝ) / ‖gt‖ * (ht - h)| +
            |(s : ℝ) * h / ‖gt‖ * (1 - ‖gt‖ / ‖g‖)| := by
          simpa only [Real.norm_eq_abs] using
            (norm_add_le ((s : ℝ) / ‖gt‖ * (ht - h))
              ((s : ℝ) * h / ‖gt‖ * (1 - ‖gt‖ / ‖g‖)))
        _ ≤ 4 * (ε / 100) + 12 * Leps ε * Δ := add_le_add hfirst hsecond
    have hlemmas := (lemma_2_1 wh w hwhnorm hw th θ).1
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
      have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
      have hs : (1 : ℝ) ≤ 2 * Real.pi := by linarith
      simpa using Real.one_le_sqrt.mpr hs
    have hfinal : disagree (ltf wh th) (ltf w θ) ≤ ε := by
      refine hlemmas.trans ?_
      have hnorms : ‖wh - w‖ / 2 ≤ 4 * Δ := by linarith
      have hths : |th - θ| / Real.sqrt (2 * Real.pi) ≤
          4 * (ε / 100) + 12 * Leps ε * Δ := by
        calc
          |th - θ| / Real.sqrt (2 * Real.pi) ≤ |th - θ| / 1 := by gcongr
          _ = |th - θ| := div_one _
          _ ≤ 4 * (ε / 100) + 12 * Leps ε * Δ := hthbound
      dsimp [Δ] at hnorms hths ⊢
      have hmult : 0 < 100 * (Leps ε + 1) := by positivity
      have hDge : 200 ≤ 100 * (Leps ε + 1) := by linarith
      have hLratio : Leps ε / (100 * (Leps ε + 1)) ≤ 1 / 100 := by
        apply (div_le_div_iff₀ hmult (by norm_num)).2
        nlinarith
      have hterm1 : 4 * (ε / (100 * (Leps ε + 1))) ≤ ε / 25 := by
        rw [show 4 * (ε / (100 * (Leps ε + 1))) = 4 * ε / (100 * (Leps ε + 1)) by ring]
        apply (div_le_iff₀ hmult).2
        have h := mul_le_mul_of_nonneg_left hDge hε.le
        nlinarith
      have hterm2 : 12 * Leps ε * (ε / (100 * (Leps ε + 1))) ≤ 12 * ε / 100 := by
        have h := mul_le_mul_of_nonneg_left hLratio
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hε.le)
        calc
          _ = 12 * ε * (Leps ε / (100 * (Leps ε + 1))) := by ring
          _ ≤ 12 * ε * (1 / 100) := h
          _ = 12 * ε / 100 := by ring
      linarith
    have heq : ltf a b = ltf wh th := by
      funext x
      rw [ha, hb]
      dsimp [wh, th]
      have hVsmul : -(s : ℝ) • V = ‖gt‖⁻¹ • (-(s : ℝ) • gt) := by
        dsimp [V]
        rw [smul_comm]
      have hthsmul : (s : ℝ) * ht / ‖gt‖ = ‖gt‖⁻¹ * ((s : ℝ) * ht) := by
        field_simp
      rw [hVsmul, hthsmul]
      exact (QuantumLTF.Membership.ltf_inv_smul (-(s : ℝ) • gt) x ((s : ℝ) * ht) ‖gt‖ (by linarith)).symm
    rw [heq]
    exact hfinal
