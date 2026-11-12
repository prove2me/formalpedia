-- Prove2me | solution 1 for RWPI.Limit.eq_42
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:14:31.393713+00:00
-- url     : https://prove2.me/submissions/280b1e2c-3cb5-4b43-9059-7018ab08dd1b

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace SolRWPILimitEq42

private noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private lemma abs_sgn (x : ℝ) : |sgn x| = 1 := by
  unfold sgn
  split_ifs <;> simp

private lemma mul_sgn (x : ℝ) : x * sgn x = |x| := by
  unfold sgn
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]

private lemma dotProduct_le_norm_mul_norm {m : ℕ} (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (v Δ : Fin m → ℝ) :
    v ⬝ᵥ Δ ≤ ‖WithLp.toLp p v‖ * ‖WithLp.toLp q Δ‖ := by
  have : p.HolderConjugate q := hpq
  have : q.HolderConjugate p := hpq.symm
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hsum : v ⬝ᵥ Δ ≤ ∑ i : Fin m, ‖v i‖ * ‖Δ i‖ := by
    change ∑ i : Fin m, v i * Δ i ≤ ∑ i : Fin m, ‖v i‖ * ‖Δ i‖
    refine Finset.sum_le_sum fun i _ => ?_
    calc v i * Δ i ≤ |v i * Δ i| := le_abs_self _
      _ = ‖v i‖ * ‖Δ i‖ := by simp [abs_mul]
  rcases isEmpty_or_nonempty (Fin m) with hempty | hne
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact hsum.trans (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rcases eq_or_ne p 1 with rfl | hp1
  · have hqtop : q = ∞ := ENNReal.HolderConjugate.unique 1 q ∞
    subst hqtop
    rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_ciSup, Finset.sum_mul]
    refine hsum.trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left
      (le_ciSup (f := fun j : Fin m => ‖Δ j‖) (Finite.bddAbove_range _) i) (norm_nonneg _)
  rcases eq_or_ne q 1 with rfl | hq1
  · have hptop : p = ∞ := ENNReal.HolderConjugate.unique 1 p ∞
    subst hptop
    rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_of_L1, Finset.mul_sum]
    refine hsum.trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (f := fun j : Fin m => ‖v j‖) (Finite.bddAbove_range _) i) (norm_nonneg _)
  · have hp_gt : 1 < p := lt_of_le_of_ne (ENNReal.HolderConjugate.one_le p q) hp1.symm
    have hq_gt : 1 < q := lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) hq1.symm
    have hp_ne_top : p ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mpr hq_gt).ne
    have hq_ne_top : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp_gt).ne
    have hpq_real : p.toReal.HolderConjugate q.toReal :=
      ENNReal.HolderConjugate.toReal_of_ne_top hp_ne_top hq_ne_top
    have hp_pos : 0 < p.toReal := zero_lt_one.trans hpq_real.lt
    have hq_pos : 0 < q.toReal := zero_lt_one.trans hpq_real.symm.lt
    rw [PiLp.norm_eq_sum hp_pos, PiLp.norm_eq_sum hq_pos]
    exact hsum.trans (Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq_real
      (fun i _ => norm_nonneg (v i)) (fun i _ => norm_nonneg (Δ i)))

private lemma exists_norm_eq_one_dotProduct_eq {m : ℕ} (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (v : Fin m → ℝ) (hv : v ≠ 0) :
    ∃ u : Fin m → ℝ, ‖WithLp.toLp q u‖ = 1 ∧ v ⬝ᵥ u = ‖WithLp.toLp p v‖ := by
  have : p.HolderConjugate q := hpq
  have : q.HolderConjugate p := hpq.symm
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hne : Nonempty (Fin m) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    exact hv (Subsingleton.elim v 0)
  rcases eq_or_ne p 1 with rfl | hp1
  · have hqtop : q = ∞ := ENNReal.HolderConjugate.unique 1 q ∞
    subst hqtop
    refine ⟨fun i => sgn (v i), ?_, ?_⟩
    · rw [PiLp.norm_eq_ciSup]
      change ⨆ i : Fin m, ‖sgn (v i)‖ = 1
      simp_rw [Real.norm_eq_abs, abs_sgn]
      exact ciSup_const
    · rw [PiLp.norm_eq_of_L1]
      change ∑ i : Fin m, v i * sgn (v i) = ∑ i : Fin m, ‖v i‖
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_sgn, Real.norm_eq_abs]
  rcases eq_or_ne q 1 with rfl | hq1
  · have hptop : p = ∞ := ENNReal.HolderConjugate.unique 1 p ∞
    subst hptop
    obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i : Fin m => ‖v i‖)
      Finset.univ_nonempty
    refine ⟨Pi.single i₀ (sgn (v i₀)), ?_, ?_⟩
    · rw [PiLp.norm_eq_of_L1]
      change ∑ i : Fin m, ‖(Pi.single i₀ (sgn (v i₀)) : Fin m → ℝ) i‖ = 1
      rw [Finset.sum_eq_single i₀]
      · simp [Real.norm_eq_abs, abs_sgn]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
    · have hsup : ‖WithLp.toLp ∞ v‖ = ‖v i₀‖ := by
        rw [PiLp.norm_eq_ciSup]
        exact le_antisymm (ciSup_le fun i => hi₀ i (Finset.mem_univ i))
          (le_ciSup (f := fun j : Fin m => ‖v j‖) (Finite.bddAbove_range _) i₀)
      rw [hsup, dotProduct_single, mul_sgn, Real.norm_eq_abs]
  · have hp_gt : 1 < p := lt_of_le_of_ne (ENNReal.HolderConjugate.one_le p q) hp1.symm
    have hq_gt : 1 < q := lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) hq1.symm
    have hp_ne_top : p ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mpr hq_gt).ne
    have hq_ne_top : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp_gt).ne
    have hpq_real : p.toReal.HolderConjugate q.toReal :=
      ENNReal.HolderConjugate.toReal_of_ne_top hp_ne_top hq_ne_top
    set pr := p.toReal
    set qr := q.toReal
    have hpr_gt : 1 < pr := hpq_real.lt
    have hqr_gt : 1 < qr := hpq_real.symm.lt
    have hpr_pos : 0 < pr := zero_lt_one.trans hpr_gt
    have hqr_pos : 0 < qr := zero_lt_one.trans hqr_gt
    set a := ‖WithLp.toLp p v‖
    have ha_pos : 0 < a := by
      rw [norm_pos_iff]
      intro h0
      exact hv (by simpa using congrArg WithLp.ofLp h0)
    have hsum_v : ∑ i : Fin m, |v i| ^ pr = a ^ pr := by
      have hnorm : a = (∑ i : Fin m, |v i| ^ pr) ^ (1 / pr) := by
        simpa [a, pr, Real.norm_eq_abs] using PiLp.norm_eq_sum hpr_pos (WithLp.toLp p v)
      have hnonneg : 0 ≤ ∑ i : Fin m, |v i| ^ pr :=
        Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
      rw [hnorm, ← Real.rpow_mul hnonneg, one_div_mul_cancel hpr_pos.ne', Real.rpow_one]
    have hpr_qr : (pr - 1) * qr = pr := by
      have h1 : pr⁻¹ + qr⁻¹ = 1 := hpq_real.inv_add_inv_eq_one
      field_simp [hpr_pos.ne', hqr_pos.ne'] at h1 ⊢
      linarith
    set w : Fin m → ℝ := fun i => sgn (v i) * |v i| ^ (pr - 1)
    have hsum_w : ∑ i : Fin m, |w i| ^ qr = a ^ pr := by
      rw [← hsum_v]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hw_abs : |w i| = |v i| ^ (pr - 1) := by
        simp only [w, abs_mul, abs_sgn, one_mul,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (v i)) _)]
      rw [hw_abs, ← Real.rpow_mul (abs_nonneg _), hpr_qr]
    set u : Fin m → ℝ := fun i => a ^ (1 - pr) * w i
    refine ⟨u, ?_, ?_⟩
    · rw [PiLp.norm_eq_sum hqr_pos]
      have hu_sum : ∑ i : Fin m, ‖(WithLp.toLp q u) i‖ ^ qr =
          (a ^ (1 - pr)) ^ qr * ∑ i : Fin m, |w i| ^ qr := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hpos_scale : 0 ≤ a ^ (1 - pr) := Real.rpow_nonneg ha_pos.le _
        change |a ^ (1 - pr) * w i| ^ qr = (a ^ (1 - pr)) ^ qr * |w i| ^ qr
        rw [abs_mul, abs_of_nonneg hpos_scale, Real.mul_rpow hpos_scale (abs_nonneg _)]
      rw [hu_sum, hsum_w, ← Real.rpow_mul ha_pos.le, ← Real.rpow_add ha_pos]
      have hexp : (1 - pr) * qr + pr = 0 := by linarith [hpr_qr]
      rw [hexp, Real.rpow_zero, Real.one_rpow]
    · have hvw : v ⬝ᵥ w = a ^ pr := by
        rw [← hsum_v]
        change ∑ i : Fin m, v i * (sgn (v i) * |v i| ^ (pr - 1)) = ∑ i : Fin m, |v i| ^ pr
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, mul_sgn]
        rcases eq_or_ne (|v i|) 0 with hvi | hvi
        · rw [hvi, zero_mul, Real.zero_rpow hpr_pos.ne']
        · have hvpos : 0 < |v i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hvi)
          have hexp : 1 + (pr - 1) = pr := by ring
          conv_rhs => rw [← hexp, Real.rpow_add hvpos, Real.rpow_one]
      have hu_dot : v ⬝ᵥ u = a ^ (1 - pr) * (v ⬝ᵥ w) := by
        change ∑ i : Fin m, v i * (a ^ (1 - pr) * w i) = a ^ (1 - pr) * ∑ i : Fin m, v i * w i
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hu_dot, hvw, ← Real.rpow_add ha_pos]
      have hexp : 1 - pr + pr = 1 := by ring
      rw [hexp, Real.rpow_one]

end SolRWPILimitEq42

theorem solution {m : ℕ} (ρ : ℝ) (hρ : 1 < ρ) (q p : ENNReal) (hpq : p.HolderConjugate q)
    (v : Fin m → ℝ) :
    IsGreatest (Set.range fun Δ : Fin m → ℝ => v ⬝ᵥ Δ - ‖WithLp.toLp q Δ‖ ^ ρ)
      (‖WithLp.toLp p v‖ ^ (ρ / (ρ - 1)) * (1 / ρ) ^ (1 / (ρ - 1)) * (1 - 1 / ρ)) := by
  have : p.HolderConjugate q := hpq
  have : q.HolderConjugate p := hpq.symm
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hρ_pos : 0 < ρ := zero_lt_one.trans hρ
  have hρ1_pos : 0 < ρ - 1 := sub_pos.mpr hρ
  set β : ℝ := ρ / (ρ - 1)
  have hβ_pos : 0 < β := div_pos hρ_pos hρ1_pos
  have hconj : ρ.HolderConjugate β :=
    (Real.holderConjugate_iff_eq_conjExponent hρ).mpr rfl
  set a : ℝ := ‖WithLp.toLp p v‖
  have ha_nonneg : 0 ≤ a := norm_nonneg _
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne v 0 with rfl | hv
    · refine ⟨0, ?_⟩
      have ha0 : a = 0 := by simp [a]
      simp [ha0, Real.zero_rpow hρ_pos.ne', Real.zero_rpow hβ_pos.ne']
    · obtain ⟨u, hu_norm, hu_dot⟩ :=
        SolRWPILimitEq42.exists_norm_eq_one_dotProduct_eq p q hpq v hv
      have ha_pos : 0 < a := by
        rw [norm_pos_iff]
        intro h0
        exact hv (by simpa using congrArg WithLp.ofLp h0)
      have hinvρ_pos : 0 < 1 / ρ := one_div_pos.mpr hρ_pos
      set t : ℝ := a ^ (1 / (ρ - 1)) * (1 / ρ) ^ (1 / (ρ - 1))
      have ht_nonneg : 0 ≤ t :=
        mul_nonneg (Real.rpow_nonneg ha_pos.le _) (Real.rpow_nonneg hinvρ_pos.le _)
      refine ⟨t • u, ?_⟩
      have hnorm_tu : ‖WithLp.toLp q (t • u)‖ = t := by
        change ‖t • WithLp.toLp q u‖ = t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg, hu_norm, mul_one]
      have hdot_tu : v ⬝ᵥ (t • u) = a * t := by
        rw [dotProduct_smul, smul_eq_mul, hu_dot, mul_comm]
      dsimp only
      rw [hdot_tu, hnorm_tu]
      have hexp_a : 1 + 1 / (ρ - 1) = β := by
        dsimp [β]; field_simp [hρ1_pos.ne']; ring
      have hat : a * t = a ^ β * (1 / ρ) ^ (1 / (ρ - 1)) := by
        calc a * t = (a * a ^ (1 / (ρ - 1))) * (1 / ρ) ^ (1 / (ρ - 1)) := by dsimp [t]; ring
          _ = a ^ β * (1 / ρ) ^ (1 / (ρ - 1)) := by
            congr 1
            conv_rhs => rw [← hexp_a, Real.rpow_add ha_pos, Real.rpow_one]
      have htρ : t ^ ρ = a ^ β * (1 / ρ) ^ (1 / (ρ - 1)) * (1 / ρ) := by
        dsimp [t]
        rw [Real.mul_rpow (Real.rpow_nonneg ha_pos.le _) (Real.rpow_nonneg hinvρ_pos.le _),
          ← Real.rpow_mul ha_pos.le, ← Real.rpow_mul hinvρ_pos.le]
        have hexp1 : 1 / (ρ - 1) * ρ = β := by dsimp [β]; ring
        have hexp2 : β = 1 / (ρ - 1) + 1 := by
          dsimp [β]; field_simp [hρ1_pos.ne']; ring
        rw [hexp1]
        conv_lhs => arg 2; rw [hexp2, Real.rpow_add hinvρ_pos, Real.rpow_one]
        ring
      rw [hat, htρ]
      ring
  · rintro _ ⟨Δ, rfl⟩
    set t : ℝ := ‖WithLp.toLp q Δ‖
    have ht_nonneg : 0 ≤ t := norm_nonneg _
    have hdot : v ⬝ᵥ Δ ≤ a * t :=
      SolRWPILimitEq42.dotProduct_le_norm_mul_norm p q hpq v Δ
    have hinvρ_pos : 0 < 1 / ρ := one_div_pos.mpr hρ_pos
    set X : ℝ := ρ ^ (1 / ρ) * t
    set Y : ℝ := a * (1 / ρ) ^ (1 / ρ)
    have hX_nonneg : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hρ_pos.le _) ht_nonneg
    have hY_nonneg : 0 ≤ Y := mul_nonneg ha_nonneg (Real.rpow_nonneg hinvρ_pos.le _)
    have hyoung : X * Y ≤ X ^ ρ / ρ + Y ^ β / β := by
      have h := Real.young_inequality X Y hconj
      simpa [abs_of_nonneg hX_nonneg, abs_of_nonneg hY_nonneg] using h
    have hXY : X * Y = a * t := by
      dsimp [X, Y]
      have h1 : ρ ^ (1 / ρ) * (1 / ρ) ^ (1 / ρ) = 1 := by
        rw [← Real.mul_rpow hρ_pos.le hinvρ_pos.le, mul_one_div_cancel hρ_pos.ne', Real.one_rpow]
      calc ρ ^ (1 / ρ) * t * (a * (1 / ρ) ^ (1 / ρ))
          = (ρ ^ (1 / ρ) * (1 / ρ) ^ (1 / ρ)) * (a * t) := by ring
        _ = a * t := by rw [h1, one_mul]
    have hXρ : X ^ ρ / ρ = t ^ ρ := by
      dsimp [X]
      rw [Real.mul_rpow (Real.rpow_nonneg hρ_pos.le _) ht_nonneg,
        ← Real.rpow_mul hρ_pos.le, one_div_mul_cancel hρ_pos.ne', Real.rpow_one,
        mul_div_cancel_left₀ _ hρ_pos.ne']
    have hYβ : Y ^ β / β = a ^ β * (1 / ρ) ^ (1 / (ρ - 1)) * (1 - 1 / ρ) := by
      dsimp [Y]
      rw [Real.mul_rpow ha_nonneg (Real.rpow_nonneg hinvρ_pos.le _),
        ← Real.rpow_mul hinvρ_pos.le]
      have hexp : 1 / ρ * β = 1 / (ρ - 1) := by
        dsimp [β]; field_simp [hρ_pos.ne', hρ1_pos.ne']
      have hdivβ : (a ^ β * (1 / ρ) ^ (1 / (ρ - 1))) / β =
          a ^ β * (1 / ρ) ^ (1 / (ρ - 1)) * (1 - 1 / ρ) := by
        dsimp [β]
        field_simp [hρ_pos.ne', hρ1_pos.ne']
      rw [hexp, hdivβ]
    rw [hXY, hXρ, hYβ] at hyoung
    linarith
