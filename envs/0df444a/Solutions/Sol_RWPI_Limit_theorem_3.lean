-- Prove2me | solution 1 for RWPI.Limit.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T20:57:05.023203+00:00
-- url     : https://prove2.me/submissions/1af13ebf-71bd-4006-852a-9db4e0846122

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_RWPI_Limit_rowNorm
import Definitions.Def_RWPI_Limit_Rbar
import Definitions.Def_RWPI_Limit_dualRep
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Theorems.Thm_RWPI_Limit_asymptotic_upper_bound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology RWPI.Limit RWPI.SqrtLasso
  WassersteinDRO.Regularization
open scoped ENNReal RealInnerProductSpace

namespace SolRWPILimitThm3

private noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private lemma abs_sgn (x : ℝ) : |sgn x| = 1 := by
  unfold sgn; split_ifs <;> simp

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
      refine Finset.sum_congr rfl fun i _ => by rw [mul_sgn, Real.norm_eq_abs]
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
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ i₀) h
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
    let pr := p.toReal
    let qr := q.toReal
    have hpr_pos : 0 < pr := zero_lt_one.trans hpq_real.lt
    have hqr_pos : 0 < qr := zero_lt_one.trans hpq_real.symm.lt
    let a := ‖WithLp.toLp p v‖
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
    let w : Fin m → ℝ := fun i => sgn (v i) * |v i| ^ (pr - 1)
    have hsum_w : ∑ i : Fin m, |w i| ^ qr = a ^ pr := by
      rw [← hsum_v]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hw_abs : |w i| = |v i| ^ (pr - 1) := by
        simp only [w, abs_mul, abs_sgn, one_mul,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (v i)) _)]
      rw [hw_abs, ← Real.rpow_mul (abs_nonneg _), hpr_qr]
    let u : Fin m → ℝ := fun i => a ^ (1 - pr) * w i
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

private lemma norm_le_toLp_norm {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Fin d → ℝ) :
    ‖x‖ ≤ ‖WithLp.toLp p x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp p x))).mpr fun j => ?_
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [PiLp.norm_eq_ciSup]
    exact le_ciSup (f := fun i : Fin d => ‖x i‖) (Finite.bddAbove_range _) j
  · have hp_one : 1 ≤ p := Fact.out
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp_one).ne' hp_top
    rw [PiLp.norm_eq_sum hp_pos]
    have hj : ‖x j‖ = (‖x j‖ ^ p.toReal) ^ (1 / p.toReal) := by
      rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp_pos.ne', Real.rpow_one]
    rw [hj]
    refine Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) ?_ (one_div_nonneg.mpr hp_pos.le)
    exact Finset.single_le_sum (f := fun i : Fin d => ‖x i‖ ^ p.toReal)
      (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)

private lemma toLp_norm_single_le_one {d : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] (j : Fin d) :
    ‖WithLp.toLp q (Pi.single j (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
  have : Nonempty (Fin d) := ⟨j⟩
  rcases eq_or_ne q ∞ with rfl | hq_top
  · rw [PiLp.norm_eq_ciSup]
    refine ciSup_le fun i => ?_
    change ‖(Pi.single j (1 : ℝ) : Fin d → ℝ) i‖ ≤ 1
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  · have hq_one : 1 ≤ q := Fact.out
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq_one).ne' hq_top
    rw [PiLp.norm_eq_sum hq_pos]
    have hsum : ∑ i : Fin d,
        ‖(WithLp.toLp q (Pi.single j (1 : ℝ) : Fin d → ℝ)) i‖ ^ q.toReal = 1 := by
      change ∑ i : Fin d, ‖(Pi.single j (1 : ℝ) : Fin d → ℝ) i‖ ^ q.toReal = 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_eq_of_ne hij, Real.zero_rpow hq_pos.ne']
      · intro h_abs; exact absurd (Finset.mem_univ j) h_abs
    rw [hsum, Real.one_rpow]

private lemma toLp_norm_single_eq_one {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin d) :
    ‖WithLp.toLp p (Pi.single j (1 : ℝ) : Fin d → ℝ)‖ = 1 := by
  refine le_antisymm (toLp_norm_single_le_one p j) ?_
  calc (1 : ℝ) = ‖(Pi.single j (1 : ℝ) : Fin d → ℝ) j‖ := by simp
    _ ≤ ‖(Pi.single j (1 : ℝ) : Fin d → ℝ)‖ := norm_le_pi_norm _ j
    _ ≤ ‖WithLp.toLp p (Pi.single j (1 : ℝ) : Fin d → ℝ)‖ := norm_le_toLp_norm p _

private lemma toLp_norm_le_sum_abs {d : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] (x : Fin d → ℝ) :
    ‖WithLp.toLp q x‖ ≤ ∑ j : Fin d, |x j| := by
  have hx : WithLp.toLp q x =
      ∑ j : Fin d, x j • WithLp.toLp q (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    ext k
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk; simp [Pi.single_eq_of_ne hjk.symm]
    · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
  rw [hx]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (toLp_norm_single_le_one q j)

private lemma toLp_norm_le_nat_mul_norm {d : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] (x : Fin d → ℝ) :
    ‖WithLp.toLp q x‖ ≤ (d : ℝ) * ‖x‖ := by
  calc ‖WithLp.toLp q x‖ ≤ ∑ j : Fin d, |x j| := toLp_norm_le_sum_abs q x
    _ ≤ ∑ _j : Fin d, ‖x‖ := Finset.sum_le_sum fun j _ => by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    _ = (d : ℝ) * ‖x‖ := by simp [Finset.sum_const, nsmul_eq_mul]

private lemma isCompact_toLp_closedBall {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : ℝ) :
    IsCompact {x : Fin d → ℝ | ‖WithLp.toLp p x‖ ≤ R} := by
  have hclosed : IsClosed {x : Fin d → ℝ | ‖WithLp.toLp p x‖ ≤ R} :=
    isClosed_le (continuous_norm.comp (PiLp.continuous_toLp p _)) continuous_const
  refine (isCompact_closedBall (0 : Fin d → ℝ) R).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_toLp_norm p x).trans hx

private lemma isCompact_toLp_sphere {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsCompact {x : Fin d → ℝ | ‖WithLp.toLp p x‖ = 1} := by
  have hclosed : IsClosed {x : Fin d → ℝ | ‖WithLp.toLp p x‖ = 1} :=
    isClosed_eq (continuous_norm.comp (PiLp.continuous_toLp p _)) continuous_const
  exact (isCompact_toLp_closedBall p 1).of_isClosed_subset hclosed fun x hx => le_of_eq hx

private noncomputable def rowVec {m l r : ℕ} (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θs : Fin l → ℝ) (ζ : Fin r → ℝ) (w : Fin m → ℝ) : Fin m → ℝ :=
  fun k : Fin m => ∑ j : Fin r, ζ j * fderiv ℝ (fun x => h x θs) w (Pi.single k 1) j

private lemma rowNorm_eq_norm_rowVec {m l r : ℕ} (p : ℝ≥0∞)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ζ : Fin r → ℝ) (w : Fin m → ℝ) :
    rowNorm p h θs ζ w = ‖WithLp.toLp p (rowVec h θs ζ w)‖ := rfl

private lemma rowVec_smul {m l r : ℕ} (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θs : Fin l → ℝ) (a : ℝ) (ζ : Fin r → ℝ) (w : Fin m → ℝ) :
    rowVec h θs (a • ζ) w = a • rowVec h θs ζ w := by
  ext k; simp [rowVec, Finset.mul_sum, mul_assoc]

private lemma rowNorm_smul {m l r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (a : ℝ) (ζ : Fin r → ℝ) (w : Fin m → ℝ) :
    rowNorm p h θs (a • ζ) w = |a| * rowNorm p h θs ζ w := by
  change ‖WithLp.toLp p (rowVec h θs (a • ζ) w)‖ = |a| * ‖WithLp.toLp p (rowVec h θs ζ w)‖
  rw [rowVec_smul]
  change ‖a • WithLp.toLp p (rowVec h θs ζ w)‖ = _
  rw [norm_smul, Real.norm_eq_abs]

private lemma dot_fderiv_eq_rowVec_dot {m l r : ℕ}
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ζ : Fin r → ℝ) (w Δ : Fin m → ℝ) :
    ζ ⬝ᵥ fderiv ℝ (fun x => h x θs) w Δ = rowVec h θs ζ w ⬝ᵥ Δ := by
  have hΔ : Δ = ∑ k : Fin m, Δ k • Pi.single k (1 : ℝ) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [Pi.single_eq_of_ne hik.symm]
    · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
  conv_lhs => rw [hΔ]
  rw [map_sum, dotProduct_sum]
  simp only [map_smul, dotProduct, Pi.smul_apply, smul_eq_mul, rowVec]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

private lemma continuous_toLp_rowVec {m l r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs) :
    Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => WithLp.toLp p (rowVec h θs zw.1 zw.2)) := by
  have hfderiv : Continuous (fun w : Fin m → ℝ => fderiv ℝ (fun x => h x θs) w) :=
    hC1.continuous_fderiv one_ne_zero
  have hvec : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowVec h θs zw.1 zw.2) := by
    refine continuous_pi fun k => continuous_finsetSum Finset.univ fun j _ => ?_
    have h1 : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => zw.1 j) :=
      (continuous_apply j).comp continuous_fst
    have h2 : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) =>
        fderiv ℝ (fun x => h x θs) zw.2 (Pi.single k 1) j) :=
      (continuous_apply j).comp
        (((ContinuousLinearMap.apply ℝ (Fin r → ℝ) (Pi.single k 1)).continuous.comp hfderiv).comp
          continuous_snd)
    exact h1.mul h2
  exact (PiLp.continuous_toLp p _).comp hvec

private lemma dot_integral_fderiv_eq {m l r : ℕ}
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (ζ : Fin r → ℝ) (w Δ : Fin m → ℝ) (c : ℝ) :
    ζ ⬝ᵥ (∫ u in (0 : ℝ)..1, fderiv ℝ (fun x => h x θs) (w + c • (u • Δ)) Δ) =
      ∫ u in (0 : ℝ)..1, rowVec h θs ζ (w + c • (u • Δ)) ⬝ᵥ Δ := by
  let g : ℝ → (Fin r → ℝ) := fun u => fderiv ℝ (fun x => h x θs) (w + c • (u • Δ)) Δ
  have hg_cont : Continuous g := by
    have hfderiv : Continuous (fun x : Fin m → ℝ => fderiv ℝ (fun y => h y θs) x) :=
      hC1.continuous_fderiv one_ne_zero
    have hpath : Continuous (fun u : ℝ => w + c • (u • Δ)) := by fun_prop
    exact (ContinuousLinearMap.apply ℝ (Fin r → ℝ) Δ).continuous.comp (hfderiv.comp hpath)
  let Lζ : (Fin r → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => ζ ⬝ᵥ y
        map_add' := fun x y => dotProduct_add ζ x y
        map_smul' := fun a y => by simp [dotProduct_smul] }
  have hcomm : Lζ (∫ u in (0 : ℝ)..1, g u) = ∫ u in (0 : ℝ)..1, Lζ (g u) :=
    (Lζ.intervalIntegral_comp_comm (hg_cont.intervalIntegrable 0 1)).symm
  calc ζ ⬝ᵥ (∫ u in (0 : ℝ)..1, g u) = Lζ (∫ u in (0 : ℝ)..1, g u) := rfl
    _ = ∫ u in (0 : ℝ)..1, Lζ (g u) := hcomm
    _ = ∫ u in (0 : ℝ)..1, rowVec h θs ζ (w + c • (u • Δ)) ⬝ᵥ Δ :=
        intervalIntegral.integral_congr fun u _ => dot_fderiv_eq_rowVec_dot h θs ζ _ Δ

private lemma exists_trunc_gt_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (c₀ : ℝ) (ξ : Fin r → ℝ) (hpos : 0 < μ {ω | c₀ < rowNorm p h θs ξ (W0 ω)}) :
    ∃ k : ℕ, 0 < μ {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
      c₀ + 1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} := by
  by_contra hall
  push Not at hall
  have hnull : ∀ k : ℕ, μ {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
      c₀ + 1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} = 0 :=
    fun k => nonpos_iff_eq_zero.mp (hall k)
  have hsub : {ω | c₀ < rowNorm p h θs ξ (W0 ω)} ⊆
      ⋃ k : ℕ, {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
        c₀ + 1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} := by
    intro ω hω
    change c₀ < rowNorm p h θs ξ (W0 ω) at hω
    have hdiff : 0 < rowNorm p h θs ξ (W0 ω) - c₀ := sub_pos.mpr hω
    obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖W0 ω‖
    obtain ⟨k₂, hk₂⟩ := exists_nat_ge (1 / (rowNorm p h θs ξ (W0 ω) - c₀))
    refine Set.mem_iUnion.mpr ⟨max k₁ k₂, ?_, ?_⟩
    · have hk1_le : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := Nat.cast_le.mpr (le_max_left k₁ k₂)
      linarith
    · have hk2_le : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := Nat.cast_le.mpr (le_max_right k₁ k₂)
      have hdenom_pos : (0 : ℝ) < (max k₁ k₂ : ℕ) + 1 := by positivity
      have h1 : 1 ≤ (rowNorm p h θs ξ (W0 ω) - c₀) * (k₂ : ℝ) := (div_le_iff₀' hdiff).mp hk₂
      have h2 : (rowNorm p h θs ξ (W0 ω) - c₀) * (k₂ : ℝ) ≤
          (rowNorm p h θs ξ (W0 ω) - c₀) * ((max k₁ k₂ : ℕ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hdiff.le
      have h3 : 1 / ((max k₁ k₂ : ℕ) + 1 : ℝ) ≤ rowNorm p h θs ξ (W0 ω) - c₀ :=
        (div_le_iff₀ hdenom_pos).mpr (by linarith)
      linarith
  have hzero : μ {ω | c₀ < rowNorm p h θs ξ (W0 ω)} = 0 :=
    nonpos_iff_eq_zero.mp ((measure_mono hsub).trans (measure_iUnion_null hnull).le)
  exact hpos.ne' hzero

private lemma exists_uniform_compact_cover {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ}
    (K_set : Set (Fin r → ℝ)) (hK_comp : IsCompact K_set) (hK_ne : K_set.Nonempty)
    (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs) (c₀ : ℝ)
    (hgt : ∀ ξ ∈ K_set, 0 < μ {ω | c₀ < rowNorm p h θs ξ (W0 ω)}) :
    ∃ (m_cov : ℕ) (A_ev : Fin m_cov → Set (Fin m → ℝ)) (K_W η_star p_star : ℝ),
      0 < m_cov ∧ 0 < K_W ∧ 0 < η_star ∧ 0 < p_star ∧ p_star ≤ 1 ∧
      (∀ j : Fin m_cov, MeasurableSet (A_ev j)) ∧
      (∀ j : Fin m_cov, p_star ≤ μ.real (W0 ⁻¹' A_ev j)) ∧
      (∀ j : Fin m_cov, ∀ w ∈ A_ev j, ‖w‖ ≤ K_W) ∧
      (∀ ξ ∈ K_set, ∃ j : Fin m_cov, ∀ w ∈ A_ev j, c₀ + η_star ≤ rowNorm p h θs ξ w) := by
  have hrow_cont : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) =>
      rowNorm p h θs zw.1 zw.2) :=
    continuous_norm.comp (continuous_toLp_rowVec p h θs hC1)
  have hex_local : ∀ ξ ∈ K_set, ∃ (C η δ : ℝ),
      0 < C ∧ 0 < η ∧ 0 < δ ∧
      0 < μ {ω | ‖W0 ω‖ ≤ C ∧ c₀ + 2 * η ≤ rowNorm p h θs ξ (W0 ω)} ∧
      ∀ ζ ∈ K_set, dist ζ ξ < δ → ∀ w : Fin m → ℝ,
        ‖w‖ ≤ C ∧ c₀ + 2 * η ≤ rowNorm p h θs ξ w → c₀ + η ≤ rowNorm p h θs ζ w := by
    intro ξ hξ
    obtain ⟨k, hk_pos⟩ := exists_trunc_gt_const W0 p h θs c₀ ξ (hgt ξ hξ)
    let C : ℝ := (k : ℝ) + 1
    have hC_pos : 0 < C := by positivity
    let η : ℝ := 1 / (2 * C)
    have hη_pos : 0 < η := by positivity
    have h2η : 2 * η = 1 / ((k : ℝ) + 1) := by dsimp [η, C]; field_simp [hC_pos.ne']
    have hprob_pos : 0 < μ {ω | ‖W0 ω‖ ≤ C ∧ c₀ + 2 * η ≤ rowNorm p h θs ξ (W0 ω)} := by
      simpa only [C, h2η] using hk_pos
    have hK_prod : IsCompact (K_set ×ˢ Metric.closedBall (0 : Fin m → ℝ) C) :=
      hK_comp.prod (isCompact_closedBall _ _)
    have hucont := hK_prod.uniformContinuousOn_of_continuous hrow_cont.continuousOn
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hucont η hη_pos
    refine ⟨C, η, δ, hC_pos, hη_pos, hδ_pos, hprob_pos, fun ζ hζ hdist w hw => ?_⟩
    have hp1 : (ζ, w) ∈ K_set ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
      ⟨hζ, by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1⟩
    have hp2 : (ξ, w) ∈ K_set ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
      ⟨hξ, by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1⟩
    have hd : dist (ζ, w) (ξ, w) < δ := by
      simpa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist
    have hclose : |rowNorm p h θs ζ w - rowNorm p h θs ξ w| < η :=
      hδ (ζ, w) hp1 (ξ, w) hp2 hd
    linarith [abs_lt.mp hclose, hw.2]
  choose C_fn η_fn δ_fn hC_pos hη_pos hδ_pos hprob_pos hlocal using
    fun ξ : K_set => hex_local ξ.1 ξ.2
  obtain ⟨F_sub, _, hF_fin, hF_cov⟩ := hK_comp.elim_finite_subcover_image
    (b := Set.univ) (c := fun ξ : K_set => Metric.ball ξ.1 (δ_fn ξ))
    (fun _ _ => Metric.isOpen_ball)
    (fun ζ hζ => Set.mem_biUnion (Set.mem_univ (⟨ζ, hζ⟩ : K_set))
      (Metric.mem_ball_self (hδ_pos ⟨ζ, hζ⟩)))
  let F : Finset K_set := hF_fin.toFinset
  have hF_ne : F.Nonempty := by
    obtain ⟨ξ₀, hξ₀⟩ := hK_ne
    obtain ⟨ξ, hξ_mem, _⟩ := Set.mem_iUnion₂.mp (hF_cov hξ₀)
    exact ⟨ξ, hF_fin.mem_toFinset.mpr hξ_mem⟩
  let m_cov : ℕ := F.card
  have hm_pos : 0 < m_cov := Finset.card_pos.mpr hF_ne
  let e : F ≃ Fin m_cov := F.equivFin
  let K_W : ℝ := F.sup' hF_ne C_fn
  have hKW_pos : 0 < K_W := by
    obtain ⟨ξ₀, hξ₀⟩ := hF_ne
    exact (hC_pos ξ₀).trans_le (Finset.le_sup' C_fn hξ₀)
  let η_star : ℝ := F.inf' hF_ne η_fn
  have hη_star_pos : 0 < η_star :=
    (Finset.lt_inf'_iff hF_ne).mpr fun ξ _ => hη_pos ξ
  let A_sp : K_set → Set (Fin m → ℝ) := fun ξ =>
    {w | ‖w‖ ≤ C_fn ξ ∧ c₀ + 2 * η_fn ξ ≤ rowNorm p h θs ξ.1 w}
  let p_fn : K_set → ℝ := fun ξ => μ.real (W0 ⁻¹' A_sp ξ)
  have hp_fn_pos : ∀ ξ : K_set, 0 < p_fn ξ := fun ξ =>
    ENNReal.toReal_pos (hprob_pos ξ).ne' (measure_ne_top μ _)
  have hp_fn_le_one : ∀ ξ : K_set, p_fn ξ ≤ 1 := fun ξ => by
    calc μ.real (W0 ⁻¹' A_sp ξ) ≤ μ.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
      _ = 1 := by simp
  let p_star : ℝ := F.inf' hF_ne p_fn
  have hp_star_pos : 0 < p_star :=
    (Finset.lt_inf'_iff hF_ne).mpr fun ξ _ => hp_fn_pos ξ
  have hp_star_le_one : p_star ≤ 1 := by
    obtain ⟨ξ₀, hξ₀⟩ := hF_ne
    exact (Finset.inf'_le p_fn hξ₀).trans (hp_fn_le_one ξ₀)
  let A_ev : Fin m_cov → Set (Fin m → ℝ) := fun j => A_sp (e.symm j).1
  refine ⟨m_cov, A_ev, K_W, η_star, p_star, hm_pos, hKW_pos, hη_star_pos,
    hp_star_pos, hp_star_le_one, ?_, ?_, ?_, ?_⟩
  · intro j
    refine (measurableSet_le continuous_norm.measurable measurable_const).inter ?_
    exact measurableSet_le measurable_const
      (hrow_cont.comp (continuous_const.prodMk continuous_id)).measurable
  · intro j; exact Finset.inf'_le p_fn (e.symm j).2
  · intro j w hw; exact hw.1.trans (Finset.le_sup' C_fn (e.symm j).2)
  · intro ξ hξ
    obtain ⟨ξ_cov, hξ_sub, hξ_ball⟩ := Set.mem_iUnion₂.mp (hF_cov hξ)
    have hξ_F : ξ_cov ∈ F := hF_fin.mem_toFinset.mpr hξ_sub
    let j : Fin m_cov := e ⟨ξ_cov, hξ_F⟩
    refine ⟨j, fun w hw => ?_⟩
    have he_eq : (e.symm j).1 = ξ_cov := by simp [j]
    have hw' : w ∈ A_sp ξ_cov := by simpa only [A_ev, he_eq] using hw
    have h1 := hlocal ξ_cov ξ hξ (Metric.mem_ball.mp hξ_ball) w hw'
    have h2 : η_star ≤ η_fn ξ_cov := Finset.inf'_le η_fn hξ_F
    linarith

private lemma tendsto_prob_gt_of_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hZmeas : ∀ n, Measurable (Z n)) (c : ℝ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 c)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => μ {ω | η < |Z n ω - c|}) atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => Set.indicator {ω' | η < |Z n ω' - c|} 1 ω
  have hSmeas : ∀ n, MeasurableSet {ω | η < |Z n ω - c|} := fun n =>
    measurableSet_lt measurable_const (((hZmeas n).sub measurable_const).norm)
  have hFmeas : ∀ n, Measurable (F n) := fun n => measurable_one.indicator (hSmeas n)
  have hFbound : ∀ n, ∀ᵐ ω ∂μ, F n ω ≤ (fun _ : Ω => (1 : ℝ≥0∞)) ω := fun _ =>
    Eventually.of_forall fun ω => by dsimp [F, Set.indicator]; split_ifs <;> simp
  have h1int : ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ ≠ ∞ := by simp
  have hFlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have hev : ∀ᶠ n in atTop, |Z n ω - c| < η :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hω).eventually (gt_mem_nhds hη)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hnot : ω ∉ {ω' | η < |Z n ω' - c|} := not_lt.mpr hn.le
    simp [F, hnot]
  have hlin := tendsto_lintegral_of_dominated_convergence (fun _ : Ω => (1 : ℝ≥0∞))
    hFmeas hFbound h1int hFlim
  simpa [F, lintegral_indicator_one, hSmeas] using hlin

/-! ### Module A: Automatic Strict Primal Feasibility (`0 ∈ interior (convexHull (range h))`) -/

private lemma zero_mem_interior_convexHull {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hint : Integrable (fun ω => h (W0 ω) θs) μ)
    (hmean : ∫ ω, h (W0 ω) θs ∂μ = 0)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W0 ω)}) :
    (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θs)) := by
  let C : Set (Fin r → ℝ) := convexHull ℝ (Set.range fun u => h u θs)
  have hC_conv : Convex ℝ C := convex_convexHull ℝ _
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hC_univ : C = Set.univ := by
      ext x
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      have hx : x = h 0 θs := Subsingleton.elim x (h 0 θs)
      rw [hx]
      exact subset_convexHull ℝ _ ⟨0, rfl⟩
    change 0 ∈ interior C
    rw [hC_univ, interior_univ]
    trivial
  · by_contra h0_not_int
    have hex_ζ : ∃ ζ : Fin r → ℝ, ζ ≠ 0 ∧ ∀ u : Fin m → ℝ, 0 ≤ ζ ⬝ᵥ h u θs := by
      by_cases hint_ne : (interior C).Nonempty
      · obtain ⟨f, u_sep, hf_ne, hf_le, hf_ge⟩ :=
          geometric_hahn_banach_of_nonempty_interior hC_conv (convex_singleton (0 : Fin r → ℝ))
            (Set.disjoint_singleton_right.mpr h0_not_int) hint_ne (Set.singleton_nonempty _)
        let ζ : Fin r → ℝ := fun j => -f (Pi.single j (1 : ℝ))
        have hf_eval : ∀ y : Fin r → ℝ, -f y = ζ ⬝ᵥ y := by
          intro y
          have hy : y = ∑ j : Fin r, y j • (Pi.single j (1 : ℝ) : Fin r → ℝ) := by
            ext k
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            rw [Finset.sum_eq_single k]
            · simp
            · intro j _ hjk; simp [Pi.single_eq_of_ne hjk.symm]
            · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
          conv_lhs => rw [hy]
          rw [map_sum, ← Finset.sum_neg_distrib]
          simp only [map_smul, smul_eq_mul, dotProduct, ζ]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hζ_ne : ζ ≠ 0 := by
          intro h0
          apply hf_ne
          ext y
          have := hf_eval y
          rw [h0, zero_dotProduct] at this
          simpa using neg_eq_zero.mp this
        refine ⟨ζ, hζ_ne, fun u => ?_⟩
        have h1 : f (h u θs) ≤ u_sep := hf_le _ (subset_convexHull ℝ _ ⟨u, rfl⟩)
        have h2 : u_sep ≤ f 0 := hf_ge 0 rfl
        rw [map_zero] at h2
        rw [← hf_eval]
        linarith
      · have haff_ne_top : affineSpan ℝ C ≠ ⊤ := by
          intro htop
          exact hint_ne (hC_conv.interior_nonempty_iff_affineSpan_eq_top.mpr htop)
        have hvs_lt : vectorSpan ℝ C < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro hv_top
          apply haff_ne_top
          rw [eq_top_iff]
          intro x _
          have hy0 : h 0 θs ∈ affineSpan ℝ C :=
            subset_affineSpan ℝ C (subset_convexHull ℝ _ ⟨0, rfl⟩)
          have hdir : x -ᵥ h 0 θs ∈ (affineSpan ℝ C).direction := by
            rw [direction_affineSpan, hv_top]; trivial
          simpa using AffineSubspace.vadd_mem_of_mem_direction hdir hy0
        obtain ⟨f, hf_ne, hf_bot⟩ :=
          Submodule.exists_dual_map_eq_bot_of_lt_top hvs_lt inferInstance
        let ζ : Fin r → ℝ := fun j => f (Pi.single j (1 : ℝ))
        have hf_eval : ∀ y : Fin r → ℝ, f y = ζ ⬝ᵥ y := by
          intro y
          have hy : y = ∑ j : Fin r, y j • (Pi.single j (1 : ℝ) : Fin r → ℝ) := by
            ext k
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            rw [Finset.sum_eq_single k]
            · simp
            · intro j _ hjk; simp [Pi.single_eq_of_ne hjk.symm]
            · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
          conv_lhs => rw [hy]
          rw [map_sum]
          simp only [map_smul, smul_eq_mul, dotProduct, ζ]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hζ_ne : ζ ≠ 0 := by
          intro h0
          apply hf_ne
          refine LinearMap.ext fun y => ?_
          rw [hf_eval y, h0, zero_dotProduct, LinearMap.zero_apply]
        have hconst : ∀ u : Fin m → ℝ, ζ ⬝ᵥ h u θs = ζ ⬝ᵥ h 0 θs := by
          intro u
          have hvsub : h u θs -ᵥ h 0 θs ∈ vectorSpan ℝ C :=
            vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ ⟨u, rfl⟩)
              (subset_convexHull ℝ _ ⟨0, rfl⟩)
          have hf0 : f (h u θs - h 0 θs) = 0 := by
            rw [← Submodule.mem_bot ℝ, ← hf_bot]
            exact Submodule.mem_map_of_mem hvsub
          rw [map_sub, hf_eval, hf_eval] at hf0
          linarith
        let Lζ : (Fin r → ℝ) →L[ℝ] ℝ :=
          LinearMap.toContinuousLinearMap
            { toFun := fun y => ζ ⬝ᵥ y
              map_add' := fun x y => dotProduct_add ζ x y
              map_smul' := fun a y => by simp [dotProduct_smul] }
        have hc0 : ζ ⬝ᵥ h 0 θs = 0 := by
          have h1 : ∫ _ : Ω, (ζ ⬝ᵥ h 0 θs) ∂μ = ∫ ω, Lζ (h (W0 ω) θs) ∂μ :=
            integral_congr_ae (Eventually.of_forall fun ω => (hconst (W0 ω)).symm)
          rw [integral_const, probReal_univ, one_smul, Lζ.integral_comp_comm hint,
            hmean, map_zero] at h1
          exact h1
        exact ⟨ζ, hζ_ne, fun u => by rw [hconst u, hc0]⟩
    obtain ⟨ζ, hζ_ne, hζ_nn⟩ := hex_ζ
    let Lζ : (Fin r → ℝ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun y => ζ ⬝ᵥ y
          map_add' := fun x y => dotProduct_add ζ x y
          map_smul' := fun a y => by simp [dotProduct_smul] }
    have hg_int : Integrable (fun ω => Lζ (h (W0 ω) θs)) μ := Lζ.integrable_comp hint
    have hg_zero : ∫ ω, Lζ (h (W0 ω) θs) ∂μ = 0 := by
      rw [Lζ.integral_comp_comm hint, hmean, map_zero]
    have hae_zero : (fun ω => Lζ (h (W0 ω) θs)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => hζ_nn (W0 ω)) hg_int).mp hg_zero
    have hae_row0 : ∀ᵐ ω ∂μ, rowNorm p h θs ζ (W0 ω) = 0 := by
      filter_upwards [hae_zero] with ω hω
      let φ : (Fin m → ℝ) → ℝ := fun x => Lζ (h x θs)
      have hmin : IsLocalMin φ (W0 ω) := by
        refine Eventually.of_forall fun x => ?_
        change Lζ (h (W0 ω) θs) ≤ Lζ (h x θs)
        have hω' : Lζ (h (W0 ω) θs) = 0 := hω
        rw [hω']
        exact hζ_nn x
      have hfderiv_φ : HasFDerivAt φ
          (Lζ.comp (fderiv ℝ (fun x => h x θs) (W0 ω))) (W0 ω) :=
        Lζ.hasFDerivAt.comp (W0 ω) (hC1.differentiable one_ne_zero (W0 ω)).hasFDerivAt
      have hzero_clm : Lζ.comp (fderiv ℝ (fun x => h x θs) (W0 ω)) = 0 := by
        rw [← hfderiv_φ.fderiv]
        exact hmin.fderiv_eq_zero
      have hrv_zero : rowVec h θs ζ (W0 ω) = 0 := by
        ext k
        have hk := congrArg (fun L : (Fin m → ℝ) →L[ℝ] ℝ => L (Pi.single k (1 : ℝ))) hzero_clm
        simpa [ContinuousLinearMap.comp_apply, Lζ, dotProduct, rowVec] using hk
      simp [rowNorm_eq_norm_rowVec, hrv_zero]
    have hprob0 : μ {ω | 0 < rowNorm p h θs ζ (W0 ω)} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hae_row0)
      change 0 < rowNorm p h θs ζ (W0 ω) at hω
      exact hω.ne'
    exact (hA4 ζ hζ_ne).ne' hprob0

/-! ### Module B1: Tie-Free Strong Duality and Finiteness of Empirical RWP (Part 1) -/

private noncomputable def evalFS {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) : (α →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.lsum ℝ (fun u => LinearMap.toSpanSingleton ℝ E (f u))

private lemma evalFS_apply {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) (p : α →₀ ℝ) :
    evalFS f p = ∑ u ∈ p.support, p u • f u := by
  simp [evalFS, Finsupp.lsum, Finsupp.sum]

private lemma evalFS_single {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) (u : α) (a : ℝ) :
    evalFS f (Finsupp.single u a) = a • f u := by
  simp [evalFS]

private def IsProbFS {m : ℕ} (p : (Fin m → ℝ) →₀ ℝ) : Prop :=
  (∀ u, 0 ≤ p u) ∧ evalFS (fun _ => (1 : ℝ)) p = 1

private lemma isProbFS_single {m : ℕ} (u : Fin m → ℝ) :
    IsProbFS (Finsupp.single u (1 : ℝ)) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [evalFS_single, smul_eq_mul, mul_one]

private lemma isProbFS_finset_sum {m : ℕ} {κ : Type*} (s : Finset κ) (wt : κ → ℝ)
    (p : κ → ((Fin m → ℝ) →₀ ℝ)) (hwt_nn : ∀ k ∈ s, 0 ≤ wt k) (hwt_sum : ∑ k ∈ s, wt k = 1)
    (hp : ∀ k ∈ s, IsProbFS (p k)) :
    IsProbFS (∑ k ∈ s, wt k • p k) := by
  refine ⟨fun u => ?_, ?_⟩
  · rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun k hk => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg (hwt_nn k hk) ((hp k hk).1 u)
  · rw [map_sum]
    calc ∑ k ∈ s, evalFS (fun _ => (1 : ℝ)) (wt k • p k)
        = ∑ k ∈ s, wt k * evalFS (fun _ => (1 : ℝ)) (p k) :=
          Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]
      _ = ∑ k ∈ s, wt k := Finset.sum_congr rfl fun k hk => by rw [(hp k hk).2, mul_one]
      _ = 1 := hwt_sum

private lemma isProbFS_convex_comb {m : ℕ} {p q : (Fin m → ℝ) →₀ ℝ}
    (hp : IsProbFS p) (hq : IsProbFS q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbFS (a • p + b • q) := by
  refine ⟨fun u => ?_, ?_⟩
  · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 u)) (mul_nonneg hb (hq.1 u))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hab]

private lemma exists_isProbFS_of_mem_convexHull {m r : ℕ} (g : (Fin m → ℝ) → (Fin r → ℝ))
    {y : Fin r → ℝ} (hy : y ∈ convexHull ℝ (Set.range g)) :
    ∃ p : (Fin m → ℝ) →₀ ℝ, IsProbFS p ∧ evalFS g p = y := by
  obtain ⟨κ, hfin, wt, z, hwt_nn, hwt_sum, hz_mem, hz_sum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hy
  let _ : Fintype κ := hfin
  choose u hu using hz_mem
  refine ⟨∑ k : κ, wt k • Finsupp.single (u k) (1 : ℝ),
    isProbFS_finset_sum Finset.univ wt (fun k => Finsupp.single (u k) 1)
      (fun k _ => hwt_nn k) hwt_sum (fun k _ => isProbFS_single (u k)), ?_⟩
  rw [map_sum]
  simp_rw [map_smul, evalFS_single, one_smul, hu]
  exact hz_sum

private noncomputable def meanH {m r n : ℕ} (g : (Fin m → ℝ) → (Fin r → ℝ)) :
    (Fin n → ((Fin m → ℝ) →₀ ℝ)) →ₗ[ℝ] (Fin r → ℝ) where
  toFun P := (1 / (n : ℝ)) • ∑ i : Fin n, evalFS g (P i)
  map_add' P Q := by simp [Finset.sum_add_distrib, smul_add]
  map_smul' a P := by simp [Finset.smul_sum, smul_smul, mul_comm]

private noncomputable def meanC {m n : ℕ} (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (w : Fin n → (Fin m → ℝ)) :
    (Fin n → ((Fin m → ℝ) →₀ ℝ)) →ₗ[ℝ] ℝ where
  toFun P := (1 / (n : ℝ)) * ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (P i)
  map_add' P Q := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' a P := by
    dsimp
    have hsum : ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (a • P i) =
        a * ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (P i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hsum]; ring

private lemma meanC_nonneg {m n : ℕ} (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (w : Fin n → (Fin m → ℝ)) {P : Fin n → ((Fin m → ℝ) →₀ ℝ)}
    (hP : ∀ i, IsProbFS (P i)) :
    0 ≤ meanC c w P := by
  simp only [meanC, LinearMap.coe_mk, AddHom.coe_mk, evalFS_apply, smul_eq_mul]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  exact Finset.sum_nonneg fun u _ => mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg

private lemma rwp_le_meanC {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (hc_lsc : LowerSemicontinuous (Function.uncurry c)) (hc_fin : ∀ u v, c u v ≠ ⊤)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (P : Fin n → ((Fin m → ℝ) →₀ ℝ)) (hP : ∀ i, IsProbFS (P i))
    (hP_zero : meanH (fun u => h u θ) P = 0) :
    rwp c h θ (empiricalDistribution w) ≤ ENNReal.ofReal (meanC c w P) := by
  have hn_ne0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hsum_wt : ∀ i : Fin n, ∑ u ∈ (P i).support, ENNReal.ofReal (P i u) = 1 := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => (hP i).1 u)]
    have h1 : ∑ u ∈ (P i).support, P i u = 1 := by
      have := (hP i).2
      rwa [evalFS_apply, ← Finset.sum_smul, smul_eq_mul, mul_one] at this
    rw [h1, ENNReal.ofReal_one]
  let μP : Measure (Fin m → ℝ) :=
    (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, ∑ u ∈ (P i).support, ENNReal.ofReal (P i u) • Measure.dirac u
  let πP : Measure ((Fin m → ℝ) × (Fin m → ℝ)) :=
    (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, ∑ u ∈ (P i).support,
      ENNReal.ofReal (P i u) • Measure.dirac (u, w i)
  have hπ_prob : IsProbabilityMeasure πP := by
    refine ⟨?_⟩
    simp only [πP, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, hsum_wt,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hn_ne0 hn_ne_top
  have hπ_fst : πP.map Prod.fst = μP := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS]
    simp only [πP, μP, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply' _ (hS.preimage measurable_fst), Measure.dirac_apply' _ hS]
    rfl
  have hπ_snd : πP.map Prod.snd = empiricalDistribution w := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS]
    simp only [πP, empiricalDistribution, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdir : ∀ u : Fin m → ℝ,
        Measure.dirac (u, w i) (Prod.snd ⁻¹' S) = Measure.dirac (w i) S := fun u => by
      rw [Measure.dirac_apply' _ (hS.preimage measurable_snd), Measure.dirac_apply' _ hS]
      rfl
    simp_rw [hdir, ← Finset.sum_mul, hsum_wt i, one_mul]
  have hμ_prob : IsProbabilityMeasure μP := by
    rw [← hπ_fst]; exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ_int : Integrable (fun u => h u θ) μP := by
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr hn_ne0)
    refine integrable_finsetSum_measure.mpr fun i _ => ?_
    refine integrable_finsetSum_measure.mpr fun u _ => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hμ_mean : ∫ u, h u θ ∂μP = 0 := by
    have hcalc : ∫ u, h u θ ∂μP = meanH (fun u => h u θ) P := by
      simp only [μP, meanH, LinearMap.coe_mk, AddHom.coe_mk, evalFS_apply]
      rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_eq_one_div,
        integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr fun u _ =>
          (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum_measure (fun u _ =>
        (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ((hP i).1 u)]
    rw [hcalc, hP_zero]
  have hcost_π : ∫⁻ z, c z.1 z.2 ∂πP = ENNReal.ofReal (meanC c w P) := by
    dsimp [πP]
    rw [lintegral_smul_measure, lintegral_finsetSum_measure]
    have hinner : ∀ i : Fin n,
        ∫⁻ z, c z.1 z.2 ∂(∑ u ∈ (P i).support, ENNReal.ofReal (P i u) • Measure.dirac (u, w i)) =
        ENNReal.ofReal (evalFS (fun u => (c u (w i)).toReal) (P i)) := by
      intro i
      rw [lintegral_finsetSum_measure, evalFS_apply]
      simp only [smul_eq_mul]
      rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hdirac : ∫⁻ z, c z.1 z.2 ∂Measure.dirac (u, w i) = c u (w i) :=
        lintegral_dirac' (u, w i)
          (hc_lsc.measurable : Measurable fun z : (Fin m → ℝ) × (Fin m → ℝ) => c z.1 z.2)
      rw [lintegral_smul_measure, hdirac,
        ENNReal.ofReal_mul ((hP i).1 u), ENNReal.ofReal_toReal (hc_fin u (w i)), smul_eq_mul]
    simp_rw [hinner]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      rw [evalFS_apply]
      exact Finset.sum_nonneg fun u _ => mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg)]
    dsimp [meanC]
    have hn_inv : (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (n : ℝ)) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hn), ENNReal.ofReal_natCast]
    rw [hn_inv, ← ENNReal.ofReal_mul (by positivity)]
  calc rwp c h θ (empiricalDistribution w)
      ≤ transportCost c μP (empiricalDistribution w) :=
        iInf₂_le μP ⟨hμ_prob, hμ_int, hμ_mean⟩
    _ ≤ ∫⁻ z, c z.1 z.2 ∂πP := iInf₂_le πP ⟨hπ_prob, hπ_fst, hπ_snd⟩
    _ = ENNReal.ofReal (meanC c w P) := hcost_π

private lemma costQ_continuous {m : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] {ρ : ℝ} (hρ : 1 ≤ ρ) :
    Continuous (Function.uncurry (@costQ m q ρ)) := by
  have hρ_pos : 0 < ρ := zero_lt_one.trans_le hρ
  have hnorm_cont : Continuous (fun uv : (Fin m → ℝ) × (Fin m → ℝ) =>
      ‖WithLp.toLp q (uv.2 - uv.1)‖ ^ ρ) :=
    (continuous_norm.comp ((PiLp.continuous_toLp q _).comp
      (continuous_snd.sub continuous_fst))).rpow_const (fun _ => Or.inr hρ_pos.le)
  exact ENNReal.continuous_ofReal.comp hnorm_cont

private lemma rwp_costQ_lt_top {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (h0_ch : (0 : Fin r → ℝ) ∈ convexHull ℝ (Set.range fun u => h u θs)) :
    rwp (costQ q ρ) h θs (empiricalDistribution w) < ⊤ := by
  obtain ⟨q0, hq0_prob, hq0_mean⟩ := exists_isProbFS_of_mem_convexHull (fun u => h u θs) h0_ch
  let P0 : Fin n → ((Fin m → ℝ) →₀ ℝ) := fun _ => q0
  have hP0_zero : meanH (fun u => h u θs) P0 = 0 := by simp [meanH, P0, hq0_mean]
  have hle := rwp_le_meanC hn w (costQ q ρ) (costQ_continuous q hρ).lowerSemicontinuous
    (fun _ _ => ENNReal.ofReal_ne_top) h θs P0 (fun _ => hq0_prob) hP0_zero
  exact hle.trans_lt ENNReal.ofReal_lt_top

private lemma ereal_add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ := by
  cases x <;> cases y <;> simp_all

private lemma finset_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ereal_add_ne_bot (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma finset_sum_coe_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

private lemma ereal_finset_sum_le_sum {ι : Type*} (s : Finset ι) (f g : ι → EReal)
    (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact add_le_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma ereal_mul_mono_of_pos {c : ℝ} (hc : 0 < c) {x y : EReal} (hxy : x ≤ y) :
    ((c : ℝ) : EReal) * x ≤ ((c : ℝ) : EReal) * y := by
  cases x with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_le
  | coe a =>
    cases y with
    | bot => exact absurd (le_bot_iff.mp hxy) (EReal.coe_ne_bot a)
    | coe b =>
      rw [← EReal.coe_mul, ← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hxy) hc.le)
    | top => rw [EReal.coe_mul_top_of_pos hc]; exact le_top
  | top => rw [top_le_iff.mp hxy]

private lemma ereal_sub_le_of_le {x y z : ℝ} {M : EReal} (hxz : x - y ≤ z)
    (hyM : ((y : ℝ) : EReal) ≤ M) :
    ((x : ℝ) : EReal) - M ≤ ((z : ℝ) : EReal) := by
  cases M with
  | bot => exact absurd (le_bot_iff.mp hyM) (EReal.coe_ne_bot y)
  | coe m =>
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_le_coe_iff.mp hyM])
  | top => simp

private lemma coe_real_le_ennreal_toEReal (d : ℝ) {x : ℝ≥0∞} (h : ENNReal.ofReal d ≤ x) :
    ((d : ℝ) : EReal) ≤ (x : EReal) := by
  rcases le_or_gt d 0 with hd | hd
  · exact (EReal.coe_le_coe_iff.mpr hd).trans (EReal.coe_ennreal_nonneg x)
  · have hd_eq : ((d : ℝ) : EReal) = (ENNReal.ofReal d : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hd.le]
    rw [hd_eq]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h

private lemma prop3_tie_free {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (c : (Fin m → ℝ) → (Fin m → ℝ) → ENNReal)
    (hc_lsc : LowerSemicontinuous (Function.uncurry c))
    (hc_diag : ∀ u, c u u = 0) (hc_fin : ∀ u v, c u v ≠ ⊤)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (hmeas : Measurable fun u => h u θ)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θ))) :
    (rwp c h θ (empiricalDistribution w) : EReal) =
      ⨆ lam : Fin r → ℝ, -(((1 / (n : ℝ) : ℝ) : EReal) *
        ∑ i, ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u (w i) : EReal))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let Pn := empiricalDistribution w
  let R := rwp c h θ Pn
  let φ : (Fin r → ℝ) → (Fin m → ℝ) → EReal := fun lam v =>
    ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal))
  have hφ_sub : ∀ (lam : Fin r → ℝ) (u v : Fin m → ℝ),
      (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal)) =
        (((lam ⬝ᵥ h u θ - (c u v).toReal : ℝ) : EReal)) := by
    intro lam u v
    have hcv : (c u v : EReal) = (((c u v).toReal : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal (hc_fin u v)]
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
    rw [hcv, ← EReal.coe_sub]
  have hφ_ne_bot : ∀ (lam : Fin r → ℝ) (v : Fin m → ℝ), φ lam v ≠ ⊥ := by
    intro lam v
    have hle : (((lam ⬝ᵥ h v θ : ℝ) : EReal) - (c v v : EReal)) ≤ φ lam v :=
      le_iSup (fun u : Fin m → ℝ => (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal))) v
    rw [hc_diag v] at hle
    have hbot : (((lam ⬝ᵥ h v θ : ℝ) : EReal) - (0 : ℝ≥0∞)) ≠ ⊥ := by simp
    intro h_eq; rw [h_eq] at hle; exact hbot (le_bot_iff.mp hle)
  apply le_antisymm
  · have h0_ch : (0 : Fin r → ℝ) ∈ convexHull ℝ (Set.range fun u => h u θ) :=
      interior_subset hint
    obtain ⟨q0, hq0_prob, hq0_mean⟩ := exists_isProbFS_of_mem_convexHull (fun u => h u θ) h0_ch
    let P0 : Fin n → ((Fin m → ℝ) →₀ ℝ) := fun _ => q0
    have hP0_prob : ∀ i, IsProbFS (P0 i) := fun _ => hq0_prob
    have hP0_zero : meanH (fun u => h u θ) P0 = 0 := by simp [meanH, P0, hq0_mean]
    have hR_le_P0 : R ≤ ENNReal.ofReal (meanC c w P0) :=
      rwp_le_meanC hn w c hc_lsc hc_fin h θ P0 hP0_prob hP0_zero
    have hR_lt_top : R < ⊤ := hR_le_P0.trans_lt ENNReal.ofReal_lt_top
    let α_opt : ℝ := R.toReal
    have hR_ereal : (R : EReal) = ((α_opt : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hR_lt_top.ne]
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
    let K : Set ((Fin r → ℝ) × ℝ) := {yt | ∃ P : Fin n → ((Fin m → ℝ) →₀ ℝ),
      (∀ i, IsProbFS (P i)) ∧ meanH (fun u => h u θ) P = yt.1 ∧ meanC c w P < yt.2}
    have hK_conv : Convex ℝ K := by
      rintro ⟨y1, t1⟩ ⟨P1, hP1, hy1, ht1⟩ ⟨y2, t2⟩ ⟨P2, hP2, hy2, ht2⟩ a b ha hb hab
      refine ⟨a • P1 + b • P2,
        fun i => isProbFS_convex_comb (hP1 i) (hP2 i) ha hb hab, ?_, ?_⟩
      · simp [map_add, map_smul, hy1, hy2]
      · simp only [map_add, map_smul, smul_eq_mul, Prod.smul_snd, Prod.snd_add]
        rcases ha.eq_or_lt with rfl | ha_pos
        · simp only [zero_add] at hab; subst hab; linarith
        · nlinarith
    have hnot_mem : ((0 : Fin r → ℝ), α_opt) ∉ K := by
      rintro ⟨P, hP_prob, hP_zero, hP_lt⟩
      have hle : R ≤ ENNReal.ofReal (meanC c w P) :=
        rwp_le_meanC hn w c hc_lsc hc_fin h θ P hP_prob hP_zero
      have hnn : 0 ≤ meanC c w P := meanC_nonneg c w hP_prob
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      rw [ENNReal.toReal_ofReal hnn] at h1
      linarith
    obtain ⟨δ₀, hδ₀_pos, hball_sub⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    let δ₁ : ℝ := δ₀ / 2
    have hδ₁_pos : 0 < δ₁ := half_pos hδ₀_pos
    have hpos_ch : ∀ j : Fin r,
        δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ) ∈ convexHull ℝ (Set.range fun u => h u θ) := by
      intro j; apply hball_sub
      rw [Metric.mem_ball, dist_zero_right]
      have hnorm : ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
        rw [Pi.single_apply]; split_ifs <;> simp
      calc ‖δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)‖
          = δ₁ * ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ₁_pos]
        _ ≤ δ₁ * 1 := mul_le_mul_of_nonneg_left hnorm hδ₁_pos.le
        _ < δ₀ := by dsimp [δ₁]; linarith
    have hneg_ch : ∀ j : Fin r,
        -(δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)) ∈ convexHull ℝ (Set.range fun u => h u θ) := by
      intro j; apply hball_sub
      rw [Metric.mem_ball, dist_zero_right, norm_neg]
      have hnorm : ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
        rw [Pi.single_apply]; split_ifs <;> simp
      calc ‖δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)‖
          = δ₁ * ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ₁_pos]
        _ ≤ δ₁ * 1 := mul_le_mul_of_nonneg_left hnorm hδ₁_pos.le
        _ < δ₀ := by dsimp [δ₁]; linarith
    choose q_pos hq_pos_prob hq_pos_mean using fun j =>
      exists_isProbFS_of_mem_convexHull (fun u => h u θ) (hpos_ch j)
    choose q_neg hq_neg_prob hq_neg_mean using fun j =>
      exists_isProbFS_of_mem_convexHull (fun u => h u θ) (hneg_ch j)
    let P_pos : Fin r → Fin n → ((Fin m → ℝ) →₀ ℝ) := fun j _ => q_pos j
    let P_neg : Fin r → Fin n → ((Fin m → ℝ) →₀ ℝ) := fun j _ => q_neg j
    have hP_pos_mean : ∀ j : Fin r, meanH (fun u => h u θ) (P_pos j) =
        δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ) := fun j => by
      ext k
      simp only [meanH, LinearMap.coe_mk, AddHom.coe_mk, P_pos, hq_pos_mean j,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hn_pos.ne']
    have hP_neg_mean : ∀ j : Fin r, meanH (fun u => h u θ) (P_neg j) =
        -(δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)) := fun j => by
      ext k
      simp only [meanH, LinearMap.coe_mk, AddHom.coe_mk, P_neg, hq_neg_mean j,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp [hn_pos.ne']
    have hC0_nn : 0 ≤ meanC c w P0 := meanC_nonneg c w hP0_prob
    have hCpos_nn : ∀ j : Fin r, 0 ≤ meanC c w (P_pos j) := fun j =>
      meanC_nonneg c w (fun _ => hq_pos_prob j)
    have hCneg_nn : ∀ j : Fin r, 0 ≤ meanC c w (P_neg j) := fun j =>
      meanC_nonneg c w (fun _ => hq_neg_prob j)
    let M : ℝ := meanC c w P0 +
      ∑ j : Fin r, (meanC c w (P_pos j) + meanC c w (P_neg j))
    have hC0_le_M : meanC c w P0 ≤ M := by
      dsimp [M]
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => add_nonneg (hCpos_nn j) (hCneg_nn j)]
    have hCpos_le_M : ∀ j : Fin r, meanC c w (P_pos j) ≤ M := fun j => by
      have hsingle := Finset.single_le_sum
        (f := fun k => meanC c w (P_pos k) + meanC c w (P_neg k))
        (fun k _ => add_nonneg (hCpos_nn k) (hCneg_nn k)) (Finset.mem_univ j)
      dsimp [M]; linarith [hC0_nn, hCneg_nn j]
    have hCneg_le_M : ∀ j : Fin r, meanC c w (P_neg j) ≤ M := fun j => by
      have hsingle := Finset.single_le_sum
        (f := fun k => meanC c w (P_pos k) + meanC c w (P_neg k))
        (fun k _ => add_nonneg (hCpos_nn k) (hCneg_nn k)) (Finset.mem_univ j)
      dsimp [M]; linarith [hC0_nn, hCpos_nn j]
    let U : Set ((Fin r → ℝ) × ℝ) := {y : Fin r → ℝ | ∑ j : Fin r, |y j| < δ₁} ×ˢ Set.Ioi M
    have hU_open : IsOpen U :=
      (isOpen_lt (continuous_finsetSum Finset.univ fun j _ =>
        continuous_abs.comp (continuous_apply j)) continuous_const).prod isOpen_Ioi
    have h0M_mem_U : ((0 : Fin r → ℝ), M + 1) ∈ U := ⟨by simp [hδ₁_pos], by change M < M + 1; linarith⟩
    have hU_sub_K : U ⊆ K := by
      rintro ⟨y, t⟩ ⟨hy_lt, ht_gt⟩
      change ∑ j : Fin r, |y j| < δ₁ at hy_lt
      change M < t at ht_gt
      let a_pos : Fin r → ℝ := fun j => max (y j / δ₁) 0
      let a_neg : Fin r → ℝ := fun j => max (-y j / δ₁) 0
      have hap_nn : ∀ j, 0 ≤ a_pos j := fun _ => le_max_right _ _
      have han_nn : ∀ j, 0 ≤ a_neg j := fun _ => le_max_right _ _
      have hap_add : ∀ j, a_pos j + a_neg j = |y j| / δ₁ := fun j => by
        dsimp [a_pos, a_neg]
        rcases le_or_gt 0 (y j) with hj | hj
        · rw [max_eq_left (div_nonneg hj hδ₁_pos.le),
            max_eq_right (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hj) hδ₁_pos.le),
            add_zero, abs_of_nonneg hj]
        · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hj.le hδ₁_pos.le),
            max_eq_left (div_nonneg (neg_nonneg.mpr hj.le) hδ₁_pos.le),
            zero_add, abs_of_neg hj]
      have hap_sub : ∀ j, a_pos j - a_neg j = y j / δ₁ := fun j => by
        dsimp [a_pos, a_neg]
        rcases le_or_gt 0 (y j) with hj | hj
        · rw [max_eq_left (div_nonneg hj hδ₁_pos.le),
            max_eq_right (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hj) hδ₁_pos.le), sub_zero]
        · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hj.le hδ₁_pos.le),
            max_eq_left (div_nonneg (neg_nonneg.mpr hj.le) hδ₁_pos.le)]; ring
      let a0 : ℝ := 1 - ∑ j : Fin r, (a_pos j + a_neg j)
      have ha0_pos : 0 < a0 := by
        dsimp [a0]
        have hsum_eq : ∑ j : Fin r, (a_pos j + a_neg j) = (∑ j : Fin r, |y j|) / δ₁ := by
          simp_rw [hap_add, ← Finset.sum_div]
        rw [hsum_eq, sub_pos, div_lt_one hδ₁_pos]; exact hy_lt
      have hwt_one : a0 + ∑ j : Fin r, a_pos j + ∑ j : Fin r, a_neg j = 1 := by
        dsimp [a0]; rw [Finset.sum_add_distrib]; ring
      let Py : Fin n → ((Fin m → ℝ) →₀ ℝ) :=
        a0 • P0 + ∑ j : Fin r, a_pos j • P_pos j + ∑ j : Fin r, a_neg j • P_neg j
      refine ⟨Py, ?_, ?_, ?_⟩
      · intro i
        refine ⟨fun u => ?_, ?_⟩
        · simp only [Py, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finsupp.coe_add,
            Finsupp.coe_smul, Finsupp.finsetSum_apply, smul_eq_mul]
          refine add_nonneg (add_nonneg (mul_nonneg ha0_pos.le (hq0_prob.1 u)) ?_) ?_
          · exact Finset.sum_nonneg fun j _ => mul_nonneg (hap_nn j) ((hq_pos_prob j).1 u)
          · exact Finset.sum_nonneg fun j _ => mul_nonneg (han_nn j) ((hq_neg_prob j).1 u)
        · simp only [Py, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_add, map_smul,
            map_sum, smul_eq_mul, P0, P_pos, P_neg, hq0_prob.2,
            fun j => (hq_pos_prob j).2, fun j => (hq_neg_prob j).2, mul_one]
          exact hwt_one
      · simp only [Py, map_add, map_smul, map_sum, hP0_zero, smul_zero, zero_add,
          hP_pos_mean, hP_neg_mean]
        ext k
        let e : Fin r → (Fin r → ℝ) := fun j => Pi.single j (1 : ℝ)
        change (∑ j : Fin r, a_pos j • (δ₁ • e j)) k + (∑ j : Fin r, a_neg j • -(δ₁ • e j)) k = y k
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_neg]
        rw [← Finset.sum_add_distrib]
        have hk : ∑ j : Fin r, (a_pos j * (δ₁ * e j k) + -(a_neg j * (δ₁ * e j k))) =
            ∑ j : Fin r, ((a_pos j - a_neg j) * δ₁) * e j k :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [hk]
        simp_rw [hap_sub, div_mul_cancel₀ _ hδ₁_pos.ne']
        rw [Finset.sum_eq_single k]
        · simp [e]
        · intro j _ hjk; simp [e, Pi.single_eq_of_ne hjk.symm]
        · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
      · simp only [Py, map_add, map_smul, map_sum, smul_eq_mul]
        have h0 : a0 * meanC c w P0 ≤ a0 * M := mul_le_mul_of_nonneg_left hC0_le_M ha0_pos.le
        have hp : ∑ j : Fin r, a_pos j * meanC c w (P_pos j) ≤ (∑ j : Fin r, a_pos j) * M := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hCpos_le_M j) (hap_nn j)
        have hn' : ∑ j : Fin r, a_neg j * meanC c w (P_neg j) ≤ (∑ j : Fin r, a_neg j) * M := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hCneg_le_M j) (han_nn j)
        have hM_sum : a0 * M + (∑ j : Fin r, a_pos j) * M + (∑ j : Fin r, a_neg j) * M = M := by
          calc a0 * M + (∑ j : Fin r, a_pos j) * M + (∑ j : Fin r, a_neg j) * M
              = (a0 + ∑ j : Fin r, a_pos j + ∑ j : Fin r, a_neg j) * M := by ring
            _ = 1 * M := by rw [hwt_one]
            _ = M := one_mul M
        have hle_M : a0 * meanC c w P0 + ∑ j : Fin r, a_pos j * meanC c w (P_pos j) +
            ∑ j : Fin r, a_neg j * meanC c w (P_neg j) ≤ M := by linarith
        exact hle_M.trans_lt ht_gt
    have h0M_int : ((0 : Fin r → ℝ), M + 1) ∈ interior K :=
      mem_interior.mpr ⟨U, hU_sub_K, hU_open, h0M_mem_U⟩
    obtain ⟨f, u_sep, hf_ne, hf_le, hf_ge⟩ :=
      geometric_hahn_banach_of_nonempty_interior hK_conv
        (convex_singleton ((0 : Fin r → ℝ), α_opt))
        (Set.disjoint_singleton_right.mpr fun h => hnot_mem (interior_subset h))
        ⟨((0 : Fin r → ℝ), M + 1), h0M_int⟩ (Set.singleton_nonempty _)
    let L : StrongDual ℝ ((Fin r → ℝ) × ℝ) := -f
    have hL_ne : L ≠ 0 := neg_ne_zero.mpr hf_ne
    have hL_sep : ∀ z ∈ K, L ((0 : Fin r → ℝ), α_opt) ≤ L z := fun z hz => by
      change -f ((0 : Fin r → ℝ), α_opt) ≤ -f z
      linarith [hf_le z hz, hf_ge _ rfl]
    let μ_vec : Fin r → ℝ := fun j => L (Pi.single j 1, 0)
    let γ : ℝ := L (0, 1)
    have hL_eval : ∀ (y : Fin r → ℝ) (t : ℝ), L (y, t) = μ_vec ⬝ᵥ y + γ * t := fun y t => by
      let e : Fin r → (Fin r → ℝ) := fun j => Pi.single j (1 : ℝ)
      have hy_eq : y = ∑ j : Fin r, y j • e j := by
        ext k; rw [Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single k]
        · simp [e]
        · intro j _ hjk; simp [e, Pi.single_eq_of_ne hjk.symm]
        · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
      have hdecomp : (y, t) = ∑ j : Fin r, y j • (e j, (0 : ℝ)) +
          t • ((0 : Fin r → ℝ), (1 : ℝ)) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, ← hy_eq]
        · simp [Prod.snd_sum]
      rw [hdecomp, map_add, map_sum, map_smul, smul_eq_mul, mul_comm t γ]
      congr 1
      change ∑ j : Fin r, L (y j • (e j, 0)) = ∑ j : Fin r, μ_vec j * y j
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have hα_le_C0 : α_opt ≤ meanC c w P0 := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hR_le_P0
      rwa [ENNReal.toReal_ofReal hC0_nn] at h1
    have hα_lt_M1 : α_opt < M + 1 := by linarith [hC0_le_M]
    have hγ_nonneg : 0 ≤ γ := by
      have hsep0 := hL_sep _ (hU_sub_K h0M_mem_U)
      rw [hL_eval, hL_eval, dotProduct_zero, zero_add, zero_add] at hsep0
      nlinarith
    have hγ_pos : 0 < γ := by
      rcases hγ_nonneg.eq_or_lt with hγ0 | hγ_pos
      · exfalso
        have hex_j : ∃ j₀ : Fin r, μ_vec j₀ ≠ 0 := by
          by_contra h_all; push Not at h_all; apply hL_ne
          refine ContinuousLinearMap.ext fun ⟨y, t⟩ => ?_
          simp [hL_eval, dotProduct, h_all, ← hγ0]
        obtain ⟨j₀, hj₀⟩ := hex_j
        let s : ℝ := if 0 ≤ μ_vec j₀ then -(δ₁ / 2) else δ₁ / 2
        have hs_abs : |s| = δ₁ / 2 := by
          dsimp [s]; split_ifs <;> simp [abs_of_pos (half_pos hδ₁_pos)]
        have hs_mul : μ_vec j₀ * s < 0 := by
          dsimp [s]; split_ifs with hsign
          · have : 0 < μ_vec j₀ := lt_of_le_of_ne hsign hj₀.symm; nlinarith
          · have : μ_vec j₀ < 0 := lt_of_not_ge hsign; nlinarith
        let y_test : Fin r → ℝ := Pi.single j₀ s
        have hy_U : (y_test, M + 1) ∈ U := by
          refine ⟨?_, by change M < M + 1; linarith⟩
          change ∑ j : Fin r, |y_test j| < δ₁
          rw [Finset.sum_eq_single j₀]
          · simp only [y_test, Pi.single_eq_same, hs_abs]; linarith
          · intro j _ hjj₀; simp [y_test, Pi.single_eq_of_ne hjj₀]
          · intro h_abs; exact absurd (Finset.mem_univ j₀) h_abs
        have hsep_test := hL_sep _ (hU_sub_K hy_U)
        simp only [hL_eval, ← hγ0, dotProduct_zero, zero_mul, add_zero, y_test,
          dotProduct_single] at hsep_test
        linarith
      · exact hγ_pos
    let lam : Fin r → ℝ := -(γ⁻¹ • μ_vec)
    have htuple_bound : ∀ u_tup : Fin n → (Fin m → ℝ),
        (1 / (n : ℝ)) * ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ - (c (u_tup i) (w i)).toReal) ≤
          -α_opt := fun u_tup => by
      let Pu : Fin n → ((Fin m → ℝ) →₀ ℝ) := fun i => Finsupp.single (u_tup i) 1
      have hPu_prob : ∀ i, IsProbFS (Pu i) := fun i => isProbFS_single (u_tup i)
      have hPu_H : meanH (fun u => h u θ) Pu = (1 / (n : ℝ)) • ∑ i : Fin n, h (u_tup i) θ := by
        simp [meanH, Pu, evalFS_single]
      have hPu_C : meanC c w Pu = (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal := by
        simp [meanC, Pu, evalFS_single]
      have hineq : γ * α_opt ≤ μ_vec ⬝ᵥ meanH (fun u => h u θ) Pu + γ * meanC c w Pu := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have hmem : (meanH (fun u => h u θ) Pu, meanC c w Pu + ε / γ) ∈ K :=
          ⟨Pu, hPu_prob, rfl, by linarith [div_pos hε hγ_pos]⟩
        have hsep_u := hL_sep _ hmem
        rw [hL_eval, hL_eval, dotProduct_zero, zero_add, mul_add,
          mul_div_cancel₀ _ hγ_pos.ne'] at hsep_u
        linarith
      rw [hPu_H, hPu_C, dotProduct_smul, smul_eq_mul, dotProduct_sum] at hineq
      have hlam_dot : ∀ i : Fin n, μ_vec ⬝ᵥ h (u_tup i) θ = -γ * (lam ⬝ᵥ h (u_tup i) θ) := by
        intro i; simp only [lam, neg_dotProduct, smul_dotProduct, smul_eq_mul]
        field_simp [hγ_pos.ne']
      simp_rw [hlam_dot, ← Finset.mul_sum] at hineq
      have hdiv : α_opt ≤ -(1 / (n : ℝ)) * ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ) +
          (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal :=
        le_of_mul_le_mul_left (by linarith) hγ_pos
      have hcomb : (1 / (n : ℝ)) * ∑ i : Fin n,
          (lam ⬝ᵥ h (u_tup i) θ - (c (u_tup i) (w i)).toReal) =
          (1 / (n : ℝ)) * ∑ i : Fin n, lam ⬝ᵥ h (u_tup i) θ -
          (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal := by
        rw [Finset.sum_sub_distrib, mul_sub]
      linarith
    have hφ_ne_top : ∀ i₀ : Fin n, φ lam (w i₀) ≠ ⊤ := by
      classical
      intro i₀
      let B : ℝ := n * (-α_opt) -
        ∑ i ∈ Finset.univ.erase i₀, (lam ⬝ᵥ h (w i) θ - (c (w i) (w i)).toReal)
      have hle_B : φ lam (w i₀) ≤ ((B : ℝ) : EReal) := by
        refine iSup_le fun x => ?_
        rw [hφ_sub]
        refine EReal.coe_le_coe_iff.mpr ?_
        have hb := htuple_bound (Function.update w i₀ x)
        have hsum_upd : ∑ i : Fin n,
            (lam ⬝ᵥ h (Function.update w i₀ x i) θ -
              (c (Function.update w i₀ x i) (w i)).toReal) =
            (lam ⬝ᵥ h x θ - (c x (w i₀)).toReal) +
            ∑ i ∈ Finset.univ.erase i₀, (lam ⬝ᵥ h (w i) θ - (c (w i) (w i)).toReal) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
          congr 1
          · simp
          · refine Finset.sum_congr rfl fun i hi => ?_
            simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        rw [hsum_upd] at hb
        have hb' := mul_le_mul_of_nonneg_left hb hn_pos.le
        rw [← mul_assoc, mul_one_div_cancel hn_pos.ne', one_mul] at hb'
        dsimp [B]; linarith
      intro htop; rw [htop] at hle_B; exact EReal.coe_ne_top B (top_le_iff.mp hle_B)
    let s_val : Fin n → ℝ := fun i => (φ lam (w i)).toReal
    have hφ_eq_s : ∀ i : Fin n, φ lam (w i) = ((s_val i : ℝ) : EReal) := fun i =>
      (EReal.coe_toReal (hφ_ne_top i) (hφ_ne_bot lam (w i))).symm
    have hmean_s : (1 / (n : ℝ)) * ∑ i : Fin n, s_val i ≤ -α_opt := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      have hex_u : ∀ i : Fin n, ∃ u_i : Fin m → ℝ,
          s_val i - η < lam ⬝ᵥ h u_i θ - (c u_i (w i)).toReal := fun i => by
        have hlt : (((s_val i - η : ℝ) : EReal)) < φ lam (w i) := by
          rw [hφ_eq_s i]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
        obtain ⟨u_i, hu_i⟩ := lt_iSup_iff.mp hlt
        rw [hφ_sub] at hu_i
        exact ⟨u_i, EReal.coe_lt_coe_iff.mp hu_i⟩
      choose u_tup hu_tup using hex_u
      have hsum_lt := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hu_tup i).le
      have havg := (mul_le_mul_of_nonneg_left hsum_lt (by positivity : 0 ≤ 1 / (n : ℝ))).trans
        (htuple_bound u_tup)
      have hsub_η : (1 / (n : ℝ)) * ∑ i : Fin n, (s_val i - η) =
          (1 / (n : ℝ)) * ∑ i : Fin n, s_val i - η := by
        rw [Finset.sum_sub_distrib, mul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, one_div_mul_cancel hn_pos.ne', one_mul]
      linarith
    calc (R : EReal) = ((α_opt : ℝ) : EReal) := hR_ereal
      _ ≤ ((-((1 / (n : ℝ)) * ∑ i : Fin n, s_val i) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
      _ = -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam (w i)) := by
          simp_rw [hφ_eq_s]
          rw [finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg]
      _ ≤ ⨆ lam' : Fin r → ℝ, -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam' (w i)) :=
          le_iSup (fun lam' : Fin r → ℝ =>
            -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam' (w i))) lam
  · refine iSup_le fun lam => ?_
    by_cases htop : ∃ i₀ : Fin n, φ lam (w i₀) = ⊤
    · obtain ⟨i₀, hi₀⟩ := htop
      have hsum_top : ∑ i : Fin n, φ lam (w i) = ⊤ := by
        classical
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hi₀]
        exact EReal.top_add_of_ne_bot (finset_sum_ne_bot _ _ fun i _ => hφ_ne_bot lam (w i))
      rw [hsum_top, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos), EReal.neg_top]
      exact bot_le
    · push Not at htop
      classical
      let W_fin : Finset (Fin m → ℝ) := Finset.univ.image w
      let g : (Fin m → ℝ) → ℝ := fun v => if v ∈ W_fin then (φ lam v).toReal else 0
      have hg_w : ∀ i : Fin n, g (w i) = (φ lam (w i)).toReal := fun i =>
        if_pos (Finset.mem_image_of_mem w (Finset.mem_univ i))
      have hφ_eq_g : ∀ i : Fin n, φ lam (w i) = ((g (w i) : ℝ) : EReal) := fun i => by
        rw [hg_w i]; exact (EReal.coe_toReal (htop i) (hφ_ne_bot lam (w i))).symm
      have hlhs_eq : -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam (w i)) =
          ((-((1 / (n : ℝ)) * ∑ i : Fin n, g (w i)) : ℝ) : EReal) := by
        simp_rw [hφ_eq_g]; rw [finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg]
      rw [hlhs_eq]
      refine coe_real_le_ennreal_toEReal _ ?_
      refine le_iInf₂ fun P ⟨_, hP_int, hP_mean⟩ => ?_
      refine le_iInf₂ fun π ⟨_, hπ_fst, hπ_snd⟩ => ?_
      by_cases hc_top : ∫⁻ z, c z.1 z.2 ∂π = ⊤
      · rw [hc_top]; exact le_top
      have hc_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => (c z.1 z.2).toReal) π :=
        integrable_toReal_of_lintegral_ne_top hc_lsc.measurable.aemeasurable hc_top
      have hc_int_eq : ∫ z, (c z.1 z.2).toReal ∂π = (∫⁻ z, c z.1 z.2 ∂π).toReal :=
        integral_toReal hc_lsc.measurable.aemeasurable
          (Eventually.of_forall fun z => (hc_fin z.1 z.2).lt_top)
      have hW_meas : MeasurableSet (W_fin : Set (Fin m → ℝ)) := W_fin.measurableSet
      have hg_meas : Measurable g := by
        have hg_sum : g = fun v =>
            ∑ y ∈ W_fin, Set.indicator {y} (fun _ => (φ lam y).toReal) v := by
          ext v; dsimp [g]; split_ifs with hv
          · rw [Finset.sum_eq_single v]
            · simp
            · intro y _ hyv; simp [Set.indicator_of_notMem, hyv.symm]
            · intro h_abs; exact absurd hv h_abs
          · rw [Finset.sum_eq_zero]; intro y hy
            have hvy : v ≠ y := fun h_eq => hv (h_eq ▸ hy)
            simp [Set.indicator_of_notMem, hvy]
        rw [hg_sum]
        exact Finset.measurable_sum W_fin fun y _ =>
          measurable_const.indicator (measurableSet_singleton y)
      obtain ⟨Mg, hMg⟩ : ∃ Mg : ℝ, ∀ v : Fin m → ℝ, ‖g v‖ ≤ Mg := by
        refine ⟨∑ y ∈ W_fin, |(φ lam y).toReal|, fun v => ?_⟩
        rw [Real.norm_eq_abs]; dsimp [g]; split_ifs with hv
        · exact Finset.single_le_sum (f := fun y => |(φ lam y).toReal|)
            (fun _ _ => abs_nonneg _) hv
        · rw [abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hg_π_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => g z.2) π :=
        Integrable.of_bound (hg_meas.comp measurable_snd).aestronglyMeasurable Mg
          (Eventually.of_forall fun z => hMg z.2)
      have hg_int_eq : ∫ z, g z.2 ∂π = (1 / (n : ℝ)) * ∑ i : Fin n, g (w i) := by
        have hmap : ∫ z, g z.2 ∂π = ∫ v, g v ∂Pn := by
          dsimp only [Pn]
          rw [← hπ_snd]
          exact (integral_map measurable_snd.aemeasurable hg_meas.aestronglyMeasurable).symm
        rw [hmap]; dsimp [Pn, empiricalDistribution]
        rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_eq_one_div,
          smul_eq_mul, integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
        congr 1; exact Finset.sum_congr rfl fun i _ => integral_dirac g (w i)
      let L_lam : (Fin r → ℝ) →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun x => lam ⬝ᵥ x
            map_add' := fun x y => dotProduct_add lam x y
            map_smul' := fun a x => by simp [dotProduct_smul] }
      have hlam_P_int : Integrable (fun u => lam ⬝ᵥ h u θ) P := L_lam.integrable_comp hP_int
      have hlam_π_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => lam ⬝ᵥ h z.1 θ) π := by
        have h1 : Integrable (fun u => lam ⬝ᵥ h u θ) (π.map Prod.fst) := hπ_fst.symm ▸ hlam_P_int
        exact (integrable_map_measure (L_lam.continuous.measurable.comp hmeas).aestronglyMeasurable
          measurable_fst.aemeasurable).mp h1
      have hlam_int_eq : ∫ z, lam ⬝ᵥ h z.1 θ ∂π = 0 := by
        have hmap : ∫ z, lam ⬝ᵥ h z.1 θ ∂π = ∫ u, L_lam (h u θ) ∂P := by
          rw [← hπ_fst]
          exact (integral_map measurable_fst.aemeasurable
            (L_lam.continuous.measurable.comp hmeas).aestronglyMeasurable).symm
        rw [hmap, L_lam.integral_comp_comm hP_int, hP_mean, map_zero]
      have hae_W : ∀ᵐ z ∂π, z.2 ∈ W_fin := by
        rw [ae_iff]
        have hpre : {z : (Fin m → ℝ) × (Fin m → ℝ) | z.2 ∉ W_fin} = Prod.snd ⁻¹' (W_fin : Set _)ᶜ :=
          rfl
        rw [hpre, ← Measure.map_apply measurable_snd hW_meas.compl, hπ_snd]
        simp only [empiricalDistribution, Measure.smul_apply, Measure.coe_finsetSum,
          Finset.sum_apply, smul_eq_mul]
        have hsum0 : ∑ i : Fin n, Measure.dirac (w i) (W_fin : Set (Fin m → ℝ))ᶜ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [Measure.dirac_apply' _ hW_meas.compl]
          have hw_mem : w i ∈ (W_fin : Set (Fin m → ℝ)) :=
            Finset.mem_coe.mpr (Finset.mem_image_of_mem w (Finset.mem_univ i))
          simp [hw_mem]
        rw [hsum0, mul_zero]
      have hae_le : ∀ᵐ z ∂π, lam ⬝ᵥ h z.1 θ - g z.2 ≤ (c z.1 z.2).toReal := by
        filter_upwards [hae_W] with z hz
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
        rw [← hi]
        have hle_sup : (((lam ⬝ᵥ h z.1 θ : ℝ) : EReal) - (c z.1 (w i) : EReal)) ≤ φ lam (w i) :=
          le_iSup (fun u : Fin m → ℝ =>
            (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u (w i) : EReal))) z.1
        rw [hφ_sub, hφ_eq_g i] at hle_sup
        linarith [EReal.coe_le_coe_iff.mp hle_sup]
      have hint_ineq := integral_mono_ae (hlam_π_int.sub hg_π_int) hc_int hae_le
      change ∫ z, (lam ⬝ᵥ h z.1 θ - g z.2) ∂π ≤ ∫ z, (c z.1 z.2).toReal ∂π at hint_ineq
      rw [integral_sub hlam_π_int hg_π_int, hlam_int_eq, hg_int_eq, zero_sub, hc_int_eq] at hint_ineq
      rw [← ENNReal.ofReal_toReal hc_top]
      exact ENNReal.ofReal_le_ofReal hint_ineq

/-! ### Module B2: Rescaled Dual Representation (31)–(32) and Measurability (Part 2) -/

private lemma ereal_mul_iSup_of_pos {ι : Type*} [Nonempty ι] {c : ℝ} (hc : 0 < c)
    (f : ι → EReal) :
    ((c : ℝ) : EReal) * (⨆ x, f x) = ⨆ x, ((c : ℝ) : EReal) * f x := by
  apply le_antisymm
  · generalize hM : (⨆ x, ((c : ℝ) : EReal) * f x) = M
    cases M with
    | top => exact le_top
    | bot =>
      have hall : ∀ x, f x = ⊥ := fun x => by
        have hx : ((c : ℝ) : EReal) * f x ≤ ⊥ :=
          (le_iSup (fun y => ((c : ℝ) : EReal) * f y) x).trans_eq hM
        have hxeq : ((c : ℝ) : EReal) * f x = ⊥ := le_bot_iff.mp hx
        cases hfx : f x with
        | bot => rfl
        | coe r => rw [hfx, ← EReal.coe_mul] at hxeq; exact absurd hxeq (EReal.coe_ne_bot _)
        | top => rw [hfx, EReal.coe_mul_top_of_pos hc] at hxeq; exact absurd hxeq top_ne_bot
      rw [iSup_eq_bot.mpr hall, EReal.coe_mul_bot_of_pos hc]
    | coe m₀ =>
      have hall : ∀ x, f x ≤ ((m₀ / c : ℝ) : EReal) := fun x => by
        have hx : ((c : ℝ) : EReal) * f x ≤ ((m₀ : ℝ) : EReal) :=
          (le_iSup (fun y => ((c : ℝ) : EReal) * f y) x).trans_eq hM
        cases hfx : f x with
        | bot => exact bot_le
        | coe r =>
          rw [hfx, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hx
          exact EReal.coe_le_coe_iff.mpr ((le_div_iff₀' hc).mpr hx)
        | top =>
          rw [hfx, EReal.coe_mul_top_of_pos hc] at hx
          exact absurd (top_le_iff.mp hx) (EReal.coe_ne_top _)
      calc ((c : ℝ) : EReal) * (⨆ x, f x)
          ≤ ((c : ℝ) : EReal) * ((m₀ / c : ℝ) : EReal) :=
            mul_le_mul_of_nonneg_left (iSup_le hall) (EReal.coe_nonneg.mpr hc.le)
        _ = ((m₀ : ℝ) : EReal) := by rw [← EReal.coe_mul, mul_div_cancel₀ _ hc.ne']
  · exact iSup_le fun x => mul_le_mul_of_nonneg_left (le_iSup f x) (EReal.coe_nonneg.mpr hc.le)

private lemma ereal_add_iSup {ι : Type*} [Nonempty ι] (a : ℝ) (f : ι → EReal) :
    ((a : ℝ) : EReal) + (⨆ x, f x) = ⨆ x, (((a : ℝ) : EReal) + f x) := by
  apply le_antisymm
  · generalize hM : (⨆ x, (((a : ℝ) : EReal) + f x)) = M
    cases M with
    | top => exact le_top
    | bot =>
      have hall : ∀ x, f x = ⊥ := fun x => by
        have hx : ((a : ℝ) : EReal) + f x ≤ ⊥ :=
          (le_iSup (fun y => ((a : ℝ) : EReal) + f y) x).trans_eq hM
        have hxeq : ((a : ℝ) : EReal) + f x = ⊥ := le_bot_iff.mp hx
        cases hfx : f x with
        | bot => rfl
        | coe r => rw [hfx, ← EReal.coe_add] at hxeq; exact absurd hxeq (EReal.coe_ne_bot _)
        | top => rw [hfx, EReal.coe_add_top] at hxeq; exact absurd hxeq top_ne_bot
      rw [iSup_eq_bot.mpr hall, EReal.add_bot]
    | coe m₀ =>
      have hall : ∀ x, f x ≤ ((m₀ - a : ℝ) : EReal) := fun x => by
        have hx : ((a : ℝ) : EReal) + f x ≤ ((m₀ : ℝ) : EReal) :=
          (le_iSup (fun y => ((a : ℝ) : EReal) + f y) x).trans_eq hM
        cases hfx : f x with
        | bot => exact bot_le
        | coe r =>
          rw [hfx, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx
          exact EReal.coe_le_coe_iff.mpr (by linarith)
        | top =>
          rw [hfx, EReal.coe_add_top] at hx
          exact absurd (top_le_iff.mp hx) (EReal.coe_ne_top _)
      calc ((a : ℝ) : EReal) + (⨆ x, f x)
          ≤ ((a : ℝ) : EReal) + ((m₀ - a : ℝ) : EReal) := add_le_add le_rfl (iSup_le hall)
        _ = ((m₀ : ℝ) : EReal) := by rw [← EReal.coe_add, add_sub_cancel]
  · exact iSup_le fun x => add_le_add le_rfl (le_iSup f x)

private lemma ftc_line {m l r : ℕ} (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θs : Fin l → ℝ) (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (w_i Δ : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ u in (0 : ℝ)..1, fderiv ℝ (fun x => h x θs) (w_i + c • (u • Δ)) Δ =
      c⁻¹ • (h (w_i + c • Δ) θs - h w_i θs) := by
  let g : ℝ → (Fin r → ℝ) := fun u => fderiv ℝ (fun x => h x θs) (w_i + c • (u • Δ)) Δ
  have hg_cont : Continuous g := by
    have hfderiv : Continuous (fun x : Fin m → ℝ => fderiv ℝ (fun y => h y θs) x) :=
      hC1.continuous_fderiv one_ne_zero
    have hpath : Continuous (fun u : ℝ => w_i + c • (u • Δ)) := by fun_prop
    exact (ContinuousLinearMap.apply ℝ (Fin r → ℝ) Δ).continuous.comp (hfderiv.comp hpath)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (w_i + t • (c • Δ)) θs) (c • g u) u := by
    intro u _
    have hline : HasDerivAt (fun t : ℝ => w_i + t • (c • Δ)) (c • Δ) u := by
      rw [hasDerivAt_pi]
      intro k
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, id_eq] using
        ((hasDerivAt_id u).mul_const (c * Δ k)).const_add (w_i k)
    have hf : HasFDerivAt (fun x => h x θs)
        (fderiv ℝ (fun x => h x θs) (w_i + u • (c • Δ))) (w_i + u • (c • Δ)) :=
      (hC1.differentiable one_ne_zero _).hasFDerivAt
    have hcomp : HasDerivAt ((fun x => h x θs) ∘ fun t : ℝ => w_i + t • (c • Δ))
        ((fderiv ℝ (fun x => h x θs) (w_i + u • (c • Δ))) (c • Δ)) u :=
      hf.comp_hasDerivAt u hline
    exact hcomp.congr_deriv (by dsimp only [g]; rw [map_smul, smul_comm u c Δ])
  have hint : IntervalIntegrable (fun u => c • g u) volume 0 1 :=
    (hg_cont.const_smul c).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_smul] at hftc
  simp only [one_smul, zero_smul, add_zero] at hftc
  calc ∫ u in (0 : ℝ)..1, g u = c⁻¹ • (c • ∫ u in (0 : ℝ)..1, g u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • (h (w_i + c • Δ) θs - h w_i θs) := by rw [hftc]

private lemma eq_31_32_tie_free {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q : ENNReal) (hq : 1 < q)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θs))) :
    ((ENNReal.ofReal ((n : ℝ) ^ (ρ / 2)) *
        rwp (costQ q ρ) h θs (empiricalDistribution w) : ENNReal) : EReal) =
      ⨆ ζ : Fin r → ℝ, (((-(ζ ⬝ᵥ Hn h θs w)) : ℝ) : EReal) - Mn q ρ h θs w ζ := by
  have : Fact (1 ≤ q) := ⟨hq.le⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hρ_pos : 0 < ρ := zero_lt_one.trans_le hρ
  let s : ℝ := (n : ℝ) ^ (ρ / 2)
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hn_pos _
  let sqn : ℝ := Real.sqrt (n : ℝ)
  have hsqn_pos : 0 < sqn := Real.sqrt_pos.mpr hn_pos
  have hc_cont := costQ_continuous q hρ (m := m)
  have hc_diag : ∀ u : Fin m → ℝ, costQ q ρ u u = 0 := fun u => by
    simp [costQ, Real.zero_rpow hρ_pos.ne']
  have hc_fin : ∀ u v : Fin m → ℝ, costQ q ρ u v ≠ ⊤ := fun _ _ => ENNReal.ofReal_ne_top
  have hprop3 := prop3_tie_free hn w (costQ q ρ) hc_cont.lowerSemicontinuous
    hc_diag hc_fin h θs hC1.continuous.measurable hint
  let R := rwp (costQ q ρ) h θs (empiricalDistribution w)
  have hlhs_mul : ((ENNReal.ofReal s * R : ℝ≥0∞) : EReal) = ((s : ℝ) : EReal) * (R : EReal) := by
    rcases eq_or_ne R ⊤ with hR_top | hR_top
    · have hs_ne0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs_pos).ne'
      rw [hR_top, ENNReal.mul_top hs_ne0, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hs_pos]
    · conv_lhs => rw [← ENNReal.ofReal_toReal hR_top]
      rw [← ENNReal.ofReal_mul hs_pos.le, EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg hs_pos.le ENNReal.toReal_nonneg), EReal.coe_mul]
      congr 1
      conv_rhs => rw [← ENNReal.ofReal_toReal hR_top]
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
  rw [hlhs_mul, hprop3, ereal_mul_iSup_of_pos hs_pos]
  let lamEquiv : (Fin r → ℝ) ≃ (Fin r → ℝ) :=
    { toFun := fun ζ => (sqn / s) • ζ
      invFun := fun lam => (s / sqn) • lam
      left_inv := fun ζ => by
        dsimp only
        rw [smul_smul, show s / sqn * (sqn / s) = 1 by field_simp [hs_pos.ne', hsqn_pos.ne'],
          one_smul]
      right_inv := fun lam => by
        dsimp only
        rw [smul_smul, show sqn / s * (s / sqn) = 1 by field_simp [hs_pos.ne', hsqn_pos.ne'],
          one_smul] }
  rw [← lamEquiv.iSup_comp]
  refine iSup_congr fun ζ => ?_
  let lam : Fin r → ℝ := lamEquiv ζ
  let S : Fin n → EReal := fun i =>
    ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u (w i) : EReal))
  let T : Fin n → EReal := fun i =>
    ⨆ Δ : Fin m → ℝ,
      (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
          fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ)
        - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)
  have hS_ne_bot : ∀ i : Fin n, S i ≠ ⊥ := fun i => by
    have hle : (((lam ⬝ᵥ h (w i) θs : ℝ) : EReal) - (costQ q ρ (w i) (w i) : EReal)) ≤ S i :=
      le_iSup (fun u : Fin m → ℝ =>
        (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u (w i) : EReal))) (w i)
    rw [hc_diag (w i)] at hle
    have hnb : (((lam ⬝ᵥ h (w i) θs : ℝ) : EReal) - (0 : ℝ≥0∞)) ≠ ⊥ := by simp
    intro heq; rw [heq] at hle; exact hnb (le_bot_iff.mp hle)
  have hT_ne_bot : ∀ i : Fin n, T i ≠ ⊥ := fun i => by
    have hle : (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • (0 : Fin m → ℝ))) 0)
        - ‖WithLp.toLp q (0 : Fin m → ℝ)‖ ^ ρ : ℝ) : EReal) ≤ T i :=
      le_iSup (fun Δ : Fin m → ℝ =>
        (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
            fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ)
          - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)) 0
    intro heq; rw [heq] at hle; exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
  have hTS_rel : ∀ i : Fin n,
      T i = ((-(sqn * (ζ ⬝ᵥ h (w i) θs)) : ℝ) : EReal) + ((s : ℝ) : EReal) * S i := fun i => by
    let uEquiv : (Fin m → ℝ) ≃ (Fin m → ℝ) :=
      { toFun := fun Δ => w i + sqn⁻¹ • Δ
        invFun := fun u => sqn • (u - w i)
        left_inv := fun Δ => by
          dsimp only; rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsqn_pos.ne', one_smul]
        right_inv := fun u => by
          dsimp only; rw [smul_smul, inv_mul_cancel₀ hsqn_pos.ne', one_smul, add_sub_cancel] }
    have hS_rw : S i = ⨆ Δ : Fin m → ℝ,
        (((lam ⬝ᵥ h (uEquiv Δ) θs - ‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ : ℝ) : EReal)) := by
      dsimp only [S]; rw [← uEquiv.iSup_comp]
      refine iSup_congr fun Δ => ?_
      have hcost : (costQ q ρ (uEquiv Δ) (w i) : EReal) =
          (((‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ : ℝ) : EReal)) := by
        unfold costQ
        rw [EReal.coe_ennreal_ofReal, max_eq_left (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [hcost, ← EReal.coe_sub]
    rw [hS_rw, ereal_mul_iSup_of_pos hs_pos, ereal_add_iSup]
    refine iSup_congr fun Δ => ?_
    rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1
    have hftc := ftc_line h θs hC1 (w i) Δ (inv_ne_zero hsqn_pos.ne')
    rw [inv_inv] at hftc
    have hdot_ftc : ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θs) (w i + sqn⁻¹ • (u • Δ)) Δ =
        sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs - ζ ⬝ᵥ h (w i) θs) := by
      rw [hftc, dotProduct_smul, smul_eq_mul, dotProduct_sub]; rfl
    have hlam_dot : s * (lam ⬝ᵥ h (uEquiv Δ) θs) = sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs) := by
      change s * (((sqn / s) • ζ) ⬝ᵥ h (uEquiv Δ) θs) = sqn * (ζ ⬝ᵥ h (uEquiv Δ) θs)
      rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_div_cancel₀ _ hs_pos.ne']
    have hnorm_diff : w i - uEquiv Δ = -(sqn⁻¹ • Δ) := by dsimp [uEquiv]; abel
    have hcost_scale : s * ‖WithLp.toLp q (w i - uEquiv Δ)‖ ^ ρ = ‖WithLp.toLp q Δ‖ ^ ρ := by
      rw [hnorm_diff]
      have hnorm_smul : ‖WithLp.toLp q (-(sqn⁻¹ • Δ))‖ = sqn⁻¹ * ‖WithLp.toLp q Δ‖ := by
        change ‖-(sqn⁻¹ • WithLp.toLp q Δ)‖ = sqn⁻¹ * ‖WithLp.toLp q Δ‖
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqn_pos)]
      rw [hnorm_smul, Real.mul_rpow (inv_nonneg.mpr hsqn_pos.le) (norm_nonneg _)]
      have hsqn_rpow : s * (sqn⁻¹) ^ ρ = 1 := by
        dsimp [s, sqn]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn_pos.le, ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_add hn_pos]
        have hexp : ρ / 2 + -(1 / 2) * ρ = 0 := by ring
        rw [hexp, Real.rpow_zero]
      rw [← mul_assoc, hsqn_rpow, one_mul]
    rw [hdot_ftc]; linarith [hlam_dot, hcost_scale]
  by_cases htop : ∃ i₀ : Fin n, S i₀ = ⊤
  · obtain ⟨i₀, hi₀⟩ := htop
    have hTi₀ : T i₀ = ⊤ := by rw [hTS_rel i₀, hi₀, EReal.coe_mul_top_of_pos hs_pos, EReal.coe_add_top]
    have hsumS : ∑ i : Fin n, S i = ⊤ := by
      classical
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hi₀]
      exact EReal.top_add_of_ne_bot (finset_sum_ne_bot _ _ fun i _ => hS_ne_bot i)
    have hsumT : ∑ i : Fin n, T i = ⊤ := by
      classical
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hTi₀]
      exact EReal.top_add_of_ne_bot (finset_sum_ne_bot _ _ fun i _ => hT_ne_bot i)
    have hMn_top : Mn q ρ h θs w ζ = ⊤ := by
      dsimp [Mn]; change ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, T i = ⊤
      rw [hsumT, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos)]
    rw [hsumS, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos), EReal.neg_top,
      EReal.coe_mul_bot_of_pos hs_pos, hMn_top]; rfl
  · push Not at htop
    let sv : Fin n → ℝ := fun i => (S i).toReal
    have hS_eq : ∀ i : Fin n, S i = ((sv i : ℝ) : EReal) := fun i =>
      (EReal.coe_toReal (htop i) (hS_ne_bot i)).symm
    have hT_eq : ∀ i : Fin n, T i = ((-(sqn * (ζ ⬝ᵥ h (w i) θs)) + s * sv i : ℝ) : EReal) := by
      intro i; rw [hTS_rel i, hS_eq i, ← EReal.coe_mul, ← EReal.coe_add]
    have hMn_eq : Mn q ρ h θs w ζ =
        (((1 / (n : ℝ)) * ∑ i : Fin n, (-(sqn * (ζ ⬝ᵥ h (w i) θs)) + s * sv i) : ℝ) : EReal) := by
      dsimp [Mn]; change ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, T i = _
      simp_rw [hT_eq]; rw [finset_sum_coe_ereal, ← EReal.coe_mul]
    change ((s : ℝ) : EReal) * -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, S i) =
      (((-(ζ ⬝ᵥ Hn h θs w)) : ℝ) : EReal) - Mn q ρ h θs w ζ
    simp_rw [hS_eq]
    rw [finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_mul,
      hMn_eq, ← EReal.coe_sub]
    congr 1
    have hHn : ζ ⬝ᵥ Hn h θs w = sqn⁻¹ * ∑ i : Fin n, ζ ⬝ᵥ h (w i) θs := by
      dsimp [Hn]; rw [dotProduct_smul, smul_eq_mul, dotProduct_sum]
    have hsqn_div : (1 / (n : ℝ)) * sqn = sqn⁻¹ := by
      have hsq : sqn * sqn = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      field_simp [hn_pos.ne', hsqn_pos.ne']; linarith
    rw [hHn, Finset.sum_add_distrib]
    have hsum1 : ∑ i : Fin n, -(sqn * (ζ ⬝ᵥ h (w i) θs)) = -sqn * ∑ i : Fin n, ζ ⬝ᵥ h (w i) θs := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hsum2 : ∑ i : Fin n, s * sv i = s * ∑ i : Fin n, sv i := (Finset.mul_sum _ _ _).symm
    rw [hsum1, hsum2, mul_add, ← mul_assoc, ← mul_assoc]
    have h1 : (1 / (n : ℝ)) * -sqn = -sqn⁻¹ := by linarith [hsqn_div]
    rw [h1]; ring

private lemma continuous_sSup_compact {X Y : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [PseudoMetricSpace Y] {K : Set Y} (hK_comp : IsCompact K) (hK_ne : K.Nonempty)
    {g : X × Y → ℝ} (hg : Continuous g) :
    Continuous (fun x : X => sSup ((fun y => g (x, y)) '' K)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hprod_comp : IsCompact (Metric.closedBall x₀ 1 ×ˢ K) :=
    (isCompact_closedBall x₀ 1).prod hK_comp
  have hucont := hprod_comp.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hucont (ε / 2) (half_pos hε)
  refine ⟨min 1 δ', lt_min zero_lt_one hδ'_pos, fun {x} hx => ?_⟩
  have hx_ball : x ∈ Metric.closedBall x₀ 1 :=
    Metric.mem_closedBall.mpr (hx.le.trans (min_le_left 1 δ'))
  have hx0_ball : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hx_δ : dist x x₀ < δ' := hx.trans_le (min_le_right 1 δ')
  have hg_x : Continuous (fun y : Y => g (x, y)) := hg.comp (continuous_const.prodMk continuous_id)
  have hg_x0 : Continuous (fun y : Y => g (x₀, y)) := hg.comp (continuous_const.prodMk continuous_id)
  have hbdd_x : BddAbove ((fun y => g (x, y)) '' K) := (hK_comp.image hg_x).bddAbove
  have hbdd_x0 : BddAbove ((fun y => g (x₀, y)) '' K) := (hK_comp.image hg_x0).bddAbove
  have hclose : ∀ y ∈ K, |g (x, y) - g (x₀, y)| < ε / 2 := fun y hy =>
    hδ' (x, y) ⟨hx_ball, hy⟩ (x₀, y) ⟨hx0_ball, hy⟩
      (by simpa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx_δ)
  have hle1 : sSup ((fun y => g (x, y)) '' K) ≤ sSup ((fun y => g (x₀, y)) '' K) + ε / 2 := by
    refine csSup_le (hK_ne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : g (x, y) ≤ g (x₀, y) + ε / 2 := by linarith [(abs_lt.mp (hclose y hy)).2]
    have h2 : g (x₀, y) ≤ sSup ((fun y => g (x₀, y)) '' K) := le_csSup hbdd_x0 ⟨y, hy, rfl⟩
    linarith
  have hle2 : sSup ((fun y => g (x₀, y)) '' K) ≤ sSup ((fun y => g (x, y)) '' K) + ε / 2 := by
    refine csSup_le (hK_ne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : g (x₀, y) ≤ g (x, y) + ε / 2 := by linarith [(abs_lt.mp (hclose y hy)).1]
    have h2 : g (x, y) ≤ sSup ((fun y => g (x, y)) '' K) := le_csSup hbdd_x ⟨y, hy, rfl⟩
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private lemma iSup_ereal_add_of_monotone {u v : ℕ → ℝ} (hu : Monotone u) (hv : Monotone v) :
    (⨆ K : ℕ, ((u K : ℝ) : EReal)) + (⨆ K : ℕ, ((v K : ℝ) : EReal)) =
      ⨆ K : ℕ, ((u K + v K : ℝ) : EReal) := by
  apply le_antisymm
  · let U : EReal := ⨆ K : ℕ, ((u K : ℝ) : EReal)
    let V : EReal := ⨆ K : ℕ, ((v K : ℝ) : EReal)
    have hU_nb : U ≠ ⊥ := by
      have h0 : ((u 0 : ℝ) : EReal) ≤ U := le_iSup (fun K => ((u K : ℝ) : EReal)) 0
      intro h; rw [h] at h0; exact EReal.coe_ne_bot _ (le_bot_iff.mp h0)
    have hV_nb : V ≠ ⊥ := by
      have h0 : ((v 0 : ℝ) : EReal) ≤ V := le_iSup (fun K => ((v K : ℝ) : EReal)) 0
      intro h; rw [h] at h0; exact EReal.coe_ne_bot _ (le_bot_iff.mp h0)
    cases hU : U with
    | bot => exact absurd hU hU_nb
    | top =>
      have hrhs_top : (⨆ K : ℕ, ((u K + v K : ℝ) : EReal)) = ⊤ := by
        refine top_unique (le_of_forall_lt fun x hx => ?_)
        cases x with
        | bot =>
          exact (EReal.bot_lt_coe (u 0 + v 0)).trans_le
            (le_iSup (fun K : ℕ => ((u K + v K : ℝ) : EReal)) 0)
        | top => exact absurd hx (lt_irrefl _)
        | coe m =>
          have hlt : ((m - v 0 : ℝ) : EReal) < U := hU ▸ EReal.coe_lt_top _
          obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
          have hK' : m - v 0 < u K := EReal.coe_lt_coe_iff.mp hK
          have hvK : v 0 ≤ v K := hv (Nat.zero_le K)
          exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le
            (le_iSup (fun K' : ℕ => ((u K' + v K' : ℝ) : EReal)) K)
      rw [hrhs_top]; exact le_top
    | coe a₀ =>
      cases hV : V with
      | bot => exact absurd hV hV_nb
      | top =>
        have hrhs_top : (⨆ K : ℕ, ((u K + v K : ℝ) : EReal)) = ⊤ := by
          refine top_unique (le_of_forall_lt fun x hx => ?_)
          cases x with
          | bot =>
            exact (EReal.bot_lt_coe (u 0 + v 0)).trans_le
              (le_iSup (fun K : ℕ => ((u K + v K : ℝ) : EReal)) 0)
          | top => exact absurd hx (lt_irrefl _)
          | coe m =>
            have hlt : ((m - u 0 : ℝ) : EReal) < V := hV ▸ EReal.coe_lt_top _
            obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
            have hK' : m - u 0 < v K := EReal.coe_lt_coe_iff.mp hK
            have huK : u 0 ≤ u K := hu (Nat.zero_le K)
            exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le
              (le_iSup (fun K' : ℕ => ((u K' + v K' : ℝ) : EReal)) K)
        rw [hrhs_top]; exact le_top
      | coe b₀ =>
        change U + V ≤ _
        rw [hU, hV, ← EReal.coe_add]
        refine le_of_forall_lt fun x hx => ?_
        cases x with
        | bot =>
          exact (EReal.bot_lt_coe (u 0 + v 0)).trans_le
            (le_iSup (fun K : ℕ => ((u K + v K : ℝ) : EReal)) 0)
        | top => exact absurd hx (not_lt_of_ge le_top)
        | coe m =>
          have hm : m < a₀ + b₀ := EReal.coe_lt_coe_iff.mp hx
          let ε : ℝ := (a₀ + b₀ - m) / 2
          have hε : 0 < ε := by dsimp [ε]; linarith
          obtain ⟨K₁, hK₁⟩ := lt_iSup_iff.mp
            (show ((a₀ - ε : ℝ) : EReal) < U by rw [hU]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
          obtain ⟨K₂, hK₂⟩ := lt_iSup_iff.mp
            (show ((b₀ - ε : ℝ) : EReal) < V by rw [hV]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
          have h1 : a₀ - ε < u (max K₁ K₂) :=
            (EReal.coe_lt_coe_iff.mp hK₁).trans_le (hu (le_max_left K₁ K₂))
          have h2 : b₀ - ε < v (max K₁ K₂) :=
            (EReal.coe_lt_coe_iff.mp hK₂).trans_le (hv (le_max_right K₁ K₂))
          exact (EReal.coe_lt_coe_iff.mpr (by dsimp [ε] at h1 h2; linarith)).trans_le
            (le_iSup (fun K' : ℕ => ((u K' + v K' : ℝ) : EReal)) (max K₁ K₂))
  · refine iSup_le fun K => ?_
    rw [EReal.coe_add]
    exact add_le_add (le_iSup (fun K' => ((u K' : ℝ) : EReal)) K)
      (le_iSup (fun K' => ((v K' : ℝ) : EReal)) K)

private lemma iSup_ereal_finset_sum_of_monotone {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, Monotone (a i)) :
    ∑ i ∈ s, (⨆ K : ℕ, ((a i K : ℝ) : EReal)) = ⨆ K : ℕ, ((∑ i ∈ s, a i K : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i₀ s hi₀ ih =>
    rw [Finset.sum_insert hi₀, ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]
    have hmono_s : Monotone (fun K : ℕ => ∑ i ∈ s, a i K) := fun K₁ K₂ hK =>
      Finset.sum_le_sum fun i hi => ha i (Finset.mem_insert_of_mem hi) hK
    rw [iSup_ereal_add_of_monotone (ha i₀ (Finset.mem_insert_self i₀ s)) hmono_s]
    refine iSup_congr fun K => by rw [Finset.sum_insert hi₀]

private lemma cantor_biInf_iSup_comm {X : Type*} [TopologicalSpace X] [T2Space X]
    {S : Set X} (hS_comp : IsCompact S) (hS_ne : S.Nonempty)
    {F : ℕ → X → ℝ} (hF_cont : ∀ K, Continuous (F K))
    (hF_mono : ∀ x ∈ S, Monotone (fun K => F K x)) :
    (⨅ x ∈ S, ⨆ K : ℕ, ((F K x : ℝ) : EReal)) =
      ⨆ K : ℕ, ⨅ x ∈ S, ((F K x : ℝ) : EReal) := by
  apply le_antisymm
  · generalize hM : (⨆ K : ℕ, ⨅ x ∈ S, ((F K x : ℝ) : EReal)) = M
    cases M with
    | top => exact le_top
    | bot =>
      obtain ⟨x_min, hx_min_S, hx_min⟩ := hS_comp.exists_isMinOn hS_ne (hF_cont 0).continuousOn
      have hlb : ((F 0 x_min : ℝ) : EReal) ≤ ⨅ x ∈ S, ((F 0 x : ℝ) : EReal) :=
        le_iInf₂ fun x hx => EReal.coe_le_coe_iff.mpr (hx_min hx)
      have hle_bot : ((F 0 x_min : ℝ) : EReal) ≤ ⊥ :=
        hlb.trans ((le_iSup (fun K : ℕ => ⨅ x ∈ S, ((F K x : ℝ) : EReal)) 0).trans_eq hM)
      exact absurd (le_bot_iff.mp hle_bot) (EReal.coe_ne_bot _)
    | coe m₀ =>
      have h_eps : ∀ ε : ℝ, 0 < ε →
          (⨅ x ∈ S, ⨆ K : ℕ, ((F K x : ℝ) : EReal)) ≤ ((m₀ + ε : ℝ) : EReal) := by
        intro ε hε
        let c : ℝ := m₀ + ε
        let T : ℕ → Set X := fun K => S ∩ {x | F K x ≤ c}
        have hT_anti : ∀ K, T (K + 1) ⊆ T K := fun K x ⟨hxS, hle⟩ =>
          ⟨hxS, (hF_mono x hxS (Nat.le_succ K)).trans hle⟩
        have hT_ne : ∀ K, (T K).Nonempty := fun K => by
          have hlt : (⨅ x ∈ S, ((F K x : ℝ) : EReal)) < ((c : ℝ) : EReal) :=
            ((le_iSup (fun K' : ℕ => ⨅ x ∈ S, ((F K' x : ℝ) : EReal)) K).trans_eq hM).trans_lt
              (EReal.coe_lt_coe_iff.mpr (by dsimp [c]; linarith))
          obtain ⟨x, hxlt'⟩ := iInf_lt_iff.mp hlt
          obtain ⟨hxS, hxlt⟩ := iInf_lt_iff.mp hxlt'
          exact ⟨x, hxS, (EReal.coe_lt_coe_iff.mp hxlt).le⟩
        have hT0_comp : IsCompact (T 0) :=
          hS_comp.inter_right (isClosed_le (hF_cont 0) continuous_const)
        have hT_cl : ∀ K, IsClosed (T K) := fun K =>
          hS_comp.isClosed.inter (isClosed_le (hF_cont K) continuous_const)
        obtain ⟨x_star, hx_star⟩ :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
            T hT_anti hT_ne hT0_comp hT_cl
        have hxS : x_star ∈ S := (Set.mem_iInter.mp hx_star 0).1
        have hx_le : ∀ K, F K x_star ≤ c := fun K => (Set.mem_iInter.mp hx_star K).2
        exact iInf₂_le_of_le x_star hxS (iSup_le fun K => EReal.coe_le_coe_iff.mpr (hx_le K))
      generalize hA : (⨅ x ∈ S, ⨆ K : ℕ, ((F K x : ℝ) : EReal)) = A
      cases A with
      | bot => exact bot_le
      | top =>
        have h1 := hA ▸ h_eps 1 zero_lt_one
        exact absurd (top_le_iff.mp h1) (EReal.coe_ne_top _)
      | coe a₀ =>
        refine EReal.coe_le_coe_iff.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
        exact EReal.coe_le_coe_iff.mp (hA ▸ h_eps ε hε)
  · exact iSup_le fun K => iInf₂_mono fun x _ => le_iSup (fun K' => ((F K' x : ℝ) : EReal)) K

private lemma ereal_neg_biInf {α : Type*} {S : Set α} (f : α → EReal) :
    -(⨅ x ∈ S, f x) = ⨆ x ∈ S, -(f x) := by
  apply le_antisymm
  · have h1 : -(⨆ x ∈ S, -(f x)) ≤ ⨅ x ∈ S, f x := by
      refine le_iInf₂ fun x hx => ?_
      rw [← neg_neg (f x)]
      exact EReal.neg_le_neg_iff.mpr (le_iSup₂_of_le x hx le_rfl)
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr h1
  · refine iSup₂_le fun x hx => ?_
    exact EReal.neg_le_neg_iff.mpr (iInf₂_le x hx)

private noncomputable def dualSupTrunc {m l r : ℕ} (q : ℝ≥0∞) (ρ : ℝ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (K : ℕ) (lv : (Fin r → ℝ) × (Fin m → ℝ)) : ℝ :=
  sSup ((fun u : Fin m → ℝ => lv.1 ⬝ᵥ h u θs - ‖WithLp.toLp q (lv.2 - u)‖ ^ ρ) ''
    Metric.closedBall 0 (K : ℝ))

private lemma dualSupTrunc_props {m l r : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] (ρ : ℝ) (hρ : 1 ≤ ρ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs) :
    (∀ K : ℕ, Continuous (dualSupTrunc q ρ h θs K)) ∧
    (∀ lv, Monotone (fun K : ℕ => dualSupTrunc q ρ h θs K lv)) ∧
    (∀ (lam : Fin r → ℝ) (v : Fin m → ℝ),
      (⨆ K : ℕ, ((dualSupTrunc q ρ h θs K (lam, v) : ℝ) : EReal)) =
        ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u v : EReal))) := by
  have hρ_pos : 0 < ρ := zero_lt_one.trans_le hρ
  let g_base : ((Fin r → ℝ) × (Fin m → ℝ)) × (Fin m → ℝ) → ℝ :=
    fun z => z.1.1 ⬝ᵥ h z.2 θs - ‖WithLp.toLp q (z.1.2 - z.2)‖ ^ ρ
  have hg_cont : Continuous g_base := by
    have hdot_cont : Continuous (fun z : ((Fin r → ℝ) × (Fin m → ℝ)) × (Fin m → ℝ) =>
        z.1.1 ⬝ᵥ h z.2 θs) :=
      continuous_finsetSum Finset.univ fun j _ =>
        ((continuous_apply j).comp (continuous_fst.comp continuous_fst)).mul
          ((continuous_apply j).comp (hC1.continuous.comp continuous_snd))
    have hnorm_cont : Continuous (fun z : ((Fin r → ℝ) × (Fin m → ℝ)) × (Fin m → ℝ) =>
        ‖WithLp.toLp q (z.1.2 - z.2)‖ ^ ρ) :=
      (continuous_norm.comp ((PiLp.continuous_toLp q _).comp
        ((continuous_snd.comp continuous_fst).sub continuous_snd))).rpow_const
          (fun _ => Or.inr hρ_pos.le)
    exact hdot_cont.sub hnorm_cont
  have hg_slice : ∀ lv : (Fin r → ℝ) × (Fin m → ℝ),
      Continuous (fun u : Fin m → ℝ => g_base (lv, u)) :=
    fun lv => hg_cont.comp (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_, ?_⟩
  · intro K
    exact continuous_sSup_compact (isCompact_closedBall 0 (K : ℝ))
      ⟨0, Metric.mem_closedBall_self (Nat.cast_nonneg K)⟩ hg_cont
  · intro lv K₁ K₂ hK
    have hsub : Metric.closedBall (0 : Fin m → ℝ) (K₁ : ℝ) ⊆
        Metric.closedBall (0 : Fin m → ℝ) (K₂ : ℝ) :=
      Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hK)
    have hne1 : ((fun u => g_base (lv, u)) '' Metric.closedBall 0 (K₁ : ℝ)).Nonempty :=
      ⟨g_base (lv, 0), 0, Metric.mem_closedBall_self (Nat.cast_nonneg K₁), rfl⟩
    have hbdd2 : BddAbove ((fun u => g_base (lv, u)) '' Metric.closedBall 0 (K₂ : ℝ)) :=
      ((isCompact_closedBall (0 : Fin m → ℝ) (K₂ : ℝ)).image (hg_slice lv)).bddAbove
    exact csSup_le_csSup hbdd2 hne1 (Set.image_mono hsub)
  · intro lam v
    have hsub_cost : ∀ u : Fin m → ℝ,
        (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u v : EReal)) =
          ((g_base ((lam, v), u) : ℝ) : EReal) := fun u => by
      have hc : (costQ q ρ u v : EReal) = ((‖WithLp.toLp q (v - u)‖ ^ ρ : ℝ) : EReal) := by
        unfold costQ
        rw [EReal.coe_ennreal_ofReal, max_eq_left (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [hc, ← EReal.coe_sub]
    simp_rw [hsub_cost]
    apply le_antisymm
    · refine iSup_le fun K => ?_
      have hcomp : IsCompact (Metric.closedBall (0 : Fin m → ℝ) (K : ℝ)) :=
        isCompact_closedBall 0 (K : ℝ)
      have hne : (Metric.closedBall (0 : Fin m → ℝ) (K : ℝ)).Nonempty :=
        ⟨0, Metric.mem_closedBall_self (Nat.cast_nonneg K)⟩
      obtain ⟨u₀, hu₀_mem, hu₀_max⟩ := hcomp.exists_isMaxOn hne (hg_slice (lam, v)).continuousOn
      have hsup_eq : dualSupTrunc q ρ h θs K (lam, v) = g_base ((lam, v), u₀) := by
        refine le_antisymm ?_ ?_
        · refine csSup_le (hne.image _) ?_
          rintro _ ⟨u, hu, rfl⟩; exact hu₀_max hu
        · exact le_csSup (hcomp.image (hg_slice (lam, v))).bddAbove ⟨u₀, hu₀_mem, rfl⟩
      rw [hsup_eq]
      exact le_iSup (fun u : Fin m → ℝ => ((g_base ((lam, v), u) : ℝ) : EReal)) u₀
    · refine iSup_le fun u => ?_
      obtain ⟨K, hK⟩ := exists_nat_ge ‖u‖
      have hu_mem : u ∈ Metric.closedBall (0 : Fin m → ℝ) (K : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hK
      have hbdd : BddAbove ((fun u' => g_base ((lam, v), u')) '' Metric.closedBall 0 (K : ℝ)) :=
        ((isCompact_closedBall (0 : Fin m → ℝ) (K : ℝ)).image (hg_slice (lam, v))).bddAbove
      exact le_trans (EReal.coe_le_coe_iff.mpr (le_csSup hbdd ⟨u, hu_mem, rfl⟩))
        (le_iSup (fun K' : ℕ => ((dualSupTrunc q ρ h θs K' (lam, v) : ℝ) : EReal)) K)

private lemma aemeasurable_rwp_emp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θs)))
    (n : ℕ) :
    AEMeasurable (fun ω => rwp (costQ q ρ) h θs
      (empiricalDistribution (fun i : Fin n => W i ω))) μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hconst : ∀ ω : Ω,
        rwp (costQ q ρ) h θs (empiricalDistribution (fun i : Fin 0 => W i ω)) = ⊤ := by
      intro ω
      have hemp : empiricalDistribution (fun i : Fin 0 => W i ω) = 0 := by
        simp [empiricalDistribution]
      rw [hemp]
      unfold rwp transportCost
      refine iInf_eq_top.mpr fun P => iInf_eq_top.mpr fun _ => iInf_eq_top.mpr fun π =>
        iInf_eq_top.mpr fun ⟨hπ_prob, _, hπ_snd⟩ => False.elim ?_
      have h1 : (π.map Prod.snd) Set.univ = 1 := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ, measure_univ]
      rw [hπ_snd, Measure.coe_zero, Pi.zero_apply] at h1
      exact zero_ne_one h1
    simp_rw [hconst]
    exact measurable_const.aemeasurable
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hρ_pos : 0 < ρ := zero_lt_one.trans_le hρ
    have hc_cont := costQ_continuous q hρ (m := m)
    have hc_diag : ∀ u : Fin m → ℝ, costQ q ρ u u = 0 := fun u => by
      simp [costQ, Real.zero_rpow hρ_pos.ne']
    have hc_fin : ∀ u v : Fin m → ℝ, costQ q ρ u v ≠ ⊤ := fun _ _ => ENNReal.ofReal_ne_top
    obtain ⟨hφ_cont, hφ_mono, hφ_iSup⟩ := dualSupTrunc_props q ρ hρ h θs hC1
    let F_K : ℕ → (Fin r → ℝ) → (Fin n → (Fin m → ℝ)) → ℝ := fun K lam w =>
      (1 / (n : ℝ)) * ∑ i : Fin n, dualSupTrunc q ρ h θs K (lam, w i)
    have hFK_cont_lam : ∀ (K : ℕ) (w : Fin n → (Fin m → ℝ)), Continuous (fun lam => F_K K lam w) :=
      fun K w => continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
        (hφ_cont K).comp (continuous_id.prodMk continuous_const))
    have hFK_cont_w : ∀ (K : ℕ) (lam : Fin r → ℝ), Continuous (fun w => F_K K lam w) :=
      fun K lam => continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
        (hφ_cont K).comp (continuous_const.prodMk (continuous_apply i)))
    have hFK_mono : ∀ lam w, Monotone (fun K : ℕ => F_K K lam w) := fun lam w K₁ K₂ hK =>
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hφ_mono (lam, w i) hK) (by positivity)
    have hrwp_eq : ∀ w : Fin n → (Fin m → ℝ),
        (rwp (costQ q ρ) h θs (empiricalDistribution w) : EReal) =
          ⨆ L : ℕ, -(⨆ K : ℕ, ⨅ lam ∈ Metric.closedBall (0 : Fin r → ℝ) (L : ℝ),
            ((F_K K lam w : ℝ) : EReal)) := by
      intro w
      rw [prop3_tie_free hn w (costQ q ρ) hc_cont.lowerSemicontinuous hc_diag hc_fin
        h θs hC1.continuous.measurable hint]
      have hinner : ∀ lam : Fin r → ℝ,
          ((1 / (n : ℝ) : ℝ) : EReal) *
            ∑ i : Fin n, ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θs : ℝ) : EReal) - (costQ q ρ u (w i) : EReal)) =
            ⨆ K : ℕ, ((F_K K lam w : ℝ) : EReal) := by
        intro lam
        simp_rw [← hφ_iSup lam]
        rw [iSup_ereal_finset_sum_of_monotone Finset.univ
          (fun i K => dualSupTrunc q ρ h θs K (lam, w i)) (fun i _ => hφ_mono (lam, w i)),
          ereal_mul_iSup_of_pos (one_div_pos.mpr hn_pos)]
        refine iSup_congr fun K => by rw [← EReal.coe_mul]
      simp_rw [hinner]
      have hcov_L : (⨆ lam : Fin r → ℝ, -(⨆ K : ℕ, ((F_K K lam w : ℝ) : EReal))) =
          ⨆ L : ℕ, ⨆ lam ∈ Metric.closedBall (0 : Fin r → ℝ) (L : ℝ),
            -(⨆ K : ℕ, ((F_K K lam w : ℝ) : EReal)) := by
        apply le_antisymm
        · refine iSup_le fun lam => ?_
          obtain ⟨L, hL⟩ := exists_nat_ge ‖lam‖
          have hmem : lam ∈ Metric.closedBall (0 : Fin r → ℝ) (L : ℝ) := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hL
          exact le_trans (le_iSup₂_of_le lam hmem le_rfl)
            (le_iSup (fun L' : ℕ => ⨆ lam' ∈ Metric.closedBall (0 : Fin r → ℝ) (L' : ℝ),
              -(⨆ K : ℕ, ((F_K K lam' w : ℝ) : EReal))) L)
        · exact iSup_le fun L => iSup₂_le fun lam _ =>
            le_iSup (fun lam' => -(⨆ K : ℕ, ((F_K K lam' w : ℝ) : EReal))) lam
      rw [hcov_L]
      refine iSup_congr fun L => ?_
      rw [← ereal_neg_biInf, cantor_biInf_iSup_comm (isCompact_closedBall 0 (L : ℝ))
        ⟨0, Metric.mem_closedBall_self (Nat.cast_nonneg L)⟩
        (fun K => hFK_cont_lam K w) (fun lam _ => hFK_mono lam w)]
    have hmeas_ereal : Measurable (fun w : Fin n → (Fin m → ℝ) =>
        (rwp (costQ q ρ) h θs (empiricalDistribution w) : EReal)) := by
      simp_rw [hrwp_eq]
      refine Measurable.iSup fun L => continuous_neg.measurable.comp ?_
      refine Measurable.iSup fun K => ?_
      refine UpperSemicontinuous.measurable (upperSemicontinuous_biInf fun lam _ => ?_)
      exact (EReal.continuous_coe_iff.mpr (hFK_cont_w K lam)).upperSemicontinuous
    have hmeas_w : Measurable (fun w : Fin n → (Fin m → ℝ) =>
        rwp (costQ q ρ) h θs (empiricalDistribution w)) := by
      have hfn_eq : (fun w : Fin n → (Fin m → ℝ) => rwp (costQ q ρ) h θs (empiricalDistribution w)) =
          fun w => ((rwp (costQ q ρ) h θs (empiricalDistribution w) : EReal)).toENNReal :=
        funext fun _ => EReal.toENNReal_coe.symm
      rw [hfn_eq]
      exact EReal.continuous_toENNReal.measurable.comp hmeas_ereal
    exact (hmeas_w.comp (measurable_pi_iff.mpr fun i => hWmeas i)).aemeasurable


/-! ### Module C: Attainment, Finiteness, and Continuity of `Rbar` (Part 3) -/

private lemma euc_dot_abs_le {r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ζ : Fin r → ℝ) (x : EuclideanSpace ℝ (Fin r)) :
    |∑ j : Fin r, ζ j * x j| ≤ (r : ℝ) * ‖WithLp.toLp p ζ‖ * ‖x‖ := by
  calc |∑ j : Fin r, ζ j * x j|
      ≤ ∑ j : Fin r, |ζ j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin r, |ζ j| * |x j| := Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ _j : Fin r, ‖WithLp.toLp p ζ‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
        · simpa only [Real.norm_eq_abs] using (norm_le_pi_norm ζ j).trans (norm_le_toLp_norm p ζ)
        · simpa only [Real.norm_eq_abs] using
            (norm_le_pi_norm x.ofLp j).trans (norm_le_toLp_norm 2 x.ofLp)
    _ = (r : ℝ) * ‖WithLp.toLp p ζ‖ * ‖x‖ := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

private lemma euc_dot_sub_abs_le {r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ζ : Fin r → ℝ) (x y : EuclideanSpace ℝ (Fin r)) :
    |(∑ j : Fin r, ζ j * x j) - ∑ j : Fin r, ζ j * y j| ≤
      (r : ℝ) * ‖WithLp.toLp p ζ‖ * ‖x - y‖ := by
  have hsub : (∑ j : Fin r, ζ j * x j) - (∑ j : Fin r, ζ j * y j) =
      ∑ j : Fin r, ζ j * (x - y) j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_sub]
  rw [hsub]
  exact euc_dot_abs_le p ζ (x - y)

private lemma rowNorm_zero_zeta {m l r : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ) (w : Fin m → ℝ) :
    rowNorm p h θs 0 w = 0 := by
  have hrv : rowVec h θs 0 w = 0 := by ext k; simp [rowVec]
  simp [rowNorm_eq_norm_rowVec, hrv]

private lemma zero_mem_rbarFeasible {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ) (ρ : ℝ) :
    (0 : Fin r → ℝ) ∈ RbarFeasible μ W0 p h θs ρ := by
  unfold RbarFeasible
  split_ifs with h1
  · have hemp : {ω : Ω | 1 < rowNorm p h θs 0 (W0 ω)} = ∅ := by
      ext ω; simp [rowNorm_zero_zeta]
    simp [hemp]
  · exact Set.mem_univ 0

private lemma rbarObjective_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (x : EuclideanSpace ℝ (Fin r)) :
    RbarObjective μ W0 p h θs ρ x 0 = 0 := by
  unfold RbarObjective
  split_ifs with h1
  · simp
  · have hρ_gt : 1 < ρ := lt_of_le_of_ne hρ (Ne.symm h1)
    have hβ_pos : 0 < ρ / (ρ - 1) := div_pos (zero_lt_one.trans hρ_gt) (sub_pos.mpr hρ_gt)
    have hmom0 : rowMoment μ W0 p h θs ρ 0 = 0 := by
      unfold rowMoment
      simp [rowNorm_zero_zeta, Real.zero_rpow hβ_pos.ne']
    simp [hmom0]

private lemma rbar_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (x : EuclideanSpace ℝ (Fin r)) :
    (0 : EReal) ≤ Rbar μ W0 p h θs ρ x := by
  unfold Rbar
  rw [← rbarObjective_zero W0 p h θs hρ x]
  exact le_iSup₂_of_le 0 (zero_mem_rbarFeasible W0 p h θs ρ) le_rfl

private def rbarFeasibleOne {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ) : Set (Fin r → ℝ) :=
  {ζ | μ {ω | 1 < rowNorm p h θs ζ (W0 ω)} = 0}

private lemma rbarFeasibleOne_props {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ} (hr : 0 < r)
    (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W0 ω)}) :
    (0 : Fin r → ℝ) ∈ rbarFeasibleOne μ W0 p h θs ∧
    (∀ ζ ∈ rbarFeasibleOne μ W0 p h θs, -ζ ∈ rbarFeasibleOne μ W0 p h θs) ∧
    IsClosed (rbarFeasibleOne μ W0 p h θs) ∧
    ∃ B_F : ℝ, 0 < B_F ∧
      (∀ ζ ∈ rbarFeasibleOne μ W0 p h θs, ‖WithLp.toLp p ζ‖ ≤ B_F) ∧
      IsCompact (rbarFeasibleOne μ W0 p h θs) := by
  let F_set := rbarFeasibleOne μ W0 p h θs
  have h0_mem : (0 : Fin r → ℝ) ∈ F_set := by
    change μ {ω | 1 < rowNorm p h θs 0 (W0 ω)} = 0
    have hemp : {ω : Ω | 1 < rowNorm p h θs 0 (W0 ω)} = ∅ := by ext ω; simp [rowNorm_zero_zeta]
    simp [hemp]
  have hneg_mem : ∀ ζ ∈ F_set, -ζ ∈ F_set := by
    intro ζ hζ
    change μ {ω | 1 < rowNorm p h θs (-ζ) (W0 ω)} = 0
    have heq : ∀ ω, rowNorm p h θs (-ζ) (W0 ω) = rowNorm p h θs ζ (W0 ω) := fun ω => by
      have h1 := rowNorm_smul p h θs (-1 : ℝ) ζ (W0 ω)
      simpa using h1
    simp_rw [heq]
    exact hζ
  have hrow_cont : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2) :=
    continuous_norm.comp (continuous_toLp_rowVec p h θs hC1)
  have hF_closed : IsClosed F_set := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro ζ hζ
    have hpos : 0 < μ {ω | 1 < rowNorm p h θs ζ (W0 ω)} := pos_iff_ne_zero.mpr hζ
    obtain ⟨k, hk_pos⟩ := exists_trunc_gt_const W0 p h θs 1 ζ hpos
    let C : ℝ := (k : ℝ) + 1
    have hC_pos : 0 < C := by positivity
    let η : ℝ := 1 / (2 * C)
    have hη_pos : 0 < η := by positivity
    have h2η : 2 * η = 1 / ((k : ℝ) + 1) := by dsimp [η, C]; field_simp [hC_pos.ne']
    have hK_prod : IsCompact (Metric.closedBall ζ 1 ×ˢ Metric.closedBall (0 : Fin m → ℝ) C) :=
      (isCompact_closedBall ζ 1).prod (isCompact_closedBall 0 C)
    have hucont := hK_prod.uniformContinuousOn_of_continuous hrow_cont.continuousOn
    obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hucont η hη_pos
    refine ⟨min 1 δ', lt_min zero_lt_one hδ'_pos, fun ζ' hζ' => ?_⟩
    have hdist1 : dist ζ' ζ ≤ 1 := (Metric.mem_ball.mp hζ').le.trans (min_le_left 1 δ')
    have hdistδ : dist ζ' ζ < δ' := (Metric.mem_ball.mp hζ').trans_le (min_le_right 1 δ')
    have hsub : {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧ 1 + 1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ζ (W0 ω)} ⊆
        {ω | 1 < rowNorm p h θs ζ' (W0 ω)} := by
      intro ω ⟨hw_norm, hw_row⟩
      have hp1 : (ζ', W0 ω) ∈ Metric.closedBall ζ 1 ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
        ⟨Metric.mem_closedBall.mpr hdist1, by simpa [Metric.mem_closedBall, dist_zero_right, C] using hw_norm⟩
      have hp2 : (ζ, W0 ω) ∈ Metric.closedBall ζ 1 ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
        ⟨Metric.mem_closedBall_self zero_le_one,
          by simpa [Metric.mem_closedBall, dist_zero_right, C] using hw_norm⟩
      have hclose : |rowNorm p h θs ζ' (W0 ω) - rowNorm p h θs ζ (W0 ω)| < η :=
        hδ' (ζ', W0 ω) hp1 (ζ, W0 ω) hp2
          (by simpa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdistδ)
      rw [← h2η] at hw_row
      change 1 < rowNorm p h θs ζ' (W0 ω)
      linarith [abs_lt.mp hclose]
    have hpos' : 0 < μ {ω | 1 < rowNorm p h θs ζ' (W0 ω)} := hk_pos.trans_le (measure_mono hsub)
    exact hpos'.ne'
  let Sp : Set (Fin r → ℝ) := {ξ | ‖WithLp.toLp p ξ‖ = 1}
  have hSp_ne : Sp.Nonempty := ⟨Pi.single ⟨0, hr⟩ 1, toLp_norm_single_eq_one p ⟨0, hr⟩⟩
  have hSp_gt : ∀ ξ ∈ Sp, 0 < μ {ω | 0 < rowNorm p h θs ξ (W0 ω)} := by
    intro ξ hξ
    have hξ_ne : ξ ≠ 0 := by
      intro h0; rw [h0] at hξ; change ‖(0 : WithLp p (Fin r → ℝ))‖ = 1 at hξ; norm_num at hξ
    exact hA4 ξ hξ_ne
  obtain ⟨m_cov, A_ev, _, η_star, p_star, _, _, hη_pos, hp_star_pos, _, _, hA_prob, _, hA_cov⟩ :=
    exists_uniform_compact_cover Sp (isCompact_toLp_sphere p) hSp_ne W0 p h θs hC1 0 hSp_gt
  let B_F : ℝ := 1 / η_star
  have hBF_pos : 0 < B_F := one_div_pos.mpr hη_pos
  have hF_bdd : ∀ ζ ∈ F_set, ‖WithLp.toLp p ζ‖ ≤ B_F := by
    intro ζ hζ
    by_cases hζ0 : ζ = 0
    · subst hζ0; change ‖(0 : WithLp p (Fin r → ℝ))‖ ≤ B_F; rw [norm_zero]; exact hBF_pos.le
    · let t : ℝ := ‖WithLp.toLp p ζ‖
      have ht_pos : 0 < t := by
        by_contra ht
        have h0 : WithLp.toLp p ζ = 0 :=
          norm_eq_zero.mp (le_antisymm (not_lt.mp ht) (norm_nonneg _))
        exact hζ0 (congrArg WithLp.ofLp h0)
      let ξ : Fin r → ℝ := t⁻¹ • ζ
      have hξ_Sp : ξ ∈ Sp := by
        change ‖t⁻¹ • WithLp.toLp p ζ‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht_pos), inv_mul_cancel₀ ht_pos.ne']
      obtain ⟨j, hj⟩ := hA_cov ξ hξ_Sp
      by_contra ht_gt
      have ht_gt' : 1 / η_star < t := not_le.mp ht_gt
      have hmul_gt : 1 < t * η_star := (div_lt_iff₀ hη_pos).mp ht_gt'
      have hsub : W0 ⁻¹' A_ev j ⊆ {ω | 1 < rowNorm p h θs ζ (W0 ω)} := by
        intro ω hω
        have hζ_eq : ζ = t • ξ := by simp [ξ, smul_smul, mul_inv_cancel₀ ht_pos.ne']
        have hrow_ge : η_star ≤ rowNorm p h θs ξ (W0 ω) := by
          have := hj (W0 ω) hω; linarith
        change 1 < rowNorm p h θs ζ (W0 ω)
        rw [hζ_eq, rowNorm_smul, abs_of_pos ht_pos]
        exact hmul_gt.trans_le (mul_le_mul_of_nonneg_left hrow_ge ht_pos.le)
      have hmeas0 : μ (W0 ⁻¹' A_ev j) = 0 := measure_mono_null hsub hζ
      have hreal0 : μ.real (W0 ⁻¹' A_ev j) = 0 := by simp [Measure.real, hmeas0]
      linarith [hA_prob j]
  have hF_comp : IsCompact F_set :=
    (isCompact_toLp_closedBall p B_F).of_isClosed_subset hF_closed hF_bdd
  exact ⟨h0_mem, hneg_mem, hF_closed, B_F, hBF_pos, hF_bdd, hF_comp⟩

private lemma exists_rowMoment_coercive {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ} (hr : 0 < r)
    (W0 : Ω → (Fin m → ℝ)) (hW0_meas : Measurable W0) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    {ρ : ℝ} (hρ_gt : 1 < ρ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W0 ω)}) :
    ∃ c_coer : ℝ, 0 < c_coer ∧ ∀ ζ : Fin r → ℝ,
      ENNReal.ofReal (c_coer * ‖WithLp.toLp p ζ‖ ^ (ρ / (ρ - 1))) ≤
        ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θs ρ ζ := by
  let β : ℝ := ρ / (ρ - 1)
  have hρ_sub : 0 < ρ - 1 := sub_pos.mpr hρ_gt
  have hβ_pos : 0 < β := div_pos (zero_lt_one.trans hρ_gt) hρ_sub
  let Sp : Set (Fin r → ℝ) := {ξ | ‖WithLp.toLp p ξ‖ = 1}
  have hSp_ne : Sp.Nonempty := ⟨Pi.single ⟨0, hr⟩ 1, toLp_norm_single_eq_one p ⟨0, hr⟩⟩
  have hSp_gt : ∀ ξ ∈ Sp, 0 < μ {ω | 0 < rowNorm p h θs ξ (W0 ω)} := by
    intro ξ hξ
    have hξ_ne : ξ ≠ 0 := by
      intro h0; rw [h0] at hξ; change ‖(0 : WithLp p (Fin r → ℝ))‖ = 1 at hξ; norm_num at hξ
    exact hA4 ξ hξ_ne
  obtain ⟨m_cov, A_ev, _, η_star, p_star, _, _, hη_pos, hp_star_pos, _, hA_meas, hA_prob, _, hA_cov⟩ :=
    exists_uniform_compact_cover Sp (isCompact_toLp_sphere p) hSp_ne W0 p h θs hC1 0 hSp_gt
  let c_coer : ℝ := (ρ - 1) * (p_star * η_star ^ β)
  have hc_pos : 0 < c_coer := mul_pos hρ_sub (mul_pos hp_star_pos (Real.rpow_pos_of_pos hη_pos _))
  refine ⟨c_coer, hc_pos, fun ζ => ?_⟩
  by_cases hζ0 : ζ = 0
  · subst hζ0
    change ENNReal.ofReal (c_coer * ‖(0 : WithLp p (Fin r → ℝ))‖ ^ β) ≤ _
    rw [norm_zero, Real.zero_rpow hβ_pos.ne', mul_zero, ENNReal.ofReal_zero]
    exact bot_le
  · let t : ℝ := ‖WithLp.toLp p ζ‖
    have ht_pos : 0 < t := by
      by_contra ht
      have h0 : WithLp.toLp p ζ = 0 :=
        norm_eq_zero.mp (le_antisymm (not_lt.mp ht) (norm_nonneg _))
      exact hζ0 (congrArg WithLp.ofLp h0)
    let ξ : Fin r → ℝ := t⁻¹ • ζ
    have hξ_Sp : ξ ∈ Sp := by
      change ‖t⁻¹ • WithLp.toLp p ζ‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht_pos), inv_mul_cancel₀ ht_pos.ne']
    obtain ⟨j, hj⟩ := hA_cov ξ hξ_Sp
    let S_j : Set Ω := W0 ⁻¹' A_ev j
    have hSj_meas : MeasurableSet S_j := (hA_meas j).preimage hW0_meas
    have hpt : ∀ ω ∈ S_j, η_star ^ β * t ^ β ≤ rowNorm p h θs ζ (W0 ω) ^ β := by
      intro ω hω
      have hζ_eq : ζ = t • ξ := by simp [ξ, smul_smul, mul_inv_cancel₀ ht_pos.ne']
      have hrow_ge : η_star ≤ rowNorm p h θs ξ (W0 ω) := by
        have := hj (W0 ω) hω; linarith
      have hprod_le : η_star * t ≤ rowNorm p h θs ζ (W0 ω) := by
        rw [hζ_eq, rowNorm_smul, abs_of_pos ht_pos]
        linarith [mul_le_mul_of_nonneg_left hrow_ge ht_pos.le]
      rw [← Real.mul_rpow hη_pos.le ht_pos.le]
      exact Real.rpow_le_rpow (mul_nonneg hη_pos.le ht_pos.le) hprod_le hβ_pos.le
    have hmom_lb : ENNReal.ofReal (η_star ^ β * t ^ β) * μ S_j ≤ rowMoment μ W0 p h θs ρ ζ := by
      have hind : ∫⁻ ω, ENNReal.ofReal (η_star ^ β * t ^ β) * S_j.indicator 1 ω ∂μ =
          ENNReal.ofReal (η_star ^ β * t ^ β) * μ S_j := by
        rw [lintegral_const_mul _ (measurable_one.indicator hSj_meas), lintegral_indicator_one hSj_meas]
      rw [← hind]
      refine lintegral_mono fun ω => ?_
      by_cases hω : ω ∈ S_j
      · simp only [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        exact ENNReal.ofReal_le_ofReal (hpt ω hω)
      · simp [hω]
    have hp_le_μ : ENNReal.ofReal p_star ≤ μ S_j := by
      calc ENNReal.ofReal p_star ≤ ENNReal.ofReal (μ.real S_j) := ENNReal.ofReal_le_ofReal (hA_prob j)
        _ = μ S_j := ENNReal.ofReal_toReal (measure_ne_top μ S_j)
    have hmom_lb2 : ENNReal.ofReal (p_star * η_star ^ β * t ^ β) ≤ rowMoment μ W0 p h θs ρ ζ := by
      have h1 : ENNReal.ofReal (p_star * η_star ^ β * t ^ β) =
          ENNReal.ofReal (η_star ^ β * t ^ β) * ENNReal.ofReal p_star := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hη_pos.le _) (Real.rpow_nonneg ht_pos.le _))]
        congr 1; ring
      rw [h1]
      exact (mul_le_mul_of_nonneg_left hp_le_μ bot_le).trans hmom_lb
    have hlhs : ENNReal.ofReal (c_coer * t ^ β) =
        ENNReal.ofReal (ρ - 1) * ENNReal.ofReal (p_star * η_star ^ β * t ^ β) := by
      rw [← ENNReal.ofReal_mul hρ_sub.le]
      congr 1; dsimp [c_coer]; ring
    rw [hlhs]
    exact mul_le_mul_of_nonneg_left hmom_lb2 bot_le

private lemma rbar_gt_one_ball_max {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (hW0_meas : Measurable W0) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    {ρ : ℝ} (hρ_gt : 1 < ρ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    {c_coer : ℝ} (hc_pos : 0 < c_coer)
    (hcoer : ∀ ζ : Fin r → ℝ,
      ENNReal.ofReal (c_coer * ‖WithLp.toLp p ζ‖ ^ (ρ / (ρ - 1))) ≤
        ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θs ρ ζ)
    {M : ℝ} (hM_nn : 0 ≤ M) :
    ∃ R_M : ℝ, 1 ≤ R_M ∧ ∀ x : EuclideanSpace ℝ (Fin r), ‖x‖ ≤ M →
      ∃ ζ₀ : Fin r → ℝ, ‖WithLp.toLp p ζ₀‖ ≤ R_M ∧
        RbarObjective μ W0 p h θs ρ x ζ₀ = Rbar μ W0 p h θs ρ x ∧
        Rbar μ W0 p h θs ρ x < ⊤ := by
  have hρ : 1 ≤ ρ := hρ_gt.le
  have hρ_ne1 : ρ ≠ 1 := hρ_gt.ne'
  have hρ_pos : 0 < ρ := zero_lt_one.trans hρ_gt
  have hρ_sub : 0 < ρ - 1 := sub_pos.mpr hρ_gt
  let β : ℝ := ρ / (ρ - 1)
  have hβ_pos : 0 < β := div_pos hρ_pos hρ_sub
  let A_num : ℝ := (ρ * (r : ℝ) * M + 1) / c_coer
  have hA_pos : 0 < A_num := div_pos (by positivity) hc_pos
  let R_M : ℝ := max 1 (A_num ^ (ρ - 1))
  have hRM_ge1 : 1 ≤ R_M := le_max_left _ _
  have hRM_pos : 0 < R_M := zero_lt_one.trans_le hRM_ge1
  refine ⟨R_M, hRM_ge1, fun x hxM => ?_⟩
  let B_M : Set (Fin r → ℝ) := {ζ | ‖WithLp.toLp p ζ‖ ≤ R_M}
  have h0_BM : (0 : Fin r → ℝ) ∈ B_M := by
    change ‖(0 : WithLp p (Fin r → ℝ))‖ ≤ R_M; rw [norm_zero]; exact hRM_pos.le
  have hout_neg : ∀ ζ : Fin r → ℝ, ζ ∉ B_M → RbarObjective μ W0 p h θs ρ x ζ < 0 := by
    intro ζ hζ_out
    have ht_gt : R_M < ‖WithLp.toLp p ζ‖ := not_le.mp hζ_out
    let t : ℝ := ‖WithLp.toLp p ζ‖
    have ht_gt1 : 1 < t := hRM_ge1.trans_lt ht_gt
    have ht_pos : 0 < t := zero_lt_one.trans ht_gt1
    have hA_lt_t : A_num ^ (ρ - 1) < t := (le_max_right 1 _).trans_lt ht_gt
    have hA_lt_rpow : A_num < t ^ (1 / (ρ - 1)) := by
      have h1 := Real.rpow_lt_rpow (Real.rpow_nonneg hA_pos.le _) hA_lt_t (one_div_pos.mpr hρ_sub)
      rwa [← Real.rpow_mul hA_pos.le, mul_one_div_cancel hρ_sub.ne', Real.rpow_one] at h1
    have hmul1 : ρ * (r : ℝ) * M + 1 < c_coer * t ^ (1 / (ρ - 1)) :=
      (div_lt_iff₀' hc_pos).mp hA_lt_rpow
    have hmul2 : (ρ * (r : ℝ) * M + 1) * t < c_coer * t ^ β := by
      have h1 : (ρ * (r : ℝ) * M + 1) * t < c_coer * (t ^ (1 / (ρ - 1)) * t) := by
        linarith [mul_lt_mul_of_pos_right hmul1 ht_pos]
      have hexp : t ^ (1 / (ρ - 1)) * t = t ^ β := by
        calc t ^ (1 / (ρ - 1)) * t = t ^ (1 / (ρ - 1)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = t ^ (1 / (ρ - 1) + 1) := (Real.rpow_add ht_pos _ _).symm
          _ = t ^ β := by congr 1; dsimp [β]; field_simp [hρ_sub.ne']; ring
      rwa [hexp] at h1
    have hdot_le : ρ * ∑ j : Fin r, ζ j * x j ≤ ρ * (r : ℝ) * M * t := by
      have h1 := (le_abs_self _).trans (euc_dot_abs_le p ζ x)
      have h2 : (r : ℝ) * t * ‖x‖ ≤ (r : ℝ) * t * M :=
        mul_le_mul_of_nonneg_left hxM (mul_nonneg (Nat.cast_nonneg r) ht_pos.le)
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hρ_pos.le
      linarith
    have hdiff_neg : ρ * (∑ j : Fin r, ζ j * x j) - c_coer * t ^ β < 0 := by linarith
    unfold RbarObjective
    rw [if_neg hρ_ne1]
    have hsub_le : ((ρ * ∑ j : Fin r, ζ j * x j : ℝ) : EReal) -
          ((ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θs ρ ζ : ENNReal) : EReal) ≤
        ((ρ * ∑ j : Fin r, ζ j * x j : ℝ) : EReal) -
          ((ENNReal.ofReal (c_coer * t ^ β) : ENNReal) : EReal) :=
      EReal.sub_le_sub le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hcoer ζ))
    have hrhs_eq : ((ρ * ∑ j : Fin r, ζ j * x j : ℝ) : EReal) -
          ((ENNReal.ofReal (c_coer * t ^ β) : ENNReal) : EReal) =
        ((ρ * (∑ j : Fin r, ζ j * x j) - c_coer * t ^ β : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg hc_pos.le (Real.rpow_nonneg ht_pos.le _)), ← EReal.coe_sub]
    exact (hsub_le.trans_eq hrhs_eq).trans_lt (EReal.coe_lt_coe_iff.mpr hdiff_neg)
  have hRbar_eq_BM : Rbar μ W0 p h θs ρ x = ⨆ ζ ∈ B_M, RbarObjective μ W0 p h θs ρ x ζ := by
    unfold Rbar RbarFeasible
    rw [if_neg hρ_ne1]
    apply le_antisymm
    · refine iSup₂_le fun ζ _ => ?_
      by_cases hζ : ζ ∈ B_M
      · exact le_iSup₂_of_le ζ hζ le_rfl
      · have h0_le : (0 : EReal) ≤ ⨆ ζ' ∈ B_M, RbarObjective μ W0 p h θs ρ x ζ' := by
          rw [← rbarObjective_zero W0 p h θs hρ x]
          exact le_iSup₂_of_le 0 h0_BM le_rfl
        exact (hout_neg ζ hζ).le.trans h0_le
    · exact iSup₂_le fun ζ _ => le_iSup₂_of_le ζ (Set.mem_univ ζ) le_rfl
  have hRbar_ub : Rbar μ W0 p h θs ρ x ≤ ((ρ * ((r : ℝ) * R_M * M) : ℝ) : EReal) := by
    rw [hRbar_eq_BM]
    refine iSup₂_le fun ζ hζ => ?_
    unfold RbarObjective
    rw [if_neg hρ_ne1]
    have hdot : ρ * ∑ j : Fin r, ζ j * x j ≤ ρ * ((r : ℝ) * R_M * M) := by
      have h1 := (le_abs_self _).trans (euc_dot_abs_le p ζ x)
      have h2 : (r : ℝ) * ‖WithLp.toLp p ζ‖ * ‖x‖ ≤ (r : ℝ) * R_M * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hζ (Nat.cast_nonneg r)) hxM
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg r) hRM_pos.le)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hρ_pos.le
    have hsub0 : ((ρ * ∑ j : Fin r, ζ j * x j : ℝ) : EReal) -
          ((ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θs ρ ζ : ENNReal) : EReal) ≤
        ((ρ * ∑ j : Fin r, ζ j * x j : ℝ) : EReal) - (0 : EReal) :=
      EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
    rw [sub_zero] at hsub0
    exact hsub0.trans (EReal.coe_le_coe_iff.mpr hdot)
  have hRbar_lt_top : Rbar μ W0 p h θs ρ x < ⊤ := hRbar_ub.trans_lt (EReal.coe_lt_top _)
  have hRbar_nn : (0 : EReal) ≤ Rbar μ W0 p h θs ρ x := rbar_nonneg W0 p h θs hρ x
  have hRbar_nb : Rbar μ W0 p h θs ρ x ≠ ⊥ := by
    intro hbot; rw [hbot] at hRbar_nn; exact absurd (le_bot_iff.mp hRbar_nn) (EReal.coe_ne_bot 0)
  let m_star : ℝ := (Rbar μ W0 p h θs ρ x).toReal
  have hRbar_coe : Rbar μ W0 p h θs ρ x = ((m_star : ℝ) : EReal) :=
    (EReal.coe_toReal hRbar_lt_top.ne hRbar_nb).symm
  have hex_seq : ∀ k : ℕ, ∃ ζ ∈ B_M,
      ((m_star - 1 / ((k : ℝ) + 1) : ℝ) : EReal) < RbarObjective μ W0 p h θs ρ x ζ := by
    intro k
    have hk_pos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt : ((m_star - 1 / ((k : ℝ) + 1) : ℝ) : EReal) <
        ⨆ ζ ∈ B_M, RbarObjective μ W0 p h θs ρ x ζ := by
      rw [← hRbar_eq_BM, hRbar_coe]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨ζ, hlt'⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hζ_BM, hζ_lt⟩ := lt_iSup_iff.mp hlt'
    exact ⟨ζ, hζ_BM, hζ_lt⟩
  choose ζ_seq hζ_BM hζ_gt using hex_seq
  obtain ⟨ζ₀, hζ₀_BM, φ, hφ_mono, hφ_lim⟩ :=
    (isCompact_toLp_closedBall p R_M).tendsto_subseq hζ_BM
  let q_real : ℕ → ℝ := fun k =>
    (ρ * (∑ j : Fin r, ζ_seq (φ k) j * x j) - m_star + 1 / ((φ k : ℝ) + 1)) / (ρ - 1)
  let q_lim : ℝ := (ρ * (∑ j : Fin r, ζ₀ j * x j) - m_star) / (ρ - 1)
  have hmom_le_q : ∀ k : ℕ, 0 ≤ q_real k ∧
      rowMoment μ W0 p h θs ρ (ζ_seq (φ k)) ≤ ENNReal.ofReal (q_real k) := by
    intro k
    have hgt := hζ_gt (φ k)
    unfold RbarObjective at hgt
    rw [if_neg hρ_ne1] at hgt
    have hmom_ne_top : rowMoment μ W0 p h θs ρ (ζ_seq (φ k)) ≠ ⊤ := by
      intro htop
      have hprod_top : ENNReal.ofReal (ρ - 1) * rowMoment μ W0 p h θs ρ (ζ_seq (φ k)) = ⊤ := by
        rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρ_sub).ne']
      rw [hprod_top, EReal.coe_ennreal_top, EReal.sub_top] at hgt
      exact absurd hgt (not_lt_of_ge bot_le)
    let M_k : ℝ := (rowMoment μ W0 p h θs ρ (ζ_seq (φ k))).toReal
    have hMk_nn : 0 ≤ M_k := ENNReal.toReal_nonneg
    have hprod_eq : ((ENNReal.ofReal (ρ - 1) *
        rowMoment μ W0 p h θs ρ (ζ_seq (φ k)) : ENNReal) : EReal) =
        (((ρ - 1) * M_k : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hmom_ne_top]
      rw [← ENNReal.ofReal_mul hρ_sub.le, EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg hρ_sub.le hMk_nn)]
    rw [hprod_eq, ← EReal.coe_sub] at hgt
    have hgt_real : m_star - 1 / ((φ k : ℝ) + 1) <
        ρ * (∑ j : Fin r, ζ_seq (φ k) j * x j) - (ρ - 1) * M_k :=
      EReal.coe_lt_coe_iff.mp hgt
    have hMk_le : M_k ≤ q_real k := by
      rw [le_div_iff₀ hρ_sub]
      linarith
    refine ⟨hMk_nn.trans hMk_le, ?_⟩
    rw [← ENNReal.ofReal_toReal hmom_ne_top]
    exact ENNReal.ofReal_le_ofReal hMk_le
  have hq_tendsto : Tendsto q_real atTop (𝓝 q_lim) := by
    have hdot_lim : Tendsto (fun k : ℕ => ∑ j : Fin r, ζ_seq (φ k) j * x j) atTop
        (𝓝 (∑ j : Fin r, ζ₀ j * x j)) :=
      tendsto_finsetSum Finset.univ fun j _ =>
        (((continuous_apply j).tendsto ζ₀).comp hφ_lim).mul_const (x j)
    have hinv_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hinv_lim : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      hinv_nat.comp hφ_mono.tendsto_atTop
    have hnum_lim : Tendsto
        (fun k : ℕ => ρ * (∑ j : Fin r, ζ_seq (φ k) j * x j) - m_star + 1 / ((φ k : ℝ) + 1))
        atTop (𝓝 (ρ * (∑ j : Fin r, ζ₀ j * x j) - m_star + 0)) :=
      ((hdot_lim.const_mul ρ).sub_const m_star).add hinv_lim
    rw [add_zero] at hnum_lim
    exact hnum_lim.div_const (ρ - 1)
  have hqlim_nn : 0 ≤ q_lim := ge_of_tendsto' hq_tendsto fun k => (hmom_le_q k).1
  have hrow_cont : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) => rowNorm p h θs zw.1 zw.2) :=
    continuous_norm.comp (continuous_toLp_rowVec p h θs hC1)
  have hfatou : rowMoment μ W0 p h θs ρ ζ₀ ≤
      liminf (fun k : ℕ => rowMoment μ W0 p h θs ρ (ζ_seq (φ k))) atTop := by
    let u_fn : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ENNReal.ofReal (rowNorm p h θs (ζ_seq (φ k)) (W0 ω) ^ β)
    have hu_meas : ∀ k : ℕ, Measurable (u_fn k) := fun k =>
      ENNReal.measurable_ofReal.comp
        (((hrow_cont.comp (continuous_const.prodMk continuous_id)).measurable.comp hW0_meas).pow_const β)
    have hu_lim : ∀ ω : Ω,
        ENNReal.ofReal (rowNorm p h θs ζ₀ (W0 ω) ^ β) = liminf (fun k => u_fn k ω) atTop := by
      intro ω
      have h1 : Continuous (fun ζ : Fin r → ℝ =>
          ENNReal.ofReal (rowNorm p h θs ζ (W0 ω) ^ β)) :=
        ENNReal.continuous_ofReal.comp
          ((hrow_cont.comp (continuous_id.prodMk continuous_const)).rpow_const fun _ => Or.inr hβ_pos.le)
      exact ((h1.tendsto ζ₀).comp hφ_lim).liminf_eq.symm
    calc rowMoment μ W0 p h θs ρ ζ₀
        = ∫⁻ ω, liminf (fun k => u_fn k ω) atTop ∂μ :=
          lintegral_congr fun ω => hu_lim ω
      _ ≤ liminf (fun k => ∫⁻ ω, u_fn k ω ∂μ) atTop := lintegral_liminf_le hu_meas
      _ = liminf (fun k => rowMoment μ W0 p h θs ρ (ζ_seq (φ k))) atTop := rfl
  have hmom0_le_eps : ∀ ε : ℝ, 0 < ε →
      rowMoment μ W0 p h θs ρ ζ₀ ≤ ENNReal.ofReal (q_lim + ε) := by
    intro ε hε
    have hev : ∀ᶠ k in atTop, q_real k < q_lim + ε :=
      hq_tendsto.eventually (gt_mem_nhds (by linarith))
    have hev_enn : ∀ᶠ k in atTop,
        rowMoment μ W0 p h θs ρ (ζ_seq (φ k)) ≤ ENNReal.ofReal (q_lim + ε) := by
      filter_upwards [hev] with k hk
      exact (hmom_le_q k).2.trans (ENNReal.ofReal_le_ofReal hk.le)
    exact hfatou.trans (liminf_le_of_frequently_le' hev_enn.frequently)
  have hmom0_ne_top : rowMoment μ W0 p h θs ρ ζ₀ ≠ ⊤ :=
    ((hmom0_le_eps 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top).ne
  have hmom0_toReal_le : (rowMoment μ W0 p h θs ρ ζ₀).toReal ≤ q_lim := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmom0_le_eps ε hε)
    rwa [ENNReal.toReal_ofReal (by linarith)] at h1
  have hobj0_ge : Rbar μ W0 p h θs ρ x ≤ RbarObjective μ W0 p h θs ρ x ζ₀ := by
    rw [hRbar_coe]
    unfold RbarObjective
    rw [if_neg hρ_ne1]
    have hprod_eq : ((ENNReal.ofReal (ρ - 1) *
        rowMoment μ W0 p h θs ρ ζ₀ : ENNReal) : EReal) =
        (((ρ - 1) * (rowMoment μ W0 p h θs ρ ζ₀).toReal : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hmom0_ne_top]
      rw [← ENNReal.ofReal_mul hρ_sub.le, EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg hρ_sub.le ENNReal.toReal_nonneg)]
    rw [hprod_eq, ← EReal.coe_sub]
    refine EReal.coe_le_coe_iff.mpr ?_
    have hmul_le : (ρ - 1) * (rowMoment μ W0 p h θs ρ ζ₀).toReal ≤
        ρ * (∑ j : Fin r, ζ₀ j * x j) - m_star := by
      have := mul_le_mul_of_nonneg_left hmom0_toReal_le hρ_sub.le
      dsimp [q_lim] at this
      rwa [mul_div_cancel₀ _ hρ_sub.ne'] at this
    linarith
  have hobj0_le : RbarObjective μ W0 p h θs ρ x ζ₀ ≤ Rbar μ W0 p h θs ρ x := by
    rw [hRbar_eq_BM]
    exact le_iSup₂_of_le ζ₀ hζ₀_BM le_rfl
  exact ⟨ζ₀, hζ₀_BM, le_antisymm hobj0_le hobj0_ge, hRbar_lt_top⟩

private lemma rbar_props {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ}
    (W0 : Ω → (Fin m → ℝ)) (hW0_meas : Measurable W0) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W0 ω)}) :
    (∀ x : EuclideanSpace ℝ (Fin r), ∃ ζ₀ ∈ RbarFeasible μ W0 p h θs ρ,
      RbarObjective μ W0 p h θs ρ x ζ₀ = Rbar μ W0 p h θs ρ x) ∧
    (∀ x : EuclideanSpace ℝ (Fin r),
      (0 : EReal) ≤ Rbar μ W0 p h θs ρ x ∧ Rbar μ W0 p h θs ρ x < ⊤) ∧
    Continuous (fun x : EuclideanSpace ℝ (Fin r) => (Rbar μ W0 p h θs ρ x).toReal) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hRbar_zero : ∀ x : EuclideanSpace ℝ (Fin 0), Rbar μ W0 p h θs ρ x = 0 := by
      intro x
      refine le_antisymm ?_ (rbar_nonneg W0 p h θs hρ x)
      unfold Rbar
      refine iSup₂_le fun ζ _ => ?_
      have hζ : ζ = 0 := Subsingleton.elim ζ 0
      rw [hζ, rbarObjective_zero W0 p h θs hρ x]
    refine ⟨fun x => ⟨0, zero_mem_rbarFeasible W0 p h θs ρ, ?_⟩,
      fun x => ?_, ?_⟩
    · rw [hRbar_zero x, rbarObjective_zero W0 p h θs hρ x]
    · rw [hRbar_zero x]; exact ⟨le_rfl, EReal.coe_lt_top 0⟩
    · simp_rw [hRbar_zero]; exact continuous_const
  · rcases eq_or_lt_of_le hρ with rfl | hρ_gt
    · obtain ⟨h0_F, _, _, B_F, hBF_pos, hF_bdd, hF_comp⟩ :=
        rbarFeasibleOne_props hr W0 p h θs hC1 hA4
      have hfeas_eq : RbarFeasible μ W0 p h θs 1 = rbarFeasibleOne μ W0 p h θs := by
        unfold RbarFeasible rbarFeasibleOne; simp
      have hmax_all : ∀ x : EuclideanSpace ℝ (Fin r),
          ∃ ζ₀ ∈ rbarFeasibleOne μ W0 p h θs,
            Rbar μ W0 p h θs 1 x = ((∑ j : Fin r, ζ₀ j * x j : ℝ) : EReal) ∧
            ∀ ζ ∈ rbarFeasibleOne μ W0 p h θs,
              ∑ j : Fin r, ζ j * x j ≤ ∑ j : Fin r, ζ₀ j * x j := by
        intro x
        have hlin_cont : Continuous (fun ζ : Fin r → ℝ => ∑ j : Fin r, ζ j * x j) :=
          continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).mul continuous_const
        obtain ⟨ζ₀, hζ₀_mem, hζ₀_max⟩ :=
          hF_comp.exists_isMaxOn ⟨0, h0_F⟩ hlin_cont.continuousOn
        refine ⟨ζ₀, hζ₀_mem, ?_, fun ζ hζ => hζ₀_max hζ⟩
        unfold Rbar RbarObjective
        simp only [hfeas_eq, ↓reduceIte]
        exact le_antisymm
          (iSup₂_le fun ζ hζ => EReal.coe_le_coe_iff.mpr (hζ₀_max hζ))
          (le_iSup₂_of_le ζ₀ hζ₀_mem le_rfl)
      refine ⟨fun x => ?_, fun x => ?_, ?_⟩
      · obtain ⟨ζ₀, hζ₀_mem, hR_eq, _⟩ := hmax_all x
        refine ⟨ζ₀, hfeas_eq.symm ▸ hζ₀_mem, ?_⟩
        rw [hR_eq]; unfold RbarObjective; simp
      · obtain ⟨ζ₀, _, hR_eq, _⟩ := hmax_all x
        exact ⟨rbar_nonneg W0 p h θs le_rfl x, hR_eq ▸ EReal.coe_lt_top _⟩
      · rw [Metric.continuous_iff]
        intro x₀ ε hε
        let L_lip : ℝ := (r : ℝ) * B_F + 1
        have hL_pos : 0 < L_lip := by positivity
        refine ⟨ε / L_lip, div_pos hε hL_pos, fun x hx => ?_⟩
        obtain ⟨ζ_x, hζx_mem, hRx_eq, hζx_max⟩ := hmax_all x
        obtain ⟨ζ_0, hζ0_mem, hR0_eq, hζ0_max⟩ := hmax_all x₀
        have htoReal_x : (Rbar μ W0 p h θs 1 x).toReal = ∑ j : Fin r, ζ_x j * x j := by
          rw [hRx_eq, EReal.toReal_coe]
        have htoReal_0 : (Rbar μ W0 p h θs 1 x₀).toReal = ∑ j : Fin r, ζ_0 j * x₀ j := by
          rw [hR0_eq, EReal.toReal_coe]
        have hdiff1 : (Rbar μ W0 p h θs 1 x).toReal - (Rbar μ W0 p h θs 1 x₀).toReal ≤
            (r : ℝ) * B_F * ‖x - x₀‖ := by
          rw [htoReal_x, htoReal_0]
          calc (∑ j : Fin r, ζ_x j * x j) - (∑ j : Fin r, ζ_0 j * x₀ j)
              ≤ (∑ j : Fin r, ζ_x j * x j) - (∑ j : Fin r, ζ_x j * x₀ j) :=
                sub_le_sub_left (hζ0_max ζ_x hζx_mem) _
            _ ≤ |(∑ j : Fin r, ζ_x j * x j) - (∑ j : Fin r, ζ_x j * x₀ j)| := le_abs_self _
            _ ≤ (r : ℝ) * ‖WithLp.toLp p ζ_x‖ * ‖x - x₀‖ := euc_dot_sub_abs_le p ζ_x x x₀
            _ ≤ (r : ℝ) * B_F * ‖x - x₀‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hF_bdd ζ_x hζx_mem) (Nat.cast_nonneg r))
                  (norm_nonneg _)
        have hdiff2 : (Rbar μ W0 p h θs 1 x₀).toReal - (Rbar μ W0 p h θs 1 x).toReal ≤
            (r : ℝ) * B_F * ‖x - x₀‖ := by
          rw [htoReal_x, htoReal_0]
          calc (∑ j : Fin r, ζ_0 j * x₀ j) - (∑ j : Fin r, ζ_x j * x j)
              ≤ (∑ j : Fin r, ζ_0 j * x₀ j) - (∑ j : Fin r, ζ_0 j * x j) :=
                sub_le_sub_left (hζx_max ζ_0 hζ0_mem) _
            _ ≤ |(∑ j : Fin r, ζ_0 j * x₀ j) - (∑ j : Fin r, ζ_0 j * x j)| := le_abs_self _
            _ ≤ (r : ℝ) * ‖WithLp.toLp p ζ_0‖ * ‖x₀ - x‖ := euc_dot_sub_abs_le p ζ_0 x₀ x
            _ = (r : ℝ) * ‖WithLp.toLp p ζ_0‖ * ‖x - x₀‖ := by rw [norm_sub_rev]
            _ ≤ (r : ℝ) * B_F * ‖x - x₀‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hF_bdd ζ_0 hζ0_mem) (Nat.cast_nonneg r))
                  (norm_nonneg _)
        have habs_le : |(Rbar μ W0 p h θs 1 x).toReal - (Rbar μ W0 p h θs 1 x₀).toReal| ≤
            L_lip * dist x x₀ := by
          rw [← dist_eq_norm] at hdiff1 hdiff2
          rw [abs_le]
          have h1 : (r : ℝ) * B_F * dist x x₀ ≤ L_lip * dist x x₀ :=
            mul_le_mul_of_nonneg_right (by dsimp [L_lip]; linarith) dist_nonneg
          exact ⟨by linarith, by linarith⟩
        rw [Real.dist_eq]
        exact habs_le.trans_lt ((mul_lt_mul_of_pos_left hx hL_pos).trans_eq
          (mul_div_cancel₀ ε hL_pos.ne'))
    · have hρ_ne1 : ρ ≠ 1 := hρ_gt.ne'
      have hρ_sub : 0 < ρ - 1 := sub_pos.mpr hρ_gt
      have hρ_pos : 0 < ρ := zero_lt_one.trans hρ_gt
      obtain ⟨c_coer, hc_pos, hcoer⟩ :=
        exists_rowMoment_coercive hr W0 hW0_meas p h θs hρ_gt hC1 hA4
      refine ⟨fun x => ?_, fun x => ?_, ?_⟩
      · obtain ⟨R_M, _, hmax⟩ :=
          rbar_gt_one_ball_max W0 hW0_meas p h θs hρ_gt hC1 hc_pos hcoer (norm_nonneg x)
        obtain ⟨ζ₀, _, hobj_eq, _⟩ := hmax x le_rfl
        have hfeas : ζ₀ ∈ RbarFeasible μ W0 p h θs ρ := by
          unfold RbarFeasible; simp [hρ_ne1]
        exact ⟨ζ₀, hfeas, hobj_eq⟩
      · obtain ⟨R_M, _, hmax⟩ :=
          rbar_gt_one_ball_max W0 hW0_meas p h θs hρ_gt hC1 hc_pos hcoer (norm_nonneg x)
        obtain ⟨_, _, _, hlt_top⟩ := hmax x le_rfl
        exact ⟨rbar_nonneg W0 p h θs hρ x, hlt_top⟩
      · rw [continuous_iff_continuousAt]
        intro x₀
        rw [Metric.continuousAt_iff]
        intro ε hε
        let M : ℝ := ‖x₀‖ + 1
        have hM_nn : 0 ≤ M := by positivity
        obtain ⟨R_M, hRM_ge1, hmax⟩ :=
          rbar_gt_one_ball_max W0 hW0_meas p h θs hρ_gt hC1 hc_pos hcoer hM_nn
        have hRM_pos : 0 < R_M := zero_lt_one.trans_le hRM_ge1
        let L_lip : ℝ := ρ * (r : ℝ) * R_M + 1
        have hL_pos : 0 < L_lip := by positivity
        refine ⟨min 1 (ε / L_lip), lt_min zero_lt_one (div_pos hε hL_pos), fun {x} hx => ?_⟩
        have hx_dist1 : dist x x₀ ≤ 1 := hx.le.trans (min_le_left 1 _)
        have hx_distL : dist x x₀ < ε / L_lip := hx.trans_le (min_le_right 1 _)
        have hx_norm : ‖x‖ ≤ M := by
          have := norm_sub_norm_le x x₀
          rw [← dist_eq_norm] at this
          dsimp [M]; linarith
        have hx0_norm : ‖x₀‖ ≤ M := by dsimp [M]; linarith
        have hsub_bound : ∀ y z : EuclideanSpace ℝ (Fin r), ‖y‖ ≤ M → ‖z‖ ≤ M →
            (Rbar μ W0 p h θs ρ y).toReal - (Rbar μ W0 p h θs ρ z).toReal ≤
              ρ * (r : ℝ) * R_M * ‖y - z‖ := by
          intro y z hy hz
          obtain ⟨ζ_y, hζy_norm, hRy_eq, hRy_lt_top⟩ := hmax y hy
          obtain ⟨_, _, _, hRz_lt_top⟩ := hmax z hz
          have hRy_nn : (0 : EReal) ≤ Rbar μ W0 p h θs ρ y := rbar_nonneg W0 p h θs hρ y
          have hRz_nn : (0 : EReal) ≤ Rbar μ W0 p h θs ρ z := rbar_nonneg W0 p h θs hρ z
          have hRy_nb : Rbar μ W0 p h θs ρ y ≠ ⊥ := by
            intro hb; rw [hb] at hRy_nn; exact absurd (le_bot_iff.mp hRy_nn) (EReal.coe_ne_bot 0)
          have hRz_nb : Rbar μ W0 p h θs ρ z ≠ ⊥ := by
            intro hb; rw [hb] at hRz_nn; exact absurd (le_bot_iff.mp hRz_nn) (EReal.coe_ne_bot 0)
          have hmom_ne_top : rowMoment μ W0 p h θs ρ ζ_y ≠ ⊤ := by
            intro htop
            have hobj_bot : RbarObjective μ W0 p h θs ρ y ζ_y = ⊥ := by
              unfold RbarObjective
              rw [if_neg hρ_ne1, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρ_sub).ne',
                EReal.coe_ennreal_top, EReal.sub_top]
            exact hRy_nb (hRy_eq ▸ hobj_bot)
          let m_mom : ℝ := (rowMoment μ W0 p h θs ρ ζ_y).toReal
          have hobj_real : ∀ w : EuclideanSpace ℝ (Fin r),
              RbarObjective μ W0 p h θs ρ w ζ_y =
                ((ρ * (∑ j : Fin r, ζ_y j * w j) - (ρ - 1) * m_mom : ℝ) : EReal) := by
            intro w
            unfold RbarObjective
            rw [if_neg hρ_ne1]
            have hprod : ((ENNReal.ofReal (ρ - 1) *
                rowMoment μ W0 p h θs ρ ζ_y : ENNReal) : EReal) =
                (((ρ - 1) * m_mom : ℝ) : EReal) := by
              conv_lhs => rw [← ENNReal.ofReal_toReal hmom_ne_top]
              rw [← ENNReal.ofReal_mul hρ_sub.le, EReal.coe_ennreal_ofReal,
                max_eq_left (mul_nonneg hρ_sub.le ENNReal.toReal_nonneg)]
            rw [hprod, ← EReal.coe_sub]
          have hRy_val : (Rbar μ W0 p h θs ρ y).toReal =
              ρ * (∑ j : Fin r, ζ_y j * y j) - (ρ - 1) * m_mom := by
            rw [← hRy_eq, hobj_real y, EReal.toReal_coe]
          have hRz_ge : ρ * (∑ j : Fin r, ζ_y j * z j) - (ρ - 1) * m_mom ≤
              (Rbar μ W0 p h θs ρ z).toReal := by
            have hle : RbarObjective μ W0 p h θs ρ z ζ_y ≤ Rbar μ W0 p h θs ρ z := by
              unfold Rbar RbarFeasible; rw [if_neg hρ_ne1]
              exact le_iSup₂_of_le ζ_y (Set.mem_univ ζ_y) le_rfl
            rw [hobj_real z, ← EReal.coe_toReal hRz_lt_top.ne hRz_nb] at hle
            exact EReal.coe_le_coe_iff.mp hle
          have hsub1 : (Rbar μ W0 p h θs ρ y).toReal - (Rbar μ W0 p h θs ρ z).toReal ≤
              ρ * ((∑ j : Fin r, ζ_y j * y j) - (∑ j : Fin r, ζ_y j * z j)) := by
            rw [hRy_val]; linarith
          have hsub2 : |(∑ j : Fin r, ζ_y j * y j) - (∑ j : Fin r, ζ_y j * z j)| ≤
              (r : ℝ) * R_M * ‖y - z‖ :=
            (euc_dot_sub_abs_le p ζ_y y z).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hζy_norm (Nat.cast_nonneg r)) (norm_nonneg _))
          calc (Rbar μ W0 p h θs ρ y).toReal - (Rbar μ W0 p h θs ρ z).toReal
              ≤ ρ * ((∑ j : Fin r, ζ_y j * y j) - (∑ j : Fin r, ζ_y j * z j)) := hsub1
            _ ≤ ρ * |(∑ j : Fin r, ζ_y j * y j) - (∑ j : Fin r, ζ_y j * z j)| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) hρ_pos.le
            _ ≤ ρ * ((r : ℝ) * R_M * ‖y - z‖) :=
                mul_le_mul_of_nonneg_left hsub2 hρ_pos.le
            _ = ρ * (r : ℝ) * R_M * ‖y - z‖ := by ring
        have hdiff1 := hsub_bound x x₀ hx_norm hx0_norm
        have hdiff2 := hsub_bound x₀ x hx0_norm hx_norm
        rw [norm_sub_rev] at hdiff2
        have habs_le : |(Rbar μ W0 p h θs ρ x).toReal - (Rbar μ W0 p h θs ρ x₀).toReal| ≤
            L_lip * dist x x₀ := by
          rw [← dist_eq_norm] at hdiff1 hdiff2
          rw [abs_le]
          have h1 : ρ * (r : ℝ) * R_M * dist x x₀ ≤ L_lip * dist x x₀ :=
            mul_le_mul_of_nonneg_right (by dsimp [L_lip]; linarith) dist_nonneg
          exact ⟨by linarith, by linarith⟩
        rw [Real.dist_eq]
        exact habs_le.trans_lt ((mul_lt_mul_of_pos_left hx_distL hL_pos).trans_eq
          (mul_div_cancel₀ ε hL_pos.ne'))


end SolRWPILimitThm3

open SolRWPILimitThm3

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    -- A1)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    -- A2)
    (hint : Integrable (fun ω => h (W 0 ω) θs) μ) (hmean : ∫ ω, h (W 0 ω) θs ∂μ = 0)
    (hL2 : MemLp (fun ω => h (W 0 ω) θs) 2 μ)
    -- A3)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    -- A4)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W 0 ω)}) :
    (∀ n : ℕ, 1 ≤ n → ∀ ω, rwp (costQ q ρ) h θs
        (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω)) < ⊤) ∧
    (∀ n : ℕ, AEMeasurable (fun ω => rwp (costQ q ρ) h θs
        (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω))) μ) ∧
    (∀ x : EuclideanSpace ℝ (Fin r), ∃ ζ₀ ∈ RbarFeasible μ (W 0) p h θs ρ,
        RbarObjective μ (W 0) p h θs ρ x ζ₀ = Rbar μ (W 0) p h θs ρ x) ∧
    (∀ f : ℝ → ℝ, Continuous f → Monotone f → (∃ C : ℝ, ∀ t, |f t| ≤ C) →
      limsup (fun n : ℕ => ∫ ω, f ((n : ℝ) ^ (ρ / 2) * (rwp (costQ q ρ) h θs
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => W i ω))).toReal) ∂μ)
        atTop
      ≤ ∫ x, f (Rbar μ (W 0) p h θs ρ x).toReal ∂(multivariateGaussian 0 (covMatrix μ (W 0) h θs))) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨hq.le⟩
  have h0 := zero_mem_interior_convexHull (W 0) p h θs hint hmean hC1 hA4
  exact ⟨(fun n hn ω => rwp_costQ_lt_top (lt_of_lt_of_le Nat.zero_lt_one hn)
      (fun i : Fin n => W i ω) h θs ρ hρ q (interior_subset h0)),
    aemeasurable_rwp_emp W hWmeas h θs ρ hρ q hC1 h0,
    (rbar_props (W 0) (hWmeas 0) p h θs ρ hρ hC1 hA4).1,
    RWPI.Limit.asymptotic_upper_bound W hWmeas hindep hident h θs ρ hρ q p hq hpq
      hint hmean hL2 hC1 hA4⟩
