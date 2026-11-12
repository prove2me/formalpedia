-- Prove2me | solution 1 for RWPI.Limit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:38:11.888086+00:00
-- url     : https://prove2.me/submissions/f145a676-28a2-46f4-98f7-2652a0876d30

import Mathlib
import Definitions.Def_RWPI_Limit_dualRep
import Definitions.Def_RWPI_Limit_rowNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology RWPI.Limit
open scoped ENNReal

namespace SolRWPILimitLemma2

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

private lemma norm_le_toLp_norm {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Fin d → ℝ) :
    ‖x‖ ≤ ‖WithLp.toLp p x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp p x))).mpr fun j => ?_
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [PiLp.norm_eq_ciSup]
    exact le_ciSup (f := fun i : Fin d => ‖x i‖) (Finite.bddAbove_range _) j
  · have hp_one : 1 ≤ p := Fact.out
    have hp_zero : p ≠ 0 := (zero_lt_one.trans_le hp_one).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
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
    have hq_zero : q ≠ 0 := (zero_lt_one.trans_le hq_one).ne'
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_zero hq_top
    rw [PiLp.norm_eq_sum hq_pos]
    have hsum : ∑ i : Fin d,
        ‖(WithLp.toLp q (Pi.single j (1 : ℝ) : Fin d → ℝ)) i‖ ^ q.toReal = 1 := by
      change ∑ i : Fin d, ‖(Pi.single j (1 : ℝ) : Fin d → ℝ) i‖ ^ q.toReal = 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij, Real.zero_rpow hq_pos.ne']
      · intro h_abs
        exact absurd (Finset.mem_univ j) h_abs
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
  ext k
  simp [rowVec, Finset.mul_sum, mul_assoc]

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
  set g : ℝ → (Fin r → ℝ) := fun u => fderiv ℝ (fun x => h x θs) (w + c • (u • Δ)) Δ
  have hg_cont : Continuous g := by
    have hfderiv : Continuous (fun x : Fin m → ℝ => fderiv ℝ (fun y => h y θs) x) :=
      hC1.continuous_fderiv one_ne_zero
    have hpath : Continuous (fun u : ℝ => w + c • (u • Δ)) := by fun_prop
    exact (ContinuousLinearMap.apply ℝ (Fin r → ℝ) Δ).continuous.comp (hfderiv.comp hpath)
  set Lζ : (Fin r → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => ζ ⬝ᵥ y
        map_add' := fun x y => dotProduct_add ζ x y
        map_smul' := fun a y => by simp [dotProduct_smul] }
  have hcomm : Lζ (∫ u in (0 : ℝ)..1, g u) = ∫ u in (0 : ℝ)..1, Lζ (g u) :=
    (Lζ.intervalIntegral_comp_comm (hg_cont.intervalIntegrable 0 1)).symm
  calc ζ ⬝ᵥ (∫ u in (0 : ℝ)..1, g u) = Lζ (∫ u in (0 : ℝ)..1, g u) := rfl
    _ = ∫ u in (0 : ℝ)..1, Lζ (g u) := hcomm
    _ = ∫ u in (0 : ℝ)..1, rowVec h θs ζ (w + c • (u • Δ)) ⬝ᵥ Δ := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact dot_fderiv_eq_rowVec_dot h θs ζ (w + c • (u • Δ)) Δ

private lemma exists_trunc_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m l r : ℕ} (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ξ : Fin r → ℝ) (hpos : 0 < μ {ω | 0 < rowNorm p h θs ξ (W0 ω)}) :
    ∃ k : ℕ, 0 < μ {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
      1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} := by
  by_contra hall
  push Not at hall
  have hnull : ∀ k : ℕ, μ {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
      1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} = 0 :=
    fun k => nonpos_iff_eq_zero.mp (hall k)
  have hsub : {ω | 0 < rowNorm p h θs ξ (W0 ω)} ⊆
      ⋃ k : ℕ, {ω | ‖W0 ω‖ ≤ (k : ℝ) + 1 ∧
        1 / ((k : ℝ) + 1) ≤ rowNorm p h θs ξ (W0 ω)} := by
    intro ω hω
    change 0 < rowNorm p h θs ξ (W0 ω) at hω
    obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖W0 ω‖
    obtain ⟨k₂, hk₂⟩ := exists_nat_ge (1 / rowNorm p h θs ξ (W0 ω))
    refine Set.mem_iUnion.mpr ⟨max k₁ k₂, ?_, ?_⟩
    · have hk1_le : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := Nat.cast_le.mpr (le_max_left k₁ k₂)
      linarith
    · have hk2_le : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := Nat.cast_le.mpr (le_max_right k₁ k₂)
      have hdenom_pos : (0 : ℝ) < (max k₁ k₂ : ℕ) + 1 := by positivity
      rw [div_le_iff₀ hdenom_pos]
      have h1 : 1 ≤ rowNorm p h θs ξ (W0 ω) * (k₂ : ℝ) := (div_le_iff₀' hω).mp hk₂
      have h2 : rowNorm p h θs ξ (W0 ω) * (k₂ : ℝ) ≤
          rowNorm p h θs ξ (W0 ω) * ((max k₁ k₂ : ℕ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hω.le
      linarith
  have hzero : μ {ω | 0 < rowNorm p h θs ξ (W0 ω)} = 0 :=
    nonpos_iff_eq_zero.mp ((measure_mono hsub).trans (measure_iUnion_null hnull).le)
  exact hpos.ne' hzero

private lemma tendsto_prob_gt_of_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hZmeas : ∀ n, Measurable (Z n)) (c : ℝ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 c)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => μ {ω | η < |Z n ω - c|}) atTop (𝓝 0) := by
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => Set.indicator {ω' | η < |Z n ω' - c|} 1 ω
  have hSmeas : ∀ n, MeasurableSet {ω | η < |Z n ω - c|} := fun n =>
    measurableSet_lt measurable_const (((hZmeas n).sub measurable_const).norm)
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    measurable_one.indicator (hSmeas n)
  have hFbound : ∀ n, ∀ᵐ ω ∂μ, F n ω ≤ (fun _ : Ω => (1 : ℝ≥0∞)) ω := fun n =>
    Eventually.of_forall fun ω => by
      dsimp [F, Set.indicator]
      split_ifs <;> simp
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

private lemma finset_sum_coe_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = (((∑ i ∈ s, f i) : ℝ) : EReal) := by
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
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc]
    exact bot_le
  | coe a =>
    cases y with
    | bot => exact absurd (le_bot_iff.mp hxy) (EReal.coe_ne_bot a)
    | coe b =>
      rw [← EReal.coe_mul, ← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hxy) hc.le)
    | top =>
      rw [EReal.coe_mul_top_of_pos hc]
      exact le_top
  | top =>
    have hy : y = ⊤ := top_le_iff.mp hxy
    rw [hy]

private lemma ereal_sub_nonpos_of_le {x y : ℝ} {M : EReal} (hxy : x ≤ y)
    (hyM : ((y : ℝ) : EReal) ≤ M) :
    ((x : ℝ) : EReal) - M ≤ 0 := by
  cases M with
  | bot => exact absurd (le_bot_iff.mp hyM) (EReal.coe_ne_bot y)
  | coe m =>
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_le_coe_iff.mp hyM])
  | top => simp

private lemma tight_Hn_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ} (hr : 0 < r)
    (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hint : Integrable (fun ω => h (W 0 ω) θs) μ) (hmean : ∫ ω, h (W 0 ω) θs ∂μ = 0)
    (hL2 : MemLp (fun ω => h (W 0 ω) θs) 2 μ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K_H : ℝ, 0 < K_H ∧ ∀ n : ℕ, 1 ≤ n →
      μ {ω | K_H < ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖} ≤
        ENNReal.ofReal (ε / 2) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hg_meas : ∀ j : Fin r, Measurable (fun w : Fin m → ℝ => h w θs j) := fun j =>
    ((continuous_apply j).comp hC1.continuous).measurable
  have hX0_memLp : ∀ j : Fin r, MemLp (fun ω => h (W 0 ω) θs j) 2 μ := fun j =>
    (ContinuousLinearMap.proj j : (Fin r → ℝ) →L[ℝ] ℝ).comp_memLp' hL2
  have hX_ident : ∀ (j : Fin r) (i : ℕ),
      IdentDistrib (fun ω => h (W i ω) θs j) (fun ω => h (W 0 ω) θs j) μ μ :=
    fun j i => (hident i).comp (hg_meas j)
  have hX_memLp : ∀ (j : Fin r) (i : ℕ), MemLp (fun ω => h (W i ω) θs j) 2 μ := fun j i =>
    (hX_ident j i).memLp_iff.mpr (hX0_memLp j)
  have hX_int : ∀ (j : Fin r) (i : ℕ), Integrable (fun ω => h (W i ω) θs j) μ := fun j i =>
    (hX_ident j i).integrable_iff.mpr
      ((ContinuousLinearMap.proj j : (Fin r → ℝ) →L[ℝ] ℝ).integrable_comp hint)
  have hX_mean : ∀ (j : Fin r) (i : ℕ), ∫ ω, h (W i ω) θs j ∂μ = 0 := fun j i => by
    rw [(hX_ident j i).integral_eq]
    have hcomm := (ContinuousLinearMap.proj j : (Fin r → ℝ) →L[ℝ] ℝ).integral_comp_comm hint
    have h1 : (ContinuousLinearMap.proj j : (Fin r → ℝ) →L[ℝ] ℝ) (∫ ω, h (W 0 ω) θs ∂μ) = 0 := by
      rw [hmean, map_zero]
    exact hcomm.trans h1
  have hX_sq_int : ∀ (j : Fin r) (i : ℕ), Integrable (fun ω => (h (W i ω) θs j) ^ 2) μ :=
    fun j i => (hX_memLp j i).integrable_sq
  have hX_sq_eq : ∀ (j : Fin r) (i : ℕ),
      ∫ ω, (h (W i ω) θs j) ^ 2 ∂μ = ∫ ω, (h (W 0 ω) θs j) ^ 2 ∂μ := fun j i => by
    have hid_sq : IdentDistrib (fun ω => (h (W i ω) θs j) ^ 2)
        (fun ω => (h (W 0 ω) θs j) ^ 2) μ μ :=
      (hX_ident j i).comp (measurable_id.pow_const 2)
    exact hid_sq.integral_eq
  set σ2 : Fin r → ℝ := fun j => ∫ ω, (h (W 0 ω) θs j) ^ 2 ∂μ
  have hσ2_nn : ∀ j : Fin r, 0 ≤ σ2 j := fun j =>
    integral_nonneg fun ω => sq_nonneg _
  set S_tot : ℝ := ∑ j : Fin r, σ2 j + 1
  have hS_pos : 0 < S_tot := by
    dsimp [S_tot]
    linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hσ2_nn j]
  set M_H : ℝ := Real.sqrt (2 * S_tot / ε)
  have hMH_pos : 0 < M_H := Real.sqrt_pos.mpr (by positivity)
  have hMH_sq : M_H ^ 2 = 2 * S_tot / ε := Real.sq_sqrt (by positivity)
  refine ⟨(r : ℝ) * M_H, mul_pos hr_pos hMH_pos, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcoord_bound : ∀ j : Fin r,
      μ {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|} ≤
        ENNReal.ofReal (σ2 j / M_H ^ 2) := by
    intro j
    set Z : Ω → ℝ := fun ω => (Hn h θs (fun i : Fin n => W i ω) j) ^ 2
    have hZ_eq : ∀ ω, Z ω = (1 / (n : ℝ)) *
        ∑ i : Fin n, ∑ k : Fin n, (h (W i ω) θs j * h (W k ω) θs j) := by
      intro ω
      dsimp [Z, Hn]
      simp only [Finset.sum_apply]
      rw [mul_pow, inv_pow, Real.sq_sqrt hn_pos.le, inv_eq_one_div, sq, Finset.sum_mul_sum]
    have hprod_int : ∀ i k : Fin n,
        Integrable (fun ω => h (W i ω) θs j * h (W k ω) θs j) μ := by
      intro i k
      refine Integrable.mono' ((hX_sq_int j i).add (hX_sq_int j k))
        ((((hg_meas j).comp (hWmeas i)).mul ((hg_meas j).comp (hWmeas k))).aestronglyMeasurable)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h2ab : 2 * (|h (W i ω) θs j| * |h (W k ω) θs j|) ≤
          (h (W i ω) θs j) ^ 2 + (h (W k ω) θs j) ^ 2 := by
        have := sq_nonneg (|h (W i ω) θs j| - |h (W k ω) θs j|)
        nlinarith [sq_abs (h (W i ω) θs j), sq_abs (h (W k ω) θs j),
          abs_nonneg (h (W i ω) θs j), abs_nonneg (h (W k ω) θs j)]
      change |h (W i ω) θs j| * |h (W k ω) θs j| ≤
        (h (W i ω) θs j) ^ 2 + (h (W k ω) θs j) ^ 2
      linarith [mul_nonneg (abs_nonneg (h (W i ω) θs j)) (abs_nonneg (h (W k ω) θs j))]
    have hZ_int : Integrable Z μ := by
      have hfun : Z = fun ω => (1 / (n : ℝ)) *
          ∑ i : Fin n, ∑ k : Fin n, (h (W i ω) θs j * h (W k ω) θs j) := funext hZ_eq
      rw [hfun]
      exact (integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun k _ => hprod_int i k).const_mul _
    have hprod_mean : ∀ i k : Fin n,
        ∫ ω, h (W i ω) θs j * h (W k ω) θs j ∂μ = if i = k then σ2 j else 0 := by
      intro i k
      by_cases hik : i = k
      · subst hik
        simp only [ ↓reduceIte, ← sq ]
        exact hX_sq_eq j i
      · simp only [hik, ↓reduceIte]
        have hind_j : iIndepFun (fun m ω => h (W m ω) θs j) μ :=
          hindep.comp (fun _ => fun w => h w θs j) (fun _ => hg_meas j)
        have hpair : (fun ω => h (W i ω) θs j) ⟂ᵢ[μ] (fun ω => h (W k ω) θs j) :=
          hind_j.indepFun (Fin.val_ne_of_ne hik)
        rw [hpair.integral_fun_mul_eq_mul_integral
          (((hg_meas j).comp (hWmeas i)).aestronglyMeasurable)
          (((hg_meas j).comp (hWmeas k)).aestronglyMeasurable)]
        change (∫ ω, h (W i ω) θs j ∂μ) * (∫ ω, h (W k ω) θs j ∂μ) = 0
        rw [hX_mean j i, zero_mul]
    have hZ_mean : ∫ ω, Z ω ∂μ = σ2 j := by
      have hfun : Z = fun ω => (1 / (n : ℝ)) *
          ∑ i : Fin n, ∑ k : Fin n, (h (W i ω) θs j * h (W k ω) θs j) := funext hZ_eq
      rw [hfun, integral_const_mul, integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ fun k _ => hprod_int i k)]
      have hinner : ∀ i : Fin n,
          ∫ ω, (∑ k : Fin n, h (W i ω) θs j * h (W k ω) θs j) ∂μ = σ2 j := by
        intro i
        rw [integral_finsetSum _ (fun k _ => hprod_int i k)]
        simp_rw [hprod_mean i]
        simp
      simp_rw [hinner]
      simp [Finset.sum_const, nsmul_eq_mul, hn_pos.ne']
    have hsub_ev : {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|} ⊆
        {ω | M_H ^ 2 ≤ Z ω} := by
      intro ω hω
      change M_H < |Hn h θs (fun i : Fin n => W i ω) j| at hω
      change M_H ^ 2 ≤ (Hn h θs (fun i : Fin n => W i ω) j) ^ 2
      nlinarith [sq_abs (Hn h θs (fun i : Fin n => W i ω) j), hMH_pos]
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => sq_nonneg _) hZ_int (M_H ^ 2)
    rw [hZ_mean] at hmarkov
    have hreal_le : μ.real {ω | M_H ^ 2 ≤ Z ω} ≤ σ2 j / M_H ^ 2 :=
      (le_div_iff₀' (pow_pos hMH_pos 2)).mpr hmarkov
    calc μ {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|}
        ≤ μ {ω | M_H ^ 2 ≤ Z ω} := measure_mono hsub_ev
      _ = ENNReal.ofReal (μ.real {ω | M_H ^ 2 ≤ Z ω}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      _ ≤ ENNReal.ofReal (σ2 j / M_H ^ 2) := ENNReal.ofReal_le_ofReal hreal_le
  have hsub_union : {ω | (r : ℝ) * M_H < ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖} ⊆
      ⋃ j : Fin r, {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|} := by
    intro ω hω
    change (r : ℝ) * M_H < ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖ at hω
    have hsum_lt : (r : ℝ) * M_H <
        ∑ j : Fin r, |Hn h θs (fun i : Fin n => W i ω) j| :=
      hω.trans_le (toLp_norm_le_sum_abs q _)
    by_contra hall
    have hj : ∀ j : Fin r, |Hn h θs (fun i : Fin n => W i ω) j| ≤ M_H :=
      fun j => not_lt.mp fun hlt => hall (Set.mem_iUnion.mpr ⟨j, hlt⟩)
    have hle : ∑ j : Fin r, |Hn h θs (fun i : Fin n => W i ω) j| ≤ (r : ℝ) * M_H := by
      calc ∑ j : Fin r, |Hn h θs (fun i : Fin n => W i ω) j|
          ≤ ∑ _j : Fin r, M_H := Finset.sum_le_sum fun j _ => hj j
        _ = (r : ℝ) * M_H := by simp [Finset.sum_const, nsmul_eq_mul]
    linarith
  calc μ {ω | (r : ℝ) * M_H < ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖}
      ≤ μ (⋃ j : Fin r, {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|}) :=
        measure_mono hsub_union
    _ ≤ ∑ j : Fin r, μ {ω | M_H < |Hn h θs (fun i : Fin n => W i ω) j|} :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ j : Fin r, ENNReal.ofReal (σ2 j / M_H ^ 2) :=
        Finset.sum_le_sum fun j _ => hcoord_bound j
    _ = ENNReal.ofReal (∑ j : Fin r, σ2 j / M_H ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (hσ2_nn j) (pow_nonneg hMH_pos.le 2)]
    _ ≤ ENNReal.ofReal (ε / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_div, hMH_sq]
        have h1 : ∑ j : Fin r, σ2 j ≤ S_tot := by dsimp [S_tot]; linarith
        calc (∑ j : Fin r, σ2 j) / (2 * S_tot / ε)
            ≤ S_tot / (2 * S_tot / ε) :=
              div_le_div_of_nonneg_right h1 (by positivity)
          _ = ε / 2 := by field_simp [hS_pos.ne', hε.ne']

private lemma exists_uniform_sphere_cover {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m l r : ℕ} (hr : 0 < r)
    (W0 : Ω → (Fin m → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W0 ω)}) :
    ∃ (m_cov : ℕ) (A_ev : Fin m_cov → Set (Fin m → ℝ)) (K_W η_star p_star : ℝ),
      0 < m_cov ∧ 0 < K_W ∧ 0 < η_star ∧ 0 < p_star ∧ p_star ≤ 1 ∧
      (∀ j : Fin m_cov, MeasurableSet (A_ev j)) ∧
      (∀ j : Fin m_cov, p_star ≤ μ.real (W0 ⁻¹' A_ev j)) ∧
      (∀ j : Fin m_cov, ∀ w ∈ A_ev j, ‖w‖ ≤ K_W) ∧
      (∀ ξ : Fin r → ℝ, ‖WithLp.toLp p ξ‖ = 1 →
        ∃ j : Fin m_cov, ∀ w ∈ A_ev j, η_star ≤ rowNorm p h θs ξ w) := by
  let Sp : Set (Fin r → ℝ) := {ξ | ‖WithLp.toLp p ξ‖ = 1}
  have hSp_comp : IsCompact Sp := isCompact_toLp_sphere p
  let j0 : Fin r := ⟨0, hr⟩
  have hj0_mem : (Pi.single j0 (1 : ℝ) : Fin r → ℝ) ∈ Sp := toLp_norm_single_eq_one p j0
  have hrow_cont : Continuous (fun zw : (Fin r → ℝ) × (Fin m → ℝ) =>
      rowNorm p h θs zw.1 zw.2) :=
    continuous_norm.comp (continuous_toLp_rowVec p h θs hC1)
  have hex_local : ∀ ξ ∈ Sp, ∃ (C η δ : ℝ),
      0 < C ∧ 0 < η ∧ 0 < δ ∧
      0 < μ {ω | ‖W0 ω‖ ≤ C ∧ 2 * η ≤ rowNorm p h θs ξ (W0 ω)} ∧
      ∀ ζ ∈ Sp, dist ζ ξ < δ → ∀ w : Fin m → ℝ,
        ‖w‖ ≤ C ∧ 2 * η ≤ rowNorm p h θs ξ w → η ≤ rowNorm p h θs ζ w := by
    intro ξ hξ
    have hξ_ne : ξ ≠ 0 := by
      intro h0
      have : ‖WithLp.toLp p ξ‖ = 0 := by simp [h0]
      linarith [show ‖WithLp.toLp p ξ‖ = 1 from hξ]
    obtain ⟨k, hk_pos⟩ := exists_trunc_pos W0 p h θs ξ (hA4 ξ hξ_ne)
    let C : ℝ := (k : ℝ) + 1
    have hC_pos : 0 < C := by positivity
    let η : ℝ := 1 / (2 * C)
    have hη_pos : 0 < η := by positivity
    have h2η : 2 * η = 1 / ((k : ℝ) + 1) := by dsimp [η, C]; field_simp [hC_pos.ne']
    have hprob_pos : 0 < μ {ω | ‖W0 ω‖ ≤ C ∧ 2 * η ≤ rowNorm p h θs ξ (W0 ω)} := by
      simpa only [C, h2η] using hk_pos
    have hK_prod : IsCompact (Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) C) :=
      hSp_comp.prod (isCompact_closedBall _ _)
    have hucont := hK_prod.uniformContinuousOn_of_continuous hrow_cont.continuousOn
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hucont η hη_pos
    refine ⟨C, η, δ, hC_pos, hη_pos, hδ_pos, hprob_pos, fun ζ hζ hdist w hw => ?_⟩
    have hp1 : (ζ, w) ∈ Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
      ⟨hζ, by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1⟩
    have hp2 : (ξ, w) ∈ Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) C :=
      ⟨hξ, by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1⟩
    have hd : dist (ζ, w) (ξ, w) < δ := by
      simpa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist
    have hclose : |rowNorm p h θs ζ w - rowNorm p h θs ξ w| < η :=
      hδ (ζ, w) hp1 (ξ, w) hp2 hd
    linarith [abs_lt.mp hclose, hw.2]
  choose C_fn η_fn δ_fn hC_pos hη_pos hδ_pos hprob_pos hlocal using
    fun ξ : Sp => hex_local ξ.1 ξ.2
  obtain ⟨F_sub, _, hF_fin, hF_cov⟩ := hSp_comp.elim_finite_subcover_image
    (b := Set.univ) (c := fun ξ : Sp => Metric.ball ξ.1 (δ_fn ξ))
    (fun ξ _ => Metric.isOpen_ball)
    (fun ζ hζ => Set.mem_biUnion (Set.mem_univ (⟨ζ, hζ⟩ : Sp))
      (Metric.mem_ball_self (hδ_pos ⟨ζ, hζ⟩)))
  let F : Finset Sp := hF_fin.toFinset
  have hF_ne : F.Nonempty := by
    obtain ⟨ξ, hξ_mem, _⟩ := Set.mem_iUnion₂.mp (hF_cov hj0_mem)
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
  let A_sp : Sp → Set (Fin m → ℝ) := fun ξ =>
    {w | ‖w‖ ≤ C_fn ξ ∧ 2 * η_fn ξ ≤ rowNorm p h θs ξ.1 w}
  let p_fn : Sp → ℝ := fun ξ => μ.real (W0 ⁻¹' A_sp ξ)
  have hp_fn_pos : ∀ ξ : Sp, 0 < p_fn ξ := fun ξ =>
    ENNReal.toReal_pos (hprob_pos ξ).ne' (measure_ne_top μ _)
  have hp_fn_le_one : ∀ ξ : Sp, p_fn ξ ≤ 1 := fun ξ => by
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
  · intro j
    exact Finset.inf'_le p_fn (e.symm j).2
  · intro j w hw
    exact hw.1.trans (Finset.le_sup' C_fn (e.symm j).2)
  · intro ξ hξ
    obtain ⟨ξ_cov, hξ_sub, hξ_ball⟩ := Set.mem_iUnion₂.mp (hF_cov hξ)
    have hξ_F : ξ_cov ∈ F := hF_fin.mem_toFinset.mpr hξ_sub
    let j : Fin m_cov := e ⟨ξ_cov, hξ_F⟩
    refine ⟨j, fun w hw => ?_⟩
    have he_eq : (e.symm j).1 = ξ_cov := by simp [j]
    have hw' : w ∈ A_sp ξ_cov := by simpa only [A_ev, he_eq] using hw
    exact (Finset.inf'_le η_fn hξ_F).trans
      (hlocal ξ_cov ξ hξ (Metric.mem_ball.mp hξ_ball) w hw')

private lemma single_sample_sup_lb {m l r : ℕ} (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p.HolderConjugate q)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (ρ : ℝ) {a η_star τ : ℝ} (ha_pos : 0 < a) (hη_pos : 0 < η_star) (hτ_pos : 0 < τ)
    {n : ℕ} {ζ ξ₀ : Fin r → ℝ} (hζ_eq : ζ = a • ξ₀)
    {w : Fin m → ℝ} (hrow_ge : η_star ≤ rowNorm p h θs ξ₀ w)
    (hclose : ∀ w' : Fin m → ℝ, ‖w' - w‖ ≤ (Real.sqrt (n : ℝ))⁻¹ * τ →
      ‖WithLp.toLp p (rowVec h θs ξ₀ w' - rowVec h θs ξ₀ w)‖ < η_star / 2) :
    (((a * η_star * τ / 2 - τ ^ ρ : ℝ) : EReal)) ≤
      ⨆ Δ : Fin m → ℝ,
        (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
            fderiv ℝ (fun x => h x θs) (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ)) Δ)
          - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal) := by
  let v : Fin m → ℝ := rowVec h θs ξ₀ w
  have hv_norm : η_star ≤ ‖WithLp.toLp p v‖ := hrow_ge
  have hv_ne : v ≠ 0 := by
    intro h0
    have : ‖WithLp.toLp p v‖ = 0 := by simp [v, h0]
    linarith
  obtain ⟨u_dir, hu_norm, hu_dot⟩ := exists_norm_eq_one_dotProduct_eq p q hpq v hv_ne
  let Δ₀ : Fin m → ℝ := τ • u_dir
  have hΔ_norm : ‖WithLp.toLp q Δ₀‖ = τ := by
    change ‖τ • WithLp.toLp q u_dir‖ = τ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ_pos, hu_norm, mul_one]
  have hΔ_sup : ‖Δ₀‖ ≤ τ := (norm_le_toLp_norm q Δ₀).trans hΔ_norm.le
  have hint_lb : a * η_star * τ / 2 ≤
      ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θs) (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀)) Δ₀ := by
    rw [dot_integral_fderiv_eq h θs hC1]
    have hcont_int : Continuous (fun u : ℝ =>
        rowVec h θs ζ (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀)) ⬝ᵥ Δ₀) := by
      have hpath : Continuous (fun u : ℝ => (ζ, w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀))) := by
        fun_prop
      have hofLp : Continuous (fun u : ℝ =>
          rowVec h θs ζ (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀))) :=
        (PiLp.continuous_ofLp p _).comp ((continuous_toLp_rowVec p h θs hC1).comp hpath)
      exact continuous_finsetSum Finset.univ fun k _ =>
        ((continuous_apply k).comp hofLp).mul continuous_const
    have hpt_lb : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        a * η_star * τ / 2 ≤
          rowVec h θs ζ (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀)) ⬝ᵥ Δ₀ := by
      rintro u ⟨hu0, hu1⟩
      let w' : Fin m → ℝ := w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ₀)
      have hw'_diff : ‖w' - w‖ ≤ (Real.sqrt (n : ℝ))⁻¹ * τ := by
        have hsub_eq : w' - w = ((Real.sqrt (n : ℝ))⁻¹ * u) • Δ₀ := by
          dsimp [w']; rw [add_sub_cancel_left, smul_smul]
        rw [hsub_eq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hu0)]
        have hu_le : (Real.sqrt (n : ℝ))⁻¹ * u ≤ (Real.sqrt (n : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hu1 (inv_nonneg.mpr (Real.sqrt_nonneg _))
        rw [mul_one] at hu_le
        calc ((Real.sqrt (n : ℝ))⁻¹ * u) * ‖Δ₀‖ ≤ ((Real.sqrt (n : ℝ))⁻¹ * u) * τ :=
              mul_le_mul_of_nonneg_left hΔ_sup
                (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hu0)
          _ ≤ (Real.sqrt (n : ℝ))⁻¹ * τ := mul_le_mul_of_nonneg_right hu_le hτ_pos.le
      have hvec_close : ‖WithLp.toLp p (rowVec h θs ξ₀ w' - v)‖ < η_star / 2 :=
        hclose w' hw'_diff
      have herr_dot : (v - rowVec h θs ξ₀ w') ⬝ᵥ Δ₀ ≤ (η_star / 2) * τ := by
        calc (v - rowVec h θs ξ₀ w') ⬝ᵥ Δ₀
            ≤ ‖WithLp.toLp p (v - rowVec h θs ξ₀ w')‖ * ‖WithLp.toLp q Δ₀‖ :=
              dotProduct_le_norm_mul_norm p q hpq _ _
          _ = ‖WithLp.toLp p (rowVec h θs ξ₀ w' - v)‖ * τ := by
              rw [hΔ_norm, ← norm_neg]
              congr 2; ext k; simp
          _ ≤ (η_star / 2) * τ := mul_le_mul_of_nonneg_right hvec_close.le hτ_pos.le
      have hv_dot_Δ : η_star * τ ≤ v ⬝ᵥ Δ₀ := by
        dsimp [Δ₀]
        rw [dotProduct_smul, smul_eq_mul, hu_dot, mul_comm τ]
        exact mul_le_mul_of_nonneg_right hv_norm hτ_pos.le
      have hξ0_dot : η_star * τ / 2 ≤ rowVec h θs ξ₀ w' ⬝ᵥ Δ₀ := by
        have hsplit : v ⬝ᵥ Δ₀ - rowVec h θs ξ₀ w' ⬝ᵥ Δ₀ = (v - rowVec h θs ξ₀ w') ⬝ᵥ Δ₀ :=
          (sub_dotProduct _ _ _).symm
        linarith
      rw [hζ_eq, rowVec_smul, smul_dotProduct, smul_eq_mul]
      have hmul := mul_le_mul_of_nonneg_left hξ0_dot ha_pos.le
      linarith
    have hint_mono := intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_const (μ := volume)) (hcont_int.intervalIntegrable 0 1) hpt_lb
    simpa using hint_mono
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (le_iSup (fun Δ : Fin m → ℝ =>
    (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θs) (w + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ)) Δ)
      - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)) Δ₀)
  rw [hΔ_norm]
  linarith

end SolRWPILimitLemma2

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m l r : ℕ} (W : ℕ → Ω → (Fin m → ℝ)) (hWmeas : ∀ i, Measurable (W i))
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (hint : Integrable (fun ω => h (W 0 ω) θs) μ) (hmean : ∫ ω, h (W 0 ω) θs ∂μ = 0)
    (hL2 : MemLp (fun ω => h (W 0 ω) θs) 2 μ)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hA4 : ∀ ζ : Fin r → ℝ, ζ ≠ 0 → 0 < μ {ω | 0 < rowNorm p h θs ζ (W 0 ω)}) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, n₀ ≤ n →
      μ {ω | ∃ ζ : Fin r → ℝ, b ≤ ‖WithLp.toLp p ζ‖ ∧
        (0 : EReal) < (((-(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))) : ℝ) : EReal)
          - Mn q ρ h θs (fun i : Fin n => W i ω) ζ} ≤ ENNReal.ofReal ε := by
  have _ := hq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  intro ε hε
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, fun n _ => ?_⟩
    have hempty : {ω : Ω | ∃ ζ : Fin 0 → ℝ, 1 ≤ ‖WithLp.toLp p ζ‖ ∧
        (0 : EReal) < (((-(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))) : ℝ) : EReal)
          - Mn q ρ h θs (fun i : Fin n => W i ω) ζ} = ∅ := by
      ext ω
      constructor
      · rintro ⟨ζ, hζ, _⟩
        have hζ0 : ζ = 0 := Subsingleton.elim ζ 0
        rw [hζ0, WithLp.toLp_zero, norm_zero] at hζ
        linarith
      · simp
    rw [hempty, measure_empty]
    exact bot_le
  · obtain ⟨m_cov, A_ev, K_W, η_star, p_star, _, hKW_pos, hη_star_pos, hp_star_pos,
      hp_star_le_one, hA_meas, hp_ge, hA_norm, hA_cov⟩ :=
      SolRWPILimitLemma2.exists_uniform_sphere_cover hr (W 0) p h θs hC1 hA4
    obtain ⟨K_H, hKH_pos, hKH_tight⟩ :=
      SolRWPILimitLemma2.tight_Hn_norm hr W hWmeas hindep hident h θs q hint hmean hL2 hC1 hε
    let τ : ℝ := 8 * (K_H + 1) / (p_star * η_star)
    have hτ_pos : 0 < τ := by positivity
    have hτ_eq : p_star * η_star * τ / 8 = K_H + 1 := by
      dsimp [τ]
      field_simp [hp_star_pos.ne', hη_star_pos.ne']
    let Sp : Set (Fin r → ℝ) := {ξ | ‖WithLp.toLp p ξ‖ = 1}
    have hK_vec : IsCompact (Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) (K_W + τ)) :=
      (SolRWPILimitLemma2.isCompact_toLp_sphere p).prod (isCompact_closedBall _ _)
    have hucont_vec := hK_vec.uniformContinuousOn_of_continuous
      (SolRWPILimitLemma2.continuous_toLp_rowVec p h θs hC1).continuousOn
    obtain ⟨δ_W, hδW_pos, hδW⟩ :=
      Metric.uniformContinuousOn_iff.mp hucont_vec (η_star / 2) (half_pos hη_star_pos)
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((τ / δ_W) ^ 2)
    let N₁' : ℕ := max N₁ 1
    have hN₁'_pos : 0 < N₁' := lt_of_lt_of_le zero_lt_one (le_max_right N₁ 1)
    have hstep_small : ∀ n : ℕ, N₁' ≤ n → (Real.sqrt (n : ℝ))⁻¹ * τ < δ_W := by
      intro n hn
      have hn_ge_N1 : N₁ ≤ n := (le_max_left N₁ 1).trans hn
      have hn_gt : (τ / δ_W) ^ 2 < (n : ℝ) := hN₁.trans_le (Nat.cast_le.mpr hn_ge_N1)
      have hsq_lt : τ / δ_W < Real.sqrt (n : ℝ) := by
        calc τ / δ_W = Real.sqrt ((τ / δ_W) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ < Real.sqrt (n : ℝ) := Real.sqrt_lt_sqrt (by positivity) hn_gt
      have hsqn_pos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hN₁'_pos.trans_le hn))
      rw [inv_mul_eq_div, div_lt_iff₀ hsqn_pos, mul_comm]
      exact (div_lt_iff₀ hδW_pos).mp hsq_lt
    let I_ind : Fin m_cov → (Fin m → ℝ) → ℝ := fun j w => Set.indicator (A_ev j) 1 w
    have hI_meas : ∀ j : Fin m_cov, Measurable (I_ind j) := fun j =>
      measurable_const.indicator (hA_meas j)
    have hI_int : ∀ j : Fin m_cov, Integrable (fun ω => I_ind j (W 0 ω)) μ := fun j =>
      Integrable.of_bound ((hI_meas j).comp (hWmeas 0)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          dsimp [I_ind, Set.indicator]; split_ifs <;> norm_num)
    have hI_mean : ∀ j : Fin m_cov, ∫ ω, I_ind j (W 0 ω) ∂μ = μ.real (W 0 ⁻¹' A_ev j) := by
      intro j
      have hind_eq : (fun ω => I_ind j (W 0 ω)) = Set.indicator (W 0 ⁻¹' A_ev j) 1 := by
        ext ω; dsimp only [I_ind, Set.indicator, Set.mem_preimage]; rfl
      rw [hind_eq]
      exact integral_indicator_one ((hA_meas j).preimage (hWmeas 0))
    have hI_slln : ∀ j : Fin m_cov, Tendsto (fun n : ℕ => μ {ω | p_star / 2 <
        |(1 / (n : ℝ)) * ∑ i : Fin n, I_ind j (W i ω) - μ.real (W 0 ⁻¹' A_ev j)|})
        atTop (𝓝 0) := by
      intro j
      let Y : ℕ → Ω → ℝ := fun i ω => I_ind j (W i ω)
      have hY_indep : iIndepFun Y μ := hindep.comp (fun _ => I_ind j) (fun _ => hI_meas j)
      have hY_pair : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) Y) :=
        fun i k hik => hY_indep.indepFun hik
      have hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ :=
        fun i => (hident i).comp (hI_meas j)
      have hslln := ProbabilityTheory.strong_law_ae_real Y (hI_int j) hY_pair hY_ident
      have hae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ i : Fin n, Y i ω) atTop
          (𝓝 (μ.real (W 0 ⁻¹' A_ev j))) := by
        rw [← hI_mean j]
        filter_upwards [hslln] with ω hω
        refine hω.congr fun n => ?_
        rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n, one_div_mul_eq_div]
      have hZmeas : ∀ n : ℕ, Measurable (fun ω => (1 / (n : ℝ)) * ∑ i : Fin n, Y i ω) :=
        fun n => measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ =>
          (hI_meas j).comp (hWmeas i))
      exact SolRWPILimitLemma2.tendsto_prob_gt_of_tendsto_ae _ hZmeas _ hae
        (half_pos hp_star_pos)
    have hsum_slln : Tendsto (fun n : ℕ => ∑ j : Fin m_cov, μ {ω | p_star / 2 <
        |(1 / (n : ℝ)) * ∑ i : Fin n, I_ind j (W i ω) - μ.real (W 0 ⁻¹' A_ev j)|})
        atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun j _ => hI_slln j
    have hε2_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
      ENNReal.ofReal_pos.mpr (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := (hsum_slln.eventually (gt_mem_nhds hε2_pos)).exists_forall_of_atTop
    let n₀ : ℕ := max N₁' N₂
    have hn₀_pos : 0 < n₀ := hN₁'_pos.trans_le (le_max_left N₁' N₂)
    let b : ℝ := max 1 (8 * τ ^ ρ / (p_star * η_star * τ))
    have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨n₀, hn₀_pos, b, hb_pos, fun n hn => ?_⟩
    have hn_ge_1 : 1 ≤ n := Nat.succ_le_of_lt (hn₀_pos.trans_le hn)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hn₀_pos.trans_le hn)
    have hn_N1 : N₁' ≤ n := (le_max_left N₁' N₂).trans hn
    have hn_N2 : N₂ ≤ n := (le_max_right N₁' N₂).trans hn
    let E_H : Set Ω := {ω | K_H < ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖}
    let E_LLN : Set Ω := ⋃ j : Fin m_cov, {ω | p_star / 2 <
      |(1 / (n : ℝ)) * ∑ i : Fin n, I_ind j (W i ω) - μ.real (W 0 ⁻¹' A_ev j)|}
    let S_bad : Set Ω := {ω | ∃ ζ : Fin r → ℝ, b ≤ ‖WithLp.toLp p ζ‖ ∧
      (0 : EReal) < (((-(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))) : ℝ) : EReal)
        - Mn q ρ h θs (fun i : Fin n => W i ω) ζ}
    have hS_sub : S_bad ⊆ E_H ∪ E_LLN := by
      rintro ω ⟨ζ, hζ_norm, hpos_obj⟩
      by_contra hgood
      have hnot_H : ω ∉ E_H := fun h1 => hgood (Or.inl h1)
      have hnot_LLN : ω ∉ E_LLN := fun h2 => hgood (Or.inr h2)
      have hHn_le : ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖ ≤ K_H :=
        not_lt.mp hnot_H
      let a : ℝ := ‖WithLp.toLp p ζ‖
      have ha_ge_b : b ≤ a := hζ_norm
      have ha_pos : 0 < a := hb_pos.trans_le ha_ge_b
      let ξ₀ : Fin r → ℝ := a⁻¹ • ζ
      have hζ_eq : ζ = a • ξ₀ := by simp [ξ₀, smul_smul, mul_inv_cancel₀ ha_pos.ne']
      have hξ₀_Sp : ‖WithLp.toLp p ξ₀‖ = 1 := by
        change ‖a⁻¹ • WithLp.toLp p ζ‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha_pos)]
        exact inv_mul_cancel₀ ha_pos.ne'
      obtain ⟨j_cov, hj_cov⟩ := hA_cov ξ₀ hξ₀_Sp
      have hfreq_ge : p_star / 2 ≤ (1 / (n : ℝ)) * ∑ i : Fin n, I_ind j_cov (W i ω) := by
        have hle : |(1 / (n : ℝ)) * ∑ i : Fin n, I_ind j_cov (W i ω) -
            μ.real (W 0 ⁻¹' A_ev j_cov)| ≤ p_star / 2 :=
          not_lt.mp fun hlt => hnot_LLN (Set.mem_iUnion.mpr ⟨j_cov, hlt⟩)
        linarith [(abs_le.mp hle).1, hp_ge j_cov]
      have hτ_bound : τ ^ ρ ≤ p_star * η_star * τ / 8 * a := by
        have hb2 : 8 * τ ^ ρ / (p_star * η_star * τ) ≤ a := (le_max_right _ _).trans ha_ge_b
        have hden : 0 < p_star * η_star * τ := by positivity
        have h1 : 8 * τ ^ ρ ≤ a * (p_star * η_star * τ) := (div_le_iff₀ hden).mp hb2
        linarith
      have hval_nn : 0 ≤ a * η_star * τ / 2 - τ ^ ρ := by
        have hp_le : p_star * η_star * τ / 8 * a ≤ a * η_star * τ / 2 := by
          have hpos_prod : 0 ≤ η_star * τ * a := by positivity
          have h1 : p_star * (η_star * τ * a) ≤ 4 * (η_star * τ * a) :=
            mul_le_mul_of_nonneg_right (hp_star_le_one.trans (by norm_num)) hpos_prod
          linarith
        linarith [hτ_bound]
      let T_i : Fin n → EReal := fun i => ⨆ Δ : Fin m → ℝ,
        (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
            fderiv ℝ (fun x => h x θs) (W i ω + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ)) Δ)
          - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)
      have hTi_lb : ∀ i : Fin n,
          (((I_ind j_cov (W i ω) * (a * η_star * τ / 2 - τ ^ ρ) : ℝ) : EReal)) ≤ T_i i := by
        intro i
        by_cases hmem : W i ω ∈ A_ev j_cov
        · have hI1 : I_ind j_cov (W i ω) = 1 := Set.indicator_of_mem hmem 1
          rw [hI1, one_mul]
          have hw_le_KW : ‖W i ω‖ ≤ K_W := hA_norm j_cov (W i ω) hmem
          have hrow_ge : η_star ≤ rowNorm p h θs ξ₀ (W i ω) := hj_cov (W i ω) hmem
          refine SolRWPILimitLemma2.single_sample_sup_lb p q hpq h θs hC1 ρ ha_pos
            hη_star_pos hτ_pos hζ_eq hrow_ge fun w' hw'_diff => ?_
          have hsqn_ge_1 : 1 ≤ Real.sqrt (n : ℝ) := by
            calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
              _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (Nat.one_le_cast.mpr hn_ge_1)
          have hinv_le_1 : (Real.sqrt (n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqn_ge_1
          have hw'_ball : ‖w'‖ ≤ K_W + τ := by
            calc ‖w'‖ = ‖W i ω + (w' - W i ω)‖ := by abel_nf
              _ ≤ ‖W i ω‖ + ‖w' - W i ω‖ := norm_add_le _ _
              _ ≤ K_W + (Real.sqrt (n : ℝ))⁻¹ * τ := add_le_add hw_le_KW hw'_diff
              _ ≤ K_W + 1 * τ := add_le_add le_rfl
                  (mul_le_mul_of_nonneg_right hinv_le_1 hτ_pos.le)
              _ = K_W + τ := by ring
          have hw_ball : ‖W i ω‖ ≤ K_W + τ := by linarith
          have hp1 : (ξ₀, w') ∈ Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) (K_W + τ) :=
            ⟨hξ₀_Sp, by simpa [Metric.mem_closedBall, dist_zero_right] using hw'_ball⟩
          have hp2 : (ξ₀, W i ω) ∈ Sp ×ˢ Metric.closedBall (0 : Fin m → ℝ) (K_W + τ) :=
            ⟨hξ₀_Sp, by simpa [Metric.mem_closedBall, dist_zero_right] using hw_ball⟩
          have hd_W : dist (ξ₀, w') (ξ₀, W i ω) < δ_W := by
            rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
            exact hw'_diff.trans_lt (hstep_small n hn_N1)
          simpa [dist_eq_norm] using hδW (ξ₀, w') hp1 (ξ₀, W i ω) hp2 hd_W
        · have hI0 : I_ind j_cov (W i ω) = 0 := Set.indicator_of_notMem hmem 1
          rw [hI0, zero_mul]
          refine le_trans ?_ (le_iSup (fun Δ : Fin m → ℝ =>
            (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
                fderiv ℝ (fun x => h x θs) (W i ω + (Real.sqrt (n : ℝ))⁻¹ • (u • Δ)) Δ)
              - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)) (0 : Fin m → ℝ))
          simp [Real.zero_rpow (zero_lt_one.trans_le hρ).ne']
      have hMn_lb : ((((K_H + 1) * a : ℝ) : EReal)) ≤
          Mn q ρ h θs (fun i : Fin n => W i ω) ζ := by
        have hsum_lb := SolRWPILimitLemma2.ereal_finset_sum_le_sum Finset.univ _ T_i
          fun i _ => hTi_lb i
        rw [SolRWPILimitLemma2.finset_sum_coe_ereal] at hsum_lb
        have hmul_lb := SolRWPILimitLemma2.ereal_mul_mono_of_pos (one_div_pos.mpr hn_pos) hsum_lb
        rw [← EReal.coe_mul] at hmul_lb
        refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hmul_lb
        rw [← Finset.sum_mul, ← mul_assoc]
        calc (K_H + 1) * a = (p_star * η_star * τ / 8) * a := by rw [← hτ_eq]
          _ = p_star * (a * η_star * τ / 4) - (p_star * η_star * τ / 8) * a := by ring
          _ ≤ p_star * (a * η_star * τ / 4) - τ ^ ρ := by linarith [hτ_bound]
          _ ≤ p_star * (a * η_star * τ / 4) - p_star / 2 * τ ^ ρ := by
              have : p_star / 2 * τ ^ ρ ≤ 1 * τ ^ ρ :=
                mul_le_mul_of_nonneg_right (by linarith [hp_star_le_one])
                  (Real.rpow_nonneg hτ_pos.le _)
              linarith
          _ = (p_star / 2) * (a * η_star * τ / 2 - τ ^ ρ) := by ring
          _ ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, I_ind j_cov (W i ω)) *
                (a * η_star * τ / 2 - τ ^ ρ) :=
              mul_le_mul_of_nonneg_right hfreq_ge hval_nn
      have hHn_dot : -(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω)) ≤ K_H * a := by
        calc -(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))
            = (-ζ) ⬝ᵥ Hn h θs (fun i : Fin n => W i ω) := (neg_dotProduct _ _).symm
          _ ≤ ‖WithLp.toLp p (-ζ)‖ * ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖ :=
              SolRWPILimitLemma2.dotProduct_le_norm_mul_norm p q hpq _ _
          _ = a * ‖WithLp.toLp q (Hn h θs (fun i : Fin n => W i ω))‖ := by
              change ‖-WithLp.toLp p ζ‖ * _ = a * _
              rw [norm_neg]
          _ ≤ a * K_H := mul_le_mul_of_nonneg_left hHn_le ha_pos.le
          _ = K_H * a := mul_comm _ _
      have hle_zero : (((-(ζ ⬝ᵥ Hn h θs (fun i : Fin n => W i ω))) : ℝ) : EReal) -
          Mn q ρ h θs (fun i : Fin n => W i ω) ζ ≤ 0 :=
        SolRWPILimitLemma2.ereal_sub_nonpos_of_le (by linarith) hMn_lb
      exact not_lt_of_ge hle_zero hpos_obj
    have hE_LLN_le : μ E_LLN ≤ ENNReal.ofReal (ε / 2) :=
      (measure_iUnion_fintype_le μ _).trans (hN₂ n hn_N2).le
    have hE_H_le : μ E_H ≤ ENNReal.ofReal (ε / 2) := hKH_tight n hn_ge_1
    calc μ S_bad ≤ μ (E_H ∪ E_LLN) := measure_mono hS_sub
      _ ≤ μ E_H + μ E_LLN := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hE_H_le hE_LLN_le
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
