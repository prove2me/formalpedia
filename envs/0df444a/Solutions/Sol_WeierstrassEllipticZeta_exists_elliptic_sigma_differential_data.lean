-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_elliptic_sigma_differential_data
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T21:06:16.371612+00:00
-- url     : https://prove2.me/submissions/6adf9775-7e41-4521-816b-6e34c3c40b42

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Analytic.Order

noncomputable section
open Filter
open scoped Topology

open WeierstrassEllipticZeta

private def canonicalFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (z + z ^ 2 / 2)

private lemma factor_deriv (z : ℂ) :
    HasDerivAt canonicalFactor (-z ^ 2 * Complex.exp (z + z ^ 2 / 2)) z := by
  convert! ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
    (((hasDerivAt_id z).add (((hasDerivAt_id z).pow 2).div_const 2)).cexp) using 1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  ring

private lemma factor_entire : Differentiable ℂ canonicalFactor :=
  fun z ↦ (factor_deriv z).differentiableAt

private lemma factor_cubic_bound : ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
    ∀ z : ℂ, ‖z‖ < r → ‖canonicalFactor z - 1‖ ≤ C * ‖z‖ ^ 3 := by
  have hd : deriv canonicalFactor = fun z ↦ -z ^ 2 * Complex.exp (z + z ^ 2 / 2) :=
    funext fun z ↦ (factor_deriv z).deriv
  have h2 : iteratedDeriv 2 canonicalFactor 0 = 0 := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hd]
    have H : HasDerivAt (fun z : ℂ ↦ -z ^ 2 * Complex.exp (z + z ^ 2 / 2)) 0 0 := by
      have he := (((hasDerivAt_id (0 : ℂ)).add
        (((hasDerivAt_id (0 : ℂ)).pow 2).div_const 2)).cexp)
      convert! (((hasDerivAt_id (0 : ℂ)).pow 2).neg).mul he using 1
      simp
    exact H.deriv
  obtain ⟨F, hF, heq⟩ := (factor_entire.analyticAt 0).exists_eventuallyEq_sum_add_pow_mul 3
  have heq' : ∀ᶠ z in 𝓝 (0 : ℂ), canonicalFactor z - 1 = z ^ 3 * F z := by
    filter_upwards [heq] with z hz
    apply sub_eq_iff_eq_add.mpr
    simpa [Finset.sum_range_succ, iteratedDeriv_one, hd, h2, canonicalFactor,
      add_comm] using hz
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < ‖F 0‖ + 1 :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (heq'.and hbound)
  refine ⟨‖F 0‖ + 1, r, by positivity, hr, fun z hz ↦ ?_⟩
  have H := hball (by simpa [dist_zero_right] using hz)
  rw [H.1, norm_mul, norm_pow]
  nlinarith [pow_nonneg (norm_nonneg z) 3]

private lemma factor_uniform_bound (L : PeriodPair) (R : ℝ) (hR : 0 < R) :
    ∃ u : L.lattice → ℝ, Summable u ∧
      ∀ᶠ l : L.lattice in cofinite, ∀ z : ℂ, ‖z‖ < R →
        ‖canonicalFactor (z / (l : ℂ)) - 1‖ ≤ u l := by
  obtain ⟨C, r, hC, hr, hbound⟩ := factor_cubic_bound
  refine ⟨fun l ↦ C * R ^ 3 * ‖l‖ ^ (-3 : ℝ),
    (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _, ?_⟩
  have hlarge : ∀ᶠ l : L.lattice in cofinite, R / r < ‖l‖ := by
    refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) (R / r))).subset ?_
    intro l hl
    simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hl
  filter_upwards [hlarge] with l hl z hz
  have hlpos : 0 < ‖(l : ℂ)‖ := lt_trans (div_pos hR hr) hl
  have hratio : ‖z / (l : ℂ)‖ < r := by
    rw [norm_div, div_lt_iff₀ hlpos]
    have H := (div_lt_iff₀ hr).mp hl
    change R < ‖(l : ℂ)‖ * r at H
    nlinarith
  calc
    _ ≤ C * ‖z / (l : ℂ)‖ ^ 3 := hbound _ hratio
    _ ≤ C * (R / ‖(l : ℂ)‖) ^ 3 := by rw [norm_div]; gcongr
    _ = C * R ^ 3 * ‖l‖ ^ (-3 : ℝ) := by simp [div_eq_mul_inv, mul_pow, mul_assoc]

private lemma factor_multipliable_locally (L : PeriodPair) :
    MultipliableLocallyUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ canonicalFactor (z / (l : ℂ))) Set.univ := by
  use fun z ↦ ∏' l : L.lattice, canonicalFactor (z / (l : ℂ))
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR, hnorm⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨u, hu, hbound⟩ := factor_uniform_bound L R hR
  have h := hu.hasProdUniformlyOn_one_add hK (f := fun (l : L.lattice) (z : ℂ) ↦
    canonicalFactor (z / (l : ℂ)) - 1) ?_ ?_
  · simpa only [add_sub_cancel] using h
  · filter_upwards [hbound] with l hl z hz using hl z (hnorm z hz)
  · intro l
    exact ((factor_entire.comp (differentiable_id.div_const (l : ℂ))).sub
      (differentiable_const 1)).continuous.continuousOn

private lemma summable_factor_sub_one (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice ↦ ‖canonicalFactor (z / (l : ℂ)) - 1‖ := by
  obtain ⟨u, hu, hbound⟩ := factor_uniform_bound L (‖z‖ + 1) (by positivity)
  apply hu.of_norm_bounded_eventually
  filter_upwards [hbound] with l hl
  simpa using hl z (by linarith)

private lemma factor_ne_zero (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) : canonicalFactor (z / (l : ℂ)) ≠ 0 := by
  unfold canonicalFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : (l : ℂ) = 0
  · simp [hl]
  · intro h
    have hzl : z = (l : ℂ) := (div_eq_one_iff_eq hl).mp (sub_eq_zero.mp h).symm
    exact hz (hzl ▸ l.property)

private lemma product_ne_zero (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    ∏' l : L.lattice, canonicalFactor (z / (l : ℂ)) ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun l : L.lattice ↦ canonicalFactor (z / (l : ℂ)) - 1)
    (fun l ↦ by simpa only [add_sub_cancel] using factor_ne_zero L l z hz)
    (summable_factor_sub_one L z)
  simpa only [add_sub_cancel] using h

private lemma factor_logDeriv (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    logDeriv (fun w : ℂ ↦ canonicalFactor (w / (l : ℂ))) z =
      if l = 0 then 0 else 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2 := by
  classical
  by_cases hl : l = 0
  · simp [hl, canonicalFactor]
  have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
  have hzl : z - (l : ℂ) ≠ 0 := fun h ↦ hz (sub_eq_zero.mp h ▸ l.property)
  have hlin : 1 - z / (l : ℂ) ≠ 0 := by
    intro h
    exact hzl (sub_eq_zero.mpr ((div_eq_one_iff_eq hlc).mp (sub_eq_zero.mp h).symm))
  have hder := (factor_deriv (z / (l : ℂ))).comp z
    ((hasDerivAt_id z).div_const (l : ℂ))
  have hd : deriv (fun w : ℂ ↦ canonicalFactor (w / (l : ℂ))) z =
      -(z / (l : ℂ)) ^ 2 * Complex.exp (z / (l : ℂ) + (z / (l : ℂ)) ^ 2 / 2) *
        (1 / (l : ℂ)) := by simpa using! hder.deriv
  rw [logDeriv_apply, hd, if_neg hl, canonicalFactor]
  have he := Complex.exp_ne_zero (z / (l : ℂ) + (z / (l : ℂ)) ^ 2 / 2)
  have hlz : -z + (l : ℂ) ≠ 0 := by
    rw [neg_add_eq_sub]
    exact sub_ne_zero.mpr (sub_ne_zero.mp hzl).symm
  field_simp [hlz]
  ring_nf
  field_simp [hlz]
  ring

private lemma product_entire (L : PeriodPair) :
    Differentiable ℂ (fun z ↦ ∏' l : L.lattice, canonicalFactor (z / (l : ℂ))) := by
  rw [← differentiableOn_univ]
  exact (factor_multipliable_locally L).hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ by
      simpa only [Finset.prod_fn] using! DifferentiableOn.finsetProd (u := s)
        (fun l _ ↦ (factor_entire.comp
          (differentiable_id.div_const (l : ℂ))).differentiableOn)) isOpen_univ

private lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r)
    (l : ℂ) (hl : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) + 1 / l + z / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hlpos : 0 < ‖l‖ := by linarith
  have hlne : l ≠ 0 := norm_pos_iff.mp hlpos
  have hzl : z - l ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    subst z
    linarith
  have hnorm : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    exact le_trans (by linarith) (norm_sub_norm_le l z)
  calc
    _ = ‖z ^ 2 / (l ^ 2 * (z - l))‖ := by
      congr 1
      field_simp
      ring
    _ = ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) := by simp
    _ ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

private theorem zeta_series_converges (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l ↦ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    fun r hr ↦ Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h z hz l rfl
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact zetaSummand_bound r hr z hz l h

theorem solution
    (L : PeriodPair) :
    Nonempty (EllipticSigmaDifferentialData L) := by
  let P : ℂ → ℂ := fun z ↦ ∏' l : L.lattice, canonicalFactor (z / (l : ℂ))
  have hP : Differentiable ℂ P := product_entire L
  refine ⟨{ sigma := fun z ↦ z * P z
            entire := differentiable_id.mul hP
            zero := by simp
            deriv_zero := ?_
            hasDerivAt := ?_ }⟩
  · have h := (hasDerivAt_id (0 : ℂ)).mul (hP 0).hasDerivAt
    simpa [P, canonicalFactor] using! h
  · intro z hz
    have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
    have hPne : P z ≠ 0 := product_ne_zero L z hz
    have hsum : Summable fun l : L.lattice ↦
        logDeriv (fun w : ℂ ↦ canonicalFactor (w / (l : ℂ))) z :=
      (zeta_series_converges L).hasSum.summable.congr
        (fun l ↦ (factor_logDeriv L l z hz).symm)
    have hlogP := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
      (fun l ↦ factor_ne_zero L l z hz)
      (fun l ↦ (factor_entire.comp
        (differentiable_id.div_const (l : ℂ))).differentiableOn)
      hsum (factor_multipliable_locally L) hPne
    have hlog : logDeriv (fun w ↦ w * P w) z = weierstrassZeta L z := by
      have hm : logDeriv (fun w : ℂ ↦ w * P w) z = 1 / z + logDeriv P z := by
        simpa using! logDeriv_mul z hz0 hPne differentiableAt_id (hP z)
      apply hm.trans
      convert! congrArg (1 / z + ·)
        (hlogP.trans (tsum_congr fun l ↦ factor_logDeriv L l z hz)) using 1
    have heq : deriv (fun w ↦ w * P w) z = weierstrassZeta L z * (z * P z) :=
      (div_eq_iff (mul_ne_zero hz0 hPne)).mp hlog
    rw [← heq]
    exact ((differentiable_id.mul hP) z).hasDerivAt
