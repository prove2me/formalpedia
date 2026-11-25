-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.psi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:49.397346+00:00
-- url     : https://prove2.me/submissions/6dfbf983-4817-4cfb-87ff-b4c3c97169a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_normSq_le_tW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_unitIndicator_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_powIndicator_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k) {s : ℝ}
    (hs : 0 ≤ s) {x : ι → ℂ} (hx : x ∈ Bset q) (hg : ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0) :
    PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
  classical
  obtain ⟨ht1, ht2, hxq⟩ := hx
  have htpos : 0 < tW q x := by linarith

  have hcoord : ∀ z : ℂ, Complex.normSq z ≤ 1 → |z.re| ≤ 1 ∧ |z.im| ≤ 1 := by
    intro z hz
    rw [Complex.normSq_apply] at hz
    constructor
    · nlinarith [sq_abs z.re, abs_nonneg z.re, mul_self_nonneg z.im]
    · nlinarith [sq_abs z.im, abs_nonneg z.im, mul_self_nonneg z.re]
  have hnsq : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := by
    intro z
    first
    | exact Complex.normSq_eq_norm_sq z
    | (rw [Complex.sq_norm])
    | (rw [Complex.normSq_eq_abs, Complex.norm_eq_abs])
  have hsmall : ∀ i, i ≠ q → Complex.normSq (x i) ≤ 1 := by
    intro i hi
    have h1 := normSq_le_tW q x i hi
    nlinarith [htpos]
  have hqsmall : Complex.normSq (x q) ≤ 1 := by
    rw [hnsq]
    nlinarith [norm_nonneg (x q)]

  have hnnj : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  have htsq : tW q x ^ 2 = ∑ j, (if j = q then 0 else Complex.normSq (x j)) := by
    unfold tW
    rw [Real.sq_sqrt (Finset.sum_nonneg hnnj)]
  have him : (1 - star (x p) / (tW q x : ℂ)).im = (x p).im / tW q x := by
    simp [Complex.div_ofReal_im]
    try ring
  have hA : |(x p).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    have h1 : |(1 - star (x p) / (tW q x : ℂ)).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
      first
      | exact Complex.abs_im_le_norm _
      | exact Complex.abs_im_le_abs _
    rw [him, abs_div, abs_of_pos htpos] at h1
    have h2 : |(x p).im| ≤ |(x p).im| / tW q x := by
      first
      | (rw [le_div_iff₀ htpos]; nlinarith [abs_nonneg (x p).im])
      | (rw [le_div_iff htpos]; nlinarith [abs_nonneg (x p).im])
    linarith
  have hB : ∀ i, i ≠ p → i ≠ q → |(x i).re| * |(x i).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    intro i hip hiq
    have hsum : Complex.normSq (x p) + Complex.normSq (x i) ≤ tW q x ^ 2 := by
      rw [htsq]
      have hsub : ∑ j ∈ ({p, i} : Finset ι), (if j = q then 0 else Complex.normSq (x j)) ≤
          ∑ j, (if j = q then 0 else Complex.normSq (x j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => hnnj j (Finset.mem_univ j))
      rw [Finset.sum_pair (Ne.symm hip), if_neg hpq, if_neg hiq] at hsub
      exact hsub
    have hw : ‖star (x p) / (tW q x : ℂ)‖ = ‖x p‖ / tW q x := by
      rw [norm_div, norm_star]
      first
      | (rw [Complex.norm_real, Real.norm_of_nonneg htpos.le])
      | (simp [abs_of_pos htpos]; done)
      | (simp [Complex.abs_of_nonneg htpos.le]; done)
    have htri : ‖(1 : ℂ)‖ - ‖star (x p) / (tW q x : ℂ)‖ ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, hw] at htri
    rw [hnsq (x p)] at hsum
    have hre2 : 2 * (|(x i).re| * |(x i).im|) ≤ Complex.normSq (x i) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_abs (x i).re, sq_abs (x i).im, sq_nonneg (|(x i).re| - |(x i).im|)]
    have hr0 := norm_nonneg (x p)
    have hni := Complex.normSq_nonneg (x i)
    have hrt : ‖x p‖ ≤ tW q x := by nlinarith
    have hm : |(x i).re| * |(x i).im| ≤ tW q x - ‖x p‖ := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrt) (by linarith : (0 : ℝ) ≤ 2 - tW q x - ‖x p‖)]
    have hd : ‖x p‖ / tW q x ≤ 1 - tW q x + ‖x p‖ := by
      first
      | (rw [div_le_iff₀ htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
      | (rw [div_le_iff htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
    linarith
  have hpim : 0 < |(x p).im| := abs_pos.2 (hg p).1
  have hu : 0 < ‖1 - star (x p) / (tW q x : ℂ)‖ := lt_of_lt_of_le hpim hA
  have hP : PsiF p q s x = ENNReal.ofReal (‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)) := by
    unfold PsiF
    rw [← ENNReal.ofReal_rpow_of_pos hu]
    congr 1
    first
    | exact (ofReal_norm_eq_coe_nnnorm _).symm
    | (rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm])
    | exact (enorm_eq_nnnorm _).symm.trans (ofReal_norm_eq_enorm _).symm
    | (simp; rfl)
  rw [hP]
  apply ENNReal.ofReal_le_ofReal
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hβ0 : 0 ≤ s / k := div_nonneg hs hk0.le
  have key : ∀ a : ℝ, 0 < a → a ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ →
      ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ a ^ (-(s / k)) := by
    intro a ha hau
    first
    | exact Real.rpow_le_rpow_of_nonpos ha hau (by linarith)
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_le_inv_of_le (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
  have hfac : ∀ i, i ≠ q → ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ gF p q (s / k) i (x i) := by
    intro i hiq
    obtain ⟨hr1, hi1⟩ := hcoord (x i) (hsmall i hiq)
    by_cases hip : i = p
    · rw [hip] at hr1 hi1 ⊢
      have he : gF p q (s / k) p (x p) = |(x p).im| ^ (-(s / k)) := by
        rw [show gF p q (s / k) p (x p) = one1 (x p).re * pw1 (s / k) (x p).im by simp [gF, hpq],
          unitIndicator_eq hr1, powIndicator_eq hi1, one_mul]
      rw [he]
      exact key _ hpim hA
    · have he : gF p q (s / k) i (x i) = (|(x i).re| * |(x i).im|) ^ (-(s / k)) := by
        rw [show gF p q (s / k) i (x i) = pw1 (s / k) (x i).re * pw1 (s / k) (x i).im by
          simp [gF, hiq, hip], powIndicator_eq hr1, powIndicator_eq hi1, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [he]
      exact key _ (mul_pos (abs_pos.2 (hg i).2) (abs_pos.2 (hg i).1)) (hB i hip hiq)
  have hq1 : gF p q (s / k) q (x q) = 1 := by
    obtain ⟨hr1, hi1⟩ := hcoord (x q) hqsmall
    rw [show gF p q (s / k) q (x q) = one1 (x q).re * one1 (x q).im by simp [gF], unitIndicator_eq hr1, unitIndicator_eq hi1, one_mul]
  have hsplit := Finset.mul_prod_erase Finset.univ (fun i => gF p q (s / k) i (x i)) (Finset.mem_univ q)
  try simp only at hsplit
  rw [← hsplit, hq1, one_mul]
  have hcard : (Finset.univ.erase q).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, hk]
    simp
  calc ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)
      = ∏ i ∈ Finset.univ.erase q, ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) := by
        rw [Finset.prod_const, hcard, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
        congr 1
        first
        | (rw [neg_mul, div_mul_cancel₀ _ hkne])
        | (rw [neg_mul, div_mul_cancel₀ hkne])
        | (field_simp; done)
        | (field_simp; ring)
    _ ≤ ∏ i ∈ Finset.univ.erase q, gF p q (s / k) i (x i) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Real.rpow_nonneg hu.le _
        · intro i hi
          exact hfac i (Finset.ne_of_mem_erase hi)
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
