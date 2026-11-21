-- Prove2me | solution 1 for RandomSizeStable.Stability.rank_cut_certificate_dStar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:48:19.211185+00:00
-- url     : https://prove2.me/submissions/48491918-bac6-4a47-b19f-e93acc94dd1b

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_DrawLaw
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_01
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_02
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_03
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_04
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_05
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_06
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_07
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_08
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_09
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_10
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_11
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_12
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_13
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_14
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsLow_15
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_01
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_02
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_03
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_04
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_05
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_06
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_07
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_08
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_09
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_10
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_11
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_12
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_13
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_14
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_15
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_16
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_17
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_18
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_01
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_02
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_03
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_04
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_p1_ok
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cells_near_zero
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cells_near_one

section
set_option autoImplicit false

open MeasureTheory RandomSizeStable.Stability

noncomputable section

namespace RandomSizeStable.Stability.RankCutCert


/-! ### The draw law D* -/

lemma dStar_toReal (k : ℕ+) : (dStar k).toReal =
    (if k = 1 then 19 / 73 else 0) + (if k = 2 then 35 / 146 else 0) +
      (if k = 32 then 1 / 2 else 0) := by
  rw [dStar, PMF.map_apply, tsum_fintype, Fin.sum_univ_three]
  simp only [PMF.ofFintype_apply]
  by_cases h1 : k = 1
  · subst h1; norm_num
  by_cases h2 : k = 2
  · subst h2; norm_num
  by_cases h3 : k = 32
  · subst h3; norm_num
  simp [h1, h2, h3]

lemma pgf_dStar (t : ℝ) : pgf dStar t = phi t := by
  unfold pgf
  rw [tsum_eq_sum (s := {1, 2, 32})]
  · simp [dStar_toReal, Finset.sum_insert, phi]
    ring
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [dStar_toReal, hk.1, hk.2.1, hk.2.2]

lemma benchmark_dStar : benchmark dStar = mu := by
  unfold benchmark
  rw [tsum_eq_sum (s := {1, 2, 32})]
  · simp [dStar_toReal, Finset.sum_insert, mu]
    norm_num
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [dStar_toReal, hk.1, hk.2.1, hk.2.2]

/-- The derivative of `phi`. -/
def phid (x : ℝ) : ℝ := 19 / 73 + 35 / 73 * x + 16 * x ^ 31

@[fun_prop]
lemma continuous_phi : Continuous phi := by unfold phi; fun_prop

@[fun_prop]
lemma continuous_Phi : Continuous Phi := by unfold Phi; fun_prop

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (phid x) x := by
  have h1 := (hasDerivAt_id x).const_mul (19 / 73 : ℝ)
  have h2 := (hasDerivAt_pow 2 x).const_mul (35 / 146 : ℝ)
  have h3 := (hasDerivAt_pow 32 x).div_const (2 : ℝ)
  have h4 : HasDerivAt phi _ x := (h1.add h2).add h3
  exact h4.congr_deriv (by simp [phid]; ring)

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have h1 := (hasDerivAt_pow 2 x).const_mul (19 / 146 : ℝ)
  have h2 := (hasDerivAt_pow 3 x).const_mul (35 / 438 : ℝ)
  have h3 := (hasDerivAt_pow 33 x).div_const (66 : ℝ)
  have h4 : HasDerivAt Phi _ x := (h1.add h2).add h3
  exact h4.congr_deriv (by simp [phi]; ring)

lemma primitive_dStar (u : ℝ) : primitive dStar u = Phi u := by
  unfold primitive
  simp_rw [pgf_dStar]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_Phi x)
    (continuous_phi.intervalIntegrable _ _)]
  simp [Phi]

lemma phi_le_phi {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phi x ≤ phi y := by
  unfold phi; gcongr

lemma phid_le_phid {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phid x ≤ phid y := by
  unfold phid; gcongr

/-! ### Numeric facts about the witness -/

lemma b_pos : 0 < b := by norm_num [b]

lemma b_lt_one : b < 1 := by norm_num [b]

lemma b_lt_h (j : Fin 9) : b < h j := by fin_cases j <;> norm_num [b, h]

lemma h_lt_one (j : Fin 9) : h j < 1 := by fin_cases j <;> norm_num [h]

lemma eta_pos (j : Fin 9) : 0 < eta j := by fin_cases j <;> norm_num [eta]

lemma one_le_eta_phid (j : Fin 9) : 1 ≤ eta j * phid b := by
  fin_cases j <;> norm_num [eta, phid, b]

lemma lo_nonneg (j : Fin 9) : 0 ≤ lo j := by fin_cases j <;> norm_num [lo]

lemma lo_le_hi (j : Fin 9) : lo j ≤ hi j := by fin_cases j <;> norm_num [lo, hi]

lemma hi_le_b (j : Fin 9) : hi j ≤ b := by fin_cases j <;> norm_num [hi, b]

/-- The density part of the rank measure, before clamping. -/
def gfun (j : Fin 9) (x : ℝ) : ℝ := eta j * (phi x - phi b) - (x - b)

/-- The atom at `b`. -/
def mpt (j : Fin 9) : ℝ := C0 - gfun j (h j)

lemma mpt_nonneg (j : Fin 9) : 0 ≤ mpt j := by
  fin_cases j <;> norm_num [mpt, gfun, phi, C0, b, h, eta]

lemma gfun_b (j : Fin 9) : gfun j b = 0 := by simp [gfun]

lemma hasDerivAt_gfun (j : Fin 9) (x : ℝ) : HasDerivAt (gfun j) (eta j * phid x - 1) x := by
  have h1 := ((hasDerivAt_phi x).sub_const (phi b)).const_mul (eta j)
  have h2 : HasDerivAt (gfun j) _ x := h1.sub ((hasDerivAt_id x).sub_const b)
  exact h2.congr_deriv (by simp)

lemma continuous_gfun (j : Fin 9) : Continuous (gfun j) := by unfold gfun; fun_prop

lemma gfun_monoOn (j : Fin 9) : MonotoneOn (gfun j) (Set.Icc b (h j)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact (continuous_gfun j).continuousOn
  · exact fun x _ => (hasDerivAt_gfun j x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_gfun j x).deriv]
    have h1 := phid_le_phid b_pos.le hx.1.le
    have h2 := one_le_eta_phid j
    have h3 := eta_pos j
    nlinarith

/-- Clamp to `[b, h j]`. -/
def clampH (j : Fin 9) (x : ℝ) : ℝ := max b (min x (h j))

lemma clampH_mem (j : Fin 9) (x : ℝ) : clampH j x ∈ Set.Icc b (h j) :=
  ⟨le_max_left _ _, max_le (b_lt_h j).le (min_le_right _ _)⟩

lemma clampH_of_le (j : Fin 9) {x : ℝ} (hx : x ≤ b) : clampH j x = b := by
  unfold clampH
  exact max_eq_left ((min_le_left _ _).trans hx)

lemma clampH_of_ge (j : Fin 9) {x : ℝ} (hx : h j ≤ x) : clampH j x = h j := by
  unfold clampH
  rw [min_eq_right hx]; exact max_eq_right (b_lt_h j).le

lemma clampH_of_mem (j : Fin 9) {x : ℝ} (h1 : b ≤ x) (h2 : x ≤ h j) : clampH j x = x := by
  unfold clampH
  rw [min_eq_left h2]; exact max_eq_right h1

/-- The (continuous) distribution function of the density part. -/
def Ff (j : Fin 9) (x : ℝ) : ℝ := gfun j (clampH j x)

lemma Ff_mono (j : Fin 9) : Monotone (Ff j) := by
  intro x y hxy
  apply gfun_monoOn j (clampH_mem j x) (clampH_mem j y)
  unfold clampH
  exact max_le_max le_rfl (min_le_min hxy le_rfl)

lemma Ff_cont (j : Fin 9) : Continuous (Ff j) := by
  unfold Ff clampH
  exact (continuous_gfun j).comp (by fun_prop)

/-- The Stieltjes function of the density part. -/
def Fst (j : Fin 9) : StieltjesFunction ℝ where
  toFun := Ff j
  mono' := Ff_mono j
  right_continuous' _ := (Ff_cont j).continuousWithinAt

lemma Fst_apply (j : Fin 9) (x : ℝ) : Fst j x = Ff j x := rfl

lemma Fst_leftLim (j : Fin 9) (x : ℝ) : Function.leftLim (Fst j) x = Ff j x :=
  ((Fst j).mono.continuousWithinAt_Iio_iff_leftLim_eq).1 (Ff_cont j).continuousWithinAt

lemma Fst_tendsto_top (j : Fin 9) :
    Filter.Tendsto (Fst j) Filter.atTop (nhds (gfun j (h j))) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (h j)] with x hx
  rw [Fst_apply, Ff, clampH_of_ge j hx]

lemma Fst_tendsto_bot (j : Fin 9) :
    Filter.Tendsto (Fst j) Filter.atBot (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_le_atBot b] with x hx
  rw [Fst_apply, Ff, clampH_of_le j hx, gfun_b]

/-- The rank measure nu_j. -/
def nuR (j : Fin 9) : Measure ℝ :=
  ENNReal.ofReal (mpt j) • Measure.dirac b + (Fst j).measure

lemma gfun_h_nonneg (j : Fin 9) : 0 ≤ gfun j (h j) := by
  rw [← gfun_b j]
  exact gfun_monoOn j ⟨le_rfl, (b_lt_h j).le⟩ ⟨(b_lt_h j).le, le_rfl⟩ (b_lt_h j).le

lemma Ff_le (j : Fin 9) (x : ℝ) : Ff j x ≤ gfun j (h j) :=
  gfun_monoOn j (clampH_mem j x) ⟨(b_lt_h j).le, le_rfl⟩ (clampH_mem j x).2

lemma nuR_univ (j : Fin 9) : nuR j Set.univ = ENNReal.ofReal C0 := by
  simp only [nuR, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    (Fst j).measure_univ (Fst_tendsto_bot j) (Fst_tendsto_top j), sub_zero]
  rw [← ENNReal.ofReal_add (mpt_nonneg j) (gfun_h_nonneg j)]
  congr 1
  simp [mpt]

lemma nuR_ne_top (j : Fin 9) (s : Set ℝ) : nuR j s ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [nuR_univ]; exact ENNReal.ofReal_ne_top)
    (measure_mono (Set.subset_univ _))

lemma nuR_compl (j : Fin 9) : nuR j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  have hc : (Set.Icc (0 : ℝ) 1)ᶜ = Set.Iio 0 ∪ Set.Ioi 1 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      by_contra hc
      exact hx ⟨not_lt.1 (fun h' => hc (Or.inl h')), not_lt.1 (fun h' => hc (Or.inr h'))⟩
    · rintro (hx | hx) ⟨h1, h2⟩ <;> linarith
  rw [hc]
  apply measure_union_null
  · simp only [nuR, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      (Fst j).measure_Iio (Fst_tendsto_bot j), Fst_leftLim, Ff,
      clampH_of_le j (show (0 : ℝ) ≤ b from b_pos.le), gfun_b, sub_zero,
      ENNReal.ofReal_zero, add_zero]
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp [b_pos.le]
  · simp only [nuR, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      (Fst j).measure_Ioi (Fst_tendsto_top j), Fst_apply, Ff,
      clampH_of_ge j (h_lt_one j).le, sub_self, ENNReal.ofReal_zero, add_zero]
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    simp [b_lt_one.le]

lemma nuR_Ici (j : Fin 9) (x : ℝ) : (nuR j (Set.Ici x)).toReal = tail j x := by
  simp only [nuR, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    (Fst j).measure_Ici (Fst_tendsto_top j), Fst_leftLim]
  rw [Measure.dirac_apply' _ measurableSet_Ici]
  have hle := Ff_le j x
  by_cases hxb : x ≤ b
  · have hm : b ∈ Set.Ici x := hxb
    rw [Set.indicator_of_mem hm, Pi.one_apply, mul_one,
      ← ENNReal.ofReal_add (mpt_nonneg j) (sub_nonneg.2 hle),
      ENNReal.toReal_ofReal (add_nonneg (mpt_nonneg j) (sub_nonneg.2 hle))]
    rw [Ff, clampH_of_le j hxb, gfun_b]
    simp [tail, hxb, mpt]
  · have hm : b ∉ Set.Ici x := fun hh => hxb hh
    rw [Set.indicator_of_notMem hm, mul_zero, zero_add, ENNReal.toReal_ofReal (sub_nonneg.2 hle)]
    push Not at hxb
    by_cases hxh : x < h j
    · rw [Ff, clampH_of_mem j hxb.le hxh.le]
      simp only [tail, not_le.2 hxb, hxh, if_false, if_true, gfun]
      ring
    · push Not at hxh
      rw [Ff, clampH_of_ge j hxh]
      simp [tail, not_le.2 hxb, not_lt.2 hxh]

lemma nuR_Ico (j : Fin 9) {x y : ℝ} (hxy : x ≤ y) :
    (nuR j (Set.Ico x y)).toReal = tail j x - tail j y := by
  have hsub : Set.Ici y ⊆ Set.Ici x := Set.Ici_subset_Ici.2 hxy
  have hd : Set.Ico x y = Set.Ici x \ Set.Ici y := by
    ext z; simp [Set.mem_Ico]
  rw [hd, measure_sdiff hsub measurableSet_Ici.nullMeasurableSet (nuR_ne_top j _),
    ENNReal.toReal_sub_of_le (measure_mono hsub) (nuR_ne_top j _), nuR_Ici, nuR_Ici]

lemma tail_one (j : Fin 9) : tail j 1 = 0 := by
  simp [tail, not_le.2 b_lt_one, not_lt.2 (h_lt_one j).le]

/-! ### Pieces of the cut inequality -/

lemma rho_nonneg (j : Fin 9) (y : ℝ) : 0 ≤ rho j y := by
  have := lo_nonneg j
  have := b_pos
  have := lo_le_hi j
  unfold rho
  split_ifs <;> linarith

lemma rho_le (j : Fin 9) {y r : ℝ} (hr : r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1)
    (hyr : y ≤ r) : rho j y ≤ r := by
  have := lo_le_hi j
  have := hi_le_b j
  unfold rho
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs <;> linarith

lemma phi_rho_le (j : Fin 9) {y r : ℝ} (hr : r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1)
    (hyr : y ≤ r) : phi (rho j y) ≤ phi r :=
  phi_le_phi (rho_nonneg j y) (rho_le j hr hyr)

lemma B_le_B_one {a p A : ℝ} (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ A) (hA : A ≤ 1) :
    B a p A ≤ B a p 1 := by
  set d := p - a with hd_def
  have hd : ∀ x, HasDerivAt (fun t => Phi t - Phi (t - d)) (phi x - phi (x - d)) x := by
    intro x
    have h1 := (hasDerivAt_Phi (x - d)).comp x ((hasDerivAt_id x).sub_const d)
    have h2 : HasDerivAt (fun t => Phi t - Phi (t - d)) _ x := (hasDerivAt_Phi x).sub h1
    exact h2.congr_deriv (by ring)
  have key : MonotoneOn (fun t => Phi t - Phi (t - d)) (Set.Ici d) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact (continuous_Phi.sub (continuous_Phi.comp (continuous_sub_right d))).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have hx' : (0 : ℝ) ≤ x - d := by have := Set.mem_Ioi.1 hx; linarith
      have := phi_le_phi hx' (by linarith)
      linarith
  have hA' : A ∈ Set.Ici d := by simp only [Set.mem_Ici]; linarith
  have h1' : (1 : ℝ) ∈ Set.Ici d := by simp only [Set.mem_Ici]; linarith
  have := key hA' h1' hA
  simp only at this
  unfold B
  have e1 : a + A - p = A - d := by rw [hd_def]; ring
  have e2 : a + 1 - p = 1 - d := by rw [hd_def]; ring
  rw [e1, e2]
  linarith

lemma setS_Ici {a r A : ℝ} (har : a ≤ r) (hrA : r < A) :
    {z : ℝ | a ≤ min z r ∧ min z r < A} = Set.Ici a := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_Ici, le_min_iff, min_lt_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, _⟩; exact h1
  · intro h1; exact ⟨⟨h1, har⟩, Or.inr hrA⟩

lemma setS_Ico {a r A : ℝ} (har : a ≤ r) (hAr : A ≤ r) :
    {z : ℝ | a ≤ min z r ∧ min z r < A} = Set.Ico a A := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_Ico, le_min_iff, min_lt_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact absurd h2 (not_lt.2 hAr)
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, har⟩, Or.inl h2⟩

lemma cover (r : ℝ) (h0 : 0 ≤ r) (hb : r ≤ b) : ∃ j, r ∈ Set.Icc (lo j) (hi j) := by
  rcases le_or_gt r (3 / 100) with h1 | h1
  · refine ⟨8, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (7 / 50) with h2 | h2
  · refine ⟨7, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (21 / 100) with h3 | h3
  · refine ⟨6, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (13 / 50) with h4 | h4
  · refine ⟨5, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (3 / 10) with h5 | h5
  · refine ⟨4, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (7 / 20) with h6 | h6
  · refine ⟨3, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (21 / 50) with h7 | h7
  · refine ⟨2, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  rcases le_or_gt r (49 / 100) with h8 | h8
  · refine ⟨1, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;> simp [lo, hi] <;> linarith [show b = 2840189 / 5000000 from rfl]

/-- The cut inequality for the explicit witness, in terms of `Phi`, `mu`, `phi`. -/
lemma cut (lam : ℝ → ℝ) (tau : Fin 9 → ℝ → ℝ)
    (hlam : ∀ p, 0 < p → p < 1 → 0 ≤ lam p)
    (htau : ∀ j p, 0 < p → p ≤ 1 → 0 ≤ tau j p)
    (hG : ∀ (j : Fin 9) (a p A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 → 0 < p → p < 1 →
      0 ≤ G1 j (lam p) (tau j p) a p ∧ 0 ≤ G2 j (lam p) (tau j p) a p A)
    (h1 : ∀ (j : Fin 9) (a : ℝ), 0 ≤ a → a ≤ 1 → a + tau j 1 * (mu - phi (rho j a)) ≤ tail j a)
    (j : Fin 9) (r : ℝ) (hr : r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1)
    (a p A : ℝ) (ha : 0 ≤ a) (hapr : a ≤ min p r) (hpA : p ≤ A) (hA : A ≤ 1) :
    a + (if 0 < p ∧ p < 1 then lam p else 0) * B a p A +
        (if p = 0 then 0 else tau j p) * (mu - phi r) ≤
      (nuR j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal := by
  have hap : a ≤ p := hapr.trans (min_le_left _ _)
  have har : a ≤ r := hapr.trans (min_le_right _ _)
  have hp0 : 0 ≤ p := ha.trans hap
  rcases eq_or_lt_of_le hp0 with hp | hp
  · subst hp
    have ha0 : a = 0 := le_antisymm hap ha
    subst ha0
    simp
  have hpne : p ≠ 0 := hp.ne'
  rcases eq_or_lt_of_le (hpA.trans hA) with hp1 | hp1
  · -- p = 1, hence A = 1
    have hA1 : A = 1 := le_antisymm hA (hp1 ▸ hpA)
    subst hp1
    subst hA1
    have hrho := phi_rho_le j hr har
    have ht := htau j 1 one_pos le_rfl
    have hh := h1 j a ha hap
    have hRHS : (nuR j {z : ℝ | a ≤ min z r ∧ min z r < 1}).toReal = tail j a := by
      rcases lt_or_ge r 1 with hr1 | hr1
      · rw [setS_Ici har hr1, nuR_Ici]
      · rw [setS_Ico har hr1, nuR_Ico j hap, tail_one, sub_zero]
    rw [hRHS]
    simp only [lt_irrefl, and_false, if_false, zero_mul, add_zero, one_ne_zero]
    nlinarith
  have hif1 : (0 < p ∧ p < 1) := ⟨hp, hp1⟩
  rw [if_pos hif1, if_neg hpne]
  have hl := hlam p hp hp1
  have ht := htau j p hp hp1.le
  obtain ⟨hG1, hG2⟩ := hG j a p A ha hap hpA hA hp hp1
  rcases lt_or_ge r A with hrA | hAr
  · rw [setS_Ici har hrA, nuR_Ici]
    have hB := B_le_B_one ha hap hpA hA
    have hrho := phi_rho_le j hr har
    have e1 : lam p * B a p A ≤ lam p * B a p 1 := mul_le_mul_of_nonneg_left hB hl
    have e2 : tau j p * (mu - phi r) ≤ tau j p * (mu - phi (rho j a)) :=
      mul_le_mul_of_nonneg_left (by linarith) ht
    unfold G1 at hG1
    linarith
  · rw [setS_Ico har hAr, nuR_Ico j (hap.trans hpA)]
    have hrho := phi_rho_le j hr hAr
    have e2 : tau j p * (mu - phi r) ≤ tau j p * (mu - phi (rho j A)) :=
      mul_le_mul_of_nonneg_left (by linarith) ht
    unfold G2 at hG2
    linarith

/-- The target statement, with the multipliers supplied: the inequalities G1 ≥ 0, G2 ≥ 0 on the open
p-range and the p = 1 inequality give a rank-cut certificate at D*. -/
theorem reduction (lam : ℝ → ℝ) (tau : Fin 9 → ℝ → ℝ)
    (hlam : ∀ p, 0 < p → p < 1 → 0 ≤ lam p)
    (htau : ∀ j p, 0 < p → p ≤ 1 → 0 ≤ tau j p)
    (hG : ∀ (j : Fin 9) (a p A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 → 0 < p → p < 1 →
      0 ≤ G1 j (lam p) (tau j p) a p ∧ 0 ≤ G2 j (lam p) (tau j p) a p A)
    (h1 : ∀ (j : Fin 9) (a : ℝ), 0 ≤ a → a ≤ 1 → a + tau j 1 * (mu - phi (rho j a)) ≤ tail j a) :
    ∃ (b : ℝ) (lam : ℝ → ℝ) (lo hi : Fin 9 → ℝ) (nu : Fin 9 → Measure ℝ)
      (tau : Fin 9 → ℝ → ℝ),
      (0 ≤ (113609 / 200000 : ℝ)) ∧
      (b ∈ Set.Icc (0 : ℝ) 1) ∧ (pgf dStar b ≤ benchmark dStar) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p) ∧
      (lam 0 = 0) ∧ (lam 1 = 0) ∧
      (∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j)) ∧
      (∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) ∧
      (∀ j, nu j Set.univ = ENNReal.ofReal (113609 / 200000 : ℝ)) ∧
      (∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p) ∧
      (∀ j, tau j 0 = 0) ∧
      (∀ (j : Fin 9) (r : ℝ),
        r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
        ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
          a + lam p * (primitive dStar a + primitive dStar A - primitive dStar (a + A - p)
            - p * benchmark dStar) + tau j p * (benchmark dStar - pgf dStar r) ≤
          (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) := by
  refine ⟨b, fun p => if 0 < p ∧ p < 1 then lam p else 0, lo, hi, nuR,
    fun j p => if p = 0 then 0 else tau j p, by norm_num, ⟨b_pos.le, b_lt_one.le⟩, ?_, ?_, ?_, ?_,
    fun j => Set.Icc_subset_Icc (lo_nonneg j) (hi_le_b j), fun r hr => cover r hr.1 hr.2,
    nuR_compl, nuR_univ, ?_, ?_, ?_⟩
  · rw [pgf_dStar, benchmark_dStar]
    norm_num [phi, b, mu]
  · intro p _
    dsimp only
    split_ifs with hp
    · exact hlam p hp.1 hp.2
    · exact le_rfl
  · simp
  · simp
  · intro j p hp
    dsimp only
    split_ifs with hp0
    · exact le_rfl
    · exact htau j p (lt_of_le_of_ne hp.1 (Ne.symm hp0)) hp.2
  · intro j
    simp
  · intro j r hr a p A ha hapr hpA hA
    have := cut lam tau hlam htau hG h1 j r hr a p A ha hapr hpA hA
    simpa only [primitive_dStar, benchmark_dStar, pgf_dStar, B] using this

end RandomSizeStable.Stability.RankCutCert
end
end

section
/-! Assembly: the target from finitely many certified p-cells and the p = 1 condition (Blueprint). -/

set_option autoImplicit false

open MeasureTheory RandomSizeStable.Stability

namespace RandomSizeStable.Stability.RankCutCert

theorem assemble_pointwise
    (hcell : ∀ p : ℝ, 0 < p → p < 1 → ∃ (p0 p1 l0 l1 l2 : ℝ) (t0 t1 : Fin 9 → ℝ),
      CellOK p0 p1 l0 l1 l2 t0 t1 ∧ p0 ≤ p ∧ p ≤ p1)
    (tN0 tN1 : Fin 9 → ℝ) (hN : ∀ j, 0 ≤ tN0 j + tN1 j) (h1 : P1OK tN0 tN1) :
    ∃ (b : ℝ) (lam : ℝ → ℝ) (lo hi : Fin 9 → ℝ) (nu : Fin 9 → Measure ℝ)
      (tau : Fin 9 → ℝ → ℝ),
      (0 ≤ (113609 / 200000 : ℝ)) ∧
      (b ∈ Set.Icc (0 : ℝ) 1) ∧ (pgf dStar b ≤ benchmark dStar) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p) ∧
      (lam 0 = 0) ∧ (lam 1 = 0) ∧
      (∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j)) ∧
      (∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) ∧
      (∀ j, nu j Set.univ = ENNReal.ofReal (113609 / 200000 : ℝ)) ∧
      (∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p) ∧
      (∀ j, tau j 0 = 0) ∧
      (∀ (j : Fin 9) (r : ℝ),
        r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
        ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
          a + lam p * (primitive dStar a + primitive dStar A - primitive dStar (a + A - p)
            - p * benchmark dStar) + tau j p * (benchmark dStar - pgf dStar r) ≤
          (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) := by
  classical
  choose p0 p1 l0 l1 l2 t0 t1 hok hle0 hle1 using hcell
  let lam : ℝ → ℝ := fun p =>
    if h : 0 < p ∧ p < 1 then lamCell (l0 p h.1 h.2) (l1 p h.1 h.2) (l2 p h.1 h.2) p else 0
  let tau : Fin 9 → ℝ → ℝ := fun j p =>
    if p = 1 then tN0 j + tN1 j else
      if h : 0 < p ∧ p < 1 then tauCell (t0 p h.1 h.2 j) (t1 p h.1 h.2 j) p else 0
  refine reduction lam tau ?_ ?_ ?_ ?_
  · intro p hp hp1
    have h : 0 < p ∧ p < 1 := ⟨hp, hp1⟩
    simp only [lam, dif_pos h]
    exact (hok p hp hp1 p hp hp1 (hle0 p hp hp1) (hle1 p hp hp1)).1
  · intro j p hp hp1
    rcases eq_or_lt_of_le hp1 with he | hlt
    · simp only [tau, if_pos he]; exact hN j
    · have h : 0 < p ∧ p < 1 := ⟨hp, hlt⟩
      simp only [tau, if_neg hlt.ne, dif_pos h]
      exact (hok p hp hlt p hp hlt (hle0 p hp hlt) (hle1 p hp hlt)).2.1 j
  · intro j a p A ha hap hpA hA hp hp1'
    have h : 0 < p ∧ p < 1 := ⟨hp, hp1'⟩
    simp only [lam, tau, dif_pos h, if_neg hp1'.ne]
    exact (hok p hp hp1' p hp hp1' (hle0 p hp hp1') (hle1 p hp hp1')).2.2 j a A ha hap hpA hA
  · intro j a ha ha1
    simp only [tau, if_pos rfl]
    exact h1 j a ha ha1

end RandomSizeStable.Stability.RankCutCert
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory RandomSizeStable.Stability RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsCover : ∀ p : ℝ, 0 < p → p < 1 → ∃ (p0 p1 l0 l1 l2 : ℝ) (t0 t1 : Fin 9 → ℝ),
    CellOK p0 p1 l0 l1 l2 t0 t1 ∧ p0 ≤ p ∧ p ≤ p1 := by
  intro p hp0 hp1
  by_cases hz : p ≤ (1 / 512 : ℝ)
  · obtain ⟨n, p0, p1, l0, l1, l2, t0, t1, hok, hcov⟩ := RandomSizeStable.Stability.RankCutCert.cells_near_zero
    obtain ⟨k, hk⟩ := hcov p hp0 hz
    exact ⟨_, _, _, _, _, _, _, hok k, hk⟩
  by_cases ho : (4095 / 4096 : ℝ) ≤ p
  · obtain ⟨n, p0, p1, l0, l1, l2, t0, t1, hok, hcov⟩ := RandomSizeStable.Stability.RankCutCert.cells_near_one
    obtain ⟨k, hk⟩ := hcov p ho hp1
    exact ⟨_, _, _, _, _, _, _, hok k, hk⟩
  by_cases c0 : p ≤ (35 / 16384 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_01, le_of_lt (not_le.mp hz), c0⟩
  by_cases c1 : p ≤ (19 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_02, le_of_lt (not_le.mp c0), c1⟩
  by_cases c2 : p ≤ (41 / 16384 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_03, le_of_lt (not_le.mp c1), c2⟩
  by_cases c3 : p ≤ (11 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_04, le_of_lt (not_le.mp c2), c3⟩
  by_cases c4 : p ≤ (47 / 16384 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_05, le_of_lt (not_le.mp c3), c4⟩
  by_cases c5 : p ≤ (25 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_06, le_of_lt (not_le.mp c4), c5⟩
  by_cases c6 : p ≤ (7 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_07, le_of_lt (not_le.mp c5), c6⟩
  by_cases c7 : p ≤ (17 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_08, le_of_lt (not_le.mp c6), c7⟩
  by_cases c8 : p ≤ (5 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_09, le_of_lt (not_le.mp c7), c8⟩
  by_cases c9 : p ≤ (101 / 16384 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_10, le_of_lt (not_le.mp c8), c9⟩
  by_cases c10 : p ≤ (61 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_11, le_of_lt (not_le.mp c9), c10⟩
  by_cases c11 : p ≤ (143 / 16384 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_12, le_of_lt (not_le.mp c10), c11⟩
  by_cases c12 : p ≤ (41 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_13, le_of_lt (not_le.mp c11), c12⟩
  by_cases c13 : p ≤ (123 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_14, le_of_lt (not_le.mp c12), c13⟩
  by_cases c14 : p ≤ (41 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsLow_15, le_of_lt (not_le.mp c13), c14⟩
  by_cases c15 : p ≤ (143 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).1, le_of_lt (not_le.mp c14), c15⟩
  by_cases c16 : p ≤ (205 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).2.1, le_of_lt (not_le.mp c15), c16⟩
  by_cases c17 : p ≤ (307 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).2.2.1, le_of_lt (not_le.mp c16), c17⟩
  by_cases c18 : p ≤ (205 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).2.2.2.1, le_of_lt (not_le.mp c17), c18⟩
  by_cases c19 : p ≤ (1 / 8 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).2.2.2.2.1, le_of_lt (not_le.mp c18), c19⟩
  by_cases c20 : p ≤ (307 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_01).2.2.2.2.2, le_of_lt (not_le.mp c19), c20⟩
  by_cases c21 : p ≤ (717 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).1, le_of_lt (not_le.mp c20), c21⟩
  by_cases c22 : p ≤ (819 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.1, le_of_lt (not_le.mp c21), c22⟩
  by_cases c23 : p ≤ (461 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.1, le_of_lt (not_le.mp c22), c23⟩
  by_cases c24 : p ≤ (1 / 4 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.1, le_of_lt (not_le.mp c23), c24⟩
  by_cases c25 : p ≤ (563 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.1, le_of_lt (not_le.mp c24), c25⟩
  by_cases c26 : p ≤ (1229 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.2.1, le_of_lt (not_le.mp c25), c26⟩
  by_cases c27 : p ≤ (1331 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.2.2.1, le_of_lt (not_le.mp c26), c27⟩
  by_cases c28 : p ≤ (717 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.2.2.2.1, le_of_lt (not_le.mp c27), c28⟩
  by_cases c29 : p ≤ (3 / 8 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.2.2.2.2.1, le_of_lt (not_le.mp c28), c29⟩
  by_cases c30 : p ≤ (819 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_02).2.2.2.2.2.2.2.2.2, le_of_lt (not_le.mp c29), c30⟩
  by_cases c31 : p ≤ (1741 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).1, le_of_lt (not_le.mp c30), c31⟩
  by_cases c32 : p ≤ (1843 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.1, le_of_lt (not_le.mp c31), c32⟩
  by_cases c33 : p ≤ (973 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.2.1, le_of_lt (not_le.mp c32), c33⟩
  by_cases c34 : p ≤ (1 / 2 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.2.2.1, le_of_lt (not_le.mp c33), c34⟩
  by_cases c35 : p ≤ (1075 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.2.2.2.1, le_of_lt (not_le.mp c34), c35⟩
  by_cases c36 : p ≤ (2253 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.2.2.2.2.1, le_of_lt (not_le.mp c35), c36⟩
  by_cases c37 : p ≤ (2355 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_03).2.2.2.2.2.2, le_of_lt (not_le.mp c36), c37⟩
  by_cases c38 : p ≤ (1229 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_04).1, le_of_lt (not_le.mp c37), c38⟩
  by_cases c39 : p ≤ (5 / 8 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_04).2.1, le_of_lt (not_le.mp c38), c39⟩
  by_cases c40 : p ≤ (1331 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_04).2.2, le_of_lt (not_le.mp c39), c40⟩
  by_cases c41 : p ≤ (5427 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_05).1, le_of_lt (not_le.mp c40), c41⟩
  by_cases c42 : p ≤ (2765 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_05).2, le_of_lt (not_le.mp c41), c42⟩
  by_cases c43 : p ≤ (11 / 16 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_06).1, le_of_lt (not_le.mp c42), c43⟩
  by_cases c44 : p ≤ (2867 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_06).2, le_of_lt (not_le.mp c43), c44⟩
  by_cases c45 : p ≤ (361 / 512 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_07).1, le_of_lt (not_le.mp c44), c45⟩
  by_cases c46 : p ≤ (727 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_07).2.1, le_of_lt (not_le.mp c45), c46⟩
  by_cases c47 : p ≤ (2929 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_07).2.2.1, le_of_lt (not_le.mp c46), c47⟩
  by_cases c48 : p ≤ (2949 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_07).2.2.2, le_of_lt (not_le.mp c47), c48⟩
  by_cases c49 : p ≤ (1485 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_08).1, le_of_lt (not_le.mp c48), c49⟩
  by_cases c50 : p ≤ (1495 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_08).2.1, le_of_lt (not_le.mp c49), c50⟩
  by_cases c51 : p ≤ (3011 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_08).2.2.1, le_of_lt (not_le.mp c50), c51⟩
  by_cases c52 : p ≤ (3031 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_08).2.2.2, le_of_lt (not_le.mp c51), c52⟩
  by_cases c53 : p ≤ (6083 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_09).1, le_of_lt (not_le.mp c52), c53⟩
  by_cases c54 : p ≤ (763 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_09).2, le_of_lt (not_le.mp c53), c54⟩
  by_cases c55 : p ≤ (3057 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_10).1, le_of_lt (not_le.mp c54), c55⟩
  by_cases c56 : p ≤ (6119 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_10).2, le_of_lt (not_le.mp c55), c56⟩
  by_cases c57 : p ≤ (1531 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_11).1, le_of_lt (not_le.mp c56), c57⟩
  by_cases c58 : p ≤ (6129 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_11).2, le_of_lt (not_le.mp c57), c58⟩
  by_cases c59 : p ≤ (3067 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_12).1, le_of_lt (not_le.mp c58), c59⟩
  by_cases c60 : p ≤ (6139 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_12).2.1, le_of_lt (not_le.mp c59), c60⟩
  by_cases c61 : p ≤ (3 / 4 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_12).2.2, le_of_lt (not_le.mp c60), c61⟩
  by_cases c62 : p ≤ (1541 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_13).1, le_of_lt (not_le.mp c61), c62⟩
  by_cases c63 : p ≤ (773 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_13).2, le_of_lt (not_le.mp c62), c63⟩
  by_cases c64 : p ≤ (6205 / 8192 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_14).1, le_of_lt (not_le.mp c63), c64⟩
  by_cases c65 : p ≤ (3113 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_14).2.1, le_of_lt (not_le.mp c64), c65⟩
  by_cases c66 : p ≤ (3133 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_14).2.2, le_of_lt (not_le.mp c65), c66⟩
  by_cases c67 : p ≤ (1577 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_15).1, le_of_lt (not_le.mp c66), c67⟩
  by_cases c68 : p ≤ (1587 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_15).2.1, le_of_lt (not_le.mp c67), c68⟩
  by_cases c69 : p ≤ (3195 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_15).2.2.1, le_of_lt (not_le.mp c68), c69⟩
  by_cases c70 : p ≤ (3215 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_15).2.2.2.1, le_of_lt (not_le.mp c69), c70⟩
  by_cases c71 : p ≤ (809 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_15).2.2.2.2, le_of_lt (not_le.mp c70), c71⟩
  by_cases c72 : p ≤ (407 / 512 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_16).1, le_of_lt (not_le.mp c71), c72⟩
  by_cases c73 : p ≤ (3277 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_16).2.1, le_of_lt (not_le.mp c72), c73⟩
  by_cases c74 : p ≤ (3379 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_16).2.2.1, le_of_lt (not_le.mp c73), c74⟩
  by_cases c75 : p ≤ (1741 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_16).2.2.2, le_of_lt (not_le.mp c74), c75⟩
  by_cases c76 : p ≤ (7 / 8 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_17).1, le_of_lt (not_le.mp c75), c76⟩
  by_cases c77 : p ≤ (1843 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_17).2.1, le_of_lt (not_le.mp c76), c77⟩
  by_cases c78 : p ≤ (3789 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsMid_17).2.2, le_of_lt (not_le.mp c77), c78⟩
  by_cases c79 : p ≤ (3891 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsMid_18, le_of_lt (not_le.mp c78), c79⟩
  by_cases c80 : p ≤ (3973 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsHigh_01).1, le_of_lt (not_le.mp c79), c80⟩
  by_cases c81 : p ≤ (4035 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsHigh_01).2.1, le_of_lt (not_le.mp c80), c81⟩
  by_cases c82 : p ≤ (1019 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, (RandomSizeStable.Stability.RankCutCert.cellsHigh_01).2.2, le_of_lt (not_le.mp c81), c82⟩
  by_cases c83 : p ≤ (2043 / 2048 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsHigh_02, le_of_lt (not_le.mp c82), c83⟩
  by_cases c84 : p ≤ (1023 / 1024 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsHigh_03, le_of_lt (not_le.mp c83), c84⟩
  by_cases c85 : p ≤ (4095 / 4096 : ℝ)
  · exact ⟨_, _, _, _, _, _, _, RandomSizeStable.Stability.RankCutCert.cellsHigh_04, le_of_lt (not_le.mp c84), c85⟩
  exact absurd (le_of_lt (not_le.mp c85)) ho

theorem RandomSizeStable.Stability.RankCutCert.rank_cut_certificate_dStar_dev :

    ∃ (b : ℝ) (lam : ℝ → ℝ) (lo hi : Fin 9 → ℝ) (nu : Fin 9 → Measure ℝ)
      (tau : Fin 9 → ℝ → ℝ),
      (0 ≤ (113609 / 200000 : ℝ)) ∧
      (b ∈ Set.Icc (0 : ℝ) 1) ∧ (pgf dStar b ≤ benchmark dStar) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam p) ∧
      (lam 0 = 0) ∧ (lam 1 = 0) ∧
      (∀ j, Set.Icc (lo j) (hi j) ⊆ Set.Icc 0 b) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) b, ∃ j, r ∈ Set.Icc (lo j) (hi j)) ∧
      (∀ j, nu j ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) ∧
      (∀ j, nu j Set.univ = ENNReal.ofReal (113609 / 200000 : ℝ)) ∧
      (∀ j p, p ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau j p) ∧
      (∀ j, tau j 0 = 0) ∧
      (∀ (j : Fin 9) (r : ℝ),
        r ∈ Set.Icc (lo j) (hi j) ∪ Set.Icc b 1 →
        ∀ a p A : ℝ, 0 ≤ a → a ≤ min p r → p ≤ A → A ≤ 1 →
          a + lam p * (primitive dStar a + primitive dStar A - primitive dStar (a + A - p)
            - p * benchmark dStar) + tau j p * (benchmark dStar - pgf dStar r) ≤
          (nu j {z : ℝ | a ≤ min z r ∧ min z r < A}).toReal) :=
  assemble_pointwise RandomSizeStable.Stability.RankCutCert.cellsCover _ _ RandomSizeStable.Stability.RankCutCert.p1_ok.1 RandomSizeStable.Stability.RankCutCert.p1_ok.2
end

theorem solution : type_of% @RandomSizeStable.Stability.RankCutCert.rank_cut_certificate_dStar_dev := @RandomSizeStable.Stability.RankCutCert.rank_cut_certificate_dStar_dev
