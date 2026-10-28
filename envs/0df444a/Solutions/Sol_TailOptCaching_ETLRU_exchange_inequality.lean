-- Prove2me | solution 1 for TailOptCaching.ETLRU.exchange_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:52:35.369007+00:00
-- url     : https://prove2.me/submissions/af03686b-28fc-4939-bb75-3b2ceda6b009

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal
open MeasureTheory

namespace TailOptCaching.ETLRU

def qsC : ℕ → ℕ := fun i => if i = 0 then 1 else if i = 2 then 2 else 0

noncomputable def PC : Params where
  C := 2
  ξ := 0
  ξ_nonneg := le_refl _
  lamConv := 1 / 1000
  lamConv_pos := by norm_num
  lamBar := fun i => if i = 0 ∨ i = 1 then 2 else 1 / 1000
  lamBar_pos := by intro i; split_ifs <;> norm_num
  Qlaw := fun i => PMF.pure (qsC i)
  Alaw := fun _ => PMF.pure 0
  decayLaw := fun _ => Measure.dirac 1
  decayLaw_prob := fun _ => inferInstance
  decayLaw_mem := by
    intro r
    rw [Measure.dirac_apply' _ (measurableSet_Ioc.compl)]
    simp

lemma decay_one (s : State) : decay 1 s = s := by
  cases s; simp [decay]

lemma arrivalExp_PC (s : State) (F : ℕ → ℕ → ℕ → ℝ≥0∞) :
    arrivalExp PC s F = ∑ θ ∈ Finset.range (s.n + 1), arrivalProb PC s θ * F θ (qsC θ) 0 := by
  unfold arrivalExp
  refine Finset.sum_congr rfl fun θ _ => ?_
  congr 1
  rw [tsum_eq_single (qsC θ)]
  · simp only [PC, PMF.pure_apply, if_true, one_mul]
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  · intro b hb; simp [PC, PMF.pure_apply, hb]

lemma optValue_succ_PC (r : ℕ) (s : State) :
    optValue PC (r + 1) s = ∑ θ ∈ Finset.range (s.n + 1), arrivalProb PC s θ *
      (stageCost PC s θ (qsC θ) +
        ⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y), optValue PC r (post PC s θ (qsC θ) 0 Y)) := by
  rw [optValue]
  have : PC.decayLaw s.lam = Measure.dirac 1 := rfl
  rw [this, lintegral_dirac, decay_one, arrivalExp_PC]

lemma optValue_one_PC (s : State) :
    optValue PC 1 s = ∑ θ ∈ Finset.range (s.n + 1), arrivalProb PC s θ * stageCost PC s θ (qsC θ) := by
  rw [optValue_succ_PC]
  refine Finset.sum_congr rfl fun θ _ => ?_
  congr 1
  have : (⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y), optValue PC 0 (post PC s θ (qsC θ) 0 Y)) = 0 := by
    apply le_antisymm
    · refine iInf_le_of_le (fun _ => 0) (iInf_le_of_le ?_ ?_)
      · exact ⟨Nat.zero_le _, fun i _ => Nat.zero_le _, by simp⟩
      · simp [optValue]
    · exact zero_le
  rw [this, add_zero]

lemma optValue_one_real (w : State) (hw : ∀ i < w.n, 0 ≤ w.lam i) :
    optValue PC 1 w = ENNReal.ofReal (∑ θ ∈ Finset.range (w.n + 1),
      (if θ < w.n then w.lam θ else if θ = w.n then (1 / 1000 : ℝ) else 0) /
        (1 / 1000 + ∑ i ∈ Finset.range w.n, w.lam i) *
        max ((w.L θ : ℝ) + qsC θ - w.X θ) 0) := by
  rw [optValue_one_PC]
  have hden : 0 < (1 / 1000 : ℝ) + ∑ i ∈ Finset.range w.n, w.lam i := by
    have : 0 ≤ ∑ i ∈ Finset.range w.n, w.lam i :=
      Finset.sum_nonneg fun i hi => hw i (Finset.mem_range.mp hi)
    linarith
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun θ hθ => ?_
    have hnum : 0 ≤ (if θ < w.n then w.lam θ else if θ = w.n then (1 / 1000 : ℝ) else 0) := by
      split_ifs with h1 h2
      · exact hw θ h1
      · norm_num
      · exact le_refl _
    rw [ENNReal.ofReal_mul (div_nonneg hnum hden.le)]
    unfold arrivalProb stageCost
    have hm : ENNReal.ofReal (max ((w.L θ : ℝ) + qsC θ - w.X θ) 0) =
        ENNReal.ofReal ((w.L θ : ℝ) + qsC θ - w.X θ) := by
      rcases le_total ((w.L θ : ℝ) + qsC θ - w.X θ) 0 with h | h
      · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h]; simp
      · rw [max_eq_left h]
    rw [hm]
    simp only [PC, sub_zero]
  · intro θ hθ
    have hnum : 0 ≤ (if θ < w.n then w.lam θ else if θ = w.n then (1 / 1000 : ℝ) else 0) := by
      split_ifs with h1 h2
      · exact hw θ h1
      · norm_num
      · exact le_refl _
    exact mul_nonneg (div_nonneg hnum hden.le) (le_max_right _ _)


noncomputable def zC : State where
  n := 3
  lam := fun i => if i = 0 then 7 / 4 else if i = 1 then 2 else if i = 2 then 1 / 1000 else 0
  L := fun i => if i < 3 then 1 else 0
  X := fun i => if i < 3 then 1 else 0

lemma branch_lb (s : State) (θ : ℕ) (lb : ℝ)
    (h : ∀ Y, Feasible PC s θ (qsC θ) 0 Y →
      ENNReal.ofReal lb ≤ optValue PC 1 (post PC s θ (qsC θ) 0 Y)) :
    ENNReal.ofReal lb ≤ ⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y),
      optValue PC 1 (post PC s θ (qsC θ) 0 Y) :=
  le_iInf fun Y => le_iInf fun hY => h Y hY

lemma branch_ub (s : State) (θ : ℕ) (ub : ℝ) (Y : ℕ → ℕ) (hY : Feasible PC s θ (qsC θ) 0 Y)
    (h : optValue PC 1 (post PC s θ (qsC θ) 0 Y) ≤ ENNReal.ofReal ub) :
    (⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y),
      optValue PC 1 (post PC s θ (qsC θ) 0 Y)) ≤ ENNReal.ofReal ub :=
  iInf_le_of_le Y (iInf_le_of_le hY h)

lemma zC_lam_nonneg : ∀ i, 0 ≤ zC.lam i := by
  intro i; simp only [zC]; split_ifs <;> norm_num

lemma post_lam_nonneg (s : State) (hs : ∀ i, 0 ≤ s.lam i) (θ q a : ℕ) (Y : ℕ → ℕ) :
    ∀ i, 0 ≤ (post PC s θ q a Y).lam i := by
  intro i
  simp only [post]
  by_cases h : i = θ
  · subst h; simp only [Function.update_self, PC]; split_ifs <;> norm_num
  · rw [Function.update_of_ne h]; exact hs i


/-- weights of the arrival distribution. -/
noncomputable def wt (s : State) (θ : ℕ) : ℝ :=
  (if θ < s.n then s.lam θ else if θ = s.n then (1 / 1000 : ℝ) else 0) /
    (1 / 1000 + ∑ i ∈ Finset.range s.n, s.lam i)

/-- stage cost, real version. -/
noncomputable def cst (s : State) (θ : ℕ) : ℝ := (s.L θ : ℝ) + qsC θ - s.X θ

lemma wt_nonneg (s : State) (hs : ∀ i, 0 ≤ s.lam i) (θ : ℕ) : 0 ≤ wt s θ := by
  unfold wt
  have h1 : 0 ≤ ∑ i ∈ Finset.range s.n, s.lam i := Finset.sum_nonneg fun i _ => hs i
  apply div_nonneg
  · split_ifs
    · exact hs _
    · norm_num
    · exact le_refl _
  · linarith

lemma arrivalProb_eq (s : State) (θ : ℕ) : arrivalProb PC s θ = ENNReal.ofReal (wt s θ) := rfl

lemma stageCost_eq (s : State) (θ : ℕ) : stageCost PC s θ (qsC θ) = ENNReal.ofReal (cst s θ) := by
  simp [stageCost, cst, PC]

lemma term_lb (s : State) (hs : ∀ i, 0 ≤ s.lam i) (θ : ℕ) (lb : ℝ) (hc : 0 ≤ cst s θ) (hlb : 0 ≤ lb)
    (h : ∀ Y, Feasible PC s θ (qsC θ) 0 Y →
      ENNReal.ofReal lb ≤ optValue PC 1 (post PC s θ (qsC θ) 0 Y)) :
    ENNReal.ofReal (wt s θ * (cst s θ + lb)) ≤ arrivalProb PC s θ *
      (stageCost PC s θ (qsC θ) +
        ⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y), optValue PC 1 (post PC s θ (qsC θ) 0 Y)) := by
  rw [arrivalProb_eq, stageCost_eq, ENNReal.ofReal_mul (wt_nonneg s hs θ), ENNReal.ofReal_add hc hlb]
  gcongr
  exact branch_lb s θ lb h

lemma term_ub (s : State) (hs : ∀ i, 0 ≤ s.lam i) (θ : ℕ) (ub : ℝ) (hc : 0 ≤ cst s θ) (hub : 0 ≤ ub)
    (Y : ℕ → ℕ) (hY : Feasible PC s θ (qsC θ) 0 Y)
    (h : optValue PC 1 (post PC s θ (qsC θ) 0 Y) ≤ ENNReal.ofReal ub) :
    arrivalProb PC s θ *
      (stageCost PC s θ (qsC θ) +
        ⨅ (Y : ℕ → ℕ) (_ : Feasible PC s θ (qsC θ) 0 Y), optValue PC 1 (post PC s θ (qsC θ) 0 Y))
    ≤ ENNReal.ofReal (wt s θ * (cst s θ + ub)) := by
  rw [arrivalProb_eq, stageCost_eq, ENNReal.ofReal_mul (wt_nonneg s hs θ), ENNReal.ofReal_add hc hub]
  gcongr
  exact branch_ub s θ ub Y hY h

/-- lower bound of V1 on a post state (generic closing tactic is applied per case). -/
lemma A0_lb : ∀ Y, Feasible PC (evict zC 0) 0 (qsC 0) 0 Y →
      ENNReal.ofReal (9/10) ≤ optValue PC 1 (post PC (evict zC 0) 0 (qsC 0) 0 Y) := by
  intro Y hY
  obtain ⟨h1, h2, h3⟩ := hY
  have e1 := h2 1 (by norm_num)
  have e2 := h2 2 (by norm_num)
  simp [PC, qsC, evict, zC, Function.update, nAfter, Finset.sum_range_succ] at h1 e1 e2 h3
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 0) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  generalize Y 0 = a at h1 h3 ⊢
  generalize Y 1 = b at e1 h3 ⊢
  generalize Y 2 = c at e2 h3 ⊢
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | (exfalso; omega) | norm_num

lemma A1_lb : ∀ Y, Feasible PC (evict zC 0) 1 (qsC 1) 0 Y →
      ENNReal.ofReal (9/10) ≤ optValue PC 1 (post PC (evict zC 0) 1 (qsC 1) 0 Y) := by
  intro Y hY
  obtain ⟨h1, h2, h3⟩ := hY
  have e0 := h2 0 (by norm_num)
  have e2 := h2 2 (by norm_num)
  simp [PC, qsC, evict, zC, Function.update, nAfter, Finset.sum_range_succ] at h1 e0 e2 h3
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 0) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  simp only [e0] at h3 ⊢
  generalize Y 1 = b at h1 h3 ⊢
  generalize Y 2 = c at e2 h3 ⊢
  interval_cases b <;> interval_cases c <;> first | (exfalso; omega) | norm_num


lemma B0_feas : Feasible PC (evict zC 1) 0 (qsC 0) 0 (fun i => if i = 0 then 2 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [PC, qsC, evict, zC, Function.update]
  · intro i hi
    simp [hi, evict, zC, Function.update]
  · simp [PC, nAfter, Finset.sum_range_succ]

lemma B0_ub : optValue PC 1 (post PC (evict zC 1) 0 (qsC 0) 0 (fun i => if i = 0 then 2 else 0))
    ≤ ENNReal.ofReal (1001 / 1000) := by
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 1) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  norm_num

lemma B1_feas : Feasible PC (evict zC 1) 1 (qsC 1) 0 (fun i => if i < 2 then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [PC, qsC, evict, zC, Function.update]
  · intro i hi
    simp [evict, zC, Function.update]
    split_ifs <;> omega
  · show ∑ i ∈ Finset.range (max 3 2), (if i < 2 then 1 else 0) ≤ 2
    decide

lemma B1_ub : optValue PC 1 (post PC (evict zC 1) 1 (qsC 1) 0 (fun i => if i < 2 then 1 else 0))
    ≤ ENNReal.ofReal (1 / 2) := by
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 1) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  norm_num

lemma B2_ub : optValue PC 1 (post PC (evict zC 1) 2 (qsC 2) 0 (fun _ => 0))
    ≤ ENNReal.ofReal 2 := by
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 1) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  norm_num

lemma B3_ub : optValue PC 1 (post PC (evict zC 1) 3 (qsC 3) 0 (fun _ => 0))
    ≤ ENNReal.ofReal 2 := by
  rw [optValue_one_real _ (fun i _ => post_lam_nonneg (evict zC 1) (fun i => zC_lam_nonneg i) _ _ _ _ i)]
  apply ENNReal.ofReal_le_ofReal
  simp [Finset.sum_range_succ, post, evict, zC, nAfter, qsC, PC]
  norm_num

lemma zero_feas (s : State) (θ : ℕ) : Feasible PC s θ (qsC θ) 0 (fun _ => 0) :=
  ⟨Nat.zero_le _, fun i _ => Nat.zero_le _, by simp⟩


lemma cst_nonneg (j : ℕ) : ∀ θ < 4, 0 ≤ cst (evict zC j) θ := by
  intro θ hθ
  unfold cst evict zC qsC
  simp only []
  by_cases h : θ = j
  · subst h
    simp only [Function.update_self]
    interval_cases θ <;> norm_num
  · rw [Function.update_of_ne h]
    interval_cases θ <;> norm_num

noncomputable def lbA (θ : ℕ) : ℝ := if θ = 0 ∨ θ = 1 then 9 / 10 else 0
noncomputable def ubB (θ : ℕ) : ℝ := if θ = 0 then 1001 / 1000 else if θ = 1 then 1 / 2 else 2

lemma lbA_nonneg (θ : ℕ) : 0 ≤ lbA θ := by unfold lbA; split_ifs <;> norm_num
lemma ubB_nonneg (θ : ℕ) : 0 ≤ ubB θ := by unfold ubB; split_ifs <;> norm_num

lemma V2A_lb : ENNReal.ofReal (∑ θ ∈ Finset.range 4, wt (evict zC 0) θ * (cst (evict zC 0) θ + lbA θ))
    ≤ optValue PC 2 (evict zC 0) := by
  have h4 : (evict zC 0).n + 1 = 4 := rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, optValue_succ_PC, h4]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro θ hθ
    have hθ' : θ < 4 := Finset.mem_range.mp hθ
    apply term_lb (evict zC 0) (fun i => zC_lam_nonneg i) θ (lbA θ) (cst_nonneg 0 θ hθ') (lbA_nonneg θ)
    interval_cases θ
    · rw [show lbA 0 = 9 / 10 by norm_num [lbA]]; exact A0_lb
    · rw [show lbA 1 = 9 / 10 by norm_num [lbA]]; exact A1_lb
    · intro Y _; simp [lbA]
    · intro Y _; simp [lbA]
  · intro θ hθ
    exact mul_nonneg (wt_nonneg _ (fun i => zC_lam_nonneg i) θ)
      (add_nonneg (cst_nonneg 0 θ (Finset.mem_range.mp hθ)) (lbA_nonneg θ))

lemma V2B_ub : optValue PC 2 (evict zC 1) ≤
    ENNReal.ofReal (∑ θ ∈ Finset.range 4, wt (evict zC 1) θ * (cst (evict zC 1) θ + ubB θ)) := by
  have h4 : (evict zC 1).n + 1 = 4 := rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, optValue_succ_PC, h4]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro θ hθ
    have hθ' : θ < 4 := Finset.mem_range.mp hθ
    interval_cases θ
    · exact term_ub (evict zC 1) (fun i => zC_lam_nonneg i) 0 (ubB 0) (cst_nonneg 1 0 hθ') (ubB_nonneg 0) _ B0_feas
        (by rw [show ubB 0 = 1001 / 1000 by norm_num [ubB]]; exact B0_ub)
    · exact term_ub (evict zC 1) (fun i => zC_lam_nonneg i) 1 (ubB 1) (cst_nonneg 1 1 hθ') (ubB_nonneg 1) _ B1_feas
        (by rw [show ubB 1 = 1 / 2 by norm_num [ubB]]; exact B1_ub)
    · exact term_ub (evict zC 1) (fun i => zC_lam_nonneg i) 2 (ubB 2) (cst_nonneg 1 2 hθ') (ubB_nonneg 2) _ (zero_feas _ 2)
        (by rw [show ubB 2 = 2 by norm_num [ubB]]; exact B2_ub)
    · exact term_ub (evict zC 1) (fun i => zC_lam_nonneg i) 3 (ubB 3) (cst_nonneg 1 3 hθ') (ubB_nonneg 3) _ (zero_feas _ 3)
        (by rw [show ubB 3 = 2 by norm_num [ubB]]; exact B3_ub)
  · intro θ hθ
    exact mul_nonneg (wt_nonneg _ (fun i => zC_lam_nonneg i) θ)
      (add_nonneg (cst_nonneg 1 θ (Finset.mem_range.mp hθ)) (ubB_nonneg θ))

lemma real_gap :
    ∑ θ ∈ Finset.range 4, wt (evict zC 1) θ * (cst (evict zC 1) θ + ubB θ) <
    ∑ θ ∈ Finset.range 4, wt (evict zC 0) θ * (cst (evict zC 0) θ + lbA θ) := by
  simp [Finset.sum_range_succ, wt, cst, evict, zC, qsC, lbA, ubB, Function.update]
  norm_num


lemma zC_wf (j : ℕ) (hj : j < 3) : WellFormed PC (evict zC j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi3 : i < 3 := hi
    interval_cases i <;> norm_num [PC, evict, zC]
  · intro i hi
    have hi3 : 3 ≤ i := hi
    have h1 : ¬ i = 0 := by omega
    have h2 : ¬ i = 1 := by omega
    have h3 : ¬ i = 2 := by omega
    have h4 : ¬ i < 3 := by omega
    simp [evict, zC, h1, h2, h3, h4]
    by_cases hij : i = j
    · omega
    · simp [Function.update_of_ne hij, h4]
  · intro i
    simp only [evict, zC]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij]
  · interval_cases j <;> simp [evict, zC, PC, Finset.sum_range_succ, Function.update]

lemma tailProb_PC (i L X : ℕ) :
    tailProb PC i L X = if (X : ℝ) ≤ (L : ℝ) + qsC i - 0 then 1 else 0 := by
  unfold tailProb
  rw [tsum_eq_single (qsC i)]
  · simp [PC, PMF.pure_apply]
  · intro b hb; simp [PC, PMF.pure_apply, hb]

end TailOptCaching.ETLRU

open TailOptCaching.ETLRU

theorem solution : ¬ (∀ (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (r : ℕ) (z : State)
    (i j : ℕ) (hi : i < z.n) (hj : j < z.n) (hXi : 1 ≤ z.X i) (hXj : 1 ≤ z.X j)
    (hwi : WellFormed P (evict z i)) (hwj : WellFormed P (evict z j))
    (hcap : ∑ l ∈ Finset.range z.n, z.X l = P.C + 1)
    (hscore : score P z i < score P z j),
    optValue P r (evict z i) ≤ optValue P r (evict z j)) := by
  intro h
  have key := h PC ⟨0, by simp [PC]⟩ 2 zC 0 1 (by decide) (by decide) (by simp [zC]) (by simp [zC])
    (zC_wf 0 (by norm_num)) (zC_wf 1 (by norm_num))
    (by
      show ∑ l ∈ Finset.range 3, (if l < 3 then 1 else 0) = 2 + 1
      decide)
    (by
      simp only [score, tailProb_PC]
      simp [zC, qsC]
      norm_num)
  have h1 := V2A_lb
  have h2 := V2B_ub
  have hgap := real_gap
  have hlt : ENNReal.ofReal (∑ θ ∈ Finset.range 4, wt (evict zC 1) θ * (cst (evict zC 1) θ + ubB θ)) <
      ENNReal.ofReal (∑ θ ∈ Finset.range 4, wt (evict zC 0) θ * (cst (evict zC 0) θ + lbA θ)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · exact hgap
    · exact lt_of_le_of_lt (Finset.sum_nonneg fun θ hθ => mul_nonneg
        (wt_nonneg _ (fun i => zC_lam_nonneg i) θ)
        (add_nonneg (cst_nonneg 1 θ (Finset.mem_range.mp hθ)) (ubB_nonneg θ))) hgap
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (key.trans h2) hlt) h1) (lt_irrefl _)
