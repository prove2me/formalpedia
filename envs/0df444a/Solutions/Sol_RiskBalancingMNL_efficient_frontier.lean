-- Prove2me | solution 1 for RiskBalancingMNL.efficient_frontier
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:56:26.226702+00:00
-- url     : https://prove2.me/submissions/5640598f-f5a7-4b12-9f30-b16d918e87eb

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Definitions.Def_RiskBalancingMNL_lambertW
import Theorems.Thm_RiskBalancingMNL_markup_share_inverse
import Theorems.Thm_RiskBalancingMNL_lemma_1
import Theorems.Thm_RiskBalancingMNL_eq_9_10
import Theorems.Thm_RiskBalancingMNL_eq_13_unique_root
import Theorems.Thm_RiskBalancingMNL_lemma_3

open RiskBalancingMNL

private lemma lambertW_spec_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ lambertW s ∧ lambertW s * Real.exp (lambertW s) = s := by
  have hex : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = s := by
    let g : ℝ → ℝ := fun w => w * Real.exp w
    have hcont : ContinuousOn g (Set.Icc 0 s) :=
      (continuous_id.mul Real.continuous_exp).continuousOn
    have hg0 : g 0 = 0 := by simp [g]
    have hgs : s ≤ g s := by
      dsimp [g]
      exact le_mul_of_one_le_right hs (Real.one_le_exp hs)
    have hmem : s ∈ Set.Icc (g 0) (g s) := ⟨by linarith, hgs⟩
    obtain ⟨w, hw_in, hw_eq⟩ := intermediate_value_Icc hs hcont hmem
    exact ⟨w, hw_in.1, hw_eq⟩
  unfold lambertW
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem solution {n : ℕ} [NeZero n] (P : Params n) :
    (IsOptimal P 0
        (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b)) ∧
      ∀ m' : Fin n → ℝ, profit P m' ≤
        profit P (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b))) ∧
    (∀ lam : ℝ, 0 < lam → lam < lamBar P →
      (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0) ∧
      ∀ x ∈ Set.Ioo 0 (1 - lam),
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0 →
        IsOptimal P lam (constM (mHat P x)) ∧ noPurchase P (constM (mHat P x)) = x) ∧
    (∀ lam : ℝ, lamBar P ≤ lam → lam < 1 → IsOptimal P lam (constM 0)) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ m m' : Fin n → ℝ,
      IsOptimal P lam m → IsOptimal P lam m' → m = m') ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < lamBar P → ∀ m : Fin n → ℝ, IsOptimal P lam m →
      ∃ t : ℝ, 0 < t ∧ m = constM t) ∧
    (∀ lam lam' t t' : ℝ, 0 ≤ lam → lam < lam' → lam' < lamBar P →
      IsOptimal P lam (constM t) → IsOptimal P lam' (constM t') →
      t' < t ∧ noPurchase P (constM t') < noPurchase P (constM t)) := by
  obtain ⟨hm_all, hmHat_inv, hmHat_left, hmHat_mono⟩ := markup_share_inverse P
  obtain ⟨h9, hfeas_const, _⟩ := eq_9_10 P
  have hA_pos : 0 < zeroMarkupMass P :=
    (Real.exp_pos _).trans_le
      (Finset.single_le_sum (f := fun i => Real.exp (P.a i - P.b * P.c i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin n)))
  have hlamBar_pos : 0 < lamBar P := div_pos hA_pos (by linarith)
  have hlamBar_lt1 : lamBar P < 1 := by
    unfold lamBar
    rw [div_lt_one (by linarith)]
    linarith
  have hq0_zero : noPurchase P (constM 0) = 1 - lamBar P := by
    have hattr0 : ∑ j, attraction P (constM 0) j = zeroMarkupMass P := by
      unfold attraction constM zeroMarkupMass
      refine Finset.sum_congr rfl fun j _ => ?_
      ring_nf
    unfold noPurchase lamBar
    rw [hattr0]
    have hden : 1 + zeroMarkupMass P ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hmHat_x0 : mHat P (1 - lamBar P) = 0 := by
    rw [← hq0_zero]
    exact hmHat_left 0
  have hq0_mem : ∀ m : Fin n → ℝ, noPurchase P m ∈ Set.Ioo 0 1 := by
    intro m
    obtain ⟨hq_pos, hq0_pos, hsum1, _, _⟩ := hm_all m
    have hS_pos : 0 < ∑ i, share P m i :=
      (hq_pos 0).trans_le
        (Finset.single_le_sum (fun i _ => (hq_pos i).le) (Finset.mem_univ (0 : Fin n)))
    exact ⟨hq0_pos, by linarith⟩
  have hobj_eq_LTilde : ∀ lam s : ℝ,
      objective P lam (constM s) = LTilde P lam (noPurchase P (constM s)) := by
    intro lam s
    obtain ⟨h9a, h9b, h9c⟩ := h9 lam s
    rw [h9a, h9b, h9c]
    unfold LTilde
    rw [hmHat_left s]
  have hopt_low : ∀ (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < lamBar P)
      (x : ℝ) (hx : x ∈ Set.Ioo 0 (1 - lam)) (hfoc : foc P lam x = 0),
      0 < mHat P x ∧
      noPurchase P (constM (mHat P x)) = x ∧
      IsOptimal P lam (constM (mHat P x)) ∧
      ∀ m' : Fin n → ℝ, Feasible P m' → m' ≠ constM (mHat P x) →
        objective P lam m' < objective P lam (constM (mHat P x)) := by
    intro lam hlam0 hlam x hx hfoc
    obtain ⟨_, _, hgt_x0⟩ := eq_13_unique_root P lam hlam0 hlam
    obtain ⟨hmono_L, hanti_L⟩ := lemma_3 P lam hlam0 hlam x hx hfoc
    have hx0_lt_x : 1 - lamBar P < x := hgt_x0 x hx hfoc
    have hx0_pos : 0 < 1 - lamBar P := by linarith
    have hx_Ioo01 : x ∈ Set.Ioo 0 1 := ⟨hx.1, by linarith [hx.2]⟩
    have ht_pos : 0 < mHat P x := by
      rw [← hmHat_x0]
      exact hmHat_mono ⟨hx0_pos, by linarith⟩ hx_Ioo01 hx0_lt_x
    have hq0_x : noPurchase P (constM (mHat P x)) = x := hmHat_inv x hx_Ioo01.1 hx_Ioo01.2
    have hobj_x_eq : objective P lam (constM (mHat P x)) = LTilde P lam x := by
      rw [hobj_eq_LTilde, hq0_x]
    have hLT_x_pos : 0 < LTilde P lam x := by
      unfold LTilde
      exact mul_pos (mul_pos (sq_pos_of_pos ht_pos) (by linarith [hx_Ioo01.2]))
        (by linarith [hx.2])
    have hconst_strict : ∀ t : ℝ, 0 ≤ t → t ≠ mHat P x →
        objective P lam (constM t) < objective P lam (constM (mHat P x)) := by
      intro t ht_nonneg ht_ne
      let y : ℝ := noPurchase P (constM t)
      have hy_Ioo : y ∈ Set.Ioo 0 1 := hq0_mem (constM t)
      have hm_y : mHat P y = t := hmHat_left t
      have hy_ne_x : y ≠ x := by
        intro hyeq
        apply ht_ne
        rw [← hm_y, hyeq]
      have hx0_le_y : 1 - lamBar P ≤ y := by
        by_contra hlt
        have : mHat P y < mHat P (1 - lamBar P) :=
          hmHat_mono hy_Ioo ⟨hx0_pos, by linarith⟩ (lt_of_not_ge hlt)
        linarith
      rw [hobj_eq_LTilde, hobj_x_eq]
      change LTilde P lam y < LTilde P lam x
      by_cases hy_lam : 1 - lam ≤ y
      · have hLT_y_nonpos : LTilde P lam y ≤ 0 := by
          unfold LTilde
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (sq_nonneg _) (by linarith [hy_Ioo.2])) (by linarith)
        exact hLT_y_nonpos.trans_lt hLT_x_pos
      · have hy_lt : y < 1 - lam := lt_of_not_ge hy_lam
        rcases lt_or_gt_of_ne hy_ne_x with hlt | hgt
        · exact hmono_L ⟨hx0_le_y, hlt.le⟩ ⟨hx0_lt_x.le, le_rfl⟩ hlt
        · exact hanti_L ⟨le_rfl, hx.2⟩ ⟨hgt.le, hy_lt⟩ hgt
    have hconst_le : ∀ t : ℝ, 0 ≤ t →
        objective P lam (constM t) ≤ objective P lam (constM (mHat P x)) := by
      intro t ht_nonneg
      by_cases hteq : t = mHat P x
      · rw [hteq]
      · exact (hconst_strict t ht_nonneg hteq).le
    have hall_strict : ∀ m' : Fin n → ℝ, Feasible P m' → m' ≠ constM (mHat P x) →
        objective P lam m' < objective P lam (constM (mHat P x)) := by
      intro m' hm' hne
      by_cases heq : ∃ t : ℝ, m' = constM t
      · obtain ⟨t, rfl⟩ := heq
        have ht_nonneg : 0 ≤ t := (hfeas_const t).mp hm'
        have ht_ne : t ≠ mHat P x := fun h => hne (congrArg constM h)
        exact hconst_strict t ht_nonneg ht_ne
      · obtain ⟨t, ht_nonneg, hlt⟩ :=
          (lemma_1 P lam hlam0 (hlam.trans hlamBar_lt1)).1 m' hm' heq
        exact hlt.trans_le (hconst_le t ht_nonneg)
    have his_opt : IsOptimal P lam (constM (mHat P x)) := by
      refine ⟨(hfeas_const (mHat P x)).mpr ht_pos.le, fun m' hm' => ?_⟩
      by_cases hmeq : m' = constM (mHat P x)
      · rw [hmeq]
      · exact (hall_strict m' hm' hmeq).le
    exact ⟨ht_pos, hq0_x, his_opt, hall_strict⟩
  have hopt_high : ∀ (lam : ℝ) (hlam_ge : lamBar P ≤ lam) (hlam1 : lam < 1),
      IsOptimal P lam (constM 0) ∧
      ∀ m' : Fin n → ℝ, Feasible P m' → m' ≠ constM 0 → objective P lam m' < 0 := by
    intro lam hlam_ge hlam1
    have hlam0 : 0 ≤ lam := hlamBar_pos.le.trans hlam_ge
    have hobj0 : objective P lam (constM 0) = 0 := by
      unfold objective profit spread constM
      simp
    have hconst_pos_neg : ∀ t : ℝ, 0 < t → objective P lam (constM t) < 0 := by
      intro t ht_pos
      let y : ℝ := noPurchase P (constM t)
      have hy_Ioo : y ∈ Set.Ioo 0 1 := hq0_mem (constM t)
      have hx0_pos : 0 < 1 - lamBar P := by linarith
      have hx0_lt_y : 1 - lamBar P < y := by
        by_contra hle
        have : mHat P y ≤ mHat P (1 - lamBar P) := by
          rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
          · exact (hmHat_mono hy_Ioo ⟨hx0_pos, by linarith⟩ hlt).le
          · rw [heq]
        have hmy : mHat P y = t := hmHat_left t
        linarith
      obtain ⟨h9a, h9b, h9c⟩ := h9 lam t
      rw [h9a, h9b, h9c]
      exact mul_neg_of_pos_of_neg
        (mul_pos (sq_pos_of_pos ht_pos) (by linarith [hy_Ioo.2]))
        (by dsimp [y] at hx0_lt_y; linarith)
    have hconst_le0 : ∀ t : ℝ, 0 ≤ t → objective P lam (constM t) ≤ 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht with rfl | ht_pos
      · exact hobj0.le
      · exact (hconst_pos_neg t ht_pos).le
    have hall_strict : ∀ m' : Fin n → ℝ, Feasible P m' → m' ≠ constM 0 →
        objective P lam m' < 0 := by
      intro m' hm' hne
      by_cases heq : ∃ t : ℝ, m' = constM t
      · obtain ⟨t, rfl⟩ := heq
        have ht_nonneg : 0 ≤ t := (hfeas_const t).mp hm'
        have ht_ne : t ≠ 0 := fun h => hne (congrArg constM h)
        exact hconst_pos_neg t (lt_of_le_of_ne ht_nonneg ht_ne.symm)
      · obtain ⟨t, ht_nonneg, hlt⟩ := (lemma_1 P lam hlam0 hlam1).1 m' hm' heq
        exact hlt.trans_le (hconst_le0 t ht_nonneg)
    have his_opt0 : IsOptimal P lam (constM 0) := by
      refine ⟨(hfeas_const 0).mpr le_rfl, fun m' hm' => ?_⟩
      rw [hobj0]
      by_cases hmeq : m' = constM 0
      · rw [hmeq, hobj0]
      · exact (hall_strict m' hm' hmeq).le
    exact ⟨his_opt0, hall_strict⟩
  have hcl_a : IsOptimal P 0
        (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b)) ∧
      ∀ m' : Fin n → ℝ, profit P m' ≤
        profit P (constM ((1 + lambertW (∑ i, Real.exp (P.a i - P.b * P.c i - 1))) / P.b)) := by
    let SW : ℝ := ∑ i, Real.exp (P.a i - P.b * P.c i - 1)
    have hSW_nonneg : 0 ≤ SW := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    obtain ⟨hw_nonneg, hw_eq⟩ := lambertW_spec_nonneg hSW_nonneg
    let w : ℝ := lambertW SW
    let t0 : ℝ := (1 + w) / P.b
    let xw : ℝ := 1 / (1 + w)
    have h1w_pos : 0 < 1 + w := by dsimp [w]; linarith
    have hxw_mem : xw ∈ Set.Ioo 0 (1 - 0) := by
      simp only [sub_zero, Set.mem_Ioo, xw]
      refine ⟨div_pos zero_lt_one h1w_pos, ?_⟩
      rw [div_lt_one h1w_pos]
      have hSW_pos : 0 < SW :=
        (Real.exp_pos _).trans_le
          (Finset.single_le_sum (f := fun i => Real.exp (P.a i - P.b * P.c i - 1))
            (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin n)))
      have hw_pos : 0 < w := by
        dsimp [w]
        by_contra hle
        have hw0 : lambertW SW = 0 := le_antisymm (not_lt.mp hle) hw_nonneg
        rw [hw0, zero_mul] at hw_eq
        linarith
      linarith
    have hq0_t0 : noPurchase P (constM t0) = xw := by
      have hattr_t0 : ∑ j, attraction P (constM t0) j = w := by
        unfold attraction constM
        have hterm : ∀ j : Fin n,
            Real.exp (P.a j - P.b * P.c j - P.b * t0) =
              Real.exp (P.a j - P.b * P.c j - 1) * Real.exp (-w) := by
          intro j
          have hb_t0 : P.b * t0 = 1 + w := mul_div_cancel₀ (1 + w) P.hb.ne'
          rw [hb_t0, ← Real.exp_add]
          congr 1
          ring
        simp_rw [hterm, ← Finset.sum_mul]
        change SW * Real.exp (-w) = w
        have hwew : w * Real.exp w = SW := hw_eq
        rw [← hwew, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      unfold noPurchase
      rw [hattr_t0]
    have hm_xw : mHat P xw = t0 := by
      rw [← hq0_t0]
      exact hmHat_left t0
    have hfoc_xw : foc P 0 xw = 0 := by
      unfold foc
      rw [hm_xw]
      simp only [zero_mul, zero_div, add_zero]
      dsimp [t0, xw]
      have hb_ne : P.b ≠ 0 := P.hb.ne'
      have h1w_ne : 1 + w ≠ 0 := h1w_pos.ne'
      field_simp [hb_ne, h1w_ne]
      ring
    obtain ⟨_, _, his_opt_xw, _⟩ := hopt_low 0 le_rfl hlamBar_pos xw hxw_mem hfoc_xw
    rw [hm_xw] at his_opt_xw
    refine ⟨his_opt_xw, fun m' => ?_⟩
    have hπ0_nonneg : 0 ≤ profit P (constM t0) := his_opt_xw.1
    by_cases hfeas_m' : 0 ≤ profit P m'
    · have hobj_le := his_opt_xw.2 m' hfeas_m'
      unfold objective at hobj_le
      simp only [zero_mul, sub_zero] at hobj_le
      nlinarith
    · linarith
  have hcl_b : ∀ lam : ℝ, 0 < lam → lam < lamBar P →
      (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0) ∧
      ∀ x ∈ Set.Ioo 0 (1 - lam),
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = 0 →
        IsOptimal P lam (constM (mHat P x)) ∧ noPurchase P (constM (mHat P x)) = x := by
    intro lam hlam_pos hlam
    have hprinted_eq_foc : ∀ x ∈ Set.Ioo 0 (1 - lam),
        mHat P x - 1 / (P.b * x) + mHat P x / (2 * ((1 - x) / lam - 1)) = foc P lam x := by
      intro x hx
      unfold foc
      congr 1
      have hlam_ne : lam ≠ 0 := hlam_pos.ne'
      have hu_ne : 1 - x - lam ≠ 0 := by linarith [hx.2]
      have hden_eq : 2 * ((1 - x) / lam - 1) = 2 * (1 - x - lam) / lam := by
        field_simp [hlam_ne]
      rw [hden_eq]
      field_simp [hlam_ne, hu_ne]
    obtain ⟨_, hexu, _⟩ := eq_13_unique_root P lam hlam_pos.le hlam
    refine ⟨?_, fun x hx hroot => ?_⟩
    · obtain ⟨x_star, ⟨hx_mem, hx_foc⟩, hx_uniq⟩ := hexu
      refine ⟨x_star, ⟨hx_mem, by rwa [hprinted_eq_foc x_star hx_mem]⟩, ?_⟩
      rintro y ⟨hy_mem, hy_pr⟩
      rw [hprinted_eq_foc y hy_mem] at hy_pr
      exact hx_uniq y ⟨hy_mem, hy_pr⟩
    · rw [hprinted_eq_foc x hx] at hroot
      obtain ⟨_, hq0_x, his_opt_x, _⟩ := hopt_low lam hlam_pos.le hlam x hx hroot
      exact ⟨his_opt_x, hq0_x⟩
  have hcl_c : ∀ lam : ℝ, lamBar P ≤ lam → lam < 1 → IsOptimal P lam (constM 0) :=
    fun lam hge hlt1 => (hopt_high lam hge hlt1).1
  have hcl_d : ∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ m m' : Fin n → ℝ,
      IsOptimal P lam m → IsOptimal P lam m' → m = m' := by
    intro lam hlam0 hlam1 m m' hm hm'
    by_cases hlt_bar : lam < lamBar P
    · obtain ⟨_, ⟨x_star, ⟨hx_mem, hx_foc⟩, _⟩, _⟩ := eq_13_unique_root P lam hlam0 hlt_bar
      obtain ⟨_, _, his_opt_x, hstrict_x⟩ := hopt_low lam hlam0 hlt_bar x_star hx_mem hx_foc
      have hm_eq : m = constM (mHat P x_star) := by
        by_contra hne
        exact (hstrict_x m hm.1 hne).not_ge (hm.2 _ his_opt_x.1)
      have hm'_eq : m' = constM (mHat P x_star) := by
        by_contra hne
        exact (hstrict_x m' hm'.1 hne).not_ge (hm'.2 _ his_opt_x.1)
      rw [hm_eq, hm'_eq]
    · obtain ⟨his_opt0, hstrict0⟩ := hopt_high lam (not_lt.mp hlt_bar) hlam1
      have hobj0 : objective P lam (constM 0) = 0 := by
        unfold objective profit spread constM
        simp
      have hm_eq : m = constM 0 := by
        by_contra hne
        have hlt := hstrict0 m hm.1 hne
        have hge := hm.2 (constM 0) his_opt0.1
        linarith
      have hm'_eq : m' = constM 0 := by
        by_contra hne
        have hlt := hstrict0 m' hm'.1 hne
        have hge := hm'.2 (constM 0) his_opt0.1
        linarith
      rw [hm_eq, hm'_eq]
  have hcl_e : ∀ lam : ℝ, 0 ≤ lam → lam < lamBar P → ∀ m : Fin n → ℝ, IsOptimal P lam m →
      ∃ t : ℝ, 0 < t ∧ m = constM t := by
    intro lam hlam0 hlam m hm
    obtain ⟨_, ⟨x_star, ⟨hx_mem, hx_foc⟩, _⟩, _⟩ := eq_13_unique_root P lam hlam0 hlam
    obtain ⟨ht_pos, _, his_opt_x, _⟩ := hopt_low lam hlam0 hlam x_star hx_mem hx_foc
    have hm_eq := hcl_d lam hlam0 (hlam.trans hlamBar_lt1) m (constM (mHat P x_star)) hm his_opt_x
    exact ⟨mHat P x_star, ht_pos, hm_eq⟩
  refine ⟨hcl_a, hcl_b, hcl_c, hcl_d, hcl_e, ?_⟩
  intro lam lam' t t' hlam0 hlam_lt hlam'_bar hopt_t hopt_t'
  have hlam_bar : lam < lamBar P := hlam_lt.trans hlam'_bar
  have hlam'0 : 0 ≤ lam' := hlam0.trans hlam_lt.le
  obtain ⟨hfoc_mono, ⟨x, ⟨hx_mem, hx_foc⟩, _⟩, _⟩ := eq_13_unique_root P lam hlam0 hlam_bar
  obtain ⟨_, ⟨x', ⟨hx'_mem, hx'_foc⟩, _⟩, _⟩ := eq_13_unique_root P lam' hlam'0 hlam'_bar
  obtain ⟨ht_pos_x, hq0_x, his_opt_x, _⟩ := hopt_low lam hlam0 hlam_bar x hx_mem hx_foc
  obtain ⟨ht'_pos_x, hq0_x', his_opt_x', _⟩ := hopt_low lam' hlam'0 hlam'_bar x' hx'_mem hx'_foc
  have ht_eq : t = mHat P x := by
    have h := hcl_d lam hlam0 (hlam_bar.trans hlamBar_lt1) (constM t) (constM (mHat P x))
      hopt_t his_opt_x
    exact congrFun h (0 : Fin n)
  have ht'_eq : t' = mHat P x' := by
    have h := hcl_d lam' hlam'0 (hlam'_bar.trans hlamBar_lt1) (constM t') (constM (mHat P x'))
      hopt_t' his_opt_x'
    exact congrFun h (0 : Fin n)
  have hx'_in_lam : x' ∈ Set.Ioo 0 (1 - lam) := ⟨hx'_mem.1, by linarith [hx'_mem.2]⟩
  have hfoc_lt : foc P lam x' < foc P lam x := by
    rw [hx_foc, ← hx'_foc]
    unfold foc
    have hu_pos : 0 < 1 - x' - lam := by linarith [hx'_mem.2]
    have hu'_pos : 0 < 1 - x' - lam' := by linarith [hx'_mem.2]
    have h1x'_pos : 0 < 1 - x' := by linarith [hx'_mem.2]
    have hdiff_neg : lam * mHat P x' / (2 * (1 - x' - lam)) <
        lam' * mHat P x' / (2 * (1 - x' - lam')) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      have hid : lam' * mHat P x' * (2 * (1 - x' - lam)) -
          lam * mHat P x' * (2 * (1 - x' - lam')) =
          2 * (lam' - lam) * mHat P x' * (1 - x') := by ring
      have hpos : 0 < 2 * (lam' - lam) * mHat P x' * (1 - x') :=
        mul_pos (mul_pos (mul_pos zero_lt_two (sub_pos.mpr hlam_lt)) ht'_pos_x) h1x'_pos
      linarith
    linarith
  have hx'_lt_x : x' < x := by
    by_contra hle
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
    · have := hfoc_mono hx_mem hx'_in_lam hlt
      linarith
    · rw [heq] at hfoc_lt
      exact lt_irrefl _ hfoc_lt
  have ht'_lt_t : t' < t := by
    rw [ht_eq, ht'_eq]
    exact hmHat_mono ⟨hx'_mem.1, by linarith [hx'_mem.2]⟩ ⟨hx_mem.1, by linarith [hx_mem.2]⟩
      hx'_lt_x
  rw [ht_eq, ht'_eq, hq0_x, hq0_x']
  exact ⟨by rwa [← ht_eq, ← ht'_eq], hx'_lt_x⟩
