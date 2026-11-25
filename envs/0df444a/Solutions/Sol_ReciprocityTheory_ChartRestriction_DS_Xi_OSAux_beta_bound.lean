-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.beta_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:13.175892+00:00
-- url     : https://prove2.me/submissions/6be95105-2509-4618-9923-2e08511902df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rhoSq_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma one_le_Lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have h : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith
private lemma Lsq_last_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    Lsq x (Fin.last p) ≤ rhoSq x l := by
  unfold rhoSq
  have h1 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith
private lemma qB_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ qB x l := by
  have h1 := one_le_Lsq x l
  have h2 := one_le_Lsq x (Fin.last p)
  have h3 := Lsq_last_le_rhoSq x l
  have h4 : 0 ≤ Lsq x l * rhoSq x l := mul_nonneg (by linarith) (by linarith)
  unfold qB
  exact add_nonneg h4 (sq_nonneg _)
private lemma norm_bco_sq_eq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    ‖bco x l‖ ^ 2 = (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2 + (x.2.2.2 - (bS x l).im) ^ 2 := by
  have hb : bco x l = (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I - bS x l := rfl
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hb]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring
private lemma de_rpow {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) (r : ℝ) :
    de x l ^ r = (qB x l + (x.2.2.2 - (bS x l).im) ^ 2) ^ (r / 2) := by
  have h0 : 0 ≤ qB x l + (x.2.2.2 - (bS x l).im) ^ 2 := add_nonneg (qB_nonneg x l) (sq_nonneg _)
  have he : de x l = Real.sqrt (qB x l + (x.2.2.2 - (bS x l).im) ^ 2) := by
    unfold de qB
    rw [norm_bco_sq_eq]
    congr 1
    ring
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  congr 1
  ring
private lemma Lsq_zero' {p m : ℕ} (x : Xp p m) : Lsq x 0 = 1 := by
  unfold Lsq
  simp
private lemma de_sq' {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  have h1 := one_le_Lsq x l
  have h2 := one_le_Lsq x (Fin.last p)
  have h3 := Lsq_last_le_rhoSq x l
  unfold de
  rw [Real.sq_sqrt]
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
private lemma rhoSq_one_le {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 1 ≤ rhoSq x 0 := by
  unfold rhoSq
  have h : ∑ j : Fin (p + 1), (if (1 : Fin (p + 1 + 1)).val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin (p + 1), (if (0 : Fin (p + 1 + 1)).val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> first | exact le_rfl | positivity | simp_all
  linarith
private lemma bS_tailPt_zero_eq_one {p m : ℕ} (y : Yp p m) : bS (tailPt y) 0 = bS (tailPt y) 1 := by
  unfold bS tailPt
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
private lemma de_zero_bounds {p m : ℕ} (y : Yp p m) :
    de (tailPt y) 1 ^ 2 ≤ Lsq (tailPt y) 1 * de (tailPt y) 0 ^ 2 ∧
      |(tailPt y).2.2.2 - (bS (tailPt y) 1).im| ≤ de (tailPt y) 0 := by
  have hb0 := bS_tailPt_zero_eq_one y
  have hbc : bco (tailPt y) 0 = bco (tailPt y) 1 := by
    have h := hb0
    unfold bS at h
    unfold bco
    rw [h]
  have hL0 := Lsq_zero' (tailPt y)
  have hL1 := one_le_Lsq (tailPt y) 1
  have hr := rhoSq_one_le (tailPt y)
  have hr1 : Lsq (tailPt y) (Fin.last (p + 1)) ≤ rhoSq (tailPt y) 1 := Lsq_last_le_rhoSq _ _
  have hr2 := one_le_Lsq (tailPt y) (Fin.last (p + 1))
  constructor
  · rw [de_sq', de_sq', hL0, hbc]
    have h5 : Lsq (tailPt y) 1 * rhoSq (tailPt y) 1 ≤ Lsq (tailPt y) 1 * rhoSq (tailPt y) 0 :=
      mul_le_mul_of_nonneg_left hr (by linarith)
    have h6 := mul_le_mul_of_nonneg_right hL1 (sq_nonneg ‖bco (tailPt y) 1‖)
    nlinarith
  · have h0 : 0 ≤ Lsq (tailPt y) 0 * rhoSq (tailPt y) 0 := by
      rw [hL0, one_mul]; linarith
    unfold de
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    rw [norm_bco_sq_eq, hb0]
    nlinarith [sq_nonneg (-(∑ i, ‖(tailPt y).2.2.1 i‖ ^ 2) / 2 - (bS (tailPt y) 1).re)]
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ) {γ : ℝ} (he : ∀ l, 0 < e l)
    (he1 : ∀ l, e l ≤ 1) (hγ2 : γ < 2) (hα : 0 < γ / 2 - e 0) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ (a : Fin (p + 1) → ℂ) (a'' : Fin p → ℂ) (u : Fin m → ℂ),
      ∫⁻ β : ℝ, ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ (-1 + γ / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) ≤
        ENNReal.ofReal CS * ∫⁻ β : ℝ,
          ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt (a, a'', u, β)) i.succ ^
            (-(s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := by
  have hγ0 : 0 < γ := by linarith [he 0]
  obtain ⟨C, hC⟩ := hL (p + 1) (γ / 2 - e 0 + ∑ i : Fin (p + 1), s0N (p + 1) m i.succ) (γ / 2)
    (by linarith) (by linarith)
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun a a'' u => ?_⟩
  set L := Lsq (tailPt (a, a'', u, 0)) 1 with hLdef
  have hLX : ∀ β : ℝ, Lsq (tailPt (a, a'', u, β)) 1 = L := fun β => rfl
  have hL1 : 1 ≤ L := Lsq_ge_one _ 1
  have hL0 : 0 < L := by linarith
  set Al : Fin (p + 2) → ℝ := fun l => Real.sqrt (qB (tailPt (a, a'', u, 0)) l) with hAl
  set bl : Fin (p + 2) → ℝ := fun l => (bS (tailPt (a, a'', u, 0)) l).im with hbl
  set c := bl 1 with hc
  set t : Fin (p + 1) → ℝ := fun i => s0N (p + 1) m i.succ - e i.succ + if i = 0 then γ / 2 - e 0 else 0
    with ht
  have hfac : ∀ (β : ℝ) (l : Fin (p + 2)) (r : ℝ),
      de (tailPt (a, a'', u, β)) l ^ r = (Al l ^ 2 + (β - bl l) ^ 2) ^ (r / 2) := by
    intro β l r
    rw [de_rpow, hAl, hbl]
    simp only
    rw [Real.sq_sqrt (qB_nonneg _ _)]
    rfl
  have hG : ∀ β : ℝ, ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
      ∏ i : Fin (p + 1), ENNReal.ofReal
        (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) =
      slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    intro β
    have hd1 : 0 < de (tailPt (a, a'', u, β)) 1 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    unfold slowly
    simp only [Fin.prod_univ_succ]
    rw [← mul_assoc]
    congr 1
    · rw [Fin.succ_zero_eq_one', ← ENNReal.ofReal_mul (Real.rpow_nonneg hd1.le _),
        ← Real.rpow_add hd1, hfac]
      congr 2
      simp only [ht, Fin.succ_zero_eq_one', if_true]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [hfac]
      congr 2
      simp only [ht, Fin.succ_ne_zero, if_false]
      ring
  have hR : ∀ β : ℝ,
      ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt (a, a'', u, β)) i.succ ^
          (-(s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) =
      ENNReal.ofReal (L ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    intro β
    rw [← hG β, hLX, mul_assoc]
    simp only [sub_eq_add_neg]
  have hpt : ∀ β : ℝ, β ≠ c →
      ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ (-1 + γ / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) ≤
        ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (slowly t (fun i => Al i.succ) (fun i => bl i.succ) β * ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) := by
    intro β hβ
    rw [hLX, ← hG β]
    obtain ⟨hsq, habs⟩ := de_zero_bounds (a, a'', u, β)
    have habs' : |β - c| ≤ de (tailPt (a, a'', u, β)) 0 := habs
    have hsq' : de (tailPt (a, a'', u, β)) 1 ^ 2 ≤ L * de (tailPt (a, a'', u, β)) 0 ^ 2 := hsq
    have hd0 : 0 < de (tailPt (a, a'', u, β)) 0 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    have hd1 : 0 < de (tailPt (a, a'', u, β)) 1 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    have hcpos : 0 < |β - c| := abs_pos.mpr (sub_ne_zero.mpr hβ)
    have hreal : de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0)) ≤
        L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) *
          |β - c| ^ (-(γ / 2)) := by
      have hsplit : de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0)) =
          de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2 - e 0)) * de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2)) := by
        rw [← Real.rpow_add hd0]; congr 1; ring
      rw [hsplit]
      set s := Real.sqrt L with hs
      have hs0 : 0 < s := Real.sqrt_pos.mpr hL0
      have hs2 : s ^ 2 = L := Real.sq_sqrt hL0.le
      have hle : de (tailPt (a, a'', u, β)) 1 ≤ s * de (tailPt (a, a'', u, β)) 0 := by
        nlinarith [mul_pos hs0 hd0]
      have hdiv : de (tailPt (a, a'', u, β)) 1 / s ≤ de (tailPt (a, a'', u, β)) 0 := by
        rw [div_le_iff₀ hs0]; linarith
      have h1 : de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2 - e 0)) ≤
          L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) := by
        refine (Real.rpow_le_rpow_of_nonpos (div_pos hd1 hs0) hdiv (by linarith)).trans (le_of_eq ?_)
        rw [Real.div_rpow hd1.le hs0.le, Real.rpow_neg hs0.le, div_inv_eq_mul, hs,
          Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le, mul_comm]
        congr 2
        ring
      have h2 : de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2)) ≤ |β - c| ^ (-(γ / 2)) :=
        Real.rpow_le_rpow_of_nonpos hcpos habs' (by linarith)
      exact mul_le_mul h1 h2 (Real.rpow_nonneg hd0.le _)
        (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hd1.le _))
    calc _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2)) *
          ENNReal.ofReal (L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) *
            |β - c| ^ (-(γ / 2))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) :=
          by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hd1.le _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hL0.le _),
          ENNReal.ofReal_mul (Real.rpow_nonneg hL0.le _)]
        ring
  have hs0N : ∀ i : Fin (p + 2), 1 ≤ s0N (p + 1) m i := by
    intro i
    unfold s0N
    split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    simp only [ht]
    have h1 := hs0N i.succ
    have h2 := he1 i.succ
    split_ifs <;> linarith
  have hT : ∑ i, t i ≤ γ / 2 - e 0 + ∑ i : Fin (p + 1), s0N (p + 1) m i.succ := by
    simp only [ht, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have : ∑ i : Fin (p + 1), (s0N (p + 1) m i.succ - e i.succ) ≤
        ∑ i : Fin (p + 1), s0N (p + 1) m i.succ :=
      Finset.sum_le_sum (fun i _ => by linarith [he i.succ])
    linarith
  have hA : ∀ i : Fin (p + 1), L ≤ Al i.succ := by
    intro i
    have hmono : Lsq (tailPt (a, a'', u, 0)) 1 ≤ Lsq (tailPt (a, a'', u, 0)) i.succ := by
      apply Lsq_mono
      rw [← Fin.succ_zero_eq_one']
      exact Fin.succ_le_succ_iff.mpr (Fin.zero_le _)
    have hrho := rhoSq_ge (tailPt (a, a'', u, 0)) i.succ 1
    have hq : L ^ 2 ≤ qB (tailPt (a, a'', u, 0)) i.succ := by
      unfold qB
      have : L * L ≤ Lsq (tailPt (a, a'', u, 0)) i.succ * rhoSq (tailPt (a, a'', u, 0)) i.succ :=
        mul_le_mul hmono hrho hL0.le (by linarith)
      nlinarith [sq_nonneg (-(∑ i, ‖(tailPt (a, a'', u, 0)).2.2.1 i‖ ^ 2) / 2 -
        (bS (tailPt (a, a'', u, 0)) i.succ).re)]
    rw [← Real.sqrt_sq hL0.le]
    exact Real.sqrt_le_sqrt hq
  have hslow := hC t (fun i => Al i.succ) (fun i => bl i.succ - c) L hL0 ht0 hT hA
  have htr1 : ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
      ENNReal.ofReal (|β - c| ^ (-(γ / 2))) =
      ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β *
        ENNReal.ofReal (|β| ^ (-(γ / 2))) := by
    have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun β => slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
        ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) c
    rw [← h]
    refine lintegral_congr (fun β => ?_)
    simp only [add_sub_cancel_right]
    congr 1
    unfold slowly
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show β + c - bl i.succ = β - (bl i.succ - c) by ring]
  have htr2 : ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β =
      ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun β => slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) c
    rw [← h]
    refine lintegral_congr (fun β => ?_)
    unfold slowly
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show β + c - bl i.succ = β - (bl i.succ - c) by ring]
  have hK0 : 0 ≤ L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hid : L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2) * (max C 1 * L ^ (-(γ / 2))) =
      max C 1 * L ^ ((-2 + (γ / 2 - e 0)) / 2) := by
    rw [mul_comm (max C 1), ← mul_assoc, ← Real.rpow_add hL0, ← Real.rpow_add hL0, mul_comm]
    congr 2
    ring
  have hle : ENNReal.ofReal (C * L ^ (-(γ / 2))) ≤ ENNReal.ofReal (max C 1 * L ^ (-(γ / 2))) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _))
  calc _ ≤ ∫⁻ β : ℝ, ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
            ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [Measure.ae_ne volume c] with β hβ
        exact hpt β hβ
    _ = ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β *
            ENNReal.ofReal (|β| ^ (-(γ / 2))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htr1]
    _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (ENNReal.ofReal (C * L ^ (-(γ / 2))) *
            ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        rw [← htr2]
        exact mul_le_mul_of_nonneg_left hslow zero_le
    _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (ENNReal.ofReal (max C 1 * L ^ (-(γ / 2))) *
            ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        gcongr
    _ = ENNReal.ofReal (max C 1) * (ENNReal.ofReal (L ^ ((-2 + (γ / 2 - e 0)) / 2)) *
          ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK0, hid,
          ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right _ _)), mul_assoc]
    _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr (fun β => ?_)
        exact (hR β).symm
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
