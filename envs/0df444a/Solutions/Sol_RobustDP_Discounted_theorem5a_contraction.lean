-- Prove2me | solution 1 for RobustDP.Discounted.theorem5a_contraction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:04:10.75785+00:00
-- url     : https://prove2.me/submissions/ef79108a-b458-482a-9af6-b8bab19ad359

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

set_option autoImplicit false
open RobustDP.Discounted

namespace MMA

section expect

variable {X : Type*}

lemma summable_toReal (p : PMF X) : Summable fun x => (p x).toReal :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

lemma tsum_toReal (p : PMF X) : ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe]; simp

lemma summable_expect (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    Summable fun x => (p x).toReal * f x := by
  refine Summable.of_norm_bounded ((summable_toReal p).mul_right C) (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg

lemma expect_const (p : PMF X) (c : ℝ) :
    RobustDP.FiniteHorizon.expect p (fun _ => c) = c := by
  unfold RobustDP.FiniteHorizon.expect
  rw [tsum_mul_right, tsum_toReal, one_mul]

lemma expect_le_add (p : PMF X) (f g : X → ℝ) (C D : ℝ) (hf : ∀ x, |f x| ≤ C)
    (hg : ∀ x, |g x| ≤ D) (c : ℝ) (h : ∀ x, f x ≤ g x + c) :
    RobustDP.FiniteHorizon.expect p f ≤ RobustDP.FiniteHorizon.expect p g + c := by
  unfold RobustDP.FiniteHorizon.expect
  have h1 := summable_expect p f C hf
  have h2 := summable_expect p g D hg
  have h3 : Summable fun x => (p x).toReal * c := (summable_toReal p).mul_right c
  calc ∑' x, (p x).toReal * f x ≤ ∑' x, ((p x).toReal * g x + (p x).toReal * c) := by
        refine h1.tsum_le_tsum (fun x => ?_) (h2.add h3)
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg
    _ = _ := by rw [h2.tsum_add h3, tsum_mul_right, tsum_toReal, one_mul]

lemma abs_expect_le (p : PMF X) (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    |RobustDP.FiniteHorizon.expect p f| ≤ C := by
  obtain ⟨x0, _⟩ := p.support_nonempty
  have h0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hf x0)
  rw [abs_le]
  constructor
  · have := expect_le_add p (fun _ => -C) f C C (fun _ => by rw [abs_neg]; exact (abs_of_nonneg h0).le) hf 0
      (fun x => by have := (abs_le.mp (hf x)).1; linarith)
    rw [expect_const] at this; linarith
  · have := expect_le_add p f (fun _ => C) C C hf (fun _ => (abs_of_nonneg h0).le) 0
      (fun x => by have := (abs_le.mp (hf x)).2; linarith)
    rw [expect_const] at this; linarith

end expect

section Qlemmas

variable {S A : Type*} [Countable S] [Countable A]

lemma Q_abs_le (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (U : S → ℝ) (C : ℝ) (hU : ∀ s, |U s| ≤ C) (s : S) (a : A) (ha : a ∈ M.Aset s) :
    |Q M U s a| ≤ R + M.lam * C := by
  have hb : ∀ s', |M.r s a s' + M.lam * U s'| ≤ R + M.lam * C := by
    intro s'
    calc |M.r s a s' + M.lam * U s'| ≤ |M.r s a s'| + |M.lam * U s'| := abs_add_le _ _
      _ ≤ R + M.lam * C := by
        rw [abs_mul, abs_of_pos M.lam_pos]
        exact add_le_add (hR s a ha s') (mul_le_mul_of_nonneg_left (hU s') M.lam_pos.le)
  haveI : Nonempty (M.P s a) := (M.P_nonempty s a ha).to_subtype
  have hall : ∀ p : M.P s a, |RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')|
      ≤ R + M.lam * C := fun p => abs_expect_le p.1 _ _ hb
  have hbdd : BddBelow (Set.range fun p : M.P s a =>
      RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')) :=
    ⟨-(R + M.lam * C), by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (hall p)).1⟩
  rw [abs_le]
  constructor
  · exact le_ciInf (fun p => (abs_le.mp (hall p)).1)
  · obtain ⟨p⟩ := ‹Nonempty (M.P s a)›
    exact (ciInf_le hbdd p).trans (abs_le.mp (hall p)).2

lemma Q_le_Q_add (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (U W : S → ℝ) (C : ℝ) (hU : ∀ s, |U s| ≤ C) (hW : ∀ s, |W s| ≤ C) (c : ℝ)
    (h : ∀ s, U s ≤ W s + c) (s : S) (a : A) (ha : a ∈ M.Aset s) :
    Q M U s a ≤ Q M W s a + M.lam * c := by
  have hb : ∀ (V : S → ℝ), (∀ s, |V s| ≤ C) → ∀ s', |M.r s a s' + M.lam * V s'| ≤ R + M.lam * C := by
    intro V hV s'
    calc |M.r s a s' + M.lam * V s'| ≤ |M.r s a s'| + |M.lam * V s'| := abs_add_le _ _
      _ ≤ R + M.lam * C := by
        rw [abs_mul, abs_of_pos M.lam_pos]
        exact add_le_add (hR s a ha s') (mul_le_mul_of_nonneg_left (hV s') M.lam_pos.le)
  haveI : Nonempty (M.P s a) := (M.P_nonempty s a ha).to_subtype
  have hbddU : BddBelow (Set.range fun p : M.P s a =>
      RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s')) :=
    ⟨-(R + M.lam * C), by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (abs_expect_le p.1 _ _ (hb U hU))).1⟩
  have : Q M U s a - M.lam * c ≤ Q M W s a := by
    refine le_ciInf (fun p => ?_)
    have h1 : RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s') ≤
        RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * W s') + M.lam * c := by
      refine expect_le_add p.1 _ _ _ _ (hb U hU) (hb W hW) _ (fun s' => ?_)
      have := mul_le_mul_of_nonneg_left (h s') M.lam_pos.le
      rw [mul_add] at this
      linarith
    have h2 : Q M U s a ≤ RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * U s') :=
      ciInf_le hbddU p
    linarith
  linarith

end Qlemmas

section Llemmas

variable {S A : Type*} [Countable S] [Countable A]

lemma L_abs_le (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (D : Set (DecisionRule M)) (hD : D.Nonempty) (U : S → ℝ) (C : ℝ) (hU : ∀ s, |U s| ≤ C) (s : S) :
    |L M D U s| ≤ R + M.lam * C := by
  haveI : Nonempty D := hD.to_subtype
  have hb : ∀ d : D, |Q M U s (d.1.1 s)| ≤ R + M.lam * C :=
    fun d => Q_abs_le M R hR U C hU s _ (d.1.2 s)
  have hbdd : BddAbove (Set.range fun d : D => Q M U s (d.1.1 s)) :=
    ⟨R + M.lam * C, by rintro _ ⟨d, rfl⟩; exact (abs_le.mp (hb d)).2⟩
  rw [abs_le]
  constructor
  · obtain ⟨d⟩ := ‹Nonempty D›
    exact (abs_le.mp (hb d)).1.trans (le_ciSup hbdd d)
  · exact ciSup_le (fun d => (abs_le.mp (hb d)).2)

lemma L_le_L_add (M : Model S A) (R : ℝ) (hR : ∀ s, ∀ a ∈ M.Aset s, ∀ s', |M.r s a s'| ≤ R)
    (D : Set (DecisionRule M)) (hD : D.Nonempty) (U W : S → ℝ) (C : ℝ)
    (hU : ∀ s, |U s| ≤ C) (hW : ∀ s, |W s| ≤ C) (c : ℝ) (h : ∀ s, U s ≤ W s + c) (s : S) :
    L M D U s ≤ L M D W s + M.lam * c := by
  haveI : Nonempty D := hD.to_subtype
  have hbdd : BddAbove (Set.range fun d : D => Q M W s (d.1.1 s)) :=
    ⟨R + M.lam * C, by
      rintro _ ⟨d, rfl⟩
      exact (abs_le.mp (Q_abs_le M R hR W C hW s _ (d.1.2 s))).2⟩
  refine ciSup_le (fun d => ?_)
  have := Q_le_Q_add M R hR U W C hU hW c h s _ (d.1.2 s)
  have h2 : Q M W s (d.1.1 s) ≤ L M D W s := le_ciSup hbdd d
  linarith

end Llemmas

theorem contraction5a {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (D : Set (DecisionRule M)) (hD : D.Nonempty) (U W : S → ℝ) (hU : IsBounded U)
    (hW : IsBounded W) :
    IsBounded (L M D U) ∧
      supNorm (fun s => L M D U s - L M D W s) ≤ M.lam * supNorm (fun s => U s - W s) := by
  obtain ⟨R, hR⟩ := M.bounded
  obtain ⟨CU, hCU⟩ := hU
  obtain ⟨CW, hCW⟩ := hW
  refine ⟨⟨R + M.lam * CU, fun s => L_abs_le M R hR D hD U CU hCU s⟩, ?_⟩
  set c := supNorm (fun s => U s - W s) with hc
  have hbdd : BddAbove (Set.range fun s => |U s - W s|) :=
    ⟨CU + CW, by
      rintro _ ⟨s, rfl⟩
      calc |U s - W s| ≤ |U s| + |W s| := abs_sub _ _
        _ ≤ CU + CW := add_le_add (hCU s) (hCW s)⟩
  have hc0 : 0 ≤ c := Real.iSup_nonneg (fun s => abs_nonneg _)
  have hle : ∀ s, |U s - W s| ≤ c := fun s => le_ciSup hbdd s
  have hle1 : ∀ s, U s ≤ W s + c := fun s => by have := (abs_le.mp (hle s)).2; linarith
  have hle2 : ∀ s, W s ≤ U s + c := fun s => by have := (abs_le.mp (hle s)).1; linarith
  refine Real.iSup_le (fun s => ?_) (mul_nonneg M.lam_pos.le hc0)
  rw [abs_le]
  have h1 := L_le_L_add M R hR D hD U W (max CU CW)
    (fun s => (hCU s).trans (le_max_left _ _)) (fun s => (hCW s).trans (le_max_right _ _)) c hle1 s
  have h2 := L_le_L_add M R hR D hD W U (max CU CW)
    (fun s => (hCW s).trans (le_max_right _ _)) (fun s => (hCU s).trans (le_max_left _ _)) c hle2 s
  constructor <;> linarith

end MMA

theorem solution {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (D : Set (DecisionRule M)) (hD : D.Nonempty) (U W : S → ℝ) (hU : IsBounded U)
    (hW : IsBounded W) :
    IsBounded (L M D U) ∧
      supNorm (fun s => L M D U s - L M D W s) ≤ M.lam * supNorm (fun s => U s - W s) :=
  MMA.contraction5a M D hD U W hU hW
