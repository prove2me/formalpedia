-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.c_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:43:38.255556+00:00
-- url     : https://prove2.me/submissions/55c42a06-1bb5-42e0-acfa-49d5620999d6

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory
open PersonalizedRM.RevenueGap

lemma PRM_aux_unimodal_left (a t c : ℝ) (ha : 0 < a) (hat : a ≤ t) (hc : 0 < c)
    (h : a * t ≤ c ^ 2) : a / (c + a) ^ 2 ≤ t / (c + t) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (pow_pos (by linarith) 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr h)]

lemma PRM_aux_unimodal_right (b t c : ℝ) (ht : 0 < t) (htb : t ≤ b) (hc : 0 < c)
    (h : c ^ 2 ≤ b * t) : b / (c + b) ^ 2 ≤ t / (c + t) ^ 2 := by
  have hb : 0 < b := lt_of_lt_of_le ht htb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr h)]

lemma PRM_aux_mono_c (a c c0 : ℝ) (ha : 0 < a) (hc : 0 < c) (hcc : c ≤ c0) :
    a / (c0 + a) ^ 2 ≤ a / (c + a) ^ 2 := by
  apply div_le_div_of_nonneg_left ha.le (by positivity)
  have : c + a ≤ c0 + a := by linarith
  exact pow_le_pow_left₀ (by positivity) this 2

lemma PRM_aux_alg (a b t c c0 : ℝ) (ha : 0 < a) (hab : a * b = 1) (hat : a ≤ t) (htb : t ≤ b)
    (hc : 1 ≤ c) (hcc : c ≤ c0) : a / (c0 + a) ^ 2 ≤ t / (c + t) ^ 2 := by
  have hb : 0 < b := by nlinarith
  have hab' : a ≤ b := hat.trans htb
  have hc0 : 1 ≤ c0 := hc.trans hcc
  by_cases h : a * t ≤ c ^ 2
  · exact (PRM_aux_mono_c a c c0 ha (by linarith) hcc).trans
      (PRM_aux_unimodal_left a t c ha hat (by linarith) h)
  · push_neg at h
    have hbt : c ^ 2 ≤ b * t := by nlinarith
    have hiv : a / (c0 + a) ^ 2 ≤ b / (c0 + b) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ (b - a) * (c0 ^ 2 - a * b) := mul_nonneg (by linarith) (by nlinarith)
      nlinarith
    exact hiv.trans ((PRM_aux_mono_c b c c0 hb (by linarith) hcc).trans
      (PRM_aux_unimodal_right b t c (by linarith) htb (by linarith) hbt))

theorem solution {J d : ℕ} (R : ℝ) (θ : Param J d) (hθ : l1norm θ ≤ R)
    (z : Fin d → ℝ) (hz : ∀ k, |z k| ≤ 1) (S : Finset (Fin J)) (p : Fin J → ℝ)
    (hp : p ∈ priceBox J 0) (j : Fin J) (hj : j ∈ S) :
    cMin J R ≤ choiceProb θ z S p (some j) * choiceProb θ z S p none := by
  simp only [priceBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies] at hp
  have hx : ∀ l k, |featPrice z (p l) k| ≤ 1 := by
    intro l k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [featPrice, Fin.snoc_last]; rw [abs_le]; constructor <;> linarith [(hp l).1, (hp l).2]
    · simp only [featPrice, Fin.snoc_castSucc]; exact hz i
  -- every utility is bounded by R in absolute value
  have hV : ∀ l, |utility θ z p l| ≤ R := by
    intro l
    calc |utility θ z p l| ≤ ∑ k, |θ (l, k)| := by
          unfold utility
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hx l k)
      _ ≤ ∑ l', ∑ k, |θ (l', k)| :=
          Finset.single_le_sum (f := fun l' => ∑ k, |θ (l', k)|)
            (fun l' _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ l)
      _ = l1norm θ := by unfold l1norm; exact (Fintype.sum_prod_type (fun jk => |θ jk|)).symm
      _ ≤ R := hθ
  set a := Real.exp (-R) with ha
  set b := Real.exp R with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hab : a * b = 1 := by rw [ha, hb, ← Real.exp_add]; simp
  set t := Real.exp (utility θ z p j) with ht
  have hat : a ≤ t := Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hV j)).1])
  have htb : t ≤ b := Real.exp_le_exp.mpr (abs_le.mp (hV j)).2
  set X := ∑ l ∈ S.erase j, Real.exp (utility θ z p l) with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun l _ => (Real.exp_pos _).le
  have hJ1 : (1 : ℝ) ≤ J := by
    have : 0 < J := Fin.pos j
    exact_mod_cast this
  have hXle : X ≤ ((J : ℝ) - 1) * b := by
    calc X ≤ ∑ l ∈ S.erase j, b :=
          Finset.sum_le_sum fun l _ => Real.exp_le_exp.mpr (abs_le.mp (hV l)).2
      _ = ((S.erase j).card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((J : ℝ) - 1) * b := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos R).le
          rw [Finset.card_erase_of_mem hj]
          have h1 := Finset.card_le_univ S
          have h2 : 1 ≤ S.card := Finset.card_pos.mpr ⟨j, hj⟩
          simp only [Fintype.card_fin] at h1
          rw [Nat.cast_sub h2]; push_cast; linarith [(by exact_mod_cast h1 : (S.card : ℝ) ≤ J)]
  have hsum : ∑ l ∈ S, Real.exp (utility θ z p l) = t + X := by
    rw [hX, ht]; exact (Finset.add_sum_erase S _ hj).symm
  have hprod : choiceProb θ z S p (some j) * choiceProb θ z S p none = t / ((1 + X) + t) ^ 2 := by
    simp only [choiceProb, hj, if_true, hsum, ← ht]
    rw [show (1 + X) + t = 1 + (t + X) by ring, div_mul_div_comm, mul_one, sq]
  rw [hprod]
  have hc := PRM_aux_alg a b t (1 + X) (1 + ((J : ℝ) - 1) * b) ha0 hab hat htb (by linarith)
    (by linarith)
  unfold cMin
  rw [← ha, ← hb]
  calc a / (1 + a + ((J : ℝ) - 1) * b) ^ 2 = a / (1 + ((J : ℝ) - 1) * b + a) ^ 2 := by ring_nf
    _ ≤ _ := hc
