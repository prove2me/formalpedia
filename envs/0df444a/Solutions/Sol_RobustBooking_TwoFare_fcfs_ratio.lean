-- Prove2me | solution 1 for RobustBooking.TwoFare.fcfs_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:26:38.349991+00:00
-- url     : https://prove2.me/submissions/2201c883-6772-4db0-873d-ef929675e6d0

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace Aux_RB_fcfs

open RobustBooking.TwoFare

lemma rev_nonneg (f₁ f₂ n : ℝ) (h1 : 0 ≤ f₁) (h2 : 0 ≤ f₂) (A : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      0 ≤ (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (runFrom n A hist used I)).sum := by
  intro I
  induction I with
  | nil => intro hist used; simp [runFrom]
  | cons q rest ih =>
    intro hist used
    simp only [runFrom, List.zipWith_cons_cons, List.sum_cons]
    have hf : 0 ≤ fare f₁ f₂ q.cls := by cases q.cls <;> simp [fare, h1, h2]
    exact add_nonneg (mul_nonneg hf (le_max_left _ _)) (ih _ _)

lemma opt1 (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    optRevenue f₁ f₂ n (instI1 n hn) = f₁ * n := by
  unfold optRevenue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨(![0, n] : Fin 2 → ℝ), ⟨fun i => ?_, ?_⟩, ?_⟩
    · change Fin 2 at i
      fin_cases i
      · exact ⟨le_rfl, hn.le⟩
      · exact ⟨hn.le, le_rfl⟩
    · show ∑ i : Fin 2, (![0, n] : Fin 2 → ℝ) i ≤ n
      simp [Fin.sum_univ_two]
    · show f₁ * n = ∑ i : Fin 2, fare f₁ f₂ ((instI1 n hn).get i).cls * (![0, n] : Fin 2 → ℝ) i
      simp [Fin.sum_univ_two, instI1, fare]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i, fare f₁ f₂ ((instI1 n hn).get i).cls * x i ≤ ∑ i, f₁ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          apply mul_le_mul_of_nonneg_right _ (hx1 i).1
          cases ((instI1 n hn).get i).cls <;> (simp [fare]; try linarith)
      _ = f₁ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₁ * n := mul_le_mul_of_nonneg_left hx2 (by linarith)

lemma min_add_min_sub (q S C : ℝ) (hS : 0 ≤ S) :
    min q C + min S (C - min q C) = min (q + S) C := by
  rcases le_total q C with h1 | h1 <;> rcases le_total (q + S) C with h2 | h2
  · have h3 : S ≤ C - q := by linarith
    rw [min_eq_left h1, min_eq_left h3, min_eq_left h2]
  · have h3 : C - q ≤ S := by linarith
    rw [min_eq_left h1, min_eq_right h3, min_eq_right h2]
    ring
  · rw [min_eq_right h1, sub_self, min_eq_left h2]
    have h3 : S ≤ 0 := by linarith
    rw [min_eq_left h3]
    linarith
  · rw [min_eq_right h1, sub_self, min_eq_right h2, min_eq_right hS, add_zero]

lemma sum_qty_nonneg : ∀ I : List Request, 0 ≤ (I.map Request.qty).sum
  | [] => by simp
  | q :: rest => by
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg q.qty_pos.le (sum_qty_nonneg rest)

lemma fcfs_runFrom_ge (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ), used ≤ n →
      f₂ * min (I.map Request.qty).sum (n - used) ≤
        (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (runFrom n fcfs hist used I)).sum
  | [], hist, used, hused => by
    simp only [runFrom, List.map_nil, List.sum_nil, List.zipWith_nil_left]
    have h0 : min 0 (n - used) = 0 := min_eq_left (by linarith)
    rw [h0, mul_zero]
  | q :: rest, hist, used, hused => by
    simp only [runFrom, fcfs, List.zipWith_cons_cons, List.sum_cons, List.map_cons]
    have hq0 : 0 ≤ q.qty := q.qty_pos.le
    have hnu : 0 ≤ n - used := by linarith
    have hmin_idem : min q.qty (min q.qty (n - used)) = min q.qty (n - used) :=
      min_eq_right (min_le_left _ _)
    have ha_nonneg : 0 ≤ min q.qty (n - used) := le_min hq0 hnu
    have ha_eq : max 0 (min q.qty (n - used)) = min q.qty (n - used) := max_eq_right ha_nonneg
    rw [hmin_idem, ha_eq]
    have hused' : used + min q.qty (n - used) ≤ n := by
      have : min q.qty (n - used) ≤ n - used := min_le_right _ _
      linarith
    have ih := fcfs_runFrom_ge f₁ f₂ n hf₂ hf₁₂ rest
      (hist ++ [(q, min q.qty (n - used))]) (used + min q.qty (n - used)) hused'
    have hsub : n - (used + min q.qty (n - used)) = (n - used) - min q.qty (n - used) := by ring
    rw [hsub] at ih
    have hfare : f₂ ≤ fare f₁ f₂ q.cls := by
      cases q.cls <;> simp [fare, hf₁₂.le]
    have hstep : f₂ * min q.qty (n - used) ≤ fare f₁ f₂ q.cls * min q.qty (n - used) :=
      mul_le_mul_of_nonneg_right hfare ha_nonneg
    have hmin_eq := min_add_min_sub q.qty (rest.map Request.qty).sum (n - used) (sum_qty_nonneg rest)
    calc f₂ * min (q.qty + (rest.map Request.qty).sum) (n - used)
        = f₂ * (min q.qty (n - used) + min (rest.map Request.qty).sum ((n - used) - min q.qty (n - used))) := by
          rw [hmin_eq]
      _ = f₂ * min q.qty (n - used) + f₂ * min (rest.map Request.qty).sum ((n - used) - min q.qty (n - used)) := by
          ring
      _ ≤ fare f₁ f₂ q.cls * min q.qty (n - used) +
            (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) rest
              (runFrom n fcfs (hist ++ [(q, min q.qty (n - used))]) (used + min q.qty (n - used)) rest)).sum :=
          add_le_add hstep ih

lemma sum_fin_get_qty (I : List Request) :
    (∑ i : Fin I.length, (I.get i).qty) = (I.map Request.qty).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_get (by simp) (by simp)

lemma optRevenue_le (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) (I : List Request) :
    optRevenue f₁ f₂ n I ≤ f₁ * min (I.map Request.qty).sum n := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  unfold optRevenue
  apply csSup_le
  · refine ⟨0, 0, ⟨⟨fun i => ⟨le_rfl, (I.get i).qty_pos.le⟩, ?_⟩, ?_⟩⟩
    · simp [hn.le]
    · simp
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hsum_q : ∑ i, x i ≤ (I.map Request.qty).sum := by
      rw [← sum_fin_get_qty I]
      exact Finset.sum_le_sum fun i _ => (hx1 i).2
    have hsum_min : ∑ i, x i ≤ min (I.map Request.qty).sum n := le_min hsum_q hx2
    calc ∑ i, fare f₁ f₂ (I.get i).cls * x i ≤ ∑ i, f₁ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          apply mul_le_mul_of_nonneg_right _ (hx1 i).1
          cases (I.get i).cls <;> simp [fare, hf₁₂.le]
      _ = f₁ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₁ * min (I.map Request.qty).sum n := mul_le_mul_of_nonneg_left hsum_min hf₁.le

lemma rev_instI1 (f₁ f₂ n : ℝ) (hn : 0 < n) :
    revenue f₁ f₂ n fcfs (instI1 n hn) = f₂ * n := by
  simp only [revenue, accepted, runFrom, instI1, fcfs, fare, min_self, sub_zero, zero_add,
    max_eq_right hn.le, sub_self, min_eq_right hn.le, max_self, mul_zero,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil, add_zero]

end Aux_RB_fcfs

open RobustBooking.TwoFare Aux_RB_fcfs in
theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n fcfs = f₂ / f₁ := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  have hfn : 0 < f₁ * n := mul_pos hf₁ hn
  apply le_antisymm
  · have hbdd : BddBelow {c : ℝ | ∃ I : List Request, 0 < optRevenue f₁ f₂ n I ∧
        c = revenue f₁ f₂ n fcfs I / optRevenue f₁ f₂ n I} := by
      refine ⟨0, ?_⟩
      rintro c ⟨I, hI, rfl⟩
      exact div_nonneg (rev_nonneg f₁ f₂ n hf₁.le hf₂.le fcfs I [] 0) hI.le
    unfold competitiveRatio
    have m1 := csInf_le hbdd ⟨instI1 n hn, by rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn]; exact hfn, rfl⟩
    rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn, rev_instI1 f₁ f₂ n hn, mul_div_mul_right _ _ hn.ne'] at m1
    exact m1
  · unfold competitiveRatio
    apply le_csInf
    · refine ⟨revenue f₁ f₂ n fcfs (instI1 n hn) / optRevenue f₁ f₂ n (instI1 n hn),
        instI1 n hn, by rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn]; exact hfn, rfl⟩
    · rintro c ⟨I, hI, rfl⟩
      rw [le_div_iff₀ hI]
      have hopt := optRevenue_le f₁ f₂ n hf₂ hf₁₂ hn I
      have hrev := fcfs_runFrom_ge f₁ f₂ n hf₂ hf₁₂ I [] 0 hn.le
      rw [sub_zero] at hrev
      calc f₂ / f₁ * optRevenue f₁ f₂ n I
          ≤ f₂ / f₁ * (f₁ * min (I.map Request.qty).sum n) :=
            mul_le_mul_of_nonneg_left hopt (div_nonneg hf₂.le hf₁.le)
        _ = f₂ * min (I.map Request.qty).sum n := by
            field_simp
        _ ≤ revenue f₁ f₂ n fcfs I := hrev
