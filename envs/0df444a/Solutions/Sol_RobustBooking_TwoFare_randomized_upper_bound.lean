-- Prove2me | solution 1 for RobustBooking.TwoFare.randomized_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:22:20.363237+00:00
-- url     : https://prove2.me/submissions/5a787dbf-5956-45ba-a701-1077850ad703

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

open MeasureTheory

namespace Aux_RB_rub

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

lemma opt2 (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hn : 0 < n) :
    optRevenue f₁ f₂ n (instI2 n hn) = f₂ * n := by
  unfold optRevenue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => n, ⟨fun i => ⟨hn.le, ?_⟩, ?_⟩, ?_⟩
    · have : i = (⟨0, by simp [instI2]⟩ : Fin (instI2 n hn).length) := Fin.ext (by
        have := i.isLt; simp [instI2] at this; omega)
      subst this; exact le_rfl
    · show ∑ _i : Fin 1, n ≤ n
      simp
    · show f₂ * n = ∑ i : Fin 1, fare f₁ f₂ ((instI2 n hn).get i).cls * n
      simp [instI2, fare]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i, fare f₁ f₂ ((instI2 n hn).get i).cls * x i ≤ ∑ i, f₂ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : i = (⟨0, by simp [instI2]⟩ : Fin (instI2 n hn).length) := Fin.ext (by
            have := i.isLt; simp [instI2] at this; omega)
          subst this
          simp [instI2, fare]
      _ = f₂ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₂ * n := mul_le_mul_of_nonneg_left hx2 hf₂.le

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
          cases ((instI1 n hn).get i).cls <;> simp [fare] <;> linarith
      _ = f₁ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₁ * n := mul_le_mul_of_nonneg_left hx2 (by linarith)

end Aux_RB_rub

open RobustBooking.TwoFare Aux_RB_rub in
theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, Measurable fun ω => revenue f₁ f₂ n (A ω) I) :
    randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁) ∧
    min ((∫ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ∂μ) / optRevenue f₁ f₂ n (instI1 n hn))
        ((∫ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) ∂μ) / optRevenue f₁ f₂ n (instI2 n hn))
      ≤ b (f₂ / f₁) := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  let q1 : Request := ⟨.low, n, hn⟩
  let q2 : Request := ⟨.high, n, hn⟩
  let a1 : Ω → ℝ := fun ω => max 0 (min (A ω [] q1) (min n n))
  have ha1 : ∀ ω, 0 ≤ a1 ω ∧ a1 ω ≤ n := fun ω =>
    ⟨le_max_left _ _, max_le hn.le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have rev2 : ∀ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) = f₂ * a1 ω := by
    intro ω
    simp only [revenue, accepted, runFrom, instI2, fare, List.zipWith_cons_cons,
      List.zipWith_nil_right, List.sum_cons, List.sum_nil, sub_zero, add_zero]
    rfl
  have rev1 : ∀ ω, ∃ a2, 0 ≤ a2 ∧ a2 ≤ n - a1 ω ∧
      revenue f₁ f₂ n (A ω) (instI1 n hn) = f₂ * a1 ω + f₁ * a2 := by
    intro ω
    refine ⟨max 0 (min (A ω [(q1, a1 ω)] q2) (min n (n - a1 ω))), le_max_left _ _,
      max_le (by linarith [(ha1 ω).2]) ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
    simp only [revenue, accepted, runFrom, instI1, fare, List.zipWith_cons_cons,
      List.zipWith_nil_right, List.sum_cons, List.sum_nil, sub_zero, zero_add, add_zero,
      List.nil_append]
    rfl
  have hmeas : Measurable a1 := by
    have e : a1 = fun ω => revenue f₁ f₂ n (A ω) (instI2 n hn) / f₂ := by
      funext ω; rw [rev2]; field_simp
    rw [e]
    exact (hA (instI2 n hn)).div_const f₂
  have hint1 : Integrable a1 μ :=
    Integrable.of_mem_Icc 0 n hmeas.aemeasurable (Filter.Eventually.of_forall fun ω => ha1 ω)
  have hintR1 : Integrable (fun ω => revenue f₁ f₂ n (A ω) (instI1 n hn)) μ := by
    refine Integrable.of_mem_Icc 0 (f₂ * n + f₁ * n) (hA _).aemeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    obtain ⟨a2, h0, h1, he⟩ := rev1 ω
    rw [he]
    have := ha1 ω
    constructor <;> nlinarith
  set Ea := ∫ ω, a1 ω ∂μ with hEa
  have hEa0 : 0 ≤ Ea := integral_nonneg fun ω => (ha1 ω).1
  have hEan : Ea ≤ n := by
    have := integral_mono hint1 (integrable_const n) (fun ω => (ha1 ω).2)
    simpa using this
  have hE2 : ∫ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) ∂μ = f₂ * Ea := by
    simp only [rev2]; rw [integral_const_mul]
  have hE1 : ∫ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ∂μ ≤ (f₂ - f₁) * Ea + f₁ * n := by
    have hb : ∀ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ≤ (f₂ - f₁) * a1 ω + f₁ * n := by
      intro ω
      obtain ⟨a2, h0, h1, he⟩ := rev1 ω
      rw [he]; nlinarith
    have hint3 : Integrable (fun ω => (f₂ - f₁) * a1 ω + f₁ * n) μ :=
      (hint1.const_mul _).add (integrable_const _)
    refine le_trans (integral_mono hintR1 hint3 hb) (le_of_eq ?_)
    rw [integral_add (hint1.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, ← hEa]
    simp
  rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn, opt2 f₁ f₂ n hf₂ hn]
  have hr0 : 0 < f₂ / f₁ := div_pos hf₂ hf₁
  have hr1 : f₂ / f₁ < 1 := (div_lt_one hf₁).mpr hf₁₂
  have hfn : 0 < f₁ * n := mul_pos hf₁ hn
  have hrat2 : (∫ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) ∂μ) / (f₂ * n) = Ea / n := by
    rw [hE2, mul_div_mul_left _ _ hf₂.ne']
  have hrat1 : (∫ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ∂μ) / (f₁ * n) ≤
      f₂ / f₁ * (Ea / n) + 1 - Ea / n := by
    refine le_trans (div_le_div_of_nonneg_right hE1 hfn.le) (le_of_eq ?_)
    field_simp
    ring
  have hmin : min ((∫ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ∂μ) / (f₁ * n))
      ((∫ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) ∂μ) / (f₂ * n)) ≤ b (f₂ / f₁) := by
    unfold b
    set r := f₂ / f₁
    set t := Ea / n
    have h2r : 0 < 2 - r := by linarith
    rcases le_total t (1 / (2 - r)) with h | h
    · exact (min_le_right _ _).trans (hrat2 ▸ h)
    · refine (min_le_left _ _).trans (le_trans hrat1 ?_)
      have key : 1 - (1 - r) * (1 / (2 - r)) = 1 / (2 - r) := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - r)]
  refine ⟨?_, hmin⟩
  -- the randomized competitive ratio is at most the minimum
  have hbdd : BddBelow {c : ℝ | ∃ I : List Request, 0 < optRevenue f₁ f₂ n I ∧
      c = (∫ ω, revenue f₁ f₂ n (A ω) I ∂μ) / optRevenue f₁ f₂ n I} := by
    refine ⟨0, ?_⟩
    rintro c ⟨I, hI, rfl⟩
    apply div_nonneg _ hI.le
    exact integral_nonneg fun ω => rev_nonneg f₁ f₂ n hf₁.le hf₂.le (A ω) I [] 0
  unfold randCompetitiveRatio
  have m1 := csInf_le hbdd ⟨instI1 n hn, by rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn]; exact hfn, rfl⟩
  have m2 := csInf_le hbdd ⟨instI2 n hn, by rw [opt2 f₁ f₂ n hf₂ hn]; positivity, rfl⟩
  rw [opt1 f₁ f₂ n hf₂ hf₁₂ hn] at m1
  rw [opt2 f₁ f₂ n hf₂ hn] at m2
  exact le_trans (le_min m1 m2) hmin
