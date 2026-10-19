-- Prove2me | solution 1 for TokenFinance.Debt.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T07:24:14.629978+00:00
-- url     : https://prove2.me/submissions/46e53e7d-91fc-4189-a5cc-ab8c5a3791c8

-- Research directed by Alexander Richard Towell (queelius); Lean proof by OpenAI Codex.
-- Mathematical source: Katya Malinova and Andreas Park, Tokenomics: When Tokens Beat Equity.
-- Platform definitions and exact formulation: mikedeng1; statement review: Shuze Chen.
-- Mathlib contributors supplied the formal foundations.
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
set_option autoImplicit false
open Set MeasureTheory
open TokenFinance.Debt
namespace DebtResearch
lemma cp (c : ℝ) : Continuous (pim c) := by unfold pim; fun_prop
lemma ci (c D : ℝ) : Continuous (debtInv c D) := (cp c).min continuous_const
lemma ce (c D : ℝ) : Continuous (debtEnt c D) := ((cp c).sub continuous_const).max continuous_const
lemma pn (c x : ℝ) : 0 ≤ pim c x := by unfold pim; positivity
lemma pmax (c θ x : ℝ) (hcθ : c < θ) (hx : x ≤ θ) : pim c x ≤ (θ-c)^2/4 := by
  have h1 : 0 ≤ max (x-c) 0 := le_max_right _ _
  have h2 : max (x-c) 0 ≤ θ-c := max_le (by linarith) (by linarith)
  unfold pim
  nlinarith [sq_nonneg (θ-c-max (x-c) 0)]
lemma atmax (c θ : ℝ) (hcθ : c < θ) : pim c θ = (θ-c)^2/4 := by
  simp [pim, max_eq_left (show 0 ≤ θ-c by linarith)]
lemma min_lip (p a b : ℝ) : |min p a-min p b| ≤ |a-b| := by
  have h1 := le_abs_self (a-b)
  have h2 := neg_le_abs (a-b)
  apply abs_le.mpr
  constructor <;> (rcases le_total p a with ha|ha <;> rcases le_total p b with hb|hb <;>
    simp only [min_eq_left ha, min_eq_left hb, min_eq_right ha, min_eq_right hb] <;> linarith)
lemma expect_cont (c θ : ℝ) (hθ : 0 < θ) : Continuous (fun D => expect θ (debtInv c D)) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro a b
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := θ) (f := fun x => debtInv c a x - debtInv c b x) (C := |a-b|)
    (fun x _ => by simpa only [Real.norm_eq_abs, debtInv] using min_lip (pim c x) a b)
  rw [intervalIntegral.integral_sub ((ci c a).intervalIntegrable 0 θ)
    ((ci c b).intervalIntegrable 0 θ)] at hi
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos hθ] at hi
  simp only [Real.dist_eq, expect, NNReal.coe_one, one_mul, ← sub_div, abs_div, abs_of_pos hθ]
  exact (div_le_iff₀ hθ).mpr hi
lemma capped (c θ D : ℝ) (hcθ : c < θ) (hθ : 0 < θ)
    (hD : (θ-c)^2/4 ≤ D) : expect θ (debtInv c D) = expect θ (pim c) := by
  unfold expect
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hθ.le] at hx
  exact min_eq_left ((pmax c θ x hcθ hx.2).trans hD)
lemma strict_repay (c θ a b : ℝ) (hcθ : c < θ) (hθ : 0 < θ)
    (hab : a < b) (ha : a < (θ-c)^2/4) : expect θ (debtInv c a) < expect θ (debtInv c b) := by
  apply (div_lt_div_iff_of_pos_right hθ).mpr
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hθ
    (ci c a).continuousOn (ci c b).continuousOn
  · intro x _; exact min_le_min_left _ hab.le
  · refine ⟨θ, ⟨hθ.le, le_rfl⟩, ?_⟩
    change min (pim c θ) a < min (pim c θ) b
    rw [atmax c θ hcθ, min_eq_right ha.le]
    exact lt_min ha hab
lemma repay_zero (c θ : ℝ) : expect θ (debtInv c 0) = 0 := by
  have h : debtInv c 0 = fun _ => 0 := funext (fun x => min_eq_right (pn c x))
  simp [expect, h]
lemma repay_lt (c θ D : ℝ) (hc : 0 < c) (hcθ : c < θ) (hD : 0 < D) :
    expect θ (debtInv c D) < D := by
  have hθ : 0 < θ := hc.trans hcθ
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hθ
    (ci c D).continuousOn (g := fun _ => D) continuousOn_const
    (fun x _ => min_le_right (pim c x) D)
    ⟨0, ⟨le_rfl,hθ.le⟩, by simp [debtInv,pim,max_eq_right (show -c ≤ 0 by linarith),min_eq_left hD.le,hD]⟩
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
  exact (div_lt_iff₀ hθ).mpr (by nlinarith)
lemma ent_identity (c θ D : ℝ) : expect θ (debtEnt c D) = expect θ (pim c)-expect θ (debtInv c D) := by
  have h : debtEnt c D = fun x => pim c x-debtInv c D x := by
    funext x
    unfold debtEnt debtInv
    rcases le_total (pim c x) D with hh|hh
    · rw [min_eq_left hh,max_eq_right (by linarith)]; ring
    · rw [min_eq_right hh,max_eq_left (by linarith)]
  unfold expect
  rw [h,intervalIntegral.integral_sub ((cp c).intervalIntegrable 0 θ) ((ci c D).intervalIntegrable 0 θ)]
  ring
lemma main (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < npv c C0 θ) :
    (∃! D : ℝ, 0 ≤ D ∧ expect θ (debtInv c D) = C0) ∧
      ∀ D : ℝ, 0 ≤ D → expect θ (debtInv c D) = C0 →
        C0 < D ∧ D < (θ-c)^2/4 ∧ expect θ (debtEnt c D) = npv c C0 θ := by
  have hθ := hc.trans hcθ
  have hprofit : C0 < expect θ (pim c) := by unfold npv at hnpv; linarith
  have hM : 0 ≤ (θ-c)^2/4 := by positivity
  have htop := capped c θ ((θ-c)^2/4) hcθ hθ le_rfl
  obtain ⟨D,hD,hDeq⟩ := intermediate_value_Icc hM (expect_cont c θ hθ).continuousOn
    (show C0 ∈ Icc (expect θ (debtInv c 0)) (expect θ (debtInv c ((θ-c)^2/4))) by
      rw [repay_zero,htop];exact ⟨hC0.le,hprofit.le⟩)
  have below : ∀ E : ℝ, expect θ (debtInv c E) = C0 → E < (θ-c)^2/4 := by
    intro E hE
    by_contra hn
    have ht := capped c θ E hcθ hθ (le_of_not_gt hn)
    linarith
  refine ⟨⟨D,⟨hD.1,hDeq⟩,?_⟩,?_⟩
  · intro E hE
    rcases lt_trichotomy E D with he|he|he
    · have hh := strict_repay c θ E D hcθ hθ he (below E hE.2); linarith [hE.2]
    · exact he
    · have hh := strict_repay c θ D E hcθ hθ he (below D hDeq); linarith [hE.2]
  · intro E hE hEq
    have hp : 0 < E := by
      rcases hE.eq_or_lt with h|h
      · subst E;rw [repay_zero] at hEq;linarith
      · exact h
    exact ⟨by simpa [hEq] using repay_lt c θ E hc hcθ hp,
      below E hEq, by rw [ent_identity,hEq];rfl⟩
end DebtResearch

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < npv c C0 θ) :
    (∃! D : ℝ, 0 ≤ D ∧ expect θ (debtInv c D) = C0) ∧
      ∀ D : ℝ, 0 ≤ D → expect θ (debtInv c D) = C0 →
        C0 < D ∧ D < (θ - c) ^ 2 / 4 ∧ expect θ (debtEnt c D) = npv c C0 θ := by
  exact DebtResearch.main c C0 θ hc hcθ hC0 hnpv

