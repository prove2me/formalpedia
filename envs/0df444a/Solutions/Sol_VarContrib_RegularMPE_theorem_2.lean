-- Prove2me | solution 1 for VarContrib.RegularMPE.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:00:15.313747+00:00
-- url     : https://prove2.me/submissions/09705368-004c-4d8f-b842-f4afccd1518e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game
import Theorems.Thm_VarContrib_RegularMPE_lemma_1_hjb
import Theorems.Thm_VarContrib_RegularMPE_optimality_condition
import Theorems.Thm_VarContrib_RegularMPE_theorem_1_regular
import Theorems.Thm_VarContrib_RegularMPE_Vsol_monotoneOn

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

/-- The resolvent `Rπ` is bounded above by `π_M / r` on `I`. -/
theorem VarContrib_theorem_2_R_pi_le {Ω : Type*} [MeasurableSpace Ω] (m : Model)
    (S : Setting Ω) (hst : Standing m S) (πM : ℝ) (hπM : 0 < πM)
    (hb : ∀ x ∈ m.I, m.π x < πM) (x : ℝ) (hx : x ∈ m.I) :
    R m S m.π x ≤ πM / m.r := by
  have hr := hst.r_pos
  have := hst.prob
  have hXI : ∀ t ω, S.X x t ω ∈ m.I := (hst.uncontrolled x hx).1.2.1
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(m.r * t)) * πM) (Ioi 0) := by
    have h0 := (exp_neg_integrableOn_Ioi 0 hr).mul_const πM
    exact IntegrableOn.congr_fun (f := fun x : ℝ => Real.exp (-m.r * x) * πM) h0
      (fun t _ => by simp [neg_mul]) measurableSet_Ioi
  have hval : ∫ t in Ioi (0:ℝ), Real.exp (-(m.r * t)) * πM = πM / m.r := by
    rw [integral_mul_const]
    have h := integral_exp_mul_Ioi (a := -m.r) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at h
    have e : (fun t : ℝ => Real.exp (-(m.r * t))) = fun t => Real.exp (-m.r * t) := by
      funext t; ring_nf
    rw [e, h]; field_simp
  have inner : ∀ ω, (∫ t in Ioi (0:ℝ), Real.exp (-(m.r * t)) * m.π (S.X x t.toNNReal ω))
      ≤ πM / m.r := by
    intro ω
    by_cases hi : IntegrableOn
        (fun t : ℝ => Real.exp (-(m.r * t)) * m.π (S.X x t.toNNReal ω)) (Ioi 0)
    · rw [← hval]
      apply setIntegral_mono hi hint
      intro t
      exact mul_le_mul_of_nonneg_left (hb _ (hXI _ _)).le (Real.exp_pos _).le
    · rw [integral_undef hi]; exact div_nonneg hπM.le hr.le
  unfold R
  by_cases hi : Integrable
      (fun ω => ∫ t in Ioi (0:ℝ), Real.exp (-(m.r * t)) * m.π (S.X x t.toNNReal ω)) S.P
  · calc _ ≤ ∫ _ω, πM / m.r ∂S.P := integral_mono hi (integrable_const _) inner
      _ = πM / m.r := by simp
  · rw [integral_undef hi]; exact div_nonneg hπM.le hr.le

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (θ A : ℝ) (hθ : θ ∈ m.I)
    (hV : ContDiffOn ℝ 2 (Vsol m S θ A) m.I) (hu : InU m (uEq m S θ A)) :
    IsRegularMPE m S (fun _ => uEq m S θ A) ∧
    ∀ x ∈ m.I, ∀ Z : ℝ≥0 → Ω → ℝ,
      IsStateSol m S (fun y => m.μ y + uEq m S θ A y + uEq m S θ A y) x (fun _ _ => 0) Z →
        regPay m S (uEq m S θ A) Z = Vsol m S θ A x := by
  obtain ⟨h1, h2, h3, h4⟩ := lemma_1_hjb m S hst θ A hθ hV
  have hk := hst.k_pos
  have hr := hst.r_pos
  have uLt : ∀ x, x < θ → uEq m S θ A x = -(gen m (Vsol m S θ A) x + m.π x) / m.k := by
    intro x hx; simp [uEq, hx]
  have uGe : ∀ x, ¬ x < θ → uEq m S θ A x = 0 := by
    intro x hx; simp [uEq, hx]
  -- `𝒜V + π + u V' = 0` on `I`
  have hE : ∀ x ∈ m.I,
      gen m (Vsol m S θ A) x + m.π x + uEq m S θ A x * deriv (Vsol m S θ A) x = 0 := by
    intro x hx
    by_cases hxθ : x < θ
    · rw [uLt x hxθ, h3 x hx hxθ.le]; field_simp; ring
    · rw [uGe x hxθ, h1 x hx (not_lt.1 hxθ)]; ring
  have hD : ∀ x ∈ m.I, deriv (Vsol m S θ A) x ≤ m.k := by
    intro x hx; rcases le_or_gt x θ with h | h
    · exact (h3 x hx h).le
    · exact (h4 x hx h).le
  have hP : ∀ x ∈ m.I, uEq m S θ A x * (deriv (Vsol m S θ A) x - m.k) = 0 := by
    intro x hx
    by_cases hxθ : x < θ
    · rw [h3 x hx hxθ.le]; ring
    · rw [uGe x hxθ]; ring
  have hu0 : ∀ y ∈ m.I, 0 ≤ uEq m S θ A y := by
    intro y hy
    by_cases hyθ : y < θ
    · rw [uLt y hyθ]; exact div_nonneg (by linarith [h2 y hy hyθ]) hk.le
    · rw [uGe y hyθ]
  have hmono := Vsol_monotoneOn m S hst θ A hθ hV
  have hbdd : BddAbove (Vsol m S θ A '' m.I) := by
    obtain ⟨πM, hπM, hb⟩ := hst.π_bdd
    have hφθ := hst.φ_pos θ hθ
    refine ⟨πM / m.r + |A| * S.φ θ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxθ : x < θ
    · have e : Vsol m S θ A x = m.k * (x - θ) + (R m S m.π θ + A * S.φ θ) := by
        simp [Vsol, hxθ]
      rw [e]
      have := VarContrib_theorem_2_R_pi_le m S hst πM hπM hb θ hθ
      have h5 : A * S.φ θ ≤ |A| * S.φ θ := mul_le_mul_of_nonneg_right (le_abs_self A) hφθ.le
      have h6 : m.k * (x - θ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
      linarith
    · have e : Vsol m S θ A x = R m S m.π x + A * S.φ x := by simp [Vsol, hxθ]
      rw [e]
      have := VarContrib_theorem_2_R_pi_le m S hst πM hπM hb x hx
      have hφx := hst.φ_pos x hx
      have h5 : A * S.φ x ≤ |A| * S.φ x := mul_le_mul_of_nonneg_right (le_abs_self A) hφx.le
      have h7 : S.φ x ≤ S.φ θ := hst.φ_strictAnti.antitoneOn hθ hx (not_lt.1 hxθ)
      have h6 : |A| * S.φ x ≤ |A| * S.φ θ := mul_le_mul_of_nonneg_left h7 (abs_nonneg A)
      linarith
  have hT1 := theorem_1_regular m S hst (uEq m S θ A) (uEq m S θ A) hu hu0 hu hu0
    (Vsol m S θ A) hV hmono hbdd
    (fun x hx v hv => by
      apply max_le
      · have e1 := hE x hx
        have e2 : 0 ≤ v * (m.k - deriv (Vsol m S θ A) x) :=
          mul_nonneg hv (sub_nonneg.2 (hD x hx))
        nlinarith
      · linarith [hD x hx])
    (fun x hx => by
      have e1 := hE x hx
      have e2 := hP x hx
      nlinarith)
  have hOC := optimality_condition m S hst θ A hθ hV (uEq m S θ A) hu hu0
    (fun x hx => ⟨by linarith [hE x hx], by linarith [hD x hx]⟩)
    (fun x hx => by
      have e : gen m (Vsol m S θ A) x + uEq m S θ A x * deriv (Vsol m S θ A) x + m.π x = 0 := by
        linarith [hE x hx]
      rw [e]; ring)
  refine ⟨⟨fun _ => ⟨hu, hu0⟩, ?_⟩, ?_⟩
  · intro i j _ x hx Z hZ
    obtain ⟨hint, hpay, _⟩ := hT1 x hx Z hZ
    refine ⟨hint, ?_⟩
    intro ζ Z' hZ' hadm
    rw [hpay]
    exact (hOC x hx).1 ζ Z' hZ' hadm
  · intro x hx Z hZ
    exact (hT1 x hx Z hZ).2.1
