-- Prove2me | solution 1 for TelehealthParity.Access.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T17:03:06.359982+00:00
-- url     : https://prove2.me/submissions/94dff97f-c687-47a6-a55c-561b532b73d1

import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

lemma tp_g_le (κ s θ : ℝ) (hs : 0 < s) :
    (1 - θ * (1 - s ^ 2)) / (2 * s ^ 2) - κ -
        Real.sqrt (κ ^ 2 + ((1 - θ * (1 + s ^ 2)) / (2 * s ^ 2)) ^ 2)
      ≤ (1 - κ * (1 + s) ^ 2) / (1 + s ^ 2) := by
  set u := (1 - θ * (1 + s ^ 2)) / (2 * s ^ 2) with hu
  have hP : 0 < 1 + s ^ 2 := by positivity
  have hL : (2 * s * κ + (1 - s ^ 2) * u) / (1 + s ^ 2) ≤ Real.sqrt (κ ^ 2 + u ^ 2) := by
    apply le_trans (le_abs_self _)
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((1 - s ^ 2) * κ - 2 * s * u)]
  have key : (1 - θ * (1 - s ^ 2)) / (2 * s ^ 2) - κ - (2 * s * κ + (1 - s ^ 2) * u) / (1 + s ^ 2)
      = (1 - κ * (1 + s) ^ 2) / (1 + s ^ 2) := by
    rw [hu]; field_simp; ring
  linarith

lemma tp_g_star (κ s : ℝ) (hs : 0 < s) (hk : 0 ≤ κ) :
    (1 - (1 - κ * (1 - s ^ 2) * s) / (1 + s ^ 2) * (1 - s ^ 2)) / (2 * s ^ 2) - κ -
        Real.sqrt (κ ^ 2 + ((1 - (1 - κ * (1 - s ^ 2) * s) / (1 + s ^ 2) * (1 + s ^ 2)) /
          (2 * s ^ 2)) ^ 2)
      = (1 - κ * (1 + s) ^ 2) / (1 + s ^ 2) := by
  have h1 : κ ^ 2 + ((1 - (1 - κ * (1 - s ^ 2) * s) / (1 + s ^ 2) * (1 + s ^ 2)) /
          (2 * s ^ 2)) ^ 2 = (κ * (1 + s ^ 2) / (2 * s)) ^ 2 := by
    field_simp; ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp; ring

lemma tp_alg1 (E W s : ℝ) (hE : 0 < E) (hs : 0 < s) (hs1 : s < 1) (hW : (1 + s) ^ 2 * E < W) :
    s ^ 2 / (W - s ^ 2 * E) + (1 - s ^ 2) * s / W ≤ 1 / E := by
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ, 0 < δ ∧ W = (1 + s) ^ 2 * E + δ := ⟨W - (1 + s) ^ 2 * E, by linarith, by ring⟩
  have hD : 0 < (1 + s) ^ 2 * E + δ - s ^ 2 * E := by nlinarith
  have hW' : 0 < (1 + s) ^ 2 * E + δ := by positivity
  rw [div_add_div _ _ hD.ne' hW'.ne', div_le_div_iff₀ (by positivity) hE]
  have h1 : 0 < 1 - s := by linarith
  nlinarith [mul_pos hδ hE, mul_pos (mul_pos hδ hE) hs, mul_pos hE hE, mul_pos (mul_pos hE hE) hs,
    mul_pos (mul_pos (mul_pos hE hE) hs) h1, mul_pos (mul_pos (mul_pos hE hE) (pow_pos hs 3)) h1,
    mul_pos hδ hδ, mul_pos (mul_pos hδ hE) (pow_pos hs 3), mul_pos (mul_pos hE hE) (pow_pos hs 2),
    mul_pos (mul_pos hE hE) (pow_pos hs 3), mul_pos (mul_pos hE hE) (pow_pos hs 4)]

lemma tp_bar (κ s : ℝ) (hs : 0 < s) (hk : 0 ≤ κ) (hN : 0 < 1 - κ * (1 + s) ^ 2) :
    (1 - κ * (1 - s ^ 2) * s) / (1 + s ^ 2) <
      (1 + κ * (1 - s ^ 2) + Real.sqrt ((1 - κ * (1 - s ^ 2)) ^ 2 - 4 * s ^ 2 * κ)) / 2 := by
  set θ := (1 - κ * (1 - s ^ 2) * s) / (1 + s ^ 2) with hθ
  have key : (1 - κ * (1 - s ^ 2)) ^ 2 - 4 * s ^ 2 * κ - (2 * θ - (1 + κ * (1 - s ^ 2))) ^ 2
      = 4 * ((1 - κ * (1 + s) ^ 2) * (s ^ 2 + κ * s * (1 - s) ^ 2 * (1 + s + s ^ 2))) /
          (1 + s ^ 2) ^ 2 := by
    rw [hθ]; field_simp; ring
  have hpos : 0 < 4 * ((1 - κ * (1 + s) ^ 2) * (s ^ 2 + κ * s * (1 - s) ^ 2 * (1 + s + s ^ 2))) /
          (1 + s ^ 2) ^ 2 := by
    apply div_pos _ (by positivity)
    apply mul_pos (by norm_num) (mul_pos hN _)
    have : 0 ≤ κ * s * (1 - s) ^ 2 * (1 + s + s ^ 2) := by positivity
    nlinarith [pow_pos hs 2]
  have hlt : 2 * θ - (1 + κ * (1 - s ^ 2)) < Real.sqrt ((1 - κ * (1 - s ^ 2)) ^ 2 - 4 * s ^ 2 * κ) := by
    rcases lt_or_ge (2 * θ - (1 + κ * (1 - s ^ 2))) 0 with h | h
    · exact lt_of_lt_of_le h (Real.sqrt_nonneg _)
    · rw [Real.lt_sqrt h]; linarith
  linarith


lemma tp_bound (p : Params) (hp : p.Standing) (s : ℝ) (hs0 : 0 < s)
    (hadm : Admissible p (s ^ 2)) (θ : ℝ) (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    (eqProp p (s ^ 2) θ).1 + (1 + s ^ 2) * (eqProp p (s ^ 2) θ).2 ≤
        p.μ / p.lam * max (1 - p.h / p.μ / (p.V - p.cO - p.τ))
          (1 - kappa p (s ^ 2) * (1 + s) ^ 2) ∧
    (eqProp p (s ^ 2) θ).1 + (eqProp p (s ^ 2) θ).2 ≤
        p.μ / p.lam * max (1 - p.h / p.μ / (p.V - p.cO - p.τ))
          ((1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2)) := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  obtain ⟨hq0, hq1, hk0, hk1, hE1, hord, -⟩ := hadm
  obtain ⟨hθ0, hθ1⟩ := hθ
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hM : 0 < p.μ / p.lam := div_pos hμ hlam
  have hY : 0 < 1 - p.h / p.μ / (p.V - p.cO - p.τ) := by
    rw [sub_pos, div_lt_one hE0]; linarith
  have hgle := tp_g_le (kappa p (s ^ 2)) s θ hs0
  have hP : 0 < 1 + s ^ 2 := by positivity
  have hμ' : p.μ ≠ 0 := hμ.ne'
  have hlam' : p.lam ≠ 0 := hlam.ne'
  have hE0' : p.V - p.cO - p.τ ≠ 0 := hE0.ne'
  have hE1' : (1 - s ^ 2) * p.V - p.cT ≠ 0 := hE1.ne'
  unfold eqProp
  split_ifs with c1 c2 c3
  · simp only
    have e : (1 - θ) * p.μ / p.lam - p.h / ((p.V - p.cO - p.τ) * p.lam)
        = p.μ / p.lam * (1 - θ - p.h / p.μ / (p.V - p.cO - p.τ)) := by
      field_simp
    rw [e]
    have hle : 1 - θ - p.h / p.μ / (p.V - p.cO - p.τ) ≤
        1 - p.h / p.μ / (p.V - p.cO - p.τ) := by linarith
    constructor
    · rw [mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (le_trans hle (le_max_left _ _)) hM.le
    · rw [add_zero]
      exact mul_le_mul_of_nonneg_left (le_trans hle (le_max_left _ _)) hM.le
  · simp only
    have hb : 0 ≤ p.h / p.μ / ((1 - s ^ 2) * p.V - p.cT) := div_nonneg ha.le hE1.le
    constructor
    · have e : (p.μ / p.lam - (1 + s ^ 2) * θ * p.μ / p.lam +
          p.h / p.lam * (s ^ 2 / ((1 - s ^ 2) * p.V - p.cT) - 1 / (p.V - p.cO - p.τ))) +
          (1 + s ^ 2) * (θ * p.μ / p.lam - p.h / p.lam * (1 / ((1 - s ^ 2) * p.V - p.cT)))
          = p.μ / p.lam * (1 - p.h / p.μ / (p.V - p.cO - p.τ) -
              p.h / p.μ / ((1 - s ^ 2) * p.V - p.cT)) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_max_left _ _)) hM.le
    · have e : (p.μ / p.lam - (1 + s ^ 2) * θ * p.μ / p.lam +
          p.h / p.lam * (s ^ 2 / ((1 - s ^ 2) * p.V - p.cT) - 1 / (p.V - p.cO - p.τ))) +
          (θ * p.μ / p.lam - p.h / p.lam * (1 / ((1 - s ^ 2) * p.V - p.cT)))
          = p.μ / p.lam * (1 - s ^ 2 * θ - p.h / p.μ / (p.V - p.cO - p.τ) -
              (1 - s ^ 2) * (p.h / p.μ / ((1 - s ^ 2) * p.V - p.cT))) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ s ^ 2 * θ := by positivity
      have : 0 ≤ (1 - s ^ 2) * (p.h / p.μ / ((1 - s ^ 2) * p.V - p.cT)) :=
        mul_nonneg (by linarith) hb
      exact mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_max_left _ _)) hM.le
  · simp only [zero_add]
    constructor
    · rw [← mul_assoc, mul_comm (1 + s ^ 2), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hM.le
      apply le_trans _ (le_max_right _ _)
      rw [le_div_iff₀ hP] at hgle
      linarith
    · exact mul_le_mul_of_nonneg_left (le_trans hgle (le_max_right _ _)) hM.le
  · simp only [add_zero, mul_zero]
    constructor <;> exact mul_nonneg hM.le (le_trans hY.le (le_max_left _ _))

lemma tp_zero (p : Params) (hp : p.Standing) (q : ℝ) (hE1 : 0 < (1 - q) * p.V - p.cT) :
    eqProp p q 0 = (p.μ / p.lam * (1 - p.h / p.μ / (p.V - p.cO - p.τ)), 0) := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have hE0 : 0 < p.V - p.cO - p.τ := by have := div_pos hh hμ; linarith
  have hT : (0:ℝ) ≤ thetaT p q := by
    unfold thetaT; exact mul_nonneg (div_nonneg hh.le hμ.le) (div_nonneg zero_le_one hE1.le)
  have hμ' : p.μ ≠ 0 := hμ.ne'
  have hlam' : p.lam ≠ 0 := hlam.ne'
  have hE0' : p.V - p.cO - p.τ ≠ 0 := hE0.ne'
  unfold eqProp
  rw [if_pos hT]
  refine Prod.ext ?_ rfl
  simp only
  field_simp
  ring

lemma tp_star (p : Params) (hp : p.Standing) (s : ℝ) (hs0 : 0 < s)
    (hadm : Admissible p (s ^ 2))
    (hlt : (1 + s) ^ 2 * (p.V - p.cO - p.τ) < p.V - p.cT - s ^ 2 * (p.cO + p.τ)) :
    eqProp p (s ^ 2) (thetaStar p (s ^ 2)) =
      (0, p.μ / p.lam * ((1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2))) := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  obtain ⟨hq0, hq1, hk0, hk1, hE1, hord, -⟩ := hadm
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hs1 : s < 1 := by nlinarith
  have hW : 0 < p.V - p.cT - s ^ 2 * (p.cO + p.τ) := by
    have : 0 < (1 + s) ^ 2 * (p.V - p.cO - p.τ) := by positivity
    linarith
  have hP : 0 < 1 + s ^ 2 := by positivity
  have hμ' : p.μ ≠ 0 := hμ.ne'
  have hE0' : p.V - p.cO - p.τ ≠ 0 := hE0.ne'
  have hE1' : (1 - s ^ 2) * p.V - p.cT ≠ 0 := hE1.ne'
  have hW' : p.V - p.cT - s ^ 2 * (p.cO + p.τ) ≠ 0 := hW.ne'
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs0.le
  have hstar : thetaStar p (s ^ 2) = (1 - kappa p (s ^ 2) * (1 - s ^ 2) * s) / (1 + s ^ 2) := by
    unfold thetaStar; rw [hsq]
  have hTO : thetaT p (s ^ 2) < thetaO p (s ^ 2) := by
    have e : thetaO p (s ^ 2) - thetaT p (s ^ 2) = (1 - p.h / p.μ * (1 / ((1 - s ^ 2) * p.V - p.cT)
        + 1 / (p.V - p.cO - p.τ))) / (1 + s ^ 2) := by
      unfold thetaO thetaT; field_simp; ring
    have : 0 < thetaO p (s ^ 2) - thetaT p (s ^ 2) := by rw [e]; exact div_pos (by linarith) hP
    linarith
  have hOS : thetaO p (s ^ 2) ≤ thetaStar p (s ^ 2) := by
    have hA := tp_alg1 (p.V - p.cO - p.τ) (p.V - p.cT - s ^ 2 * (p.cO + p.τ)) s hE0 hs0 hs1 hlt
    have hEq : p.V - p.cT - s ^ 2 * (p.cO + p.τ) - s ^ 2 * (p.V - p.cO - p.τ)
        = (1 - s ^ 2) * p.V - p.cT := by ring
    rw [hEq] at hA
    have e : thetaStar p (s ^ 2) - thetaO p (s ^ 2) = p.h / p.μ / (1 + s ^ 2) *
        (1 / (p.V - p.cO - p.τ) - (s ^ 2 / ((1 - s ^ 2) * p.V - p.cT) +
          (1 - s ^ 2) * s / (p.V - p.cT - s ^ 2 * (p.cO + p.τ)))) := by
      rw [hstar]; unfold thetaO kappa; field_simp; ring
    have : 0 ≤ thetaStar p (s ^ 2) - thetaO p (s ^ 2) := by
      rw [e]; exact mul_nonneg (by positivity) (by linarith)
    linarith
  have hk1' : kappa p (s ^ 2) * (1 + s) ^ 2 < 1 := by
    unfold kappa
    rw [div_mul_eq_mul_div (p.h / p.μ) _ ((1 + s) ^ 2), div_lt_one hW]
    have : p.h / p.μ * (1 + s) ^ 2 < (p.V - p.cO - p.τ) * (1 + s) ^ 2 :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    linarith
  have hN : 0 < 1 - kappa p (s ^ 2) * (1 + s) ^ 2 := by linarith
  have hBar : thetaStar p (s ^ 2) < thetaBar p (s ^ 2) := by
    rw [hstar]; unfold thetaBar
    exact tp_bar (kappa p (s ^ 2)) s hs0 hk0.le hN
  unfold eqProp
  rw [if_neg (not_le.2 (by linarith)), if_neg (not_lt.2 hOS), if_pos hBar, hstar,
    tp_g_star _ _ hs0 hk0.le]

/-- The revenue threshold `s*` (with `q* = s*²`): the root in `(0,1)` of
`V s² + 2 (V − cO − τ) s = cO + τ − cT`. -/
lemma tp_root (p : Params) (hp : p.Standing) : ∃ sS : ℝ, 0 < sS ∧ sS < 1 ∧
    p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hd0 : 0 < p.cO + p.τ - p.cT := by linarith
  have hx : 0 ≤ (p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT) := by positivity
  have hroot := Real.sq_sqrt hx
  have hlt : p.V - p.cO - p.τ < Real.sqrt ((p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT)) := by
    rw [Real.lt_sqrt hE0.le]; nlinarith
  refine ⟨(Real.sqrt ((p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT)) - (p.V - p.cO - p.τ)) / p.V,
    div_pos (by linarith) hV, ?_, ?_⟩
  · rw [div_lt_one hV]
    have : Real.sqrt ((p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT)) < p.V + (p.V - p.cO - p.τ) := by
      rw [Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  · have hVs : p.V * ((Real.sqrt ((p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT)) -
        (p.V - p.cO - p.τ)) / p.V) = Real.sqrt ((p.V - p.cO - p.τ) ^ 2 + p.V * (p.cO + p.τ - p.cT)) -
        (p.V - p.cO - p.τ) := by field_simp
    apply mul_left_cancel₀ hV.ne'
    have e : ∀ t : ℝ, p.V * (p.V * t ^ 2 + 2 * (p.V - p.cO - p.τ) * t) =
        (p.V * t) ^ 2 + 2 * (p.V - p.cO - p.τ) * (p.V * t) := fun t => by ring
    rw [e, hVs]
    linear_combination hroot

lemma tp_Wge (p : Params) (hp : p.Standing) (sS : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ sS) :
    (1 + x) ^ 2 * (p.V - p.cO - p.τ) ≤ p.V - p.cT - x ^ 2 * (p.cO + p.τ) := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hxx : x * x ≤ sS * sS := mul_le_mul hx1 hx1 hx0 hsS0.le
  have i1 : p.V * (x * x) ≤ p.V * (sS * sS) := mul_le_mul_of_nonneg_left hxx hV.le
  have i2 : (p.V - p.cO - p.τ) * x ≤ (p.V - p.cO - p.τ) * sS := mul_le_mul_of_nonneg_left hx1 hE0.le
  nlinarith

lemma tp_Wpos (p : Params) (hp : p.Standing) (sS : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ sS) :
    0 < p.V - p.cT - x ^ 2 * (p.cO + p.τ) := by
  have h := tp_Wge p hp sS hsS0 hsS x hx0 hx1
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have : 0 < (1 + x) ^ 2 * (p.V - p.cO - p.τ) := by positivity
  linarith

/-- The access gap `A(θ*)/μ − A(0)/μ` as a function of `s = √q`. -/
noncomputable def tpD (p : Params) (s : ℝ) : ℝ :=
  (1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2) - (1 - p.h / p.μ / (p.V - p.cO - p.τ))

lemma tp_anti (p : Params) (hp : p.Standing) (sS : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT)
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ sS) : tpD p y < tpD p x := by
  have hWx := tp_Wge p hp sS hsS0 hsS x hx (by linarith)
  have hWy := tp_Wge p hp sS hsS0 hsS y (by linarith) hy
  have hWx0 := tp_Wpos p hp sS hsS0 hsS x hx (by linarith)
  have hWy0 := tp_Wpos p hp sS hsS0 hsS y (by linarith) hy
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hc : 0 < p.cO + p.τ := by linarith
  have hY : 0 < 1 - p.h / p.μ / (p.V - p.cO - p.τ) := by
    rw [sub_pos, div_lt_one hE0]; linarith
  unfold tpD kappa
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hsq1 : (1 + x) ^ 2 < (1 + y) ^ 2 := by nlinarith
  have hWxy : p.V - p.cT - y ^ 2 * (p.cO + p.τ) ≤ p.V - p.cT - x ^ 2 * (p.cO + p.τ) := by nlinarith
  have h1 : p.h / p.μ / (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) * (1 + x) ^ 2 <
      p.h / p.μ / (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) * (1 + y) ^ 2 := by
    rw [div_mul_eq_mul_div (p.h / p.μ) _ ((1 + x) ^ 2), div_mul_eq_mul_div (p.h / p.μ) _ ((1 + y) ^ 2),
      div_lt_div_iff₀ hWx0 hWy0]
    have i1 : p.h / p.μ * (1 + x) ^ 2 * (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) ≤
        p.h / p.μ * (1 + x) ^ 2 * (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) :=
      mul_le_mul_of_nonneg_left hWxy (by positivity)
    have i2 : p.h / p.μ * (1 + x) ^ 2 * (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) <
        p.h / p.μ * (1 + y) ^ 2 * (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hsq1 ha) hWx0
    linarith
  have h2 : p.h / p.μ / (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) * (1 + y) ^ 2 ≤
      p.h / p.μ / (p.V - p.cO - p.τ) := by
    rw [div_mul_eq_mul_div (p.h / p.μ) _ ((1 + y) ^ 2), div_le_div_iff₀ hWy0 hE0]
    have := mul_le_mul_of_nonneg_left hWy ha.le
    nlinarith
  have hPx : (0:ℝ) < 1 + x ^ 2 := by positivity
  have hPy : (0:ℝ) < 1 + y ^ 2 := by positivity
  suffices key : (1 - p.h / p.μ / (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) * (1 + y) ^ 2) / (1 + y ^ 2) <
      (1 - p.h / p.μ / (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) * (1 + x) ^ 2) / (1 + x ^ 2) by
    linarith
  rw [div_lt_div_iff₀ hPy hPx]
  have hKy : 0 < 1 - p.h / p.μ / (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) * (1 + y) ^ 2 := by linarith
  have i1 := mul_le_mul_of_nonneg_left (show 1 + x ^ 2 ≤ 1 + y ^ 2 by linarith) hKy.le
  have i2 : (1 - p.h / p.μ / (p.V - p.cT - y ^ 2 * (p.cO + p.τ)) * (1 + y) ^ 2) * (1 + y ^ 2) <
      (1 - p.h / p.μ / (p.V - p.cT - x ^ 2 * (p.cO + p.τ)) * (1 + x) ^ 2) * (1 + y ^ 2) :=
    mul_lt_mul_of_pos_right (by linarith) hPy
  linarith

lemma tp_D0 (p : Params) (hp : p.Standing) : 0 < tpD p 0 := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  unfold tpD kappa
  have e : (1 - p.h / p.μ / (p.V - p.cT - (0:ℝ) ^ 2 * (p.cO + p.τ)) * (1 + 0) ^ 2) / (1 + (0:ℝ) ^ 2)
      = 1 - p.h / p.μ / (p.V - p.cT) := by norm_num
  rw [e]
  have : p.h / p.μ / (p.V - p.cT) < p.h / p.μ / (p.V - p.cO - p.τ) :=
    div_lt_div_of_pos_left ha hE0 (by linarith)
  linarith

lemma tp_DS (p : Params) (hp : p.Standing) (sS : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT) : tpD p sS < 0 := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hY : 0 < 1 - p.h / p.μ / (p.V - p.cO - p.τ) := by
    rw [sub_pos, div_lt_one hE0]; linarith
  unfold tpD
  have hW : p.V - p.cT - sS ^ 2 * (p.cO + p.τ) = (1 + sS) ^ 2 * (p.V - p.cO - p.τ) := by
    linear_combination (-1 : ℝ) * hsS
  have hk : kappa p (sS ^ 2) * (1 + sS) ^ 2 = p.h / p.μ / (p.V - p.cO - p.τ) := by
    unfold kappa; rw [hW]
    have : (1 + sS) ^ 2 ≠ 0 := by positivity
    have : p.V - p.cO - p.τ ≠ 0 := hE0.ne'
    field_simp
  rw [hk]
  have : (1 - p.h / p.μ / (p.V - p.cO - p.τ)) / (1 + sS ^ 2) < 1 - p.h / p.μ / (p.V - p.cO - p.τ) :=
    div_lt_self hY (by nlinarith)
  linarith

lemma tp_cont (p : Params) (hp : p.Standing) (sS : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT) :
    ContinuousOn (tpD p) (Set.Icc 0 sS) := by
  have hW := tp_Wpos p hp sS hsS0 hsS
  unfold tpD
  apply ContinuousOn.sub _ continuousOn_const
  apply ContinuousOn.div _ (by fun_prop) (fun x _ => by positivity)
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.mul _ (by fun_prop)
  unfold kappa
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx; exact (hW x hx.1 hx.2).ne'

/-- The two thresholds. -/
lemma tp_thresholds (p : Params) (hp : p.Standing) : ∃ sD sS : ℝ, 0 < sD ∧ sD < sS ∧ sS < 1 ∧
    p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT ∧ tpD p sD = 0 := by
  obtain ⟨sS, hsS0, hsS1, hsS⟩ := tp_root p hp
  have hD0 := tp_D0 p hp
  have hDS := tp_DS p hp sS hsS0 hsS
  obtain ⟨sD, ⟨hsD0, hsD1⟩, hDsD⟩ :=
    intermediate_value_Icc' hsS0.le (tp_cont p hp sS hsS0 hsS)
      (show (0:ℝ) ∈ Set.Icc (tpD p sS) (tpD p 0) from ⟨hDS.le, hD0.le⟩)
  have hsD0' : 0 < sD := lt_of_le_of_ne hsD0 (by rintro rfl; linarith)
  have hsD1' : sD < sS := lt_of_le_of_ne hsD1 (by rintro rfl; linarith)
  exact ⟨sD, sS, hsD0', hsD1', hsS1, hsS, hDsD⟩

/-- Comparisons of `X = 1 − κ(1+s)²` with `Y = 1 − (h/μ)/E₀`. -/
lemma tp_low (p : Params) (hp : p.Standing) (sS s : ℝ) (hsS0 : 0 < sS) (hs0 : 0 < s)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT) (hs : s < sS) :
    (1 + s) ^ 2 * (p.V - p.cO - p.τ) < p.V - p.cT - s ^ 2 * (p.cO + p.τ) ∧
      1 - p.h / p.μ / (p.V - p.cO - p.τ) < 1 - kappa p (s ^ 2) * (1 + s) ^ 2 := by
  have hW := tp_Wpos p hp sS hsS0 hsS s hs0.le hs.le
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hss : s * s < sS * sS := mul_lt_mul'' hs hs hs0.le hs0.le
  have i1 : p.V * (s * s) < p.V * (sS * sS) := mul_lt_mul_of_pos_left hss hV
  have i2 : (p.V - p.cO - p.τ) * s < (p.V - p.cO - p.τ) * sS := mul_lt_mul_of_pos_left hs hE0
  have hlt : (1 + s) ^ 2 * (p.V - p.cO - p.τ) < p.V - p.cT - s ^ 2 * (p.cO + p.τ) := by nlinarith
  refine ⟨hlt, ?_⟩
  unfold kappa
  rw [div_mul_eq_mul_div (p.h / p.μ) _ ((1 + s) ^ 2), sub_lt_sub_iff_left, div_lt_div_iff₀ hW hE0]
  have := mul_lt_mul_of_pos_left hlt ha
  nlinarith

lemma tp_high (p : Params) (hp : p.Standing) (sS s : ℝ) (hsS0 : 0 < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT) (hs : sS < s)
    (hW : 0 < p.V - p.cT - s ^ 2 * (p.cO + p.τ)) :
    1 - kappa p (s ^ 2) * (1 + s) ^ 2 < 1 - p.h / p.μ / (p.V - p.cO - p.τ) := by
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hE0 : 0 < p.V - p.cO - p.τ := by linarith
  have hss : sS * sS < s * s := mul_lt_mul'' hs hs hsS0.le hsS0.le
  have i1 : p.V * (sS * sS) < p.V * (s * s) := mul_lt_mul_of_pos_left hss hV
  have i2 : (p.V - p.cO - p.τ) * sS < (p.V - p.cO - p.τ) * s := mul_lt_mul_of_pos_left hs hE0
  have hlt : p.V - p.cT - s ^ 2 * (p.cO + p.τ) < (1 + s) ^ 2 * (p.V - p.cO - p.τ) := by nlinarith
  unfold kappa
  rw [div_mul_eq_mul_div (p.h / p.μ) _ ((1 + s) ^ 2), sub_lt_sub_iff_left, div_lt_div_iff₀ hE0 hW]
  have := mul_lt_mul_of_pos_left hlt ha
  nlinarith

lemma tp_perq (p : Params) (hp : p.Standing) (hR : 0 < p.R) (sD sS : ℝ) (hsD0 : 0 < sD)
    (hsD1 : sD < sS)
    (hsS : p.V * sS ^ 2 + 2 * (p.V - p.cO - p.τ) * sS = p.cO + p.τ - p.cT) (hDsD : tpD p sD = 0)
    (s : ℝ) (hs0 : 0 < s) (hadm : Admissible p (s ^ 2)) :
        (s ^ 2 < sS ^ 2 → IsMaxOn (revenue p (s ^ 2) p.R) (Set.Icc 0 1) (thetaStar p (s ^ 2))) ∧
        (sS ^ 2 < s ^ 2 → IsMaxOn (revenue p (s ^ 2) p.R) (Set.Icc 0 1) 0) ∧
        (s ^ 2 < sD ^ 2 → IsMaxOn (access p (s ^ 2)) (Set.Icc 0 1) (thetaStar p (s ^ 2))) ∧
        (sD ^ 2 < s ^ 2 → IsMaxOn (access p (s ^ 2)) (Set.Icc 0 1) 0) ∧
        (sD ^ 2 < s ^ 2 → s ^ 2 < sS ^ 2 →
          access p (s ^ 2) (thetaStar p (s ^ 2)) < access p (s ^ 2) 0 ∧
            revenue p (s ^ 2) p.R 0 < revenue p (s ^ 2) p.R (thetaStar p (s ^ 2))) := by
  have hsS0 : 0 < sS := lt_trans hsD0 hsD1
  have hp' := hp
  obtain ⟨hV, hcT, hcO, hτ, hh, hμ, hlam, hR0, h2, h3⟩ := hp'
  have ha : 0 < p.h / p.μ := div_pos hh hμ
  have hM : 0 < p.μ / p.lam := div_pos hμ hlam
  have hadm' := hadm
  obtain ⟨hq0, hq1, hk0, hk1, hE1, hord, -⟩ := hadm'
  have hsqrt : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs0.le
  rw [hsqrt] at hk1
  have hX0 : 0 ≤ 1 - kappa p (s ^ 2) * (1 + s) ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hk1; linarith
  have hW : 0 < p.V - p.cT - s ^ 2 * (p.cO + p.τ) := by
    have hk0' := hk0
    unfold kappa at hk0'
    rcases div_pos_iff.1 hk0' with h | h
    · exact h.2
    · linarith [h.1]
  have hlow := tp_low p hp sS s hsS0 hs0 hsS
  have hhigh := fun h => tp_high p hp sS s hsS0 hsS h hW
  have hacc_low : s < sD → 1 - p.h / p.μ / (p.V - p.cO - p.τ) <
      (1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2) := by
    intro hs
    have := tp_anti p hp sS hsS0 hsS s sD hs0.le hs hsD1.le
    unfold tpD at this hDsD
    linarith
  have hacc_high : sD < s → (1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2) <
      1 - p.h / p.μ / (p.V - p.cO - p.τ) := by
    intro hs
    rcases le_or_gt s sS with h | h
    · have := tp_anti p hp sS hsS0 hsS sD s hsD0.le hs h
      unfold tpD at this hDsD
      linarith
    · have h1 := hhigh h
      have h2 : (1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2) ≤
          1 - kappa p (s ^ 2) * (1 + s) ^ 2 := div_le_self hX0 (by nlinarith)
      linarith
  have hrev : ∀ θ, revenue p (s ^ 2) p.R θ =
      p.R * p.lam * ((eqProp p (s ^ 2) θ).1 + (1 + s ^ 2) * (eqProp p (s ^ 2) θ).2) := by
    intro θ; unfold revenue; ring
  have hacc : ∀ θ, access p (s ^ 2) θ =
      p.lam * ((eqProp p (s ^ 2) θ).1 + (eqProp p (s ^ 2) θ).2) := by
    intro θ; unfold access; ring
  have hz := tp_zero p hp (s ^ 2) hE1
  have hRl : 0 < p.R * p.lam := mul_pos hR hlam
  have hss_iff : s ^ 2 < sS ^ 2 → s < sS := fun h => by nlinarith
  have hss_iff' : sS ^ 2 < s ^ 2 → sS < s := fun h => by nlinarith
  have hsd_iff : s ^ 2 < sD ^ 2 → s < sD := fun h => by nlinarith
  have hsd_iff' : sD ^ 2 < s ^ 2 → sD < s := fun h => by nlinarith
  have hP : (0:ℝ) < 1 + s ^ 2 := by positivity
  have hstar_val : s < sS → (eqProp p (s ^ 2) (thetaStar p (s ^ 2))).1 +
      (1 + s ^ 2) * (eqProp p (s ^ 2) (thetaStar p (s ^ 2))).2 =
        p.μ / p.lam * (1 - kappa p (s ^ 2) * (1 + s) ^ 2) := by
    intro hs
    rw [tp_star p hp s hs0 hadm (hlow hs).1]
    simp only
    field_simp
    ring
  have hstar_acc : s < sS → (eqProp p (s ^ 2) (thetaStar p (s ^ 2))).1 +
      (eqProp p (s ^ 2) (thetaStar p (s ^ 2))).2 =
        p.μ / p.lam * ((1 - kappa p (s ^ 2) * (1 + s) ^ 2) / (1 + s ^ 2)) := by
    intro hs
    rw [tp_star p hp s hs0 hadm (hlow hs).1]
    simp only [zero_add]
  have hz1 : (eqProp p (s ^ 2) 0).1 + (1 + s ^ 2) * (eqProp p (s ^ 2) 0).2 =
      p.μ / p.lam * (1 - p.h / p.μ / (p.V - p.cO - p.τ)) := by
    rw [hz]; simp
  have hz2 : (eqProp p (s ^ 2) 0).1 + (eqProp p (s ^ 2) 0).2 =
      p.μ / p.lam * (1 - p.h / p.μ / (p.V - p.cO - p.τ)) := by
    rw [hz]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hq
    have hs := hss_iff hq
    rw [isMaxOn_iff]; intro θ hθ
    have b := (tp_bound p hp s hs0 hadm θ hθ).1
    rw [max_eq_right (hlow hs).2.le] at b
    rw [hrev, hrev, hstar_val hs]
    exact mul_le_mul_of_nonneg_left b hRl.le
  · intro hq
    have hs := hss_iff' hq
    rw [isMaxOn_iff]; intro θ hθ
    have b := (tp_bound p hp s hs0 hadm θ hθ).1
    rw [max_eq_left (hhigh hs).le] at b
    rw [hrev, hrev, hz1]
    exact mul_le_mul_of_nonneg_left b hRl.le
  · intro hq
    have hs := hsd_iff hq
    rw [isMaxOn_iff]; intro θ hθ
    have b := (tp_bound p hp s hs0 hadm θ hθ).2
    rw [max_eq_right (hacc_low hs).le] at b
    rw [hacc, hacc, hstar_acc (lt_trans hs hsD1)]
    exact mul_le_mul_of_nonneg_left b hlam.le
  · intro hq
    have hs := hsd_iff' hq
    rw [isMaxOn_iff]; intro θ hθ
    have b := (tp_bound p hp s hs0 hadm θ hθ).2
    rw [max_eq_left (hacc_high hs).le] at b
    rw [hacc, hacc, hz2]
    exact mul_le_mul_of_nonneg_left b hlam.le
  · intro hq1' hq2'
    have hs1 := hsd_iff' hq1'
    have hs2 := hss_iff hq2'
    constructor
    · rw [hacc, hacc, hstar_acc hs2, hz2]
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (hacc_high hs1) hM) hlam
    · rw [hrev, hrev, hstar_val hs2, hz1]
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (hlow hs2).2 hM) hRl

theorem proposition_4 (p : Params) (hp : p.Standing) (hR : 0 < p.R) :
    ∃ qdag qstar : ℝ, 0 < qdag ∧ qdag < qstar ∧ qstar < 1 ∧
      ∀ q : ℝ, Admissible p q →
        (q < qstar → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qstar < q → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) 0) ∧
        (q < qdag → IsMaxOn (access p q) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qdag < q → IsMaxOn (access p q) (Set.Icc 0 1) 0) ∧
        (qdag < q → q < qstar →
          access p q (thetaStar p q) < access p q 0 ∧
            revenue p q p.R 0 < revenue p q p.R (thetaStar p q)) := by
  obtain ⟨sD, sS, hsD0, hsD1, hsS1, hsS, hDsD⟩ := tp_thresholds p hp
  refine ⟨sD ^ 2, sS ^ 2, by positivity, by nlinarith, by nlinarith, ?_⟩
  intro q hadm
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ q = s ^ 2 :=
    ⟨Real.sqrt q, Real.sqrt_pos.2 hadm.1, (Real.sq_sqrt hadm.1.le).symm⟩
  exact tp_perq p hp hR sD sS hsD0 hsD1 hsS hDsD s hs0 hadm

end TelehealthParity.Access


-- Platform entry point: restates the target verbatim.
namespace TelehealthParity.Access

theorem _root_.solution (p : Params) (hp : p.Standing) (hR : 0 < p.R) :
    ∃ qdag qstar : ℝ, 0 < qdag ∧ qdag < qstar ∧ qstar < 1 ∧
      ∀ q : ℝ, Admissible p q →
        (q < qstar → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qstar < q → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) 0) ∧
        (q < qdag → IsMaxOn (access p q) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qdag < q → IsMaxOn (access p q) (Set.Icc 0 1) 0) ∧
        (qdag < q → q < qstar →
          access p q (thetaStar p q) < access p q 0 ∧
            revenue p q p.R 0 < revenue p q p.R (thetaStar p q)) := by
  apply @TelehealthParity.Access.proposition_4 <;> assumption

end TelehealthParity.Access
