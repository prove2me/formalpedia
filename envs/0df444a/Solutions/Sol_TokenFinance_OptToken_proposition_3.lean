-- Prove2me | solution 1 for TokenFinance.OptToken.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T21:03:24.075996+00:00
-- url     : https://prove2.me/submissions/22cfe4ae-a796-4f44-973a-73bcc90e51e4

-- MIMO4 root reduction: TokenFinance.OptToken.proposition_3
-- (root theorem_id 5059da9e-2b1e-4889-88d0-0faddad04e63, mission 15df6dd1-b4ef-44b5-80f1-f46c416fdc7a)
-- Imports only Proved platform results (Theorems.Thm_TokenFinance_OptToken_*, all ACCEPTED):
--   eq_3 (NPV closed form), eq_13_14 / eq_15 / lemma_3 (payoff optimality at q^m),
--   eq_39_40 (StrictMono cubic + break-even bridge). The three remaining milestone
--   computations (eq_35_37, eq_16_lhs, eq_38_exists arguments) are inlined below.
-- Clause 1: q^m maximises tokEnt over all q >= 0 (case split on demand level).
-- Clause 2: E[I_t] = c t + int_c^theta (x-c)^2/(4theta) - int_{c+2t}^theta (1/theta)(c/(c+t))((x-c)/2-t)^2,
--           so E[I_t] = C0 + c t iff condition (16) holds.
-- Clause 3: IVT on the cubic rootPolynomial over [0, (theta-c)/2]; strict monotonicity
--           from eq_39_40 gives uniqueness.
-- Clause 4: eq_16_lhs closed form + break-even identity + eq_3 (NPV).
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_OptToken_RootPolynomial
import Theorems.Thm_TokenFinance_OptToken_eq_3
import Theorems.Thm_TokenFinance_OptToken_eq_13_14
import Theorems.Thm_TokenFinance_OptToken_eq_15
import Theorems.Thm_TokenFinance_OptToken_eq_39_40
import Theorems.Thm_TokenFinance_OptToken_lemma_3

open TokenFinance.OptToken

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hC0 : 0 < C0) (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    (∀ t : ℝ, 0 < t → ∀ x q : ℝ, 0 ≤ q →
      TokenFinance.Debt.tokEnt c t x q ≤ TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ∧
    (∀ t : ℝ, 0 < t → t < (θ - c) / 2 →
      (TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x)) = C0 + c * t ↔
        TokenFinance.Debt.tokenBreakEven c C0 θ t)) ∧
    (∃ t : ℝ, 0 < t ∧ t < (θ - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t ∧
      ∀ u : ℝ, 0 < u → TokenFinance.Debt.tokenBreakEven c C0 θ u → u = t) ∧
    (∀ t : ℝ, 0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t →
      TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) = TokenFinance.Debt.npv c C0 θ) := by
  have htheta : 0 < θ := lt_trans hc hcθ
  have hnθ : θ ≠ 0 := htheta.ne'
  have hnpveq : TokenFinance.Debt.npv c C0 θ = (θ - c) ^ 3 / (12 * θ) - C0 :=
    TokenFinance.OptToken.eq_3 c C0 θ hc hcθ
  have hnpvpos : 0 < (θ - c) ^ 3 / (12 * θ) - C0 := by linarith
  refine ⟨?_opt, ?_be, ?_ex, ?_final⟩

  · -- (1) the monopoly output q^m(x) maximises the entrepreneur's payoff tokEnt
    intro t ht x q _hq
    by_cases hhi : t < (x - c) / 2
    · -- high demand: q^m(x) = (x-c)/2 > t
      have h13 := TokenFinance.OptToken.eq_13_14 c t hc ht
      have hlem := TokenFinance.OptToken.lemma_3 c t hc ht
      rcases le_or_gt q t with hqt | hqt
      · -- q <= t: zero branch on the left; q^m's payoff is positive on the right
        have e1 : TokenFinance.Debt.tokEnt c t x q = 0 := by
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_neg (not_lt.mpr hqt)]
        have hpos := (h13.2 x hhi).2
        linarith
      · -- t < q: Lemma 3, both sides of which exceed tokEnt at q^m by the same c*t
        have hq2 := hlem.2.2 x q hhi hqt
        have hqm : TokenFinance.Debt.qm c x = (x - c) / 2 := max_eq_left (by linarith)
        have e1 : TokenFinance.Debt.tokEnt c t x q
            = (1 - TokenFinance.Debt.alphaT c t) * (q - t) * (x - q) - c * (q - t) := by
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_pos hqt]
        have e2 : TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
            = (1 - TokenFinance.Debt.alphaT c t) * ((x - c) / 2 - t) * (x - (x - c) / 2)
              - c * ((x - c) / 2 - t) := by
          rw [hqm]
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_pos hhi]
        linarith
    · -- low demand: (x-c)/2 <= t, hence q^m(x) <= t
      have hle : (x - c) / 2 ≤ t := not_lt.mp hhi
      have h15 := TokenFinance.OptToken.eq_15 c t hc ht x hle
      have hqlet : TokenFinance.Debt.qm c x ≤ t := by
        simp only [TokenFinance.Debt.qm]
        exact max_le hle (le_of_lt ht)
      rcases le_or_gt q t with hqt | hqt
      · -- q <= t: both sides take the zero branch
        have e1 : TokenFinance.Debt.tokEnt c t x q = 0 := by
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_neg (not_lt.mpr hqt)]
        have e2 : TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 := by
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_neg (not_lt.mpr hqlet)]
        linarith
      · -- t < q: eq_15 gives a negative payoff against q^m's zero payoff
        have hneg : TokenFinance.Debt.tokEnt c t x q < 0 := h15.2 q hqt
        have hz : TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 := h15.1
        linarith
  · intro t ht htwo
    have hupper : c + 2 * t ≤ θ := by linarith

    have hθ : 0 < θ := by linarith
    have hleθ : (0:ℝ) ≤ θ := hθ.le
    have hct : 0 < c + t := by linarith
    have hctne : c + t ≠ 0 := hct.ne'
    have hneθ : θ ≠ 0 := hθ.ne'
    -- (*) pointwise, on all of ℝ
    have hglob : ∀ x, TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x)
        = TokenFinance.Debt.pim c x + c * t -
          c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2 := by
      intro x
      rcases le_or_gt x c with hxc | hxc
      · -- x <= c: both q^m and pi^m vanish
        have hqm : TokenFinance.Debt.qm c x = 0 := by
          simp only [TokenFinance.Debt.qm]
          rw [max_eq_right (by linarith)]
        have hpim : TokenFinance.Debt.pim c x = 0 := by
          simp only [TokenFinance.Debt.pim]
          rw [max_eq_right (by linarith)]
          ring
        rw [hqm, hpim]
        simp only [TokenFinance.Debt.tokInv]
        rw [if_neg (not_lt.mpr (by linarith [ht]))]
        rw [show max ((0:ℝ) - t) 0 = 0 from max_eq_right (by linarith)]
        ring
      · have hqmp : TokenFinance.Debt.qm c x = (x - c) / 2 := by
          simp only [TokenFinance.Debt.qm]
          rw [max_eq_left (by linarith)]
        have hpimx : TokenFinance.Debt.pim c x = (x - c) ^ 2 / 4 := by
          simp only [TokenFinance.Debt.pim]
          rw [max_eq_left (by linarith)]
        rcases le_or_gt x (c + 2 * t) with h2 | h2
        · -- c <= x <= c+2t: q <= t, else-branch, max(q-t,0) = 0
          rw [hqmp, hpimx]
          simp only [TokenFinance.Debt.tokInv]
          rw [if_neg (not_lt.mpr (by linarith))]
          rw [show max ((x - c) / 2 - t) 0 = 0 from max_eq_right (by linarith)]
          ring
        · -- x > c+2t: t < q, if-branch, max(q-t,0) = q-t
          rw [hqmp, hpimx]
          simp only [TokenFinance.Debt.tokInv, TokenFinance.Debt.alphaT]
          rw [show max ((x - c) / 2 - t) 0 = (x - c) / 2 - t from max_eq_left (by linarith)]
          rw [if_pos (by linarith)]
          field_simp [hctne]
          ring
    -- continuity facts for integrability
    have hcontPim : Continuous (TokenFinance.Debt.pim c) := by
      unfold TokenFinance.Debt.pim
      fun_prop
    have hcontK : Continuous (fun x : ℝ => c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2) := by
      simp only [TokenFinance.Debt.qm]
      fun_prop
    have hA : IntervalIntegrable (fun x : ℝ => TokenFinance.Debt.pim c x + c * t)
        MeasureTheory.volume 0 θ :=
      (show Continuous (fun x : ℝ => TokenFinance.Debt.pim c x + c * t) by
        simp only [TokenFinance.Debt.pim]; fun_prop).intervalIntegrable _ _
    have hB : IntervalIntegrable
        (fun x : ℝ => c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2)
        MeasureTheory.volume 0 θ := hcontK.intervalIntegrable _ _
    have hA1 : IntervalIntegrable (TokenFinance.Debt.pim c) MeasureTheory.volume 0 θ :=
      hcontPim.intervalIntegrable _ _
    have hA2 : IntervalIntegrable (fun _ : ℝ => c * t) MeasureTheory.volume 0 θ :=
      intervalIntegrable_const
    -- pi^m integral: 0 below c, (x-c)^2/4 above
    have hpim_low : ∀ x ∈ Set.uIcc (0:ℝ) c, TokenFinance.Debt.pim c x = 0 := by
      intro x hx
      have hxc : x ≤ c := by
        rcases Set.mem_uIcc.mp hx with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · linarith [h]
      simp only [TokenFinance.Debt.pim]
      rw [max_eq_right (sub_nonpos_of_le hxc)]
      ring
    have hpim_mid : ∀ x ∈ Set.uIcc c θ, TokenFinance.Debt.pim c x = (x - c) ^ 2 / 4 := by
      intro x hx
      have hcx : c ≤ x := by
        rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · linarith [h, hleθ, hc]
      simp only [TokenFinance.Debt.pim]
      rw [max_eq_left (sub_nonneg_of_le hcx)]
    have hI_low : ∫ x in (0:ℝ)..c, TokenFinance.Debt.pim c x = 0 := by
      rw [intervalIntegral.integral_congr (fun x hx => hpim_low x hx)]
      exact intervalIntegral.integral_zero ..
    have hI_mid : ∫ x in c..θ, TokenFinance.Debt.pim c x = (θ - c) ^ 3 / 12 := by
      rw [intervalIntegral.integral_congr (fun x hx => hpim_mid x hx)]
      have hint : IntervalIntegrable (fun x : ℝ => (x - c) ^ 2 / 4) MeasureTheory.volume c θ :=
        (show Continuous (fun x : ℝ => (x - c) ^ 2 / 4) by fun_prop).intervalIntegrable c θ
      have hderiv : ∀ x ∈ Set.uIcc c θ,
          HasDerivAt (fun y : ℝ => (y - c) ^ 3 / 12) ((x - c) ^ 2 / 4) x := by
        intro x _
        have h3 := (((hasDerivAt_id' x).sub_const c).pow 3).div_const 12
        simp at h3
        convert h3 using 1 <;> first | rfl | (field_simp; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp
    have hsplit_pim : ∫ x in (0:ℝ)..θ, TokenFinance.Debt.pim c x
        = (∫ x in (0:ℝ)..c, TokenFinance.Debt.pim c x) + ∫ x in c..θ, TokenFinance.Debt.pim c x :=
      (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hcontPim.intervalIntegrable 0 c) (hcontPim.intervalIntegrable c θ)).symm
    have hmid : ∫ x in c..θ, (x - c) ^ 2 / 4 = (θ - c) ^ 3 / 12 := by
      rw [intervalIntegral.integral_congr (fun x hx => (hpim_mid x hx).symm)]
      exact hI_mid
    have hpim_eq : ∫ x in (0:ℝ)..θ, TokenFinance.Debt.pim c x
        = θ * ∫ x in c..θ, (x - c) ^ 2 / (4 * θ) := by
      rw [hsplit_pim, hI_low, zero_add, hI_mid, ← hmid]
      rw [← intervalIntegral.integral_const_mul θ]
      exact intervalIntegral.integral_congr (fun x _ => by field_simp [hneθ]; try ring)
    -- the constant part
    have hconst : ∫ x in (0:ℝ)..θ, c * t = θ * (c * t) := by
      rw [intervalIntegral.integral_const]
      simp
    -- the max part: supported on (c+2t, theta]
    have hK_zero : ∫ x in (0:ℝ)..(c + 2 * t),
        c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2 = 0 := by
      have hcong : ∀ x ∈ Set.uIcc (0:ℝ) (c + 2 * t),
          c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2 = 0 := by
        intro x hx
        have hxle : x ≤ c + 2 * t := by
          rw [Set.uIcc_of_le (by positivity)] at hx
          exact (Set.mem_Icc.mp hx).2
        have hle : TokenFinance.Debt.qm c x ≤ t := by
          simp only [TokenFinance.Debt.qm]
          exact max_le_iff.mpr ⟨by linarith, le_of_lt ht⟩
        rw [show max (TokenFinance.Debt.qm c x - t) 0 = 0 from max_eq_right (by linarith)]
        ring
      rw [intervalIntegral.integral_congr hcong]
      exact intervalIntegral.integral_zero ..
    have hK_up : ∫ x in (c + 2 * t)..θ,
        c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2
        = ∫ x in (c + 2 * t)..θ, c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
      have hcong : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
          c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2
            = c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
        intro x hx
        rw [Set.uIcc_of_le hupper] at hx
        have hxge : c + 2 * t ≤ x := (Set.mem_Icc.mp hx).1
        have hqm : TokenFinance.Debt.qm c x = (x - c) / 2 := by
          simp only [TokenFinance.Debt.qm]
          rw [max_eq_left (by linarith)]
        rw [hqm, show max ((x - c) / 2 - t) 0 = (x - c) / 2 - t from max_eq_left (by linarith)]
      rw [intervalIntegral.integral_congr hcong]
    have hK : ∫ x in (0:ℝ)..θ, c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2
        = θ * ∫ x in (c + 2 * t)..θ, 1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2) := by
      have hsplit : ∫ x in (0:ℝ)..θ,
          c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2
          = (∫ x in (0:ℝ)..(c + 2 * t), c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2) +
            ∫ x in (c + 2 * t)..θ, c / (c + t) * (max (TokenFinance.Debt.qm c x - t) 0) ^ 2 :=
        (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
          (hcontK.intervalIntegrable 0 (c + 2 * t)) (hcontK.intervalIntegrable (c + 2 * t) θ)).symm
      rw [hsplit, hK_zero, zero_add, hK_up]
      rw [← intervalIntegral.integral_const_mul θ]
      exact intervalIntegral.integral_congr (fun x _ => by field_simp [hneθ]; try ring)
    -- assemble the closed form of E[I_t]
    have hexpr : TokenFinance.Debt.expect θ
        (fun x => TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x))
        = c * t + (∫ x in c..θ, (x - c) ^ 2 / (4 * θ)) -
          ∫ x in (c + 2 * t)..θ, 1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2) := by
      simp only [TokenFinance.Debt.expect]
      rw [intervalIntegral.integral_congr (fun x _ => hglob x)]
      simp only [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_add hA1 hA2]
      rw [hpim_eq, hconst, hK]
      rw [div_eq_iff hneθ]
      ring
    -- the two remaining integrals in closed form
    have hAclosed : ∫ x in c..θ, (x - c) ^ 2 / (4 * θ) = (θ - c) ^ 3 / (12 * θ) := by
      have hcong : ∀ x ∈ Set.uIcc c θ, (x - c) ^ 2 / (4 * θ) = 1 / θ * ((x - c) ^ 2 / 4) := by
        intro x _
        field_simp [hneθ]
        try ring
      rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const_mul, hmid]
      field_simp [hneθ]
      try ring
    have hKbase : ∫ x in (c + 2 * t)..θ, c / (c + t) * ((x - c) / 2 - t) ^ 2
        = c / (c + t) * (2 / 3) * ((θ - c) / 2 - t) ^ 3 := by
      have hder : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
          HasDerivAt (fun y : ℝ => c / (c + t) * (2 / 3) * ((y - c) / 2 - t) ^ 3)
            (c / (c + t) * ((x - c) / 2 - t) ^ 2) x := by
        intro x _
        have hb : HasDerivAt (fun y : ℝ => (y - c) / 2 - t) (1 / 2 : ℝ) x := by
          have h := ((hasDerivAt_id' x).sub_const c).div_const 2
          simpa using (h.sub_const t)
        have hmul := (hb.pow 3).const_mul (c / (c + t) * (2 / 3))
        convert hmul using 1 <;> first | rfl | (field_simp [hctne]; ring)
      have hhint : IntervalIntegrable
          (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) MeasureTheory.volume (c + 2 * t) θ :=
        (show Continuous (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) by fun_prop).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hhint]
      have hzz : ((c + 2 * t - c) / 2 - t) = 0 := by ring
      rw [hzz]
      ring
    have hKclosed : ∫ x in (c + 2 * t)..θ,
        1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2)
        = c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 := by
      have hpull : ∫ x in (c + 2 * t)..θ,
          1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2)
          = 1 / θ * ∫ x in (c + 2 * t)..θ, c / (c + t) * ((x - c) / 2 - t) ^ 2 :=
        intervalIntegral.integral_const_mul (1 / θ)
          (fun x => c / (c + t) * ((x - c) / 2 - t) ^ 2)
      rw [hpull, hKbase]
      field_simp [hneθ, hctne]
      try ring
    constructor
    · intro h
      rw [hexpr, hAclosed, hKclosed] at h
      rw [TokenFinance.Debt.tokenBreakEven]
      linarith
    · intro h
      rw [TokenFinance.Debt.tokenBreakEven] at h
      rw [hexpr, hAclosed, hKclosed]
      linarith
  · -- (3) existence and uniqueness of the interior break-even token size
    have hstrict : StrictMono (TokenFinance.OptToken.rootPolynomial c C0 θ) :=
      (TokenFinance.OptToken.eq_39_40 c C0 θ hc hcθ hnpv).1
    have hbridge : ∀ t : ℝ, -c < t →
        (TokenFinance.Debt.tokenBreakEven c C0 θ t ↔
          TokenFinance.OptToken.rootPolynomial c C0 θ t = 0) :=
      (TokenFinance.OptToken.eq_39_40 c C0 θ hc hcθ hnpv).2
    have hmpos : 0 < (θ - c) / 2 := by linarith
    have hf0 : TokenFinance.OptToken.rootPolynomial c C0 θ 0 = -θ / 2 * C0 := by
      simp only [TokenFinance.OptToken.rootPolynomial]
      ring
    have hfd_pos : TokenFinance.OptToken.rootPolynomial c C0 θ ((θ - c) / 2)
        = θ * TokenFinance.Debt.npv c C0 θ * (((θ - c) / 2) / (2 * c) + 1 / 2) := by
      simp only [TokenFinance.OptToken.rootPolynomial]
      rw [hnpveq]
      field_simp [hc.ne', hnθ]
      ring
    have hpos2 : 0 < ((θ - c) / 2) / (2 * c) + 1 / 2 := by
      have h1 : 0 < (θ - c) / 2 := by linarith
      have h2 : 0 < 2 * c := by linarith
      have h3 : 0 < ((θ - c) / 2) / (2 * c) := div_pos h1 h2
      linarith
    have hcontf : ContinuousOn (TokenFinance.OptToken.rootPolynomial c C0 θ)
        (Set.Icc 0 ((θ - c) / 2)) := by
      have hC : Continuous (fun t : ℝ => TokenFinance.OptToken.rootPolynomial c C0 θ t) := by
        simp only [TokenFinance.OptToken.rootPolynomial]
        fun_prop
      exact hC.continuousOn
    have hmemf : (0:ℝ) ∈ Set.Icc (TokenFinance.OptToken.rootPolynomial c C0 θ 0)
        (TokenFinance.OptToken.rootPolynomial c C0 θ ((θ - c) / 2)) := by
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · rw [hf0]
        linarith [mul_nonneg htheta.le hC0.le]
      · rw [hfd_pos]
        have hz := mul_pos (mul_pos htheta hnpv) hpos2
        linarith
    obtain ⟨tm, htmem, htroot⟩ := intermediate_value_Icc (le_of_lt hmpos) hcontf hmemf
    have ht0 : 0 < tm := by
      rcases htmem with ⟨hle, _⟩
      rcases eq_or_lt_of_le hle with h | h
      · subst h
        rw [hf0] at htroot
        have hpos := mul_pos htheta hC0
        linarith
      · exact h
    have htd : tm < (θ - c) / 2 := by
      rcases htmem with ⟨_, hge⟩
      rcases eq_or_lt_of_le hge with h | h
      · subst h
        rw [hfd_pos] at htroot
        have hz := mul_pos (mul_pos htheta hnpv) hpos2
        linarith
      · exact h
    refine ⟨tm, ht0, htd, ?_, ?_⟩
    · rw [hbridge tm (by linarith)]
      exact htroot
    · intro u hu hbe
      have hbu : TokenFinance.OptToken.rootPolynomial c C0 θ u = 0 :=
        (hbridge u (by linarith)).mp hbe
      exact hstrict.injective (hbu.trans htroot.symm)
  · -- (4) at any break-even size the expected entrepreneur profit equals NPV
    intro t ht hbe
    rw [TokenFinance.Debt.tokenBreakEven] at hbe
    by_cases hupper : c + 2 * t ≤ θ
    · have h16 : TokenFinance.Debt.expect θ
            (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) =
          c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 := by
        have hθ : 0 < θ := by linarith
        have hct : 0 < c + t := by linarith
        have hctne : c + t ≠ 0 := hct.ne'
        have hneθ : θ ≠ 0 := hθ.ne'
        have hm0 : (0:ℝ) ≤ c + 2 * t := by positivity
        -- Below the threshold the monopolist output does not exceed t, so the payoff is 0
        have hzero : ∀ x, x ≤ c + 2 * t →
            TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 := by
          intro x hx
          have hle : TokenFinance.Debt.qm c x ≤ t := by
            simp only [TokenFinance.Debt.qm]
            exact max_le_iff.mpr ⟨by linarith, le_of_lt ht⟩
          simp only [TokenFinance.Debt.tokEnt]
          rw [if_neg (not_lt.mpr hle)]
        -- Above the threshold the payoff is the exact square (c/(c+t))((x-c)/2 - t)^2
        have hpos : ∀ x, c + 2 * t < x →
            TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
              = c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
          intro x hx
          have hqm : TokenFinance.Debt.qm c x = (x - c) / 2 := by
            simp only [TokenFinance.Debt.qm]
            rw [max_eq_left (by linarith)]
          have hgt : t < TokenFinance.Debt.qm c x := by
            rw [hqm]; linarith
          simp only [TokenFinance.Debt.tokEnt, TokenFinance.Debt.alphaT]
          rw [if_pos hgt, hqm]
          field_simp [hctne]
          ring
        -- unified max-form of the pointwise description
        have hmax : ∀ x, TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
            = c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 := by
          intro x
          rcases le_or_gt ((x - c) / 2) t with h | h
          · rw [hzero x (by linarith)]
            rw [show max ((x - (c + 2 * t)) / 2) 0 = 0 from max_eq_right (by linarith)]
            ring
          · rw [hpos x (by linarith)]
            have hident : (x - (c + 2 * t)) / 2 = (x - c) / 2 - t := by ring
            rw [hident, max_eq_left (show 0 ≤ (x - c) / 2 - t from by linarith)]
        have hMcont : Continuous
            (fun x : ℝ => c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) := by fun_prop
        simp only [TokenFinance.Debt.expect]
        rw [intervalIntegral.integral_congr (fun x _ => hmax x)]
        have hsplit :
            (∫ x in (0:ℝ)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) =
              (∫ x in (0:ℝ)..(c + 2 * t), c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) +
                (∫ x in (c + 2 * t)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) :=
          (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
            (hMcont.intervalIntegrable 0 (c + 2 * t)) (hMcont.intervalIntegrable (c + 2 * t) θ)).symm
        have hI1 : ∫ x in (0:ℝ)..(c + 2 * t), c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 = 0 := by
          have hcong : ∀ x ∈ Set.uIcc (0:ℝ) (c + 2 * t),
              c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 = 0 := by
            intro x hx
            have hxle : x ≤ c + 2 * t := by
              rw [Set.uIcc_of_le hm0] at hx
              exact (Set.mem_Icc.mp hx).2
            have hzz : max ((x - (c + 2 * t)) / 2) 0 = 0 := max_eq_right (by linarith)
            rw [hzz]
            ring
          rw [intervalIntegral.integral_congr hcong]
          exact intervalIntegral.integral_zero ..
        have hI2 : ∫ x in (c + 2 * t)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2
            = c / (c + t) * (2 / 3) * ((θ - c) / 2 - t) ^ 3 := by
          have hcong : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
              c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2
                = c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
            intro x hx
            rw [Set.uIcc_of_le hupper] at hx
            have hxge : c + 2 * t ≤ x := (Set.mem_Icc.mp hx).1
            have hident : (x - (c + 2 * t)) / 2 = (x - c) / 2 - t := by ring
            have hnn : 0 ≤ (x - c) / 2 - t := by linarith
            rw [hident, max_eq_left hnn]
          rw [intervalIntegral.integral_congr hcong]
          have hder : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
              HasDerivAt (fun y : ℝ => c / (c + t) * (2 / 3) * ((y - c) / 2 - t) ^ 3)
                (c / (c + t) * ((x - c) / 2 - t) ^ 2) x := by
            intro x _
            have hb : HasDerivAt (fun y : ℝ => (y - c) / 2 - t) (1 / 2 : ℝ) x := by
              have h := ((hasDerivAt_id' x).sub_const c).div_const 2
              simpa using (h.sub_const t)
            have hmul := (hb.pow 3).const_mul (c / (c + t) * (2 / 3))
            convert hmul using 1 <;> first | rfl | (field_simp [hctne]; ring)
          have hhint : IntervalIntegrable
              (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) MeasureTheory.volume (c + 2 * t) θ :=
            (show Continuous (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) by fun_prop).intervalIntegrable _ _
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hhint]
          have hzz : ((c + 2 * t - c) / 2 - t) = 0 := by ring
          rw [hzz]
          ring
        rw [hsplit, hI1, zero_add, hI2]
        field_simp [hneθ, hctne]
      rw [h16, hnpveq]
      linarith
    · -- impossible: t > (theta-c)/2 would make the break-even LHS negative while NPV > 0
      exfalso
      have hlt0 : (θ - c) / 2 - t < 0 := by linarith
      have key : ((θ - c) / 2 - t) ^ 3 = ((θ - c) / 2 - t) ^ 2 * ((θ - c) / 2 - t) := by ring
      have hcube : ((θ - c) / 2 - t) ^ 3 < 0 := by
        rw [key]
        exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (ne_of_lt hlt0)) hlt0
      have hcpos : 0 < c / (c + t) := div_pos hc (by linarith)
      have htpos : 0 < 2 / (3 * θ) := div_pos (by linarith) (by linarith)
      have hprod : 0 < c / (c + t) * (2 / (3 * θ)) := mul_pos hcpos htpos
      have hlhs : c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 < 0 :=
        mul_neg_of_pos_of_neg hprod hcube
      linarith
