-- Prove2me | solution 1 for TokenFinance.OptToken.eq_35_37
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T21:03:21.509984+00:00
-- url     : https://prove2.me/submissions/1d4bb677-a378-4cc2-9fe8-866fe5fce73b

-- MIMO4 solution for TokenFinance.OptToken.eq_35_37 (theorem_id b680e67b-7dbb-43ae-b71e-f7884dc2d9a4)
-- Investor break-even integrals, (35) => (37). The key device is a single closed form for the
-- investor's payoff at the monopoly output, valid for every demand x:
--
--   tokInv c t x q^m(x) = pi^m(x) + c t - (c/(c+t)) (max (q^m(x) - t, 0))^2.      (*)
--
-- Verification of (*): put q = q^m(x).
--  * x <= c: q = 0, the definition takes its else-branch, so tokInv = 0 + c t, while pi^m = 0
--    and max(q-t,0) = 0 (as t > 0) — both sides are c t.
--  * c <= x <= c+2t: q = (x-c)/2 <= t, else-branch, tokInv = q(x-q) + c(t-q); since
--    x - 2q = c this equals q^2 + c t = pi^m + c t (and max(q-t,0) = 0).
--  * x > c+2t: t < q, if-branch, tokInv = (1-alpha_t)(q-t)(x-q) - c(q-t) with
--    1 - alpha_t = c/(c+t) and x-q-(c+t) = q-t, i.e. (c/(c+t))(q-t)^2 - c(q-t) + c t... which
--    rearranges to q^2 + c t - (c/(c+t))(q-t)^2, again (*).
-- Integrating (*) over (0, theta), using pi^m = 0 below c and (max(q-t,0))^2 = 0 up to c+2t,
-- gives  E[I_t] = c t + int_c^theta (x-c)^2/(4 theta) - int_{c+2t}^theta (1/theta)(c/(c+t))((x-c)/2-t)^2 ,
-- which is exactly the asserted equivalence with (37) after subtracting c t.
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

theorem solution (c C0 θ t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hupper : c + 2 * t ≤ θ) :
    (TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x)) = C0 + c * t) ↔
      C0 = (∫ x in c..θ, (x - c) ^ 2 / (4 * θ)) -
        ∫ x in (c + 2 * t)..θ,
          1 / θ * (c / (c + t) * ((x - c) / 2 - t) ^ 2) := by
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
  constructor
  · intro h
    rw [hexpr] at h
    linarith
  · intro h
    rw [hexpr]
    linarith
