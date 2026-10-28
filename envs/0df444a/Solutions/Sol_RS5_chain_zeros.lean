-- Prove2me | solution 1 for RS5.chain_zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:33:06.926733+00:00
-- url     : https://prove2.me/submissions/130d5616-48f7-4fa1-8a51-32fe98c73175

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Band
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ZetaReflection_exists_zero_of_sign_change
namespace XiLineZeros
end XiLineZeros
/-  RS5_Band.lean -- lane B5: the IVT corollary on Mathlib's `riemannZeta`, and the BAND certificate:
    K certified sign changes along a list of dyadic sample heights give K DISTINCT zeros of
    `riemannZeta` on the critical line, strictly inside the band.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `zeta_zero_of_completed_zero` : `Lambda(1/2+it) = 0 -> riemannZeta(1/2+it) = 0`
        (Mathlib's `riemannZeta_def_of_ne_zero`; `1/2+it ≠ 0`).
      * `exists_zeta_zero_of_signs` (IVT) : `t1 < t2` and opposite certified signs of
        `Re Lambda(1/2+it)` at `t1`, `t2` give `t in (t1, t2)` with `riemannZeta(1/2+it) = 0`
        (continuity of `t -> Re Lambda(1/2+it)` is `XiLineZeros.gLine_continuous`; `Lambda` is real
        on the line, `XiLineZeros.lambda_eq_gLine`; the IVT step is `ZetaReflection.exists_zero_of_sign_change`).
      * `chain_zeros` (generic) : along a `<`-chain of heights with known signs of `gLine`, the number of
        adjacent sign changes `chgBy` is EXACTLY the length of a strictly increasing list of on-line
        zeros strictly inside `(first, last)`.
      * `band_sound` : `bandOK (s0 :: rest) = true` gives a list `xs` with
            xs.length = chgBy Sample.pos (s0 :: rest),  xs strictly increasing,
            every x in xs in (s0.t, (lastOf s0 rest).t),
            completedRiemannZeta(1/2+ix) = 0  and  riemannZeta(1/2+ix) = 0.
        This is (with strict bounds) the on-line half `hLine` of `TuringBand.BandStatement`.
      * `band_sound_finset` : the same as a `Finset ℝ` of card = K.

    ## What this does NOT give (the remaining obligation, stated precisely)

    A band certificate is a LOWER count: at least K zeros of `riemannZeta` with real part 1/2 and
    ordinate in (t_0, t_k).  To conclude that ALL zeros with ordinate in the band lie on the line one
    needs the matching UPPER count -- the number N(t_k) - N(t_0) of zeros of `riemannZeta` in the
    rectangle {0 < Re s < 1, t_0 < Im s < t_k} (with multiplicity) is <= K -- which is the
    argument-principle / Riemann-von Mangoldt (Turing) count.  On this branch that count is NOT
    available; it lives on branch cl/arb3-h1000 (PR #613: ArgChange*, H1000*, AllZerosKernel_h1000)
    and cl/arb4 (PR #620), whose `TuringBand.BandStatement` consumes exactly the `hLine` list produced
    here.  Precisely, the remaining obligation for a band [T0, T1] certified here with K changes is:
        (edge non-vanishing of riemannZeta on the rectangle boundary)
      ∧ (enclosures of the five RvM edge argument-changes pinning the box count to K)
    i.e. the second antecedent of `TuringBand.BandStatement` with n = K.

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/


open Complex

namespace RS5

open XiLineZeros

noncomputable section

/-! ## 1. Lambda zeros on the line are riemannZeta zeros -/

theorem line_ne_zero' (t : ℝ) : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- `Lambda(1/2+it) = 0` implies `riemannZeta(1/2+it) = 0`. -/
theorem zeta_zero_of_completed_zero {t : ℝ} (h : completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0) :
    riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [riemannZeta_def_of_ne_zero (line_ne_zero' t), h, zero_div]

/-! ## 2. the IVT corollary -/

/-- One on-line zero of `riemannZeta` strictly inside `(a, b)` from a sign change of `gLine`. -/
theorem exists_zeta_zero_of_sign_change {a b : ℝ} (hab : a < b) (hsign : gLine a * gLine b < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (r : ℂ) * I) = 0 := by
  obtain ⟨r, h1, h2, h3⟩ := ZetaReflection.exists_zero_of_sign_change hab hsign
  exact ⟨r, h1, h2, h3, zeta_zero_of_completed_zero h3⟩



/-! ## 3. the generic chain lemma -/

section Generic

variable {α : Type} (tt : α → ℝ) (sg : α → Bool)

theorem le_lastOf : ∀ (a : α) (l : List α), List.IsChain (fun x y => tt x < tt y) (a :: l) →
    tt a ≤ tt (lastOf a l)
  | a, [], _ => le_refl _
  | a, b :: l, h => by
    rw [List.isChain_cons_cons] at h
    exact le_trans h.1.le (le_lastOf b l h.2)

theorem sign_mul_neg {x y : ℝ} {bx b2 : Bool} (hne : (bx == b2) = false)
    (hx : (bx = true → 0 < x) ∧ (bx = false → x < 0))
    (hy : (b2 = true → 0 < y) ∧ (b2 = false → y < 0)) : x * y < 0 := by
  cases bx <;> cases b2 <;> simp at hne
  · exact mul_neg_of_neg_of_pos (hx.2 rfl) (hy.1 rfl)
  · exact mul_neg_of_pos_of_neg (hx.1 rfl) (hy.2 rfl)



end Generic

/-! ## 4. the band certificate -/









/-! ## 5. band results as a Prop, gluing, and the three output shapes -/















end

end RS5


/-  RS5_Band.lean -- lane B5: the IVT corollary on Mathlib's `riemannZeta`, and the BAND certificate:
    K certified sign changes along a list of dyadic sample heights give K DISTINCT zeros of
    `riemannZeta` on the critical line, strictly inside the band.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `zeta_zero_of_completed_zero` : `Lambda(1/2+it) = 0 -> riemannZeta(1/2+it) = 0`
        (Mathlib's `riemannZeta_def_of_ne_zero`; `1/2+it ≠ 0`).
      * `exists_zeta_zero_of_signs` (IVT) : `t1 < t2` and opposite certified signs of
        `Re Lambda(1/2+it)` at `t1`, `t2` give `t in (t1, t2)` with `riemannZeta(1/2+it) = 0`
        (continuity of `t -> Re Lambda(1/2+it)` is `XiLineZeros.gLine_continuous`; `Lambda` is real
        on the line, `XiLineZeros.lambda_eq_gLine`; the IVT step is `ZetaReflection.exists_zero_of_sign_change`).
      * `chain_zeros` (generic) : along a `<`-chain of heights with known signs of `gLine`, the number of
        adjacent sign changes `chgBy` is EXACTLY the length of a strictly increasing list of on-line
        zeros strictly inside `(first, last)`.
      * `band_sound` : `bandOK (s0 :: rest) = true` gives a list `xs` with
            xs.length = chgBy Sample.pos (s0 :: rest),  xs strictly increasing,
            every x in xs in (s0.t, (lastOf s0 rest).t),
            completedRiemannZeta(1/2+ix) = 0  and  riemannZeta(1/2+ix) = 0.
        This is (with strict bounds) the on-line half `hLine` of `TuringBand.BandStatement`.
      * `band_sound_finset` : the same as a `Finset ℝ` of card = K.

    ## What this does NOT give (the remaining obligation, stated precisely)

    A band certificate is a LOWER count: at least K zeros of `riemannZeta` with real part 1/2 and
    ordinate in (t_0, t_k).  To conclude that ALL zeros with ordinate in the band lie on the line one
    needs the matching UPPER count -- the number N(t_k) - N(t_0) of zeros of `riemannZeta` in the
    rectangle {0 < Re s < 1, t_0 < Im s < t_k} (with multiplicity) is <= K -- which is the
    argument-principle / Riemann-von Mangoldt (Turing) count.  On this branch that count is NOT
    available; it lives on branch cl/arb3-h1000 (PR #613: ArgChange*, H1000*, AllZerosKernel_h1000)
    and cl/arb4 (PR #620), whose `TuringBand.BandStatement` consumes exactly the `hLine` list produced
    here.  Precisely, the remaining obligation for a band [T0, T1] certified here with K changes is:
        (edge non-vanishing of riemannZeta on the rectangle boundary)
      ∧ (enclosures of the five RvM edge argument-changes pinning the box count to K)
    i.e. the second antecedent of `TuringBand.BandStatement` with n = K.

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/


open Complex

section
namespace RS5
end RS5
open RS5

open XiLineZeros

noncomputable section

/-! ## 1. Lambda zeros on the line are riemannZeta zeros -/





/-! ## 2. the IVT corollary -/





/-! ## 3. the generic chain lemma -/

section Generic

variable {α : Type} (tt : α → ℝ) (sg : α → Bool)






theorem solution : ∀ (a : α) (l : List α),
    List.IsChain (fun x y => tt x < tt y) (a :: l) →
    (∀ p ∈ a :: l, (sg p = true → 0 < gLine (tt p)) ∧ (sg p = false → gLine (tt p) < 0)) →
    ∃ xs : List ℝ, xs.length = chgBy sg (a :: l) ∧ xs.IsChain (· < ·) ∧
      (∀ x ∈ xs, tt a < x ∧ x < tt (lastOf a l)) ∧
      (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
        riemannZeta (1 / 2 + (x : ℂ) * I) = 0)
  | a, [], _, _ => ⟨[], rfl, List.isChain_nil, by simp, by simp⟩
  | a, b :: l, hc, hs => by
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hab, hc'⟩ := hc
    obtain ⟨xs, hlen, hch, hb, hz⟩ :=
      solution b l hc' (fun p hp => hs p (List.mem_cons_of_mem a hp))
    have hlast : lastOf a (b :: l) = lastOf b l := rfl
    have hchg : chgBy sg (a :: b :: l) = (if sg a == sg b then 0 else 1) + chgBy sg (b :: l) := rfl
    rw [hlast, hchg]
    by_cases heq : (sg a == sg b) = true
    · refine ⟨xs, by rw [hlen, if_pos heq, zero_add], hch, ?_, hz⟩
      intro x hx
      exact ⟨lt_trans hab (hb x hx).1, (hb x hx).2⟩
    · have hne : (sg a == sg b) = false := by simpa using heq
      have hsg := sign_mul_neg hne (hs a List.mem_cons_self)
        (hs b (List.mem_cons_of_mem a List.mem_cons_self))
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_zeta_zero_of_sign_change hab hsg
      refine ⟨r :: xs, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, hlen, if_neg heq]; ring
      · rw [List.isChain_cons]
        refine ⟨?_, hch⟩
        intro y hy
        have hy' : y ∈ xs := List.mem_of_mem_head? hy
        exact lt_trans hr2 (hb y hy').1
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hr1, lt_of_lt_of_le hr2 (le_lastOf tt b l hc')⟩
        · exact ⟨lt_trans hab (hb x hx).1, (hb x hx).2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hr3, hr4⟩
        · exact hz x hx
