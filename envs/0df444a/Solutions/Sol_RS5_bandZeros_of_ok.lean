-- Prove2me | solution 1 for RS5.bandZeros_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:52:10.121652+00:00
-- url     : https://prove2.me/submissions/159e619e-327c-4398-96bb-6d709b2d12ca

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
import Theorems.Thm_RS5_chain_zeros
import Theorems.Thm_RS5_sampleOK_sign
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





/-! ## 2. the IVT corollary -/





/-! ## 3. the generic chain lemma -/

section Generic

variable {α : Type} (tt : α → ℝ) (sg : α → Bool)







end Generic

/-! ## 4. the band certificate -/

theorem ltH_real {s s' : Sample} (h : ltH s s' = true) : s.t < s'.t := by
  unfold ltH at h
  rw [decide_eq_true_eq] at h
  have h' : ((s.tn * 2 ^ s'.tq : ℕ) : ℝ) < ((s'.tn * 2 ^ s.tq : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  unfold Sample.t
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact h'

theorem bandOK_facts : ∀ (s : Sample) (rest : List Sample), bandOK (s :: rest) = true →
    List.IsChain (fun x y => Sample.t x < Sample.t y) (s :: rest) ∧
      ∀ p ∈ s :: rest, sampleOK p = true
  | s, [], h => ⟨List.isChain_singleton s, by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact h⟩
  | s, s' :: rest, h => by
    have h' : (sampleOK s && ltH s s' && bandOK (s' :: rest)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := bandOK_facts s' rest h3
    refine ⟨List.isChain_cons_cons.mpr ⟨ltH_real h2, ih1⟩, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h1
    · exact ih2 p hp

/-- **The band certificate (soundness).**  If the kernel accepts the sample list, the number `K` of
    adjacent sign changes yields `K` DISTINCT zeros of `riemannZeta` on the critical line, listed in
    strictly increasing order, with ordinates STRICTLY inside `(t_0, t_k)`. -/
theorem band_sound (s0 : Sample) (rest : List Sample) (h : bandOK (s0 :: rest) = true) :
    ∃ xs : List ℝ, xs.length = chgBy Sample.pos (s0 :: rest) ∧ xs.IsChain (· < ·) ∧
      (∀ x ∈ xs, s0.t < x ∧ x < (lastOf s0 rest).t) ∧
      (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
        riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := by
  obtain ⟨hc, hs⟩ := bandOK_facts s0 rest h
  exact chain_zeros Sample.t Sample.pos s0 rest hc (fun p hp => sampleOK_sign (hs p hp))



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







end Generic

/-! ## 4. the band certificate -/









/-! ## 5. band results as a Prop, gluing, and the three output shapes -/



theorem solution (s0 : Sample) (rest : List Sample) (h : bandOK (s0 :: rest) = true) :
    BandZeros s0.t (lastOf s0 rest).t (chgBy Sample.pos (s0 :: rest)) :=
  band_sound s0 rest h
