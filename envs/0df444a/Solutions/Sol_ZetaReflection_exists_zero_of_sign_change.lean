-- Prove2me | solution 1 for ZetaReflection.exists_zero_of_sign_change
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:30:43.80783+00:00
-- url     : https://prove2.me/submissions/1a1a5efe-a395-4085-a691-e90fe67339f9

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Theorems.Thm_XiLineZeros_gLine_continuous
import Theorems.Thm_ZetaZeroLocalization_completedZeta_im_eq_zero
namespace XiLineZeros
end XiLineZeros
namespace ZetaZeroLocalization
end ZetaZeroLocalization
/- telperion 0.1.6 | family XiLineZeros | input-hash 8bf933124b3cae44
   3 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/




open Complex

namespace XiLineZeros

/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.


-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).




-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.


-- On the line, Lambda equals its real part promoted to ℂ.
theorem lambda_eq_gLine (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = (gLine t : ℂ) := by
  have him : (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).im = 0 :=
    ZetaZeroLocalization.completedZeta_im_eq_zero t
  apply Complex.ext
  · rfl
  · rw [him]; simp [gLine]










end XiLineZeros


/-  SignChain.lean -- A2 Theorem 7: the alternating-sign-chain → hLine lemma.

    Generalizes the per-instance IVT pattern of `XiLineZeros` (lambda_zero_*, lambda_two_zeros_*,
    lambda_five_zeros_*) into ONE lemma parameterized by an arbitrary grid of `n+1` points:

        alternating_signs_chain

    Given `n+1` strictly increasing grid points `p₀ < p₁ < … < pₙ` in `[T0, T1]` at which the
    real critical-line function `gLine` takes strictly sign-alternating values (encoded as the
    single per-interval condition `gLine pᵢ · gLine pᵢ₊₁ < 0`), it produces the VERBATIM T5
    `hLine` shape (see `TuringBand.BandStatement`):

        ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
          (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
          (∀ t ∈ xs, completedRiemannZeta (1/2 + t·I) = 0)

    Each of the `n` consecutive sign-change subintervals yields, by the intermediate value
    theorem on the continuous `gLine`, one interior zero; strict monotonicity of the grid
    orders the zeros into a `<`-chain.  A reflected sign-sweep (kernel-checked rational bounds
    on `gLine` at the grid points, of alternating sign) discharges `hLine` through this lemma.

    conjecture1_proved = False.
-/



open Complex ZetaZeroLocalization XiLineZeros

section
namespace ZetaReflection
end ZetaReflection
open ZetaReflection


theorem solution {a b : ℝ} (hab : a < b)
    (hsign : gLine a * gLine b < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  have hcont : ContinuousOn gLine (Set.Icc a b) := gLine_continuous.continuousOn
  -- opposite signs: either  gLine a < 0 < gLine b  or  gLine b < 0 < gLine a
  rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · -- gLine a > 0, gLine b < 0  → use intermediate_value_Icc'
    have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) hcont ⟨le_of_lt hnb, le_of_lt hpa⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpa)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hnb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp
  · -- gLine a < 0, gLine b > 0  → use intermediate_value_Icc
    have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) hcont ⟨le_of_lt hna, le_of_lt hpb⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hna)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp
