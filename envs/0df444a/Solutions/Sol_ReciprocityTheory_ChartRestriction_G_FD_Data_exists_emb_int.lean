-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.exists_emb_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:29.659217+00:00
-- url     : https://prove2.me/submissions/0295a55c-3f8a-4c79-9f65-4e673e64ab4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_re_sum_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_exists_emb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (z : X.Ψ → ℂ) (g : ℕ) (hg : 0 < g)
    (hz : ∀ γ : 𝓞 E, ∃ k : ℤ, ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) *
      (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = k) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  have hN : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    have hne : ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hg.ne')
        (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)))
    refine ⟨(k : ℚ) / ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, mul_comm]
    exact hk
  obtain ⟨ω, hω⟩ := X.exists_emb_eq z hN
  refine ⟨ω, hω, ?_⟩
  have key : ∀ γ : 𝓞 E, ∃ k : ℤ,
      Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = k := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    refine ⟨k, ?_⟩
    have hs : ∑ τ : X.Ψ, z τ * τ.1 (γ : E) = ∑ τ : X.Ψ, τ.1 (ω * γ) :=
      Finset.sum_congr rfl fun τ _ => by rw [hω τ, map_mul]
    rw [hs, X.re_sum_Psi] at hk
    have htr : Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) =
        ((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) := by
      rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    rw [htr]
    have h2 : ((((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) : ℚ) : ℝ) =
        ((k : ℚ) : ℝ) := by
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast h2
  have hint := d4l2_dual_int' (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) key
  have e : (((g * (NumberField.discr E).natAbs ^ 2 : ℕ)) : E) * ω =
      ((NumberField.discr E).natAbs : E) * (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) := by
    push_cast
    ring
  rw [e]
  exact hint
end ReciprocityTheory.ChartRestriction.G.FD.Data
