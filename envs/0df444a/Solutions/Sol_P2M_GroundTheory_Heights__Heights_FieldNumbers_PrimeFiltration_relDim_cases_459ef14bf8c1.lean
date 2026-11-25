-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:23.706269+00:00
-- url     : https://prove2.me/submissions/0c187ca3-cdc3-4724-b7a5-728a5af05eeb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {I Q : Ideal (MRing ι F)} [hQ : Q.IsPrime] (hIQ : I ≤ Q) :
    relDim Q < relDim I ∨ (Q ∈ I.minimalPrimes ∧ relDim Q = relDim I) := by
  have hmono : StrictMono (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.strictMono_map_iff.2 (WithTop.strictMono_map_iff.2 (fun a b h =>
      Int.sub_lt_sub_right (by exact_mod_cast h) _))
  have hle : ringKrullDim (MRing ι F ⧸ Q) ≤ ringKrullDim (MRing ι F ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIQ) (Ideal.Quotient.factor_surjective hIQ)
  by_cases hmin : Q ∈ I.minimalPrimes
  · rcases hle.lt_or_eq with h | h
    · exact Or.inl (hmono h)
    · exact Or.inr ⟨hmin, by simp only [relDim, h]⟩
  · left
    apply hmono
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have hW'p : W'.IsPrime := hW'.1.1
    have hlt : (⟨W', hW'p⟩ : PrimeSpectrum (MRing ι F)) < ⟨Q, hQ⟩ :=
      lt_of_le_of_ne hW'Q (fun h => hmin (by
        have : W' = Q := congrArg PrimeSpectrum.asIdeal h
        exact this ▸ hW'))
    have h1 := Order.coheight_add_one_le hlt
    have h2 : ringKrullDim (MRing ι F ⧸ W') ≤ ringKrullDim (MRing ι F ⧸ I) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'.1.2)
        (Ideal.Quotient.factor_surjective hW'.1.2)
    have h3 : ringKrullDim (MRing ι F ⧸ W') ≤ Nat.card (Σ k, ι k) :=
      (ringKrullDim_quotient_le W').trans (ringKrullDim_mvPolynomial_le F _)
    rw [ringKrullDim_quotient_prime W'] at h2 h3
    rw [ringKrullDim_quotient_prime Q]
    have h3' : Order.coheight (⟨W', hW'p⟩ : PrimeSpectrum (MRing ι F)) ≤
        (Nat.card (Σ k, ι k) : ℕ∞) := by
      exact_mod_cast h3
    have hfin : Order.coheight (⟨Q, hQ⟩ : PrimeSpectrum (MRing ι F)) ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at h1
      exact absurd (h1.trans h3') (not_le.mpr (ENat.natCast_lt_top _))
    have h4 := (ENat.add_one_le_iff hfin).1 h1
    exact lt_of_lt_of_le (by exact_mod_cast h4) h2
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
