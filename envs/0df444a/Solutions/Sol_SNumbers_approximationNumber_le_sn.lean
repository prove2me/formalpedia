-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:21:41.654726+00:00
-- url     : https://prove2.me/submissions/7854dc7a-d813-4586-9e5c-fe12de2a4697

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_Uniqueness
public import Theorems.Thm_SNumbers_le_sn_of_lt_approximationNumber
public import Theorems.Thm_SNumbers_approximationNumber_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber S n ≤ s S n := by
  by_contra h
  rw [not_le] at h
  have ht0 : 0 ≤ s S n := hs.nonneg S n
  have ha0 : 0 ≤ approximationNumber S n := approximationNumber_nonneg S n
  have hc0 : 0 ≤ (s S n + approximationNumber S n) / 2 := by linarith
  have hca : (s S n + approximationNumber S n) / 2 < approximationNumber S n := by linarith
  have hkey := le_sn_of_lt_approximationNumber hs S n hc0 hca
  linarith
end SNumbers
