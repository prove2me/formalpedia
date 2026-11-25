-- Prove2me | solution 1 for SNumbers.allSNumbers_eq_on_HilbertSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:40.970219+00:00
-- url     : https://prove2.me/submissions/e6fca51b-7900-4237-8e82-15604f8ca84a

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_Uniqueness
public import Theorems.Thm_SNumbers_approximationNumber_le_sn
public import Theorems.Thm_SNumbers_sn_le_approximationNumber


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
    s S n = approximationNumber S n :=
  le_antisymm (sn_le_approximationNumber hs S n) (approximationNumber_le_sn hs S n)
end SNumbers
