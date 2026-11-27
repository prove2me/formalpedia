-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_C_of_mem_adjoin_d114cee15beb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:10:59.935839+00:00
-- url     : https://prove2.me/submissions/6548085a-f3b0-4e6b-bd50-4360470e1b4c

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {M : Type} [CommRing M] [IsDomain M] [Algebra ℚ M]
omit [IsDomain M]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution {s : Set (Polynomial M)} (hs : ∀ r ∈ s, ∃ a, r = Polynomial.C a)
    {r : Polynomial M} (hr : r ∈ adjoin ℚ s) : ∃ a, r = Polynomial.C a := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap q => exact ⟨algebraMap ℚ M q, Polynomial.algebraMap_apply q⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (Polynomial.C_add).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, (Polynomial.C_mul).symm⟩
end GroundTheory.Heights₂.Heights.TrdegAdjoin
