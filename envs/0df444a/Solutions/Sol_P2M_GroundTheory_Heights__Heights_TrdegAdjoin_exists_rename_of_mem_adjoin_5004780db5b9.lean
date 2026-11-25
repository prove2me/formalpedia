-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:48.62895+00:00
-- url     : https://prove2.me/submissions/c4e55ced-6390-4d5c-bf5f-46fd41ac55db

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
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution {K κ : Type} [CommRing K] [Algebra ℚ K]
    {s : Set (MvPolynomial (Option κ) K)} (hs : ∀ r ∈ s, ∃ a, r = rename some a)
    {r : MvPolynomial (Option κ) K} (hr : r ∈ adjoin ℚ s) : ∃ a, r = rename some a := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap q => exact ⟨C (algebraMap ℚ K q), by rw [rename_C]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (map_add _ _ _).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, (map_mul _ _ _).symm⟩
end GroundTheory.Heights₂.Heights.TrdegAdjoin
