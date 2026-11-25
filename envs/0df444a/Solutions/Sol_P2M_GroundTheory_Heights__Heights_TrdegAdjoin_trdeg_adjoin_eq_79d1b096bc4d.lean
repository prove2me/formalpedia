-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:27.007813+00:00
-- url     : https://prove2.me/submissions/28bb80a0-1eaf-4c66-8fc6-a5a78631e0c7

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61

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
variable {R L : Type} [Field R] [CommRing L] [IsDomain L] [Algebra R L]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution {s : Set L} {κ : Type} {b : κ → L} (hb : ∀ i, b i ∈ adjoin R s)
    (hind : AlgebraicIndependent R b)
    (halg : ∀ z ∈ s, IsAlgebraic (adjoin R (Set.range b)) z) :
    Algebra.trdeg R (adjoin R s) = #κ := by
  set A := adjoin R s
  let b' : κ → A := fun i ↦ ⟨b i, hb i⟩
  have hind' : AlgebraicIndependent R b' := AlgebraicIndependent.of_comp A.val hind
  have halg' : Algebra.IsAlgebraic (adjoin R (Set.range b')) A := by
    refine ⟨fun a ↦ ?_⟩
    rw [← isAlgebraic_adjoin_range_iff A b' a]
    have hcomp : A.val ∘ b' = b := rfl
    rw [hcomp]
    exact IsAlgebraic.adjoin_of_forall_isAlgebraic (s := s) (fun z hz ↦ halg z hz.1)
      (isAlgebraic_algebraMap (R := A) a)
  exact ((hind'.isTranscendenceBasis_iff_isAlgebraic).mpr halg').cardinalMk_eq_trdeg.symm
end GroundTheory.Heights₂.Heights.TrdegAdjoin
