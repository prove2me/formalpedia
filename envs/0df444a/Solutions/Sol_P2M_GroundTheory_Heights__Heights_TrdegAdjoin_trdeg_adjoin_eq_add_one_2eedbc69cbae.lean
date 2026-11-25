-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:48.511428+00:00
-- url     : https://prove2.me/submissions/e5182444-ad63-43c7-b73d-b62d58486ba6

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d

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
theorem _root_.solution {Y Z : Set L} {e : L} (hYZ : Y ⊆ Z) (heZ : e ∈ Z)
    (he : Transcendental (adjoin R Y) e)
    (halg : ∀ z ∈ Z, IsAlgebraic (adjoin R (insert e Y)) z)
    {s : ℕ} (hs : Algebra.trdeg R (adjoin R Y) = s) :
    Algebra.trdeg R (adjoin R Z) = s + 1 := by
  set A := adjoin R Y
  have : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (algebraMap R A).injective
  obtain ⟨κ, x, hx⟩ := exists_isTranscendenceBasis' R A
  have hκ : #κ = s := hx.cardinalMk_eq_trdeg.trans hs
  set b₀ : κ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent R b₀ := hx.1.map' Subtype.val_injective
  have hb₀A : ∀ i, b₀ i ∈ A := fun i ↦ (x i).2
  have hle : adjoin R (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr hb₀A)
  have hY : ∀ y ∈ Y, IsAlgebraic (adjoin R (Set.range b₀)) y := by
    intro y hy
    have h1 := hx.isAlgebraic.isAlgebraic (⟨y, subset_adjoin hy⟩ : A)
    exact (isAlgebraic_adjoin_range_iff A x ⟨y, subset_adjoin hy⟩).mpr h1
  let b : Option κ → L := fun o ↦ o.elim e b₀
  have hind : AlgebraicIndependent R b :=
    AlgebraicIndependent.option_iff.mpr ⟨hb₀, fun h ↦ he (h.tower_top_of_subalgebra_le hle)⟩
  have hrange : Set.range b₀ ⊆ Set.range b := fun _ ⟨i, hi⟩ ↦ ⟨some i, hi⟩
  have heb : e ∈ Set.range b := ⟨none, rfl⟩
  have hleb : adjoin R (Set.range b₀) ≤ adjoin R (Set.range b) := adjoin_mono hrange
  have hmem : ∀ o, b o ∈ adjoin R Z := by
    rintro (_ | i)
    · exact subset_adjoin heZ
    · exact adjoin_mono hYZ (hb₀A i)
  have key := trdeg_adjoin_eq hmem hind fun z hz ↦ by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (s := insert e Y) ?_ (halg z hz)
    rintro w ⟨hw, hwb⟩
    rcases hw with rfl | hw
    · exact absurd heb hwb
    · exact (hY w hw).tower_top_of_subalgebra_le hleb
  rw [key, Cardinal.mk_option, hκ]
end GroundTheory.Heights₂.Heights.TrdegAdjoin
