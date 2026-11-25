-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:50.215546+00:00
-- url     : https://prove2.me/submissions/98fb8bdb-661c-4ef0-8974-44f05aec84af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω)
    (ht : AlgebraicIndependent ℚ t) (htL : ∀ i, t i ∈ ratioField y c)
    (halg : ∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) :
    Algebra.trdeg ℤ (ratioField y c) = d := by
  set L := ratioField y c
  let t' : Fin d → L := fun i ↦ ⟨t i, htL i⟩
  have hind : AlgebraicIndependent ℚ t' := AlgebraicIndependent.of_comp L.val ht
  set F := IntermediateField.adjoin ℚ (Set.range t)
  have hLe : L ≤ (algebraicClosure F Ω).restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    intro r hr
    exact (IntermediateField.mem_restrictScalars _).mpr
      ((mem_algebraicClosure_iff).mpr (halg r hr))
  have hbasis : IsTranscendenceBasis ℚ t' := by
    refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun x ↦ ?_⟩
    by_contra hx
    have h1 : AlgebraicIndependent ℚ (fun o : Option (Fin d) ↦ o.elim x t') :=
      (hind.option_iff_transcendental x).mpr hx
    have h2 : AlgebraicIndependent ℚ (fun o : Option (Fin d) ↦ o.elim (x : Ω) t) := by
      have h3 := h1.map' (f := L.val) (fun a b hab ↦ Subtype.ext hab)
      convert h3 using 1
      funext o
      cases o <;> rfl
    refine (ht.option_iff_transcendental (x : Ω)).mp h2 ?_
    have hxF : IsAlgebraic F (x : Ω) :=
      (mem_algebraicClosure_iff).mp
        ((IntermediateField.mem_restrictScalars _).mp (hLe x.2))
    exact (IntermediateField.isAlgebraic_adjoin_iff).mp hxF
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have hZ : IsTranscendenceBasis ℤ t' := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).mpr hbasis
  rw [← hZ.cardinalMk_eq_trdeg, Cardinal.mk_fin]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
