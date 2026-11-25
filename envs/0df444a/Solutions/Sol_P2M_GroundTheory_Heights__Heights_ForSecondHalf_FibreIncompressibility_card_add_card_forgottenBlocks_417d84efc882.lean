-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_card_add_card_forgottenBlocks_417d84efc882
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:12:04.2918+00:00
-- url     : https://prove2.me/submissions/7d30e7d8-af1a-4908-88b9-60821fa79007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIncomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter.PointVertical
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
theorem _root_.solution [Fintype K] {κ : K → K'} (hκ : Function.Injective κ) :
    Fintype.card K + Fintype.card (FibreBlock κ) = Fintype.card K' := by
  classical
  have h1 := Fintype.card_subtype_compl (fun k' => k' ∈ Set.range κ)
  have h2 : Fintype.card {k' // k' ∈ Set.range κ} = Fintype.card K := Set.card_range_of_injective hκ
  have h3 := Fintype.card_subtype_le (fun k' => k' ∈ Set.range κ)
  have h4 : Fintype.card (FibreBlock κ) = Fintype.card {k' // ¬ k' ∈ Set.range κ} :=
    Fintype.card_congr (Equiv.refl _)
  omega
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
