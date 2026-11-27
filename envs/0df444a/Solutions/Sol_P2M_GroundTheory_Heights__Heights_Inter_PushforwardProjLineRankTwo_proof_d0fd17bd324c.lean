-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineRankTwo_proof_d0fd17bd324c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:07.058212+00:00
-- url     : https://prove2.me/submissions/ccaafb27-ecd2-4cab-8e52-a06180e884a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLineFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimePairSetFirst

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace PushforwardProjLineRankTwo
theorem _root_.solution (hPF : PushforwardProjLineFlag.Statement) (hF : FibreDimStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hLine : LineFibreBlocks.Statement) : PushforwardProjLineRankTwo.Statement := by
  unfold PushforwardProjLineRankTwo.Statement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G k₀ L L' N hv hP' hP hk₀ hS hL hLL' hN
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (fibreIdeal κ G) 1 := hF K ι K' ι' κ v P' d 1 G hv hP' hP
  have h1 := hPF I hI K ι K' ι' κ v P' d 1 G J L L' ![N] hv hP' hP hJ hL hLL'
    (fun j => by fin_cases j; exact hN)
  have h2 := hLine G.Φ (FibreBlock κ) (fibreIdx ι' κ) k₀ (fibreIdeal κ G) J hk₀ hV hS hJ (fibreDeg κ N.a)
  have h3 : (fun j : Fin 1 => fibreDeg κ ((![N] : Fin 1 → HermLine ι') j).a) = ![fibreDeg κ N.a] := by
    funext j
    fin_cases j
    rfl
  rw [h1, h3, h2]
  rfl
end PushforwardProjLineRankTwo
end GroundTheory.Heights₂.Heights.Inter
