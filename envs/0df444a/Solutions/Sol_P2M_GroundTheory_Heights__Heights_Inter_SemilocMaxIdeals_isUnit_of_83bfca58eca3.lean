-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_isUnit_of_83bfca58eca3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:48.261307+00:00
-- url     : https://prove2.me/submissions/e45237c7-7205-4180-92e2-ae83fe4a6429

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_fracHom_ne_zero_e8d84d906420
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution (b : semiLocRing P 𝒲) {u w : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hw : IsMultiHomog w a) (huP : u ∉ P) (huW : ∀ W ∈ 𝒲, u ∉ W)
    (hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u) : IsUnit b := by
  refine IsUnit.of_mul_eq_one (⟨_, frac_mem P 𝒲 hw hu huP huW⟩ : semiLocRing P 𝒲) (Subtype.ext ?_)
  change (b : FractionRing (MRing ι ⧸ P)) * (fracHom P w / fracHom P u) = 1
  rw [mul_div_assoc', hb, div_self (fracHom_ne_zero P huP)]
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
