-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreProduct_proof_e775bbb8adf4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:44.665635+00:00
-- url     : https://prove2.me/submissions/aa95fa3e-8845-4caf-aac8-b784d4e0c296

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_T_two_llDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace FibreProduct
theorem _root_.solution (hWW : WWArithVar.Statement) (hDD : DiagDiv.Statement)
    (hDP : DiagPull.Statement) : FibreProduct.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ D a hs hg hd hc hbase hind
  obtain ⟨hY, hW, hΔ⟩ := hWW Ω ι ν κ E Φ x B e φ δ hs hg hd D hbase a hind
  obtain ⟨hex, hdiv⟩ := hDD Ω ι ν κ E Φ x B e φ δ hs hg hd hc a hind
  exact ⟨⟨hY, hW⟩, comap_wwIdeal_yyEmb x δ e φ a, hΔ, ⟨wwDeg_sub_eq_llDeg, T.two_llDeg⟩, hex, hdiv,
    (hDP Ω ι ν κ E Φ x e φ δ (a 0)).2.1⟩
end FibreProduct
end GroundTheory.Heights₂.Heights.Inter
