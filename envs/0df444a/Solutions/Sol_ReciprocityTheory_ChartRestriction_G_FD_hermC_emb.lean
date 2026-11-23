-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hermC_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:54.200523+00:00
-- url     : https://prove2.me/submissions/2be5e0e2-fd13-49ba-9a8f-5908767ff1de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    hermC τ G (Data.emb τ u) (Data.emb τ v) = τ (herm G u v) := by
  unfold hermC herm Data.emb
  simp only [map_sum, map_mul, emb_cc]
end ReciprocityTheory.ChartRestriction.G.FD
