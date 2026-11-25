-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:38.87101+00:00
-- url     : https://prove2.me/submissions/4ebb936c-5ac0-4266-ab97-cb24fbb75318

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution (hL : L.IsLB) {F : (Y ⟶ X) →₀ ℤ} (h : HasGen L F) {K' : Type} [Fintype K']
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hF : fsum φ' ε' = F) : ∃ g : LB.Gen (LB.LinComb L φ' ε'), g.IsGen := by
  obtain ⟨K, _, φ, ε, hfs, g, hg⟩ := h
  obtain ⟨t', ht', -⟩ := gen_transport (L := L) hL ((sameSum_iff_fsum φ ε φ' ε').2 (hfs.trans hF.symm)) g hg
  exact ⟨t', ht'⟩
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
