-- Prove2me | solution 1 for ReciprocityTheory.Cheb.logEmbedding_prod_fundSystem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:10.721533+00:00
-- url     : https://prove2.me/submissions/1ed87127-6498-44fa-b9c9-227f029ebacc

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (f : Fin (rank E) → ℤ) :
    logEmbedding E (Additive.ofMul (∏ i, (fundSystem E i) ^ (f i))) =
      ∑ i, (f i : ℝ) • ((basisUnitLattice E i : unitLattice E) : logSpace E) := by
  rw [ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, logEmbedding_fundSystem, Int.cast_smul_eq_zsmul]
end ReciprocityTheory.Cheb
