-- Prove2me | solution 1 for ReciprocityTheory.Cheb.liesOver_of_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:35.110158+00:00
-- url     : https://prove2.me/submissions/2053f5d5-fa7f-4cd3-83ce-5053ac5b8a07

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_under_asIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') (q : Prm E) (hP : under P = q) : P.asIdeal.LiesOver q.asIdeal :=
  ⟨by rw [← hP, under_asIdeal]⟩
end ReciprocityTheory.Cheb
