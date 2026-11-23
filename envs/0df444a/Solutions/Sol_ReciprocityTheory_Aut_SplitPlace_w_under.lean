-- Prove2me | solution 1 for ReciprocityTheory.Aut.SplitPlace.w_under
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:56.205571+00:00
-- url     : https://prove2.me/submissions/da37a08a-5faf-4ba0-9687-c5a9690a085c

import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace ReciprocityTheory.Aut
namespace SplitPlace
theorem _root_.solution (s : SplitPlace L) :
    s.w.asIdeal.comap (algebraMap (𝓞 L⁺) (𝓞 L)) = s.v.asIdeal := by
  ext a
  rw [Ideal.mem_comap]
  exact s.split_alg_mem a
end SplitPlace
end ReciprocityTheory.Aut
