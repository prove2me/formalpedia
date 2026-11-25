-- Prove2me | solution 1 for ReciprocityTheory.CA.RegGens.exists_regular_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:57.752818+00:00
-- url     : https://prove2.me/submissions/2b48b184-18a2-4463-b6bd-046240a0ac1d

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGensA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGens
import Theorems.Thm_ReciprocityTheory_CA_RegGens_exists_regular_generators_maxIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian IsLocalRing RingTheory.Sequence
universe u v
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.RegGens
namespace ReciprocityTheory.CA.RegGens
theorem _root_.solution (P : Type u) [CommRing P] [IsRegularLocalRing P] (d : ℕ)
    (hd : ringKrullDim P = d) :
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P :=
  exists_regular_generators_maxIdeal d P hd
end ReciprocityTheory.CA.RegGens
