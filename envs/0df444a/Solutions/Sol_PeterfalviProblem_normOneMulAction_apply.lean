-- Prove2me | solution 1 for PeterfalviProblem.normOneMulAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T05:05:35.578998+00:00
-- url     : https://prove2.me/submissions/cc4459b5-7513-4d62-8178-750fa44d5a49

import Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
import Definitions.Def_PeterfalviProblem_Basic_FrobeniusGroup

set_option autoImplicit false
open PeterfalviProblem
variable (p q : ℕ) [Fact p.Prime]
namespace PeterfalviProblem
theorem _root_.solution (u : normOneUnits p q) (s : GaloisField p q) :
    ((normOneMulAction p q u) (Multiplicative.ofAdd s)).toAdd =
      ((u : (GaloisField p q)ˣ) : GaloisField p q) * s :=
  rfl
end PeterfalviProblem
