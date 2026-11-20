-- Prove2me | solution 1 for P010.maximalNonCoprimeRuns_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:36:06.689224+00:00
-- url     : https://prove2.me/submissions/22a0e66b-896d-4cbd-a52b-6e20bc167a54

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (a : List ℕ) :
    (maximalNonCoprimeRuns a).flatten = a := by
  exact List.flatten_splitBy _ a
end P010
