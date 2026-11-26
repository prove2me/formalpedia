-- Prove2me | solution 1 for OpenQuantumProblem35.ame_12_5_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:27:45.769638+00:00
-- url     : https://prove2.me/submissions/d4dcfd36-e2b0-4831-8e39-94d18b73d46c

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_FormalTarget
public import Theorems.Thm_AME125_ame_12_5_open

set_option autoImplicit false
@[expose] public section
public section
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution :
    ExistsAME 12 5 :=
  AME125.ame_12_5_open
end OpenQuantumProblem35
