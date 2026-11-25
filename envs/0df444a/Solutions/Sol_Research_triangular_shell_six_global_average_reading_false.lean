-- Prove2me | solution 1 for Research.triangular_shell_six_global_average_reading_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:59.224605+00:00
-- url     : https://prove2.me/submissions/e806163e-facb-4206-863d-b6a19324916d

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_triCoordsWithinThirtySix_card
public import Theorems.Thm_Research_not_eventualShellSixDirectedAverageBound
public import Theorems.Thm_Research_not_eventualShellSixUnorderedBound

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    triCoordsWithinThirtySix.card = 126 ∧
      ¬ EventualShellSixDirectedAverageBound ∧
      ¬ EventualShellSixUnorderedBound :=
  ⟨triCoordsWithinThirtySix_card,
    not_eventualShellSixDirectedAverageBound,
    not_eventualShellSixUnorderedBound⟩
end Research
