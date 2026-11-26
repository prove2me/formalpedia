-- Prove2me | solution 1 for P2M_N4Code_min__proof_irrel_1e0402de89ff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:18.7921+00:00
-- url     : https://prove2.me/submissions/d6970421-01bb-4bcb-9b83-96783dda16f4

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {s : Finset ℕ} (H1 H2 : s.Nonempty) : s.min' H1 = s.min' H2 :=
  congrArg (fun H : s.Nonempty => s.min' H) (Subsingleton.elim H1 H2)
end N4Code
