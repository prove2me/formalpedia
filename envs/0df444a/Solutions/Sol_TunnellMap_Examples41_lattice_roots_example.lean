-- Prove2me | solution 1 for TunnellMap.Examples41.lattice_roots_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:07.143641+00:00
-- url     : https://prove2.me/submissions/497376c8-6882-4775-8229-79fecc699dad

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    rootValues frame41 20 1 (-4) = ({2, -2} : Finset ℤ) := by
  decide +kernel
end TunnellMap.Examples41
