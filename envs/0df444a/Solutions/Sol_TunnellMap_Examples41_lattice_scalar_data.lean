-- Prove2me | solution 1 for TunnellMap.Examples41.lattice_scalar_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:10.11927+00:00
-- url     : https://prove2.me/submissions/38d7ead3-7004-426b-bd07-f4ee216a6af0

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    alpha frame41 = 1 ∧
      beta frame41 = 0 ∧
      dot frame41.e₂ frame41.e₂ = 41 ∧
      delta frame41 = 0 ∧
      epsilon frame41 = 9 ∧
      dot frame41.z frame41.z = 2 ∧
      K frame41 = -9 := by
  norm_num [frame41, alpha, beta, delta, epsilon, K, dot]
end TunnellMap.Examples41
