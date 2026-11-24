-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.tv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:33.154589+00:00
-- url     : https://prove2.me/submissions/3de24c19-4843-4465-a5ca-5fe55ee4ab37

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution {i j : n} (h : i ≠ j) (s : K) : ((tv h s : GL n K) : Matrix n n K) = transvection i j s := rfl
end PositivityTheory.Sph.M2.GenA
