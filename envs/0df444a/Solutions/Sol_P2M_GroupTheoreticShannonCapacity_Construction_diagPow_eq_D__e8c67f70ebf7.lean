-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:32:58.237101+00:00
-- url     : https://prove2.me/submissions/5d8a5f65-eb25-4b13-a82c-96c07aa94249

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (β : ℝ) : diagPow n β = MAlpha.Dα n β := by
  ext i j; simp only [diagPow, MAlpha.Dα, Matrix.diagonal_apply]
end GroupTheoreticShannonCapacity.Construction
