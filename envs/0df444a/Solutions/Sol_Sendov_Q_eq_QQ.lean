-- Prove2me | solution 1 for Sendov.Q_eq_QQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:23.677715+00:00
-- url     : https://prove2.me/submissions/48611a26-9bae-4323-bc63-474b613c94ad

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (n : ℕ) (α t : ℝ) : Q n α t = QQ (c n α) (A n α) t := rfl
end Sendov
