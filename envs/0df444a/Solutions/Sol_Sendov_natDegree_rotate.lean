-- Prove2me | solution 1 for Sendov.natDegree_rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:06:27.677235+00:00
-- url     : https://prove2.me/submissions/0ecfd56b-0553-48a0-a91b-001ddbce5afb

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotate ω p).natDegree = p.natDegree := by
  rw [rotate, natDegree_comp, natDegree_C_mul hω, natDegree_X, mul_one]
end Sendov
