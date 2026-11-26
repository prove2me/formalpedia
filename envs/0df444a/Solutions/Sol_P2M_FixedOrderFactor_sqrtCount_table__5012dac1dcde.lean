-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_table__5012dac1dcde
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:15.088207+00:00
-- url     : https://prove2.me/submissions/4e6fa3d3-307b-4a21-a6b2-ffb86191e6f8

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution :
    -- r = 2
    sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 2 = 4 ∧ sqrtCount 8 5 2 = 0 ∧
    -- r = 3 (generic and squares: s = 3)
    sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 4 (generic s = 4, squares s = 2)
    sqrtCount 8 5 4 = 0 ∧ sqrtCount 8 5 2 = 0 ∧
    sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    -- r = 6 (generic s = 6, squares s = 3)
    sqrtCount 12 1 6 = 2 ∧ sqrtCount 12 1 3 = 2 ∧ sqrtCount 12 7 6 = 0 ∧ sqrtCount 12 7 3 = 0 ∧
    -- r = 8 (generic s = 8, squares s = 4, fourth powers s = 2)
    sqrtCount 16 1 8 = 2 ∧ sqrtCount 16 1 4 = 2 ∧ sqrtCount 16 1 2 = 4 ∧
    sqrtCount 16 9 8 = 0 ∧ sqrtCount 16 9 4 = 2 ∧ sqrtCount 16 9 2 = 4 ∧
    sqrtCount 32 17 8 = 2 ∧ sqrtCount 32 17 4 = 2 ∧ sqrtCount 32 17 2 = 4 ∧
    sqrtCount 32 25 8 = 0 ∧ sqrtCount 32 25 4 = 2 ∧ sqrtCount 32 25 2 = 4 := by
  decide
end FixedOrderFactor
