-- Prove2me | solution 1 for ThreeSum.BlockSourceRows.right_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:18.733193+00:00
-- url     : https://prove2.me/submissions/baa29685-d557-4a62-bf25-ddf3c31daec8

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Theorems.Thm_ThreeSum_BlockSourceRows_bits_fin
import Theorems.Thm_ThreeSum_BlockSourceRows_hash_eq_eval
import Theorems.Thm_ThreeSum_OneHotMask_eval_rawRight


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceRows
open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.BlockSourceRows
theorem _root_.solution {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,true)).val)
      (OneHotMask.extend fun i => (w (i,false)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.rightWord (row S j)) := by
  rw [hash_eq_eval (row S j) (bits S j) _ _ (bits_fin S j),OneHotMask.eval_rawRight]
end ThreeSum.BlockSourceRows
