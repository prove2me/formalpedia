-- Prove2me | solution 1 for ThreeSum.ReportingHostQueryBounds.abs_value_le_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:43.396244+00:00
-- url     : https://prove2.me/submissions/e77bbf74-ff12-438d-b0a4-e55ef6f2a872

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Theorems.Thm_ThreeSum_ReportingHostQueryBounds_abs_value_le
import Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostQueryBounds
open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.ReportingHostQueryBounds
theorem _root_.solution {W cut stage t B D : ℕ} {lim : Limits}
    (f g : Finset (Fin W) → ℤ) (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hw : (LightSparseQuery.magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word) :
    |value f g stage preL preR Q| ≤ lim.word := by
  have hbase := abs_value_le f g preL preR Q hstage hL hR hf hg
  have hm : 2^W*((2^stage*B)*(2^stage*D)) ≤ LightSparseQuery.magnitudeBound W stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmInt : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound W stage Q.card t B D : ℤ) := by exact_mod_cast hm
  exact hbase.trans (hmInt.trans hw)
end ThreeSum.ReportingHostQueryBounds
