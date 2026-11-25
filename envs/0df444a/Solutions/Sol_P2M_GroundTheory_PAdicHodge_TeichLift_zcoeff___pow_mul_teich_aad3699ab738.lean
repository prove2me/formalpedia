-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_mul_teich_aad3699ab738
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:08.028982+00:00
-- url     : https://prove2.me/submissions/db879770-3faf-4c1a-9d80-0d0760d9fc2f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (N : ℕ) (c : L) : T.zcoeff (T.π ^ N * T.teich c) = Pi.single (N : ℤ) c := by
  funext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, Pi.single_apply, if_neg (by omega)]
  · lift n to ℕ using hn
    rw [zcoeff_natCast, coeff_π_pow_mul_teich, Pi.single_apply]
    simp
end GroundTheory.PAdicHodge.TeichLift
