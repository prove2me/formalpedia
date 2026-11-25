-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:37.315655+00:00
-- url     : https://prove2.me/submissions/94b539e8-493b-44ae-91e0-1799d532a186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : LineBundle k x) (I J : Chart y) {z : Ω}
    (hz : z ∈ Q.sub (liftChart hxy (restrictUnion I J))) :
    ∃ a ∈ chartRing k x (liftChart hxy I), a ∈ locAt k x y ∧ redAt k x y a ≠ 0 ∧
      a * z ∈ Q.sub (liftChart hxy I) := by
  have hIJ : I.1 ⊆ (restrictUnion I J).1 := Finset.subset_union_left
  obtain ⟨a, ha, haz⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy (restrictUnion I J)) hIJ z).mp hz
  obtain ⟨haL, b, -, hb⟩ := redAt_isUnit_of_isUnit hsp hxy hIJ a ha
  rw [smul_eq_mul] at haz
  exact ⟨a, a.2, haL, left_ne_zero_of_mul_eq_one hb, haz⟩
end GroundTheory.Heights₂.Heights.Kleiman
