-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundleRestrict_proof_a204596daa4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:58.396868+00:00
-- url     : https://prove2.me/submissions/128fc803-5186-4fb8-8b66-c7b3741279f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017


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
variable {γ : Ω} {Q : LineBundle k x}
omit hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace LineBundleRestrict
theorem _root_.solution : LineBundleRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hsp Q
  obtain ⟨γ, hγ0, hg, hb⟩ := exists_restrict_gen hsp hxy Q
  refine ⟨LineBundle.mk (SubFamily.mk (redSys hxy Q.toSubSystem γ) (redSys_mem_iff hsp hxy hg)) ?_ ?_,
    _, restrictData_redSys hsp hxy hg _ rfl⟩
  · intro I
    obtain ⟨s, hs⟩ := Q.fg (liftChart hxy I)
    rw [redSys_sub_eq_span hsp hxy hg I hs]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro I
    exact redSys_invertible hsp hxy hγ0 hg I (hb I)
end LineBundleRestrict
end GroundTheory.Heights₂.Heights.Kleiman
