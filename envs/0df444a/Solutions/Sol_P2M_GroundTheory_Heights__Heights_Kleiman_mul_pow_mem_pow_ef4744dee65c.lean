-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:04.018277+00:00
-- url     : https://prove2.me/submissions/eb643122-4ffe-4556-99b0-0bcf9d345684

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_pow_succ_8a28807f43b3

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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq
end GroundTheory.Heights₂.Heights.Kleiman
