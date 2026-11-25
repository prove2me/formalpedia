-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:21.117438+00:00
-- url     : https://prove2.me/submissions/c941514e-2f7b-4a06-91b0-75b38fcea7fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae


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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I :=
  ⟨0, by
    rw [pow_zero, mul_one, mul_zero, SubSystem.pow_sub_eq_pow, pow_zero]
    exact Submodule.mem_one.mpr ⟨⟨c, hc⟩, rfl⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
