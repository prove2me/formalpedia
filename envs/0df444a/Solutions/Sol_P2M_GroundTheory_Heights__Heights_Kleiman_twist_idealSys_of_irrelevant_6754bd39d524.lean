-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:12.3819+00:00
-- url     : https://prove2.me/submissions/3992923d-61ea-46be-ad15-ae0fb64e2ca1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_subSystem_ext_ddefc825c292

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
universe u v w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by
  refine subSystem_ext fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
      isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
  have hle : (idealSys x pp).sub I ≤ 1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
    exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine le_antisymm (Submodule.mul_le.mpr fun q hq y hy => ?_) fun y hy => by
    simpa using Submodule.mul_mem_mul h1 hy
  obtain ⟨q', rfl⟩ := Submodule.mem_one.mp (hle hq)
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ q' hy
end GroundTheory.Heights₂.Heights.Kleiman
