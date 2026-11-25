-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_finite_secs_twistMul_b935a9ac3a23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:07.231807+00:00
-- url     : https://prove2.me/submissions/5836e028-0074-40d9-b4c8-630803c5aeef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop

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
theorem _root_.solution (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')
end GroundTheory.Heights₂.Heights.Kleiman
