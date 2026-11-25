-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_exists_complement_of_le_976f1511e062
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:34.49506+00:00
-- url     : https://prove2.me/submissions/590f3196-7add-4410-91b3-c371429109dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℝ M] {U V : Submodule ℝ M}
    (h : U ≤ V) : ∃ V' : Submodule ℝ M, V' ≤ V ∧ Disjoint U V' ∧ U ⊔ V' = V := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (U.comap V.subtype)
  refine ⟨q.map V.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxU hxV'
    obtain ⟨y, hyq, rfl⟩ := Submodule.mem_map.1 hxV'
    have hyp : y ∈ U.comap V.subtype := Submodule.mem_comap.2 hxU
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hq.disjoint) y hyp hyq
    simp [hy0]
  · refine le_antisymm (sup_le h (Submodule.map_subtype_le _ _)) ?_
    intro x hx
    have htop : (⟨x, hx⟩ : V) ∈ U.comap V.subtype ⊔ q := by
      rw [hq.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 htop
    have e : (y : M) + (z : M) = x := by simpa using congrArg Subtype.val hyz
    rw [← e]
    exact Submodule.add_mem_sup (Submodule.mem_comap.1 hy) (Submodule.mem_map_of_mem hz)
end GroundTheory.Heights₂.Heights.TheoremB
