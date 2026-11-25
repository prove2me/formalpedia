-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleProductRep_mem_of_local_baee30457324
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:36.368902+00:00
-- url     : https://prove2.me/submissions/bb524376-eba5-426b-9bc9-6613f21758bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleProductRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
namespace GroundTheory.Heights₂.Heights.Targets
namespace InvertibleProductRep
theorem _root_.solution {Ω : Type} [Field Ω] (B : Subring Ω) (Y : AddSubgroup Ω)
    (hY : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y) (z : Ω)
    (hz : ∀ m : Ideal B, m.IsMaximal → ∃ b : B, b ∉ m ∧ (b : Ω) * z ∈ Y) : z ∈ Y := by
  let A : Ideal B :=
    { carrier := {a : B | (a : Ω) * z ∈ Y}
      add_mem' := by
        intro a c ha hc
        show ((a + c : B) : Ω) * z ∈ Y
        push_cast
        rw [add_mul]
        exact Y.add_mem ha hc
      zero_mem' := by
        show ((0 : B) : Ω) * z ∈ Y
        simp
      smul_mem' := by
        intro c a ha
        show ((c * a : B) : Ω) * z ∈ Y
        push_cast
        rw [mul_assoc]
        exact hY c c.2 _ ha }
  by_cases hA : A = ⊤
  · have h1 : (1 : B) ∈ A := hA ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * z ∈ Y := h1
    simpa using h2
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨b, hb, hbz⟩ := hz m hm
    exact absurd (hle (show b ∈ A from hbz)) hb
end InvertibleProductRep
end GroundTheory.Heights₂.Heights.Targets
