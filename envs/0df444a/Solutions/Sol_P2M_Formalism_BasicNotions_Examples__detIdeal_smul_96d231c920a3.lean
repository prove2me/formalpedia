-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:49.981112+00:00
-- url     : https://prove2.me/submissions/a907f155-db0a-43f7-ba14-40e44a7e1c04

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
noncomputable section
namespace Formalism.BasicNotions.Examples₂
section Core
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
private theorem det_mem_detIdeal_lemma (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → Fin N → E)
    (hv : ∀ j, v j ∈ L) : (Matrix.of v).det ∈ detIdeal L := by
  unfold detIdeal
  exact Submodule.subset_span ⟨v, hv, rfl⟩
end Core
end Formalism.BasicNotions.Examples₂
end
end

set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∀ n ∈ detIdeal L, γ.det • n ∈ detIdeal L := by
  have hle : detIdeal L ≤ (detIdeal L).comap (LinearMap.mulLeft (𝓞 E) γ.det) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have h := det_mem_detIdeal_lemma L (fun j => γ.mulVec (v j)) (fun j => hγ _ (hv j))
    rwa [of_mulVec_eq, Matrix.det_mul, Matrix.det_transpose, mul_comm] at h
  intro n hn
  have h := hle hn
  rwa [Submodule.mem_comap, LinearMap.mulLeft_apply, ← smul_eq_mul] at h
end Formalism.BasicNotions.Examples₂
