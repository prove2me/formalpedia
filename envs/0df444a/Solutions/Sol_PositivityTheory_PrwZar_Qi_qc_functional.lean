-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.qc_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:15.269195+00:00
-- url     : https://prove2.me/submissions/d23a1a2f-3cd1-44f5-b479-7c2bcc92ba3d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCartier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution (ε : H →ₐ[K] K) {x : H} (hx : x ∈ RingHom.ker ε) (hx2 : x ∉ RingHom.ker ε ^ 2) :
    ∃ l : H →ₗ[K] K, l 1 = 0 ∧ (∀ y ∈ RingHom.ker ε ^ 2, l y = 0) ∧ l x = 1 := by
  let W : Submodule K H := Submodule.span K {(1 : H)} ⊔ (RingHom.ker ε ^ 2).restrictScalars K
  have hxW : x ∉ W := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz2 : z ∈ RingHom.ker ε ^ 2 := hz
    have hz' : z ∈ RingHom.ker ε := Ideal.pow_le_self two_ne_zero hz2
    have hc : c = 0 := by
      have h1 : ε x = 0 := hx
      have h2 : ε z = 0 := hz'
      rw [← hyz, map_add, map_smul, map_one, h2] at h1
      simpa using h1
    subst hc
    apply hx2
    rw [← hyz, zero_smul, zero_add]
    exact hz2
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  have hW : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    simpa using this
  refine ⟨(f x)⁻¹ • f, ?_, ?_, ?_⟩
  · simp [hW 1 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))]
  · intro y hy
    simp [hW y (Submodule.mem_sup_right hy)]
  · simp [hf]
end PositivityTheory.PrwZar.Qi
