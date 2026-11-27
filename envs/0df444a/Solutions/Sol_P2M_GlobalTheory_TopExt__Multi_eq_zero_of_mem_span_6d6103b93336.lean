-- Prove2me | solution 1 for P2M_GlobalTheory_TopExt__Multi_eq_zero_of_mem_span_6d6103b93336
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:59.162979+00:00
-- url     : https://prove2.me/submissions/45f692a3-acb3-4652-a8c2-5e66e09b43f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution {r n : ℕ} (hn : r < n) (v : Fin r → F) (w : Fin n → F)
    (hw : ∀ k, w k ∈ Submodule.span R (Set.range v)) : exteriorPower.ιMulti R n w = 0 := by
  simp only [Submodule.mem_span_range_iff_exists_fun] at hw
  choose u hu using hw
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s => by
    have h1 := s.1.card_le_univ
    have h2 : s.1.card = n := s.2
    simp only [Fintype.card_fin] at h1
    omega⟩
  have h0 : exteriorPower.ιMulti R n u = 0 :=
    ((Pi.basisFun R (Fin r)).exteriorPower n).ext_elem fun s => this.elim s
  have hw : w = Fintype.linearCombination R v ∘ u := funext fun k => (hu k).symm
  rw [hw, ← exteriorPower.map_apply_ιMulti, h0, map_zero]
end GlobalTheory.TopExt
