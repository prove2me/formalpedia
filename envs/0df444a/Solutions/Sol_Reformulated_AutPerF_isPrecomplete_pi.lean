-- Prove2me | solution 1 for Reformulated.AutPerF.isPrecomplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.69951+00:00
-- url     : https://prove2.me/submissions/094a2675-18d8-456b-b7be-5432ec299795

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
open Reformulated Reformulated.AutPerF
universe u
namespace Reformulated.AutPerF
theorem _root_.solution {B : Type*} [CommRing B] (q : B) (ι : Type*)
    [IsPrecomplete (span {q}) B] : IsPrecomplete (span {q}) (ι → B) := by
  have key (n : ℕ) (x : ι → B) : x ∈ (span {q} ^ n • ⊤ : Submodule B (ι → B)) ↔
      ∀ i, x i ∈ (span {q} ^ n • ⊤ : Submodule B B) := by
    simp only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, rfl⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext hy⟩
  refine ⟨fun f hf => ?_⟩
  have h (i : ι) := IsPrecomplete.prec (inferInstance : IsPrecomplete (span {q}) B)
    (f := fun n => f n i) (fun hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, key] at this
      rw [SModEq.sub_mem]
      exact this i)
  choose L hL using h
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hL i n)
end Reformulated.AutPerF
