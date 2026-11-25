-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:27.730522+00:00
-- url     : https://prove2.me/submissions/1cba37f4-f9eb-48fa-b485-36775d891029

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_HH_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_congruenceCondition_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_evd
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Low
theorem _root_.solution {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∃ b : FreeAlgebra ℂ (Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E u - evd (fun c => E c c) b ∈ PP E := by
  induction hu with
  | one => exact ⟨1, fun V _ _ E _ => by simp⟩
  | mul u p _ hp ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨i, j⟩ := p
    have key : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
        adH E (E i j) = (((i : ℕ) - (j : ℕ) : ℕ) : ℂ) • E i j := by
      intro V _ _ E hE
      rw [adH_apply, HH_comm hE, Nat.cast_sub hp]
    rcases eq_or_lt_of_le hp with h | h
    · simp only at h
      subst h
      refine ⟨b * FreeAlgebra.ι ℂ j, fun V _ _ E hE => ?_⟩
      have := congruenceCondition_mul (hb V E hE) (key V E hE)
      rw [map_mul, map_mul, ev_ι]
      simpa [evd, sub_mul] using this
    · refine ⟨0, fun V _ _ E hE => ?_⟩
      have h1 := congruenceCondition_mul (hb V E hE) (key V E hE)
      have h2 : evd (fun c => E c c) b * E i j ∈ PP E := by
        refine Submodule.subset_span ⟨(i : ℕ) - (j : ℕ) - 1, ?_⟩
        rw [adH_mul, adH_evd hE, key V E hE, zero_mul, zero_add, mul_smul_comm]
        congr 1
        have h' : (j : ℕ) < (i : ℕ) := h
        have : (i : ℕ) - (j : ℕ) = (i : ℕ) - (j : ℕ) - 1 + 1 := by omega
        exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) this
      have h3 := (PP E).add_mem h1 h2
      rw [map_mul, ev_ι, map_zero, sub_zero]
      simpa [sub_mul] using h3
  | add u v _ _ hu hv =>
    obtain ⟨b, hb⟩ := hu
    obtain ⟨b', hb'⟩ := hv
    refine ⟨b + b', fun V _ _ E hE => ?_⟩
    have := (PP E).add_mem (hb V E hE) (hb' V E hE)
    rw [map_add, map_add]
    convert this using 1; abel
  | smul c u _ hu =>
    obtain ⟨b, hb⟩ := hu
    refine ⟨c • b, fun V _ _ E hE => ?_⟩
    rw [map_smul, map_smul, ← smul_sub]
    exact (PP E).smul_mem c (hb V E hE)
end Low
end GlobalTheory.CompanionTheory.HCdecomp
