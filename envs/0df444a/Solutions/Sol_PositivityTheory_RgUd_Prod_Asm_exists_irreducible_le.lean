-- Prove2me | solution 1 for PositivityTheory.RgUd.Prod.Asm.exists_irreducible_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:24.853732+00:00
-- url     : https://prove2.me/submissions/ff5ad43b-4e99-4ee3-9f14-ba516705436f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_mem_fixed_iff
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_le_genSub
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_genSub_le
import Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_irreducible_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Prod PositivityTheory.RgUd.Prod.Asm
open GlobalTheory.PRep
namespace PositivityTheory.RgUd.Prod.Asm
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmall : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hA : GlobalTheory.PRep.IsAdmissible ρ)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    ∃ S₀ : Subrepresentation ρ, S₀ ≠ ⊥ ∧ S₀.toSubmodule ≤ S.toSubmodule ∧ S₀.toRepresentation.IsIrreducible := by
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S.toSubmodule, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hS
    apply Subrepresentation.ext
    show S.toSubmodule = (⊥ : Submodule ℂ V)
    rw [Submodule.eq_bot_iff]
    exact hcon
  obtain ⟨K, hKo, hKc, hKv⟩ := hsmall {g | ρ g v = v} ((hA.1 v).mem_nhds (by simp))
  have hFd : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  have hvF : v ∈ fixed ρ K := (mem_fixed_iff ρ K v).2 fun k => hKv k.2
  have hex : ∃ n, ∃ W : Subrepresentation ρ, W.toSubmodule ≤ S.toSubmodule ∧
      fixed ρ K ⊓ W.toSubmodule ≠ ⊥ ∧ Module.finrank ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) = n := by
    refine ⟨_, S, le_rfl, ?_, rfl⟩
    intro h
    have : v ∈ fixed ρ K ⊓ S.toSubmodule := ⟨hvF, hvS⟩
    rw [h] at this
    exact hv0 ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨W, hWS, hW0, hWn⟩ := Nat.find_spec hex
  set W₀ := genSub ρ (fixed ρ K ⊓ W.toSubmodule) with hW₀def
  have hW₀W : W₀.toSubmodule ≤ W.toSubmodule := genSub_le ρ _ W inf_le_right
  have hF₀ : fixed ρ K ⊓ W₀.toSubmodule = fixed ρ K ⊓ W.toSubmodule :=
    le_antisymm (inf_le_inf_left _ hW₀W) (le_inf inf_le_left (le_genSub ρ _))
  refine ⟨W₀, ?_, hW₀W.trans hWS, ?_⟩
  · intro h
    apply hW0
    rw [← hF₀, h]
    exact inf_bot_eq _
  · refine irreducible_of_fixed ρ K hcompl W₀ (by rwa [hF₀]) ?_ ?_
    · intro U hU hUne
      have hmin := Nat.find_min' hex ⟨U, hU.trans (hW₀W.trans hWS), hUne, rfl⟩
      rw [← hWn] at hmin
      have : FiniteDimensional ℂ (fixed ρ K ⊓ W.toSubmodule : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have hle : fixed ρ K ⊓ U.toSubmodule ≤ fixed ρ K ⊓ W.toSubmodule := hF₀ ▸ inf_le_inf_left _ hU
      have heq := Submodule.eq_of_le_of_finrank_le hle hmin
      rw [hF₀, ← heq]
      exact inf_le_right
    · intro U hU
      rw [hF₀] at hU
      exact genSub_le ρ _ U hU
end PositivityTheory.RgUd.Prod.Asm
