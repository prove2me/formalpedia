-- Prove2me | solution 1 for PI.GGMatBoundW.irreducible_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:02.700271+00:00
-- url     : https://prove2.me/submissions/06000519-0f0a-4f23-8950-7a68af2a4f8c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_finrank_eq


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
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace PI.GGMatBoundW
theorem _root_.solution (π : Representation ℂ G V) (W : Subrepresentation π) (hW : W ≠ ⊥)
    (hmin : ∀ W' : Subrepresentation π, W' ≠ ⊥ → W' ≤ W →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ W'.toSubmodule) :
    W.toRepresentation.IsIrreducible := by
  have hWs : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial (Subrepresentation W.toRepresentation) := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWs
    refine ⟨⟨⊥, ⊤, fun h => hx0 ?_⟩⟩
    have hmem : (⟨x, hxW⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at hmem
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hmem)
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hSs : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let S' : Subrepresentation π := ⟨S.toSubmodule.map W.toSubmodule.subtype, by
    rintro g _ ⟨y, hy, rfl⟩
    exact ⟨W.toRepresentation g y, S.apply_mem_toSubmodule g hy, rfl⟩⟩
  have hS'0 : S' ≠ ⊥ := by
    obtain ⟨y, hyS, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSs
    intro h
    have hmem : (y : V) ∈ S'.toSubmodule := ⟨y, hyS, rfl⟩
    rw [h] at hmem
    exact hy0 (Subtype.ext ((Submodule.mem_bot ℂ).mp hmem))
  have hle : S' ≤ W := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hrank := hmin S' hS'0 hle
  have e1 : Module.finrank ℂ S'.toSubmodule = Module.finrank ℂ S.toSubmodule :=
    (Submodule.equivMapOfInjective _ W.toSubmodule.injective_subtype S.toSubmodule).finrank_eq.symm
  have htop : S.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq (by
    have := Submodule.finrank_le S.toSubmodule
    omega)
  exact Subrepresentation.toSubmodule_injective htop
end PI.GGMatBoundW
