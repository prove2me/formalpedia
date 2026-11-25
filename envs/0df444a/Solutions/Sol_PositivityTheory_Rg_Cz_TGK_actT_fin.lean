-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.actT_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:04.653713+00:00
-- url     : https://prove2.me/submissions/34a7c8d0-d29b-46c0-9802-c78a48dd0996

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKB
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (hfin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))) (y : TV n M P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y)) := by
  classical
  haveI hS : ∀ J : P → Fin n, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ (y J))) :=
    fun J => hfin (y J)
  set T : Submodule ℂ M := ⨆ J : P → Fin n, Submodule.span ℂ (Set.range fun γ => ρ γ (y J)) with hT
  haveI : FiniteDimensional ℂ T := by rw [hT]; infer_instance
  let L : ((P → Fin n) → T) →ₗ[ℂ] TV n M P := LinearMap.pi fun I => T.subtype ∘ₗ LinearMap.proj I
  have hle : Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    have hmem : ∀ I, actT lab κ ρ γ y I ∈ T := by
      intro I
      simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.proj_apply]
      refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
      exact Submodule.mem_iSup_of_mem J (Submodule.subset_span ⟨γ, rfl⟩)
    exact ⟨fun I => ⟨_, hmem I⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end PositivityTheory.Rg.Cz.TGK
