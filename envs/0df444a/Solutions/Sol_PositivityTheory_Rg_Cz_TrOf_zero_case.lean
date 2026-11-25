-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.zero_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:37:30.39716+00:00
-- url     : https://prove2.me/submissions/8c3e793e-fdfd-40a2-b05d-bf5ee9020d70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
import Theorems.Thm_PositivityTheory_Rg_Cz_alt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_cA_apply
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution (E : Fin 0 → Fin 0 → Module.End ℂ M) (l : Fin 0 → ℤ) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin 0) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have : IsEmpty P := ⟨fun p => (b p).elim0⟩
  have hσ : ∀ σ : Equiv.Perm P, σ = 1 := fun σ => Equiv.ext fun p => isEmptyElim p
  have hG : colG col = {1} := by
    ext σ
    simp [colG, hσ σ]
  have hqd : ∀ u, qdet (tE (Finset.univ : Finset P) E) u = 1 := by
    intro u
    simp [qdet, qminor]
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, fun h0 => hv ?_, fun u => ?_⟩
  · have := LinearMap.congr_fun h0 (fun _ => v)
    simpa [cA_apply, alt_apply, hG] using this
  · rw [hqd]
    refine LinearMap.ext fun x => ?_
    simp
end PositivityTheory.Rg.Cz.TrOf
