-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:48.727161+00:00
-- url     : https://prove2.me/submissions/52c99111-7296-437a-8899-9a2eaef97c8d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_qdet_lift
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_tE_empty
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)
omit [Fintype P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl
end PositivityTheory.Rg.Cz.TA
