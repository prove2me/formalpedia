-- Prove2me | solution 1 for PI.ScRefExists.WF.proj_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:51.880079+00:00
-- url     : https://prove2.me/submissions/f417b8d8-b592-4384-922a-b017a572fe84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_ap_smul
import Theorems.Thm_PI_ScRefExists_WF_hG_LA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution {r : ℕ} (e f : Fin r → Fin I.n → I.E) (hp : p.Prime)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p)
    (S : Set (Fin I.n → I.E)) (hS : Set.range e ∪ Set.range f ⊆ S) :
    proj e f y ∈ Submodule.span (Ap I p) S := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inl ⟨a, rfl⟩)))
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inr ⟨a, rfl⟩)))
    rwa [ap_smul] at h1
end PI.ScRefExists.WF
