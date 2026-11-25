-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.conj_tensor_entry_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:56.958796+00:00
-- url     : https://prove2.me/submissions/994ec263-3dc1-4cb6-8b63-ed1f1c21c470

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_cj_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_spl_tE
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
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]
end PositivityTheory.Rg.Cz.TA
