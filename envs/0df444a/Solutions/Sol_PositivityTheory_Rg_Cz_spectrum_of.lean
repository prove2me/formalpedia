-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.spectrum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:49.412033+00:00
-- url     : https://prove2.me/submissions/327d4770-70f3-441e-ae9f-c4f3ef3b71a1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_Kl_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_cl_all
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
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → Curry → StepChar → Spectrum := by
  intro h1 h2 h3 h5 n M _ _ E hE l s hl hls m
  have hcl : ∀ j : Fin m, SpecA.Kl (xJ E j) s := SpecA.cl_all h1 h3 h5 m n M E hE l s hl hls
  have hcomm := (h2 n M E hE m).1
  have hsum : ∀ k, k ≤ m →
      SpecA.Kl (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) ((k : ℂ) * s) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[0], ?_⟩
      simp
    | succ k ihk =>
      intro hk
      have hk' : k < m := hk
      have hfil : (Finset.univ.filter fun j : Fin m => (j : ℕ) < k + 1) =
          insert ⟨k, hk'⟩ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k + 1), xJ E j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) + xJ E ⟨k, hk'⟩ := by
        rw [hfil, Finset.sum_insert (by simp), add_comm]
      rw [hsplit, show ((k + 1 : ℕ) : ℂ) * s = (k : ℂ) * s + s by push_cast; ring]
      exact SpecA.Kl_sum _ _ (Commute.sum_left _ _ _ fun j _ => hcomm j ⟨k, hk'⟩) _ _ (ihk (by omega)) (hcl ⟨k, hk'⟩)
  exact ⟨fun k hk => hsum k hk, hcl⟩
end PositivityTheory.Rg.Cz
