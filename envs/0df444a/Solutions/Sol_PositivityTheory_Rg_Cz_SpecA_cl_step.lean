-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.cl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:46.545978+00:00
-- url     : https://prove2.me/submissions/8c13ea29-1c01-4564-aa6e-7cd1acb475c3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_Kl_nat
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_Kl_lift
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_filt
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
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) (k : ℕ) (ih : Cl k) : Cl (1 + k) := by
  intro n M _ _ E hE l s hl hls j
  obtain ⟨hbij, -, hcast, hnat, -, -, -⟩ := h3 n M E 1 k
  obtain ⟨hstep1, hstep2⟩ := h5 n M E hE l hl
  choose r hr using hls
  induction j using Fin.addCases with
  | left i =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hcast 0)
    apply Kl_lift
    refine ⟨List.ofFn r, ?_⟩
    have hx : xJ E (0 : Fin 1) = Om E 0 := by simp [xJ]
    have he : (List.ofFn r).map (fun r : ℕ => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (s + r)) =
        List.ofFn fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c) := by
      rw [List.map_ofFn]
      congr 1
      funext c
      simp [hr c]
    rw [hx, he]
    exact hstep1
  | right j' =>
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hnat j')
    obtain ⟨hG, hGA, -, -⟩ := h1 n M (Fin 1) E hE Finset.univ
    have hls' : ∀ c c', ∃ r' : ℕ, Function.update l c (l c + 1) c' = s + r' := by
      intro c c'
      by_cases hcc : c' = c
      · subst hcc
        refine ⟨r c' + 1, ?_⟩
        simp [hr c']
        ring
      · exact ⟨r c', by simp [hcc, hr c']⟩
    obtain ⟨L, hL⟩ := filt (tE Finset.univ E) (Om E 0) hG (fun a b => hGA 0 (Finset.mem_univ _) a b) l s j'
      (by
        intro W hW hA c N _ _ F q hF hq hFq hAq
        exact ih n N F hF (Function.update l c (l c + 1)) s (hstep2 W N F q hW hA c hq hFq hAq) (hls' c) j')
      (List.finRange n)
    have h0 : ((List.finRange n).map fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c)).prod = 0 := by
      rw [← List.ofFn_eq_map]
      exact hstep1
    refine ⟨L, LinearMap.ext fun f => ?_⟩
    rw [LinearMap.zero_apply]
    exact hL f (fun I => by rw [h0]; rfl)
end PositivityTheory.Rg.Cz.SpecA
