-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.om_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:36.763285+00:00
-- url     : https://prove2.me/submissions/90832ebd-6907-4350-a30c-8db70baf726e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hT : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m),
      pm σ * Om E p = (Om E (σ p) * pm σ : Module.End ℂ (TV n M (Fin m)))) (k : ℕ) (ξ : TV n M (Fin m)) :
    alt (firstG m k) (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j ξ) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j (alt (firstG m k) ξ) := by
  simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [mem_firstG] at hσ
  have h1 : ∀ j, pm σ (Om E j ξ) = Om E (σ j) (pm σ ξ) := fun j => LinearMap.congr_fun (hT σ j) ξ
  simp_rw [h1]
  refine Finset.sum_equiv σ ?_ (fun _ _ => rfl)
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    by_contra hc
    rw [not_lt] at hc
    have h3 := σ.injective (hσ (σ j) hc)
    rw [h3] at hc
    omega
  · intro hj
    by_contra hc
    rw [not_lt] at hc
    rw [hσ j hc] at hj
    omega
end PositivityTheory.Rg.Cz.WallAlgP
