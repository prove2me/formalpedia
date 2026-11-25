-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.unfoldEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:06.032864+00:00
-- url     : https://prove2.me/submissions/7ab560fa-100d-4032-9d75-2fe5ac763953

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_chArg_map
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_comp_symm_comp
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_symm_comp_comp
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_Q_map
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_extractFree_fillMatrix
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_fillMatrix_extractFree
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_isFillOf_fillMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution : UnfoldEquiv := by
  intro k₀ K _ _ _ n' n c psi hpsi wt Φ r g hmem hg xj
  have hmem' : PI.UnfoldEquiv.Loc.R1cond k₀ n c r ∧ PI.UnfoldEquiv.Loc.R1cond k₀ n c r⁻¹ := hmem
  have hr : PI.UnfoldEquiv.Loc.R1cond k₀ n c r := hmem'.1
  have hrs : PI.UnfoldEquiv.Loc.R1cond k₀ n c r.symm := hmem'.2
  have hgs : ∀ v, r.symm (PI.UnfoldEquiv.Loc.inX k₀ n c v) = PI.UnfoldEquiv.Loc.inX k₀ n c (g.symm v) := by
    intro v
    rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]
  have hgg : g.toLinearMap ∘ₗ (g.symm.toLinearMap ∘ₗ xj) = xj := by
    apply LinearMap.ext
    intro v
    simp
  let F : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun t => fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t)
  let G : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun s => fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s)
  have hF : ∀ t, PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t) = r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t := fun t =>
    fillMatrix_extractFree (Q_map hrs hgs (isFillOf_fillMatrix xj t))
  have hG : ∀ s, PI.UnfoldEquiv.Loc.xx1 xj (G s) = r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s := fun s => by
    have h1 := Q_map hr hg (isFillOf_fillMatrix (g.symm.toLinearMap ∘ₗ xj) s)
    rw [hgg] at h1
    exact fillMatrix_extractFree h1
  have hbij : Function.Bijective F := by
    refine Function.bijective_iff_has_inverse.mpr ⟨G, fun t => ?_, fun s => ?_⟩
    · show fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t)) = t
      rw [hF, comp_symm_comp, extractFree_fillMatrix]
    · show fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj (G s)) = s
      rw [hG, symm_comp_comp, extractFree_fillMatrix]
  have hca : ∀ t : PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀, PI.UnfoldEquiv.Loc.chArg (PI.UnfoldEquiv.Loc.xx1 xj t) =
      PI.UnfoldEquiv.Loc.chArg (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t) + PI.UnfoldEquiv.Loc.n1Arg r := fun t => by
    have h2 := chArg_map hr (Q_map hrs hgs (isFillOf_fillMatrix xj t))
    rwa [comp_symm_comp] at h2
  simp only [PI.UnfoldEquiv.Loc.E1, Fintype.piFinset_univ]
  rw [mul_left_comm (psi _)]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective F hbij _ _ (fun t => ?_)
  rw [hF, hca, neg_add, hpsi]
  ring
end PI.UnfoldEquiv.UnitaryGroupMassFormula
