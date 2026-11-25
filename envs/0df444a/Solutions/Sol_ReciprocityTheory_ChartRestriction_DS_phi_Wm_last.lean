-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_Wm_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:25.019835+00:00
-- url     : https://prove2.me/submissions/f1cd2692-062c-40fc-b491-22a49eed47ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_one_Wm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_coord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_slice_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_word_snoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_phi_one_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by

  let e : (Fin k → Fin n × Fin n) × (Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
    { toFun := fun q => Fin.snoc q.1 q.2
      invFun := fun κ => (Fin.init κ, κ (Fin.last k))
      left_inv := fun q => by simp
      right_inv := fun κ => Fin.snoc_init_self κ }
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply, sch_coord_apply]
  rw [Fintype.sum_equiv e.symm _
    (fun q => word E (Fin.snoc q.1 q.2 : Fin (k + 1) → Fin n × Fin n) (F (Fin.snoc q.1 q.2)))
    (fun κ => by simp only [e, Equiv.coe_fn_symm_mk, Fin.snoc_init_self])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun init _ => ?_
  simp only [sch_word_snoc, Module.End.mul_apply]
  rw [← map_sum]
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hX | ⟨⟨p0⟩⟩
  · simp
  · have h := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
    rw [sch_phi_one_apply] at h
    simp only [sch_slice_apply, Fin.update_snoc_last] at h
    rw [h, map_zero]
end ReciprocityTheory.ChartRestriction.DS
