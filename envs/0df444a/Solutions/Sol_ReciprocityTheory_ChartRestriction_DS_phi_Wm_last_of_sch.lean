-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_Wm_last_of_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:36.781948+00:00
-- url     : https://prove2.me/submissions/e3563527-f238-4fe0-b203-882c1b20051f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_apply_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_phi_one_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_slice_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_word_snoc


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
theorem _root_.solution (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by
  classical
  rw [phi_apply_eq, ← (Fin.snocEquiv (fun _ => Fin n × Fin n)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero (fun init _ => ?_)
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hem | ⟨⟨p₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · have h0 := hSch _ (hF (Fin.snoc init p₀))
    rw [sch_phi_one_apply] at h0
    simp only [sch_slice_apply, Fin.update_snoc_last] at h0
    have hs : ∀ x : Fin n × Fin n, (Fin.snocEquiv (fun _ => Fin n × Fin n)) (x, init) = Fin.snoc init x :=
      fun x => rfl
    simp only [hs, sch_word_snoc, Module.End.mul_apply, ← map_sum]
    rw [show (∑ x : Fin n × Fin n, (E x.1 x.2) (F (Fin.snoc init x))) = 0 from h0, map_zero]
end ReciprocityTheory.ChartRestriction.DS
