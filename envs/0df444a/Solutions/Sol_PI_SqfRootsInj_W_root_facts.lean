-- Prove2me | solution 1 for PI.SqfRootsInj.W.root_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:32.47551+00:00
-- url     : https://prove2.me/submissions/b664edae-3066-4751-8706-25f74e8ca19a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootsInj.W
theorem _root_.solution {r : ℕ} {f : (ZMod g)[X]} (hf : IsLab g r f) {x : Fbar g}
    (hx : x ∈ rootsBar f) :
    x ≠ 0 ∧ minpoly (ZMod g) x ∣ f ∧ (minpoly (ZMod g) x).natDegree ≤ r ∧
      1 ≤ (minpoly (ZMod g) x).natDegree := by
  obtain ⟨hmon, hdeg, hc0⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots'] at hx
    rw [← eval_map_algebraMap]
    exact hx.2
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hdvd := minpoly.dvd (ZMod g) x hroot
  refine ⟨?_, hdvd, ?_, minpoly.natDegree_pos hint⟩
  · rintro rfl
    apply hc0
    have h0 := coeff_zero_eq_aeval_zero' (A := Fbar g) f
    rw [hroot] at h0
    exact (algebraMap (ZMod g) (Fbar g)).injective (by rw [h0, map_zero])
  · rw [← hdeg]
    exact natDegree_le_of_dvd hdvd hf0
end PI.SqfRootsInj.W
