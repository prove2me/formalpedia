-- Prove2me | solution 1 for PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:45.918301+00:00
-- url     : https://prove2.me/submissions/04ec284d-2b78-4697-ac7d-e530a067fafa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Misc
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]
namespace PI.OddDualWeyl.Misc
theorem _root_.solution {n : ℕ} (g g' : Matrix (Fin n) (Fin n) K) (h : colSpan O g ≤ colSpan O g') :
    ∃ v : Matrix (Fin n) (Fin n) O, g = g' * v.map (algebraMap O K) := by
  have h2 : Submodule.span O (Set.range fun c : Fin n => fun i => g i c) ≤
      Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) := h
  have hc : ∀ c : Fin n, ∃ a : Fin n → O, ∑ j, a j • (fun i => g' i j) = fun i => g i c := by
    intro c
    have hm : (fun i => g i c) ∈ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) :=
      h2 (Submodule.subset_span ⟨c, rfl⟩)
    exact (Submodule.mem_span_range_iff_exists_fun (R := O)).1 hm
  choose a ha using hc
  refine ⟨Matrix.of fun j c => a c j, ?_⟩
  ext i c
  have hi := congrFun (ha c) i
  rw [← hi, Finset.sum_apply]
  simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end PI.OddDualWeyl.Misc
