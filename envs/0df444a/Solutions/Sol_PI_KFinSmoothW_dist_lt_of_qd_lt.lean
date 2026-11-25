-- Prove2me | solution 1 for PI.KFinSmoothW.dist_lt_of_qd_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:42.5375+00:00
-- url     : https://prove2.me/submissions/37d21dc0-0d7c-495c-8043-14ab593da82c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.KFinSmoothW
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 < r) (h : qd x < r ^ 2) :
    dist x 1 < r := by
  rw [dist_eq_norm, Matrix.norm_lt_iff hr]
  intro i j
  have hle : ‖(x - 1) i j‖ ^ 2 ≤ qd x := by
    unfold qd
    rw [Matrix.sub_apply]
    calc ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
        ≤ ∑ j', ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun i' => ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((x - 1) i j)]
end PI.KFinSmoothW
