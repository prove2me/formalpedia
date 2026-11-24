-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:58.063879+00:00
-- url     : https://prove2.me/submissions/edac766a-0f85-411c-a057-6b1499adee13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {a b : ℕ} {p q : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L a)
    (hq : q ∈ prodSpan L b) : p * q ∈ prodSpan L (a + b) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨Fin.append u v, fun i ↦ ?_, ?_⟩
      · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
        · rw [Fin.append_left]; exact hu i
        · rw [Fin.append_right]; exact hv i
      · rw [Fin.prod_univ_add]
        simp [Fin.append_left, Fin.append_right]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [← algebraMap_smul K c y, smul_eq_C_mul, mul_left_comm, ← smul_eq_C_mul, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul K c x, smul_eq_C_mul, mul_assoc, ← smul_eq_C_mul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx
end GroundTheory.Heights₂.Heights.LatticeModel
