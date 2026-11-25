-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:55.461107+00:00
-- url     : https://prove2.me/submissions/a7178f17-b7e1-4b16-8fc2-5c6e84fe0898

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree

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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KLinesLineDegree
theorem _root_.solution (x : Fin n) :
    (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).toAddSubgroup =
      ((1 : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
    AddSubgroup.mem_map, Submodule.mem_one, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 K) K y, ⟨y, rfl⟩, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩
  · rintro ⟨t, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩
end GroundTheory.Heights₂.Heights.KLinesLineDegree
