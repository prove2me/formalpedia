-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesLineDegree_inter_line_12696afb69e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:04.98138+00:00
-- url     : https://prove2.me/submissions/918cdc44-db27-4c33-b14a-dc32250afdc8

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
theorem _root_.solution (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) :
    (idealLattice a ⊓ (Submodule.span K
        (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).restrictScalars (𝓞 K)).toAddSubgroup =
      ((a x : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨hv, t, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · have h := (Submodule.mem_pi.mp hv) x (Set.mem_univ _)
      simpa using h
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, t, ?_⟩
    · rw [idealLattice, Submodule.mem_pi]
      intro y _
      by_cases hy : y = x
      · subst hy
        simpa using ht
      · simp only [Pi.single_apply, hy, if_false]
        exact zero_mem _
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]
end GroundTheory.Heights₂.Heights.KLinesLineDegree
