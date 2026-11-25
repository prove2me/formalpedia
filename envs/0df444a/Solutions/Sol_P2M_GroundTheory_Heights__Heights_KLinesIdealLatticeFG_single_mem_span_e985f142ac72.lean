-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_single_mem_span_e985f142ac72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:52.784528+00:00
-- url     : https://prove2.me/submissions/3d3a3906-3103-4bea-ac7f-18ef63bf6f27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG

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
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
namespace GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
theorem _root_.solution (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by
  have hbot : (a x : Submodule (𝓞 K) K) ≠ ⊥ := by
    rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hmem : (Pi.single x y : Fin n → K) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    by_cases h : i = x
    · subst h; simpa using hy
    · simp [h]
  have heq : (Pi.single x 1 : Fin n → K) = y⁻¹ • (Pi.single x y : Fin n → K) := by
    ext i
    by_cases h : i = x
    · subst h; simp [hy0]
    · simp [h]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
