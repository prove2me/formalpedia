-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:05.337559+00:00
-- url     : https://prove2.me/submissions/8dde12f9-5307-4e6c-bdc2-6834e018f85f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdFibreRatios
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
open GroundTheory.Heights₂.Heights.StandardDualFibreRatios
namespace GroundTheory.Heights₂.Heights.StandardDualFibreRatios
theorem _root_.solution {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2
end GroundTheory.Heights₂.Heights.StandardDualFibreRatios
