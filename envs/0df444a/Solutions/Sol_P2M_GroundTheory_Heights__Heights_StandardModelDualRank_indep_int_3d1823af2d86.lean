-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:29:27.842245+00:00
-- url     : https://prove2.me/submissions/9b3c8edb-4829-4e0f-8087-1346c2c23081

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_C_a4b940bce8ef

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (q : Fin n → MvPolynomial (Fin i) ℤ)
    (h : ∑ k, embK K i (B k) * psiZ K i (q k) = 0) : ∀ k, q k = 0 := by
  have h' : ∑ k, C (B k) * MvPolynomial.map (Int.castRingHom K) (q k) = 0 := by
    apply psi_injective
    rw [map_sum, map_zero]
    simpa [psiZ, psi_C] using h
  have hB : LinearIndependent ℤ B := B.linearIndependent.restrict_scalars' ℤ
  intro k
  ext m
  have hm := congrArg (coeff m) h'
  rw [coeff_sum, coeff_zero] at hm
  simp only [coeff_C_mul, coeff_map, eq_intCast] at hm
  have := Fintype.linearIndependent_iff.mp hB (fun k => coeff m (q k)) (by simpa [zsmul_eq_mul, mul_comm] using hm) k
  simpa using this
end GroundTheory.Heights₂.Heights.StandardModelDualRank
