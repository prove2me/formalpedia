-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:26.557549+00:00
-- url     : https://prove2.me/submissions/d587da29-2f0e-4ee0-a417-e98d2d35369f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (D : ℕ) (h : MvPolynomial (Coord n) ℂ) :
    ∀ p ∈ P.ideal, coeffVec (offMonos n k₀ D) (h * atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a =>
    intro p hp
    rw [C_mul', map_smul]
    exact Submodule.smul_mem _ a (coeffVec_atBlock_mem P k₀ w D hp)
  | add f g hf hg =>
    intro p hp
    rw [add_mul, map_add]
    exact Submodule.add_mem _ (hf p hp) (hg p hp)
  | mul_X f v hf =>
    intro p hp
    by_cases hv : v.1 = k₀
    · have h0 : coeffVec (offMonos n k₀ D) (f * X v * atBlock k₀ w p) = 0 := by
        funext μ
        rw [coeffVec_apply, mul_right_comm, coeff_mul_X']
        have hμ := mem_offMonos.mp μ.2
        have hμv : μ.1 v = 0 := by
          have := le_weight_coordDeg μ.1 v
          rw [hμ, hv, offDeg, Function.update_self] at this
          exact Nat.le_zero.mp this
        rw [if_neg (by simpa [Finsupp.mem_support_iff] using hμv)]
        rfl
      rw [h0]
      exact Submodule.zero_mem _
    · have hX : atBlock k₀ w (X v) = X v := by simp [atBlock_apply, sepBlock, hv]
      rw [mul_assoc, ← hX, ← map_mul]
      exact hf _ (P.ideal.mul_mem_left _ hp)
end GroundTheory.Heights₂.Heights.BlockSurjectivity
