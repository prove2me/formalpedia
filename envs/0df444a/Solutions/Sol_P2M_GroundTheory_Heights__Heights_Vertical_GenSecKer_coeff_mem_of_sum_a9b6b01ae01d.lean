-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:26.054882+00:00
-- url     : https://prove2.me/submissions/f0c33126-5a8e-4156-91c1-7dbd1fadd5e2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecKer
theorem _root_.solution {k L : Type*} [Field k] [Field L] [Algebra k L] (K : IntermediateField k L)
    {n : ℕ} (x c : Fin n → L) (b : L) (j₀ : Fin n) (hx : ∀ j, x j ∈ K) (hx0 : x j₀ ≠ 0)
    (hsum : ∑ j, c j * x j = b) (hb : b ∈ K) (hc : ∀ j, j ≠ j₀ → c j ∈ K) : c j₀ ∈ K := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => c j * x j) (Finset.mem_univ j₀)
  have hval : c j₀ = (b - ∑ j ∈ Finset.univ.erase j₀, c j * x j) / x j₀ := by
    rw [eq_div_iff hx0, ← hsum, ← hsplit]
    ring
  rw [hval]
  exact div_mem (sub_mem hb (sum_mem fun j hj => mul_mem (hc j (Finset.ne_of_mem_erase hj)) (hx j)))
    (hx j₀)
end GroundTheory.Heights₂.Heights.Vertical.GenSecKer
