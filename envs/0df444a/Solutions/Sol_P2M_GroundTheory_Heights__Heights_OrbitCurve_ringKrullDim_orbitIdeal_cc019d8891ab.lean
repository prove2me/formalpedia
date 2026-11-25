-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:49.509192+00:00
-- url     : https://prove2.me/submissions/f1cb2b19-021e-403c-b403-0383b9621e97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isPrime_orbitIdeal_50bb33dec3b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_quot_ker_coneMapQ_a85c2d92f4e2
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ orbitIdeal x) =
      ((1 + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, -, h⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  rw [← h, ← ker_coneMapQ, ringKrullDim_quot_ker_coneMapQ hx, Nat.cast_add, Nat.cast_one, add_comm]
end GroundTheory.Heights₂.Heights.OrbitCurve
