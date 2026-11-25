-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_ker_coneMapQ_0aa641207f8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:21.141692+00:00
-- url     : https://prove2.me/submissions/7d5df42f-162a-47ff-9319-7d678c8797ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isPrime_orbitIdeal_50bb33dec3b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_strictMono
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
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) :
    RingHom.ker (coneMapQ x) = ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤ RingHom.ker (coneMapQ x) :=
    Ideal.map_le_iff_le_comap.mpr (comap_ker_coneMapQ x).ge
  refine (eq_of_le_of_not_lt hle fun hlt ↦ ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, comap_ker_coneMapQ] at h
  exact lt_irrefl _ h
end GroundTheory.Heights₂.Heights.OrbitCurve
