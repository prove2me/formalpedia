-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:44.898058+00:00
-- url     : https://prove2.me/submissions/d805dd5d-4f4f-45e0-b15c-2b21592432cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution {P : ArithVariety n} {num den e e' : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} (hden : den ∉ P.ideal)
    (h₁ : den * e - num * chartMonomial c d ∈ P.ideal)
    (h₂ : den * e' - num * chartMonomial c d' ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z (chartMonomial c d') =
      evalCone z e' * evalCone z (chartMonomial c d) := by
  have hmem : den * (e * chartMonomial c d' - e' * chartMonomial c d) ∈ P.ideal := by
    have hid : den * (e * chartMonomial c d' - e' * chartMonomial c d) =
        (den * e - num * chartMonomial c d) * chartMonomial c d' -
          (den * e' - num * chartMonomial c d') * chartMonomial c d := by ring
    rw [hid]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ h₁) (P.ideal.mul_mem_right _ h₂)
  have h := hz.2 _ ((P.isPrime.mem_or_mem hmem).resolve_left hden)
  simp only [evalCone, eval₂_sub, eval₂_mul] at h
  exact sub_eq_zero.mp h
end GroundTheory.Heights₂.Heights.MonomialMap
