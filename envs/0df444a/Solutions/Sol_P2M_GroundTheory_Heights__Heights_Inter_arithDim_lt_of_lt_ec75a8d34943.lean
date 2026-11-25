-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_arithDim_lt_of_lt_ec75a8d34943
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:26.461164+00:00
-- url     : https://prove2.me/submissions/c0e0f24a-5d27-4ba7-aa7e-f3d13d01abc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega
end GroundTheory.Heights₂.Heights.Inter
