-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPoly_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:28.747255+00:00
-- url     : https://prove2.me/submissions/aaf095cb-dba1-4e1c-88ab-297070bf7564

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paS_deg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_eq_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ p : MvPolynomial ι ℂ, p.totalDegree ≤ c ∧ F = paPF p := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    refine ⟨MvPolynomial.monomial α 1, ?_, rfl⟩
    calc (MvPolynomial.monomial α (1 : ℂ)).totalDegree ≤ α.sum (fun _ => id) :=
          MvPolynomial.totalDegree_monomial_le _ _
      _ = α.degree := sum_eq_degree α
      _ ≤ c := paS_deg hα
  | zero => exact ⟨0, by simp, by funext v; simp [paPF]⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨p + r, (MvPolynomial.totalDegree_add _ _).trans (max_le hp hr), (paPF_add p r).symm⟩
  | smul a x _ hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨MvPolynomial.C a * p, ?_, (paPF_smul a p).symm⟩
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simpa using hp
end ReciprocityTheory.ChartRestriction.G.I2
