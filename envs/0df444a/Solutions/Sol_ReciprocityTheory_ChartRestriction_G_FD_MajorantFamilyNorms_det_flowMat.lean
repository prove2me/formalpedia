-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:32.178501+00:00
-- url     : https://prove2.me/submissions/65f16274-48e9-4a08-beb2-15da19890773

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
theorem _root_.solution (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (he : hermC τ.1 X.Gm e e = 0) :
    (X.flowMatV e τ s).det = 1 := by
  unfold Data.flowMatV hermC at *
  have key : (of fun a b => (if a = b then (1 : ℂ) else 0) - I * (X.c τ : ℂ) * s * e a *
      ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) =
      1 + replicateCol Unit (fun a => -(I * (X.c τ : ℂ) * s * e a)) *
        replicateRow Unit (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) := by
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  have hd : (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
      (fun a => -(I * (X.c τ : ℂ) * s * e a)) = 0 := by
    calc (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
          (fun a => -(I * (X.c τ : ℂ) * s * e a))
        = -(I * (X.c τ : ℂ) * s) * ∑ a, ∑ b, e a * τ.1 (X.Gm a b) * (starRingEnd ℂ) (e b) := by
          simp only [dotProduct]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by rw [he, mul_zero]
  rw [key, det_one_add_replicateCol_mul_replicateRow, hd, add_zero]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
