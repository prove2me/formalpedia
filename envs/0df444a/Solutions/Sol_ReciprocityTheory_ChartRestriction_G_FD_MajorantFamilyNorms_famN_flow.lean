-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.famN_flow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:47.210772+00:00
-- url     : https://prove2.me/submissions/b02a6197-dc38-4048-af7c-24bc3ab06968

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
theorem _root_.solution (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by
  unfold Data.flowV flw famN mat
  funext a c
  show ∑ b, X.flowMatV (e τ) τ (s τ) c b * x τ b (Fin.castLE h a) =
    x τ c (Fin.castLE h a) + (-I * (X.c τ : ℂ) * s τ *
      hermC τ.1 X.Gm (fun d => x τ d (Fin.castLE h a)) (e τ)) * e τ c
  unfold Data.flowMatV hermC
  simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
