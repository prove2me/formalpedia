-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.Bm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:26:10.041013+00:00
-- url     : https://prove2.me/submissions/fdb1f53f-44f7-4f28-bd3c-ab93d77a727b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_ip_Sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_zbas_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private lemma ip_sum_lemma_3 (u : X.Ψ → Fin r → ℂ) (a : ι → ℝ) (w : ι → X.Ψ → Fin r → ℂ) :
    ip X u (∑ k, a k • w k) = ∑ k, a k * ip X u (w k) := by
  have h1 : ∀ τ b, u τ b * conj ((∑ k, a k • w k) τ b) =
      ∑ k, ((a k : ℂ) * (u τ b * conj (w k τ b))) := by
    intro τ b
    rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  simp only [ip, h1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  calc ∑ τ, ∑ b, ∑ k, X.c τ * (a k * (u τ b * conj (w k τ b)).re)
      = ∑ τ, ∑ k, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) :=
        Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ k, ∑ τ, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
end IntegralBasisReduction
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Bm X g = Am X y g * LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) := by
  ext i j
  rw [Matrix.mul_apply]
  have hS := (zbas X hy g).sum_repr (Sg X (zbas X hy g j))
  simp only [LinearMap.toMatrix_apply]
  rw [show Bm X g i j = ip X (zbas X hy g i) (Sg X (zbas X hy g j)) by
    simp only [Bm, Matrix.of_apply, zbas_apply]
    exact (ip_Sg X hy _ _).symm]
  conv_lhs => rw [← hS]
  rw [ip_sum_lemma_3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Am, Matrix.of_apply, zbas_apply]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
