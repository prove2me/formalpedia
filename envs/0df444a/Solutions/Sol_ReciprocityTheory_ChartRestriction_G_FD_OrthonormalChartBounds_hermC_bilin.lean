-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.hermC_bilin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:57.989819+00:00
-- url     : https://prove2.me/submissions/731fedfc-ae7b-4637-8621-75d2e7b155b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_fin_sum_smul_left {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (p : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) v = ∑ i, p i * hermC τ G (f i) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
private lemma hermC_fin_sum_smul_right_mul_conj {n : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (u : Fin r → ℂ)
    (q : Fin n → ℂ) (f : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ j, q j • f j) = ∑ j, hermC τ G u (f j) * conj (q j) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) (∑ j, q j • f j) =
      ∑ i, ∑ j, p i * hermC τ G (f i) (f j) * conj (q j) := by
  rw [hermC_fin_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_fin_sum_smul_right_mul_conj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
