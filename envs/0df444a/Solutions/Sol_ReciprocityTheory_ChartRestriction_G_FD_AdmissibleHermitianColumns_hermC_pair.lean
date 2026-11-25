-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.hermC_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:58.66704+00:00
-- url     : https://prove2.me/submissions/b35a6530-7ffc-433e-9a2c-ccab1d9c17dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section gram
variable (X : Data E r)
private lemma hermC_add_smul_add_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u e v : Fin r → ℂ)
    (β γ : ℂ) :
    hermC τ G (u + β • e) (v + γ • e) = hermC τ G u v + conj γ * hermC τ G u e +
      β * hermC τ G e v + β * conj γ * hermC τ G e e := by
  simp only [hermC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma hermC_swap_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc', hG]
  ring
end gram
section affine
end affine
section adm
variable (X : Data E r)
end adm
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (e u v : Fin r → ℂ) (he : hermC τ G e e = 0) (α : ℂ) :
    hermC τ G (u + (α * hermC τ G u e) • e) (v + (α * hermC τ G v e) • e) =
      hermC τ G u v + (α + conj α) * hermC τ G u e * conj (hermC τ G v e) := by
  rw [hermC_add_smul_add_smul, hermC_swap_of_conj_symm τ G hG v e, he]
  simp only [map_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
