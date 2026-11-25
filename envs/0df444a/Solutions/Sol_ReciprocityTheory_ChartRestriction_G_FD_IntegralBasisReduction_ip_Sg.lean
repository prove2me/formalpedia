-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.ip_Sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:06.419209+00:00
-- url     : https://prove2.me/submissions/5a25ee76-3074-4ff2-97b7-d1f9ab58bddb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_hermC_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by
  simp only [ip, Sg, Ly, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hdet, hg⟩ := hy τ
  have hτ : τ.1 (herm X.Gm p q) = hermC τ.1 X.Gm (X.embV p τ) (X.embV q τ) := by
    first
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [hτ, hermC_normal X hdet _ hg]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
