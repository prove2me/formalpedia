-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Mmat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:26:10.11971+00:00
-- url     : https://prove2.me/submissions/5acef555-0b12-425c-8979-6c78ff640869

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
