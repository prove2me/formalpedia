-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.hermC_uvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:31.009163+00:00
-- url     : https://prove2.me/submissions/7430563e-a015-42ac-97f3-5dc6250a692f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution {u : Fin 2 → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (a b : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) = 0 := by
  have key : hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) =
      ∑ i, ∑ k, a τ i * conj (b τ k) * τ.1 (herm X.Gm (u i) (u k)) := by
    simp only [hermC, herm, Data.uvec, Data.emb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_sum, map_mul, emb_cc, Fin.sum_univ_two, map_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [key]
  simp [hu]
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
