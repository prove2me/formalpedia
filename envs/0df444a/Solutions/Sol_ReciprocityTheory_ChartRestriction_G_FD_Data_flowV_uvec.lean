-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.flowV_uvec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:40.923203+00:00
-- url     : https://prove2.me/submissions/bb56c790-1f34-43a3-ad7e-b892902f7842

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ =
    X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ
  congr 1
  ext p q
  have hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) =
      conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l) := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
