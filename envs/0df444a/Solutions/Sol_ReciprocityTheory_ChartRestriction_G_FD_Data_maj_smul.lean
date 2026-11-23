-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.maj_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:56.494508+00:00
-- url     : https://prove2.me/submissions/ef89d1b0-aa0e-48f5-b2a4-25b9cc3f37e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  have hJ : X.Jp x τ (c • v) = c • X.Jp x τ v := by
    unfold Jp; rw [X.ppos_smul, smul_comm (2 : ℂ) c, ← smul_sub]
  have hH : ∀ u w, hermC τ.1 X.Gm (c • u) (c • w) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm u w := by
    intro u w
    unfold hermC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h1 := hself (c • v)
  rw [show X.Hf x τ (c • v) (c • v) = hermC τ.1 X.Gm (X.Jp x τ (c • v)) (c • v) from rfl, hJ, hH,
    show hermC τ.1 X.Gm (X.Jp x τ v) v = X.Hf x τ v v from rfl, hself v] at h1
  exact_mod_cast h1.symm
end ReciprocityTheory.ChartRestriction.G.FD.Data
