-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hC_ppos_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:16.899403+00:00
-- url     : https://prove2.me/submissions/dfc6bb55-8a48-47ca-9fd2-da7024ba5b69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
section onetau
variable (ξ : Fin r → E) (τ : X.Ψ)
private theorem hermC_sum_const_smul_left {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (cf : Fin n → ℂ) (w : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    hermC σ G (∑ a, cf a • w a) e = ∑ a, cf a * hermC σ G (w a) e := by
  have hadd : ∀ u u' : Fin r → ℂ, hermC σ G (u + u') e = hermC σ G u e + hermC σ G u' e := by
    intro u u'
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (k : ℂ) (u : Fin r → ℂ), hermC σ G (k • u) e = k * hermC σ G u e := by
    intro k u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h0 : hermC σ G 0 e = 0 := by simp [hermC]
  suffices H : ∀ s : Finset (Fin n),
      hermC σ G (∑ a ∈ s, cf a • w a) e = ∑ a ∈ s, cf a * hermC σ G (w a) e from H _
  intro s
  refine Finset.induction_on s ?_ ?_
  · simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsm, ih]
end onetau
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ v) (emb τ.1 ξ) =
      dotProduct (fun b => hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)))
        (Matrix.mulVec (X.gramPos x τ)⁻¹
          (fun a => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (emb τ.1 ξ))) := by
  unfold Data.ppos
  rw [hermC_sum_const_smul_left]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
