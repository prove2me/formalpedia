-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:29.29036+00:00
-- url     : https://prove2.me/submissions/ae5f3e26-5209-4ddc-962b-f7bd190b5695

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_det_Am_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_redGram_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int


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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(Bm X (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(Bm X g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_Am_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3
end ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
