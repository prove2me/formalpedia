-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.eq_zero_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:26:10.696255+00:00
-- url     : https://prove2.me/submissions/33fba80a-96cf-4c1c-9014-987cdfe5b1b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_add_conj__a59ed36e9da2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
theorem _root_.solution (X : Data E r) (d : X.Ψ → ℂ)
    (h : ∀ β : 𝓞 E, ∑ τ : X.Ψ, 2 * (d τ * conj (τ.1 (β : E))).re = 0) (τ0 : X.Ψ) :
    d τ0 = 0 := by
  classical
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  let d' : (E →+* ℂ) → ℂ := fun σ => if hσ : σ ∈ X.Ψ then d ⟨σ, hσ⟩ else 0
  have hd' : ∀ τ : X.Ψ, d' τ.1 = d τ := fun τ => by simp [d', τ.2]
  let c : (E →+* ℂ) → ℂ := fun σ =>
    if σ ∈ X.Ψ then conj (d' σ) else d' (ComplexEmbedding.conjugate σ)
  have hint : ∀ β : 𝓞 E, ∑ σ : E →+* ℂ, c σ * σ (β : E) = 0 := by
    intro β
    have hb' : ∑ τ ∈ X.Ψ, (d' τ * conj (τ (β : E)) + conj (d' τ * conj (τ (β : E)))) = 0 := by
      have h2 : ((∑ τ : X.Ψ, 2 * (d τ * conj (τ.1 (β : E))).re : ℝ) : ℂ) = 0 := by
        rw [h β]; simp
      push_cast at h2
      rw [← h2, ← Finset.sum_coe_sort X.Ψ]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hd', add_conj']
    rw [← Finset.sum_add_sum_compl X.Ψ]
    have h1 : ∑ σ ∈ X.Ψ, c σ * σ (β : E) = ∑ σ ∈ X.Ψ, conj (d' σ * conj (σ (β : E))) := by
      refine Finset.sum_congr rfl fun σ hσ => ?_
      simp [c, hσ]
    have h2 : ∑ σ ∈ X.Ψᶜ, c σ * σ (β : E) = ∑ σ ∈ X.Ψ, d' σ * conj (σ (β : E)) := by
      apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
        (fun σ => ComplexEmbedding.conjugate σ)
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
        rw [X.cmType, hcc]
        exact hσ
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
        exact (X.cmType σ).mp hσ
      · intro σ _
        exact hcc σ
      · intro σ _
        exact hcc σ
      · intro σ hσ
        simp only [Finset.mem_compl, Finset.mem_coe] at hσ
        simp [c, hσ, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, h2, ← Finset.sum_add_distrib, ← hb']
    exact Finset.sum_congr rfl fun σ _ => add_comm _ _
  have hall : ∀ x : E, ∑ σ : E →+* ℂ, c σ * σ x = 0 := by
    intro x
    obtain ⟨y, hy, hyx⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
    have hx := hint ⟨y • x, hyx⟩
    change ∑ σ : E →+* ℂ, c σ * σ (y • x) = 0 at hx
    have e2 : ∑ σ : E →+* ℂ, c σ * σ (y • x) = (y : ℂ) * ∑ σ : E →+* ℂ, c σ * σ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [zsmul_eq_mul, map_mul, map_intCast]
      ring
    rw [e2] at hx
    exact (mul_eq_zero.mp hx).resolve_left (by exact_mod_cast hy)
  have hli := (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
    (fun a b hab => RingHom.ext fun x => by
      have := congrArg (fun f : E →* ℂ => f x) hab
      simpa using this)
  have hc0 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    simpa [Finset.sum_apply] using hall x)
  have hnot : ComplexEmbedding.conjugate τ0.1 ∉ X.Ψ := (X.cmType τ0.1).mp τ0.2
  have h0 := hc0 (ComplexEmbedding.conjugate τ0.1)
  simp only [c, hnot, if_false, hcc] at h0
  rw [← hd']
  exact h0
end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
