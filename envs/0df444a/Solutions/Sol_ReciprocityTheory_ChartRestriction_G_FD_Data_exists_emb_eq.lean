-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.exists_emb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:10.284907+00:00
-- url     : https://prove2.me/submissions/ca556a68-e5c4-4580-899c-99d9410e2d8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_conj_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_sum_emb_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_re_sum_Psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (z : X.Ψ → ℂ)
    (hz : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q) :
    ∃ ω : E, ∀ τ : X.Ψ, z τ = τ.1 ω := by
  classical
  let P : (X.Ψ → ℂ) → E →ₗ[ℚ] ℝ := fun w =>
    { toFun := fun x => (∑ τ : X.Ψ, w τ * τ.1 x).re
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun q x => by
        simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
        rw [show ∑ τ : X.Ψ, w τ * ((q : ℂ) * τ.1 x) = (q : ℂ) * ∑ τ : X.Ψ, w τ * τ.1 x by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring]
        rw [← Complex.ofReal_ratCast, Complex.re_ofReal_mul] }
  set b := NumberField.integralBasis E with hbdef
  have hnd := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hnd b with hddef
  choose q hq using fun i => hz (NumberField.RingOfIntegers.basis E i)
  set ω : E := ∑ i, (2 * q i) • d i with hωdef
  have htr : ∀ j, Algebra.trace ℚ E (ω * b j) = 2 * q j := by
    intro j
    have h : Algebra.traceForm ℚ E ω (b j) = 2 * q j := by
      simp only [hωdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hddef,
        LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simpa [Algebra.traceForm_apply] using h
  have hbj : ∀ j, (b j : E) = ((NumberField.RingOfIntegers.basis E j : 𝓞 E) : E) := fun j => by
    rw [hbdef, NumberField.integralBasis_apply]
  set w : X.Ψ → ℂ := fun τ => z τ - τ.1 ω with hwdef
  have hPb : ∀ j, P w (b j) = 0 := by
    intro j
    show (∑ τ : X.Ψ, (z τ - τ.1 ω) * τ.1 (b j)).re = 0
    simp only [sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
    have e1 : (∑ τ : X.Ψ, z τ * τ.1 (b j)).re = q j := by
      rw [hbj]
      exact hq j
    have e2 : (∑ τ : X.Ψ, τ.1 ω * τ.1 (b j)).re = q j := by
      rw [show ∑ τ : X.Ψ, τ.1 ω * τ.1 (b j) = ∑ τ : X.Ψ, τ.1 (ω * b j) from
        Finset.sum_congr rfl fun τ _ => (map_mul τ.1 ω (b j)).symm]
      rw [X.re_sum_Psi, htr]
      push_cast
      ring
    rw [e1, e2, sub_self]
  have hP0 : P w = 0 := b.ext fun j => by rw [hPb j, LinearMap.zero_apply]
  have hPw : ∀ x : E, (∑ τ : X.Ψ, w τ * τ.1 x).re = 0 := fun x => LinearMap.congr_fun hP0 x
  let W : (E →+* ℂ) → ℂ := fun φ =>
    if h : φ ∈ X.Ψ then w ⟨φ, h⟩ else conj (w ⟨ComplexEmbedding.conjugate φ, (X.conj_mem_iff φ).2 h⟩)
  have hW1 : ∀ τ : X.Ψ, W τ.1 = w τ := fun τ => by
    simp only [W, dif_pos τ.2]
  have hW2 : ∀ τ : X.Ψ, W (ComplexEmbedding.conjugate τ.1) = conj (w τ) := fun τ => by
    have hn : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := fun hc => (X.conj_mem_iff τ.1).1 hc τ.2
    simp only [W, dif_neg hn]
    exact congrArg (fun σ : X.Ψ => conj (w σ)) (Subtype.ext (conjugate_conjugate' τ.1))
  have hW : ∀ x : E, ∑ φ : E →+* ℂ, W φ * φ x = 0 := by
    intro x
    rw [X.sum_emb_split (fun φ => W φ * φ x)]
    simp only [hW1, hW2, ComplexEmbedding.conjugate_coe_eq, ← map_mul (starRingEnd ℂ),
      Complex.add_conj]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hPw x, mul_zero,
      Complex.ofReal_zero]
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => (φ : E →* ℂ))
      (fun a a' h => RingHom.ext fun x => congrArg (fun f : E →* ℂ => f x) h)
  have hsumfun : ∑ φ : E →+* ℂ, W φ • (φ : E → ℂ) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hW x
  refine ⟨ω, fun τ => ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 hli W hsumfun τ.1
  rw [hW1] at h0
  exact sub_eq_zero.1 h0
end ReciprocityTheory.ChartRestriction.G.FD.Data
