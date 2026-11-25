-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:32.1538+00:00
-- url     : https://prove2.me/submissions/87c78eab-d958-4e5c-8b97-169619773748

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_eps_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_hf_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_fix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)
private lemma hermC_add_left' (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma hermC_sum_smul_left {m : ℕ} (c : Fin m → ℂ) (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
private lemma hermC_sum_smul_right {m : ℕ} (u : Fin r → ℂ) (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf
private lemma hermC_eq_conj_hermC_swap (u v : Fin r → ℂ) : hermC τ G u v = conj (hermC τ G v u) := by
  unfold hermC
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hG i j]
  simp only [cc, IsCMField.complexEmbedding_complexConj]
  ring
end
end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)
variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf
namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
theorem _root_.solution (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f))
    (hg : ∀ k l, hermC τ G (g k) (g l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (v w : Fin r → ℂ) :
    hermC τ G (Mmat τ G p f g *ᵥ v) (Mmat τ G p f g *ᵥ w) = hermC τ G v w := by
  have hconj : ∀ u u', hermC τ G u u' = conj (hermC τ G u' u) := hermC_eq_conj_hermC_swap τ G p f hG hf
  have hdec : ∀ u : Fin r → ℂ, ∃ (x : Fin r → ℂ) (cu : Fin n → ℂ),
      u = x + ∑ k, cu k • f k ∧ ∀ l, hermC τ G x (f l) = 0 := by
    intro u
    refine ⟨u + ∑ k, (-(eps p k * hermC τ G u (f k))) • f k, fun k => eps p k * hermC τ G u (f k), ?_,
      fun l => ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib]
      abel
    · rw [hermC_add_left', hermC_sum_smul_left]
      simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linear_combination (-hermC τ G u (f l)) * eps_sq p l
  have hperp : ∀ x : Fin r → ℂ, (∀ l, hermC τ G x (f l) = 0) → ∀ k, hermC τ G x (g k) = 0 := by
    intro x hx k
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hgf k)
    rw [← ha, hermC_sum_smul_right]
    simp [hx]
  obtain ⟨xv, cv, hv, hxv⟩ := hdec v
  obtain ⟨xw, cw, hw, hxw⟩ := hdec w
  have hMv : Mmat τ G p f g *ᵥ v = xv + ∑ k, cv k • g k := by
    rw [hv, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xv hxv, Mmat_comb τ G p f g hG hf]
  have hMw : Mmat τ G p f g *ᵥ w = xw + ∑ k, cw k • g k := by
    rw [hw, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xw hxw, Mmat_comb τ G p f g hG hf]
  rw [hMv, hMw, hv, hw]
  rw [expand τ G g xv xw cv cw (hperp xv hxv) (fun k => by rw [hconj, hperp xw hxw k, map_zero]),
    expand τ G f xv xw cv cw hxv (fun k => by rw [hconj, hxw k, map_zero])]
  simp only [hg, hf]
end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
