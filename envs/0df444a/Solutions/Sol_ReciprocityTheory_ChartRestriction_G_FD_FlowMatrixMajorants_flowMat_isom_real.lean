-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flowMat_isom_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:24.933497+00:00
-- url     : https://prove2.me/submissions/001c0764-4547-42a4-a9f2-1800bfb27d23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj

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
namespace FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
private lemma hermC_sub_smul_left_lemma_8 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (p - a • q) y = hermC σ G p y - a * hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma hermC_sub_smul_right_lemma_9 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (p - a • q) = hermC σ G y p - conj a * hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end FlowMatrixMajorants
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
theorem _root_.solution (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (t : ℝ)
    (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ t) u) (Matrix.mulVec (X.flowMat ξ τ t) v) =
      hermC τ.1 X.Gm u v := by
  have hMv : ∀ w : Fin r → ℂ, Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
    intro w
    funext i
    show ∑ b, X.flowMat ξ τ t i b * w b = _
    simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hermC, Data.emb]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hMv u, hMv v, hermC_sub_smul_left_lemma_8, hermC_sub_smul_right_lemma_9, hermC_sub_smul_right_lemma_9,
    hiso, ← hermC_conj τ.1 X.Gm_herm v (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
