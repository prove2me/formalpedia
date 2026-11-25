-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.maj_jp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:05.974644+00:00
-- url     : https://prove2.me/submissions/602cdc91-8612-4440-ad63-5888c8a13e56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_jp
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
private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC σ G (∑ k, u k • v k) y = ∑ k, u k * hermC σ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC σ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private lemma maj_eq_lemma_7 (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    X.maj x τ v = (hermC τ.1 X.Gm (X.jp x τ v) v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.jp
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  rw [maj_eq_lemma_7 X τ x (X.jp x τ v), maj_eq_lemma_7 X τ x v, X.jp_jp hx τ v,
    ← hermC_conj τ.1 X.Gm_herm v (X.jp x τ v), Complex.conj_re]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
