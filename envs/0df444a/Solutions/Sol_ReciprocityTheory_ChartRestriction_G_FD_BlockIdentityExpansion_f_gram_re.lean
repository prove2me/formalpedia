-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion.f_gram_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:09.88516+00:00
-- url     : https://prove2.me/submissions/ac39224d-dd32-4b38-a957-3d23ca171d04

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma hermC_sum_left_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (c : Fin m → ℂ)
    (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
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
private lemma hermC_sum_right_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (u : Fin r → ℂ)
    (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
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
end
end ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
theorem _root_.solution (X : Data E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ)
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (a : Fin (r - 2) → ℂ) :
    (hermC τ.1 X.Gm (∑ k, a k • f τ k) (∑ k, a k • f τ k)).re =
      ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖a k‖ ^ 2 else -‖a k‖ ^ 2 := by
  obtain ⟨-, -, hgr, -, -⟩ := hf τ
  rw [hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2, hgr, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Complex.mul_conj, Complex.normSq_eq_norm_sq] <;>
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
