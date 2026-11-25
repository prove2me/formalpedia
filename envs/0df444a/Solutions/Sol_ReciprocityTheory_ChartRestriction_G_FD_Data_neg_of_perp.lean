-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.neg_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:12.914975+00:00
-- url     : https://prove2.me/submissions/ccd1df57-ed42-4775-9b31-5befe247440e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_quad
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
section Herm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Herm
section Quad
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Quad
namespace Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem hermC_sum_smul_col_negative_block {p0 : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ)
    (hP : gram τ G P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (n' : Fin (r - p0) → Fin r) (hn' : ∀ j, (n' j : ℕ) = p0 + (j : ℕ)) (β : Fin (r - p0) → ℂ) :
    hermC τ G (∑ j, β j • col P (n' j)) (∑ j, β j • col P (n' j)) =
      -∑ j, β j * conj (β j) := by
  rw [hermC_quad]
  have hcol : ∀ j k, hermC τ G (col P (n' j)) (col P (n' k)) = if j = k then -1 else 0 := by
    intro j k
    have h1 : hermC τ G (col P (n' j)) (col P (n' k)) = gram τ G P (n' j) (n' k) := rfl
    rw [h1, hP, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · subst hjk
      have hlt : ¬ ((n' j : ℕ) < p0) := by rw [hn']; omega
      simp [sgn, hlt]
    · have hne : n' j ≠ n' k := fun h => hjk (Fin.ext (by
        have h2 := congrArg Fin.val h
        rw [hn', hn'] at h2
        omega))
      simp [hne, hjk]
  simp_rw [hcol]
  simp
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {e : Fin r → ℂ} (he : e ≠ 0)
    (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) : (hermC τ.1 X.Gm e e).re < 0 := by
  classical
  by_contra hneg
  push_neg at hneg
  obtain ⟨P, -, hP⟩ := X.signature τ
  have hpd := X.gramPos_posDef hx τ
  have hle := X.p0_le
  let n' : Fin (r - X.p0) → Fin r := fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩
  have hnli : ¬ LinearIndependent ℂ (Sum.elim (fun o : Option (Fin X.p0) => o.elim e (X.colP x τ))
      (fun j : Fin (r - X.p0) => col P (n' j))) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin,
      Module.finrank_fin_fun] at h1
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim] at hg
  set α0 := g (Sum.inl none) with hα0def
  set vW := ∑ a, g (Sum.inl (some a)) • X.colP x τ a with hvW
  set vN := ∑ j, g (Sum.inr j) • col P (n' j) with hvN
  have hN : hermC τ.1 X.Gm vN vN = -∑ j, g (Sum.inr j) * conj (g (Sum.inr j)) :=
    hermC_sum_smul_col_negative_block τ.1 X.Gm P hP n' (fun j => rfl) (fun j => g (Sum.inr j))
  have hsum : vW + α0 • e = -vN := by
    calc vW + α0 • e = (α0 • e + vW + vN) - vN := by abel
      _ = -vN := by rw [hg, zero_sub]
  have hWe : hermC τ.1 X.Gm vW e = 0 := by
    rw [hvW, hermC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hermC_smul_left, ← hermC_conj τ.1 X.Gm_herm e, hperp a]
    simp
  have heW : hermC τ.1 X.Gm e vW = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm vW e, hWe, map_zero]
  have hexp : hermC τ.1 X.Gm (vW + α0 • e) (vW + α0 • e) =
      hermC τ.1 X.Gm vW vW + α0 * conj α0 * hermC τ.1 X.Gm e e := by
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hermC_smul_left, hermC_smul_left,
      hermC_smul_right, hermC_smul_right, hWe, heW]
    ring
  have hWW : hermC τ.1 X.Gm vW vW =
      ∑ a, ∑ b, g (Sum.inl (some a)) * X.gramPos x τ a b * conj (g (Sum.inl (some b))) := by
    rw [hvW]
    exact hermC_quad τ.1 X.Gm _ _
  have hNN : hermC τ.1 X.Gm (-vN) (-vN) = hermC τ.1 X.Gm vN vN := by
    rw [← neg_one_smul ℂ vN, hermC_smul_left, hermC_smul_right]
    simp
  have key : hermC τ.1 X.Gm vW vW + α0 * conj α0 * hermC τ.1 X.Gm e e =
      -∑ j, g (Sum.inr j) * conj (g (Sum.inr j)) := by
    rw [← hexp, hsum, hNN, hN]
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  have hq : 0 ≤ (hermC τ.1 X.Gm vW vW).re := by
    rw [hWW]
    exact quad_re_nonneg hpd.posSemidef _
  have ha : 0 ≤ Complex.normSq α0 * (hermC τ.1 X.Gm e e).re :=
    mul_nonneg (Complex.normSq_nonneg _) hneg
  have hs : 0 ≤ ∑ j, Complex.normSq (g (Sum.inr j)) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hq0 : (hermC τ.1 X.Gm vW vW).re = 0 := by linarith
  have hs0 : ∑ j, Complex.normSq (g (Sum.inr j)) = 0 := by linarith
  have hβ : ∀ j, g (Sum.inr j) = 0 := fun j => Complex.normSq_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hs0 j
      (Finset.mem_univ _))
  have hα : (fun a => g (Sum.inl (some a))) = 0 := by
    by_contra hne
    have h5 : 0 < (hermC τ.1 X.Gm vW vW).re := by
      rw [hWW]
      exact quad_re_pos hpd hne
    linarith
  have hvW0 : vW = 0 := by
    rw [hvW]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show g (Sum.inl (some a)) = 0 from congrFun hα a, zero_smul]
  have hvN0 : vN = 0 := by
    rw [hvN]
    exact Finset.sum_eq_zero fun j _ => by rw [hβ j, zero_smul]
  have hα0 : α0 = 0 := by
    rw [hvW0, hvN0, add_zero, add_zero, smul_eq_zero] at hg
    exact hg.resolve_right he
  rcases i0 with (_ | a) | j
  · exact hi0 hα0
  · exact hi0 (congrFun hα a)
  · exact hi0 (hβ j)
end ReciprocityTheory.ChartRestriction.G.FD.Data
