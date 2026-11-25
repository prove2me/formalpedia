-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.det_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:50.055802+00:00
-- url     : https://prove2.me/submissions/72ae33f7-ecde-4f21-ac0d-98f166088a0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_gramF_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) =
      yv τ G f e (Fin.last n) * conj (yv τ G f e (Fin.last n)) * (gramF τ G f).det := by
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M = Matrix.of fun b a =>
      if a = Fin.last n then
        (yv τ G f e b - Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b)
      else if b = a then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Fin (n + 1) → Fin r → ℂ, g = fun a => ∑ b, M b a • f b := ⟨_, rfl⟩
  have hgl : g (Fin.last n) = dv τ G f e := by
    rw [hgdef, dv_eq]
    simp [hMdef]
  have hgc : ∀ a : Fin n, g a.castSucc = f a.castSucc := by
    intro a
    rw [hgdef]
    simp [hMdef, Fin.castSucc_ne_last]
  have hM : M.det = yv τ G f e (Fin.last n) := by
    rw [Matrix.det_of_upperTriangular, Fin.prod_univ_castSucc]
    · simp [hMdef, Fin.castSucc_ne_last]
    · intro i j hij
      have hij' : j < i := hij
      have hj : j ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last i))
      simp [hMdef, hj, ne_of_gt hij']
  have hgram : (gramF τ G g).det =
      (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) := by
    rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]
    have hsub : (gramF τ G g).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
        gramF τ G (fun a : Fin n => f a.castSucc) := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, gramF, Matrix.of_apply, hgc]
    have hz0 : ∀ i : Fin n, gramF τ G g i.castSucc (Fin.last n) = 0 := by
      intro i
      simp only [gramF, Matrix.of_apply, hgc, hgl]
      rw [hC_conj hG (dv τ G f e) (f i.castSucc), dv_orth τ G f e hA hA' i, map_zero]
    have hll : gramF τ G g (Fin.last n) (Fin.last n) = hermC τ G (dv τ G f e) (dv τ G f e) := by
      simp only [gramF, Matrix.of_apply, hgl]
    have hsgn : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    simp only [hz0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hsub, hll, hsgn]
    ring
  have hd := det_gramF_comb hG f M
  rw [← hgdef, hgram, hM] at hd
  rw [hd]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
