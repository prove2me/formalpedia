-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:31.739637+00:00
-- url     : https://prove2.me/submissions/33d559f8-19be-4100-b559-c9dbb484319b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) (v : TVar D N)
    (hv : ¬ (v.1 = 0 ∧ v.2 = j₀)) :
    psiS (chiImg j₀ x v) = sImg (Ω := Ω) j₀ x v := by
  obtain ⟨i, j⟩ := v
  by_cases hj : j = j₀
  · rw [hj] at hv ⊢
    have hi : i ≠ 0 := fun h => hv ⟨h, rfl⟩
    have h1 : chiImg j₀ x (i, j₀) = -∑ k, X (i, k) * C (x k) :=
      Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr (i, k)) * C (x k)) := by
      unfold sImg
      congr 1
      exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans
        (if_neg hi)
    rw [h1, h2]
    simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    rw [← hk]
    have h1 : chiImg j₀ x (i, j₀.succAbove k) = X (i, k) :=
      Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _ k
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
        algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
      unfold sImg
      congr 1
      exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k
    rw [h1, h2]
    simp [psiS, MvPolynomial.rename_X]
end ReciprocityTheory.ChartRestriction.G.T0
