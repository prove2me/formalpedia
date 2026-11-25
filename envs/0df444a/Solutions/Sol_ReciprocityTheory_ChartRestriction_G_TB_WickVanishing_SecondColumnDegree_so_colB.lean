-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_colB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:46.71031+00:00
-- url     : https://prove2.me/submissions/e5e1808e-6009-41ac-ae3b-3e0d7d590032

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_def
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_pderiv_colE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (c : ι → ι → k) (b : Fin n) (Q : MvPolynomial ι k) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    secondOrder k (cB c b) (colE b Q * R) = colE b (secondOrder k c Q) * R := by
  classical
  have hd : ∀ l l' : ι, pderiv (l, b) (pderiv (l', b) (colE b Q * R)) =
      colE b (pderiv l (pderiv l' Q)) * R := by
    intro l l'
    rw [Derivation.leibniz, hR, smul_zero, zero_add, smul_eq_mul, pderiv_colE,
      Derivation.leibniz, hR, smul_zero, add_zero, smul_eq_mul, pderiv_colE, mul_comm]
  have key : ∀ p q : ι × Fin n, C (cB c b p q) * pderiv p (pderiv q (colE b Q * R)) =
      if p.2 = b ∧ q.2 = b then C (c p.1 q.1) * (colE b (pderiv p.1 (pderiv q.1 Q)) * R) else 0 := by
    rintro ⟨l, y⟩ ⟨l', y'⟩
    simp only [cB]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hd]
    · simp
  rw [so_def, so_def]
  simp only [key, map_sum, Finset.sum_mul, map_mul, MvPolynomial.rename_C]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single b]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [mul_assoc]
    · intro y _ hy
      simp [hy]
    · simp
  · intro y _ hy
    simp [hy]
  · simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
