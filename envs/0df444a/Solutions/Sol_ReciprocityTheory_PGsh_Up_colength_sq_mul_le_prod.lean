-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.colength_sq_mul_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:00.112991+00:00
-- url     : https://prove2.me/submissions/56393ad4-4b80-4fdf-b486-d350e89dace8

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_blkLat_pts
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colen_blk
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_mul_le
import Theorems.Thm_ReciprocityTheory_PGsh_Up_valuation_pairwiseDifferenceProduct_pow_le_colength_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) :
    colen M' M ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s := by
  have hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι), v L.B.det ≠ 0 :=
    fun L => (map_ne_zero v).2 L.det_ne
  set S : Lat v (Fin n × Fin s) := blkLat Mτ
  set S' : Lat v (Fin n × Fin s) := blkLat M'τ
  have h2 := valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hMst hMτ (blkLat_pts Mτ)
  have h3 := colength_sq_mul_le a hinj hint s h A F M' S' M'τ hF hM' hM'τ (blkLat_pts M'τ)
  have hP : colen S' S = ∏ τ, colen (M'τ τ) (Mτ τ) := colen_blk M'τ Mτ
  have hid : colen M' M * colen M S = colen M' S' * colen S' S := by
    simp only [ReciprocityTheory.PGsh.colen]
    rw [div_mul_div_cancel₀ (hdet M), div_mul_div_cancel₀ (hdet S')]
  have hc : 0 < colen M S ^ 2 := by
    have : colen M S ≠ 0 := div_ne_zero (hdet M) (hdet S)
    positivity
  rw [← hP]
  refine le_of_mul_le_mul_right ?_ hc
  calc colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2
      = colen M' S' ^ 2 * v (discr a) ^ h * colen S' S ^ 2 := by
        rw [show colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2 =
          (colen M' M * colen M S) ^ 2 * v (discr a) ^ h by ring, hid]; ring
    _ ≤ v (discr a) ^ (2 * s) * colen S' S ^ 2 := by gcongr
    _ = colen S' S ^ 2 * v (discr a) ^ s * v (discr a) ^ s := by ring
    _ ≤ colen S' S ^ 2 * v (discr a) ^ s * colen M S ^ 2 := by gcongr
end ReciprocityTheory.PGsh.Up
