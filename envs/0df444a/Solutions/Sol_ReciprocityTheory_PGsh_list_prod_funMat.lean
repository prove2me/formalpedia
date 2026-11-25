-- Prove2me | solution 1 for ReciprocityTheory.PGsh.list_prod_funMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:08.715424+00:00
-- url     : https://prove2.me/submissions/a78318fd-59e4-4e5c-b0a3-dd84c0ce5882

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_funMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_funMat_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s)
    (hσ : ∀ b, φ (σ b) = φ b) (L : List (Fin s)) (hL : L.Nodup) :
    (L.map fun k => funMat (fun b => if φ b = k then σ b else b)).prod =
      funMat (fun b => if φ b ∈ L then σ b else b) := by
  induction L with
  | nil => simp [funMat_id]
  | cons k L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, funMat_mul]
    congr 1
    funext b
    by_cases hb : φ b ∈ L
    · have hk : φ b ≠ k := fun h => hL.1 (by rw [← h]; exact hb)
      simp [hb, hσ, hk]
    · by_cases hk : φ b = k <;> simp [hb, hk, hL.1]
end ReciprocityTheory.PGsh
