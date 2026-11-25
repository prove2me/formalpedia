-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.polyVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:12.543207+00:00
-- url     : https://prove2.me/submissions/98bad233-4734-4f3b-a3c6-7fb7b6b50440

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


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
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n h : ℕ} {a : Fin n → C} (F : Lat v (Fin n × Fin h))
    (hF : F.B = freeMat a h) (p : Polynomial C) (hp : ∀ k, v (p.coeff k) ≤ 1)
    (hdeg : p.natDegree < n) (u : Fin h → C) (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => p.eval (a y.1) * u y.2) ∈ F.pts := by
  classical
  refine ⟨fun y ↦ p.coeff (y.1 : ℕ) * u y.2, ?_, ?_⟩
  · intro j
    rw [map_mul]
    exact mul_le_one₀ (hp _) (zero_le) (hu _)
  · funext y
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, freeMat, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
end ReciprocityTheory.PGsh.Up
