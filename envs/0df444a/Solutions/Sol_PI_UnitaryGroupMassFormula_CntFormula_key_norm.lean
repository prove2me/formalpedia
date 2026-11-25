-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.key_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:58.80068+00:00
-- url     : https://prove2.me/submissions/963f8105-5a7a-464d-a4fb-87b192a4e917

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_sum_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_eq_zero_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
variable {F}
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) (c : ι → F) (u : Fin n → F) (hu : ∑ i, c i • X i = u)
    (j : ι) (hj : ∀ i, valuation F (c i) ≤ valuation F (c j)) (hcj : c j ≠ 0)
    (hlt : ∀ k, valuation F (u k) < valuation F (c j)) : False := by
  have hvj : 0 < valuation F (c j) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
  have hd : ∀ i, c i / c j ∈ 𝒪[F] := fun i =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_div₀]; exact (div_le_one₀ hvj).2 (hj i))
  have hz : ∑ i, resF F (c i / c j) • redM F X i = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, redM, Pi.zero_apply]
    have h := resF_sum_mul F (fun i => c i / c j) (fun i => X i k) hd (fun i => hX i k)
    rw [← h]
    apply resF_eq_zero_of_lt F
    have hs : ∑ i, c i / c j * X i k = u k / c j := by
      rw [← hu, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, map_div₀]
    exact (div_lt_one₀ hvj).2 (hlt k)
  have h1 := (Fintype.linearIndependent_iff.1 hred) _ hz j
  rw [div_self hcj, resF_one] at h1
  exact one_ne_zero h1
end PI.UnitaryGroupMassFormula.CntFormula
