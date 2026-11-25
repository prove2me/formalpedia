-- Prove2me | solution 1 for PI.Dv.TIW.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:14.749823+00:00
-- url     : https://prove2.me/submissions/8b4f2fa9-ceea-4a39-a241-dd12a3a115ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GroupDataExists
import Theorems.Thm_PI_Dv_TIW_norm_chiT_le
import Theorems.Thm_PI_Dv_TIW_prod_expand
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_finrank_le_card
import Theorems.Thm_PI_Dv_TIW_norm_trace_tau_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
  have hd : (Module.finrank K (T.W s) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast finrank_le_card (T.tau s) (T.irr s)
  rw [epsS, epsS, prod_expand, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x y : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      ((chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖ ≤ (Fintype.card G : ℝ) := by
    intro x y
    rw [map_smul, map_smul, Representation.asAlgebraHom_of, smul_eq_mul, map_mul, map_mul, norm_mul, norm_mul]
    have h1 := norm_chiT_le P0 x σ
    have h2 := norm_chiT_le P y σ
    have h3 := norm_trace_tau_le (T.tau s) (x * g' * (y * g)) σ
    calc ‖σ (chiT P0 x)‖ * ‖σ (chiT P y)‖ * ‖σ (LinearMap.trace K (T.W s) ((T.tau s) (x * g' * (y * g))))‖
        ≤ 1 * 1 * (Module.finrank K (T.W s) : ℝ) := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact hd
  calc ∑ x : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (∑ y : G, (chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖
      ≤ ∑ x : G, ∑ y : G, (Fintype.card G : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [map_sum, map_sum, map_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end PI.Dv.TIW
