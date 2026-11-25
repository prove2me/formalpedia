-- Prove2me | solution 1 for PI.OmVe.card_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:52.236403+00:00
-- url     : https://prove2.me/submissions/e8a28fb3-a97f-45ef-9e8e-cb3e2d926c55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CardAndAdd
import Theorems.Thm_PI_OmVe_ffH_add_right
import Theorems.Thm_PI_OmVe_ffH_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution [Finite K] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') K) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → K) (hY : ffGram σ J Y = T0) :
    Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y j) x = 0} * Nat.card K ^ a' = Nat.card K ^ M := by
  classical
  let f : (Fin M → K) →+ (Fin a' → K) :=
    AddMonoidHom.mk' (fun x j => PI.VolStabSW.ffH σ J (Y j) x) (fun x y => by
      funext j
      exact ffH_add_right σ J (Y j) x y)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ l, (T0⁻¹ *ᵥ v) l • Y l, ?_⟩
    funext j
    show PI.VolStabSW.ffH σ J (Y j) (∑ l, (T0⁻¹ *ᵥ v) l • Y l) = v j
    rw [ffH_sum_right σ J Finset.univ]
    have hT : ∀ l, PI.VolStabSW.ffH σ J (Y j) (Y l) = T0 j l := fun l => congrFun (congrFun hY j) l
    simp_rw [hT]
    have hinv : T0 *ᵥ (T0⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T0 hu, Matrix.one_mulVec]
    calc ∑ l, (T0⁻¹ *ᵥ v) l * T0 j l = (T0 *ᵥ (T0⁻¹ *ᵥ v)) j := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = v j := by rw [hinv]
  have hker : Nat.card {x : Fin M → K // ∀ j, PI.VolStabSW.ffH σ J (Y j) x = 0} = Nat.card f.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun h => by ext j; exact h j, fun h j => congrFun h j⟩)
  have hidx : f.ker.index = Nat.card (Fin a' → K) := by
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hpow : ∀ n : ℕ, Nat.card (Fin n → K) = Nat.card K ^ n := by
    intro n
    rw [Nat.card_fun, Nat.card_fin]
  rw [hker, ← hpow a', ← hidx, AddSubgroup.card_mul_index, hpow M]
end PI.OmVe
