-- Prove2me | solution 1 for PI.OmVe.card_half_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:05.472853+00:00
-- url     : https://prove2.me/submissions/fe2c588b-9592-44be-b354-e031d7f83272

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_FfHSelfOfSnd
import Theorems.Thm_P2M_PI_OmVe_ffH_fst__fe7b4dc579e7
import Theorems.Thm_P2M_PI_OmVe_ffH_snd__84f5c783313d
import Theorems.Thm_PI_OmVe_perp_surj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.OmVe
open PI.VolStabSW Matrix
section split
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))
private theorem natCard_ker_mul_card_pow_eq_of_surjective [Finite k] {a' : ℕ} (B : Matrix (Fin a') (Fin M) k)
    (hB : Function.Surjective B.mulVec) :
    Nat.card {u : Fin M → k // B.mulVec u = 0} * Nat.card k ^ a' = Nat.card k ^ M := by
  classical
  have _ := Fintype.ofFinite k
  have hs : LinearMap.range (Matrix.mulVecLin B) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨u, hu⟩ := hB v
    exact ⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B) :=
    Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]
  congr 1
  omega
end split
end PI.OmVe
end
end

set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))
namespace PI.OmVe
theorem _root_.solution [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).2 =
        B.mulVec (fun l => (x l).2) j := by
    intro x j
    rw [ffH_snd']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (0, w' j))
    exact ⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by
        refine Prod.ext ?_ ?_
        · rw [ffH_fst']
          simp
        · rw [hB]
          exact congrFun u.2 j, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj
end PI.OmVe
