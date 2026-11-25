-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_of_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:43.523863+00:00
-- url     : https://prove2.me/submissions/eaf647fb-47f7-4f65-9c0f-e71e0d91854b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution [IsLocalRing R] (p : ℕ)
    (hM : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (A : Matrix n n R)
    (hA : A.map (IsLocalRing.residue R) = 1) : PDvd (p : R) 1 (A - 1) := by
  have h : ∀ i j, ∃ c : R, (A - 1) i j = (p : R) ^ 1 * c := by
    intro i j
    have hij := congrFun (congrFun hA i) j
    rw [map_apply, ← Matrix.map_one (IsLocalRing.residue R) (map_zero _) (map_one _),
      map_apply] at hij
    have hmem : A i j - (1 : Matrix n n R) i j ∈ IsLocalRing.maximalIdeal R :=
      Ideal.Quotient.eq.mp hij
    rw [hM, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by rw [Matrix.sub_apply, ← hc, pow_one, mul_comm]⟩
  choose X hX using h
  exact ⟨Matrix.of X, by ext i j; rw [hX, Matrix.smul_apply, of_apply, smul_eq_mul]⟩
end PI.FinOrdRedOne.Core
