-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.measure_Om_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:48.24801+00:00
-- url     : https://prove2.me/submissions/cfa290cd-03de-4f77-9e0a-d12a1a89008d

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobB
import Theorems.Thm_PositivityTheory_ThKF0_Grow_exists_reps
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory
variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution [MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F)] [BorelSpace (κ → FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (κ → FiniteAdeleRing (𝓞 F) F)) [ν.IsAddRightInvariant] :
    ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ν (Om F κ) ≤ (m : ℝ≥0∞) ^ k * ν ((fun u => m • u) '' Om F κ) := by
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) * Fintype.card κ, fun m hm => ?_⟩
  obtain ⟨rep, h⟩ := exists_reps F m hm
  have hsub : Om F κ ⊆ ⋃ r : κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin m,
      (fun y => y + -fun i => rep (r i)) ⁻¹' ((fun u => m • u) '' Om F κ) := fun y hy => by
    choose r a ha e using fun i => h (y i) (hy i)
    refine Set.mem_iUnion.2 ⟨r, a, ha, funext fun i => ?_⟩
    change m • a i = y i + -rep (r i)
    rw [e i]
    abel
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans (le_of_eq ?_))
  simp only [measure_preimage_add_right, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, pow_mul]
end PositivityTheory.ThKF0.Grow
