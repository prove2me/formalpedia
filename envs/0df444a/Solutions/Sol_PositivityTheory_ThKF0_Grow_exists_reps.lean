-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:12.294089+00:00
-- url     : https://prove2.me/submissions/e83a92ef-54a8-4a61-8a8a-7bbbf1839d32

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobB
import Theorems.Thm_GlobalTheory_AdLat_strong_approximation_mod_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory
variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution (m : ℕ) (hm : 1 ≤ m) :
    ∃ rep : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin m) → FiniteAdeleRing (𝓞 F) F,
      ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) →
        ∃ r, ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = rep r + m • a := by
  let b := RingOfIntegers.basis F
  let φ : 𝓞 F →+* FiniteAdeleRing (𝓞 F) F := (algebraMap F _).comp (algebraMap (𝓞 F) F)
  refine ⟨fun r => φ (∑ j, ((r j : ℕ) : ℤ) • b j), fun y hy => ?_⟩
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).2 y hy
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have h0 : ∀ j, 0 ≤ b.repr x j % m := fun j => Int.emod_nonneg _ hm'.ne'
  refine ⟨fun j => ⟨(b.repr x j % m).toNat, ?_⟩, φ (∑ j, (b.repr x j / m) • b j) + a, fun v => ?_, ?_⟩
  · have := Int.emod_lt_of_pos (b.repr x j) hm'
    have := h0 j
    omega
  · exact add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v _) (ha v)
  · rw [h, nsmul_add, ← add_assoc, ← map_nsmul, ← map_add]
    congr 1
    change φ x = _
    congr 1
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.toNat_of_nonneg (h0 j), ← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]
end PositivityTheory.ThKF0.Grow
