-- Prove2me | solution 1 for UpperTheory.Reformulated.B.BoundedSums.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:47.059017+00:00
-- url     : https://prove2.me/submissions/99a494f2-fa02-47fc-849c-d13c462bf51a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoundedSums
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.BoundedSums.bdd_sum {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {α : Type}
    (T : Finset α) (s : α → ℕ → C) (h : ∀ a ∈ T, UpperTheory.Reformulated.B.BoundedSums.Bdd V (s a)) :
    UpperTheory.Reformulated.B.BoundedSums.Bdd V fun n ↦ ∑ a ∈ T, s a n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simpa using Formalism.L2.FormalSeriesBounds.VF.Ge.zero (V := V) 0⟩
  | insert a T ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨L, hL⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min K L, fun n => ?_⟩
    show V.Ge (min K L) (∑ b ∈ insert a T, s b n)
    rw [Finset.sum_insert ha]
    exact ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))
private theorem UpperTheory.Reformulated.B.BoundedSums.bddS_mul {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ : Type}
    {f g : ℕ → MvPowerSeries σ C} (hf : UpperTheory.Reformulated.B.BoundedSums.BddS V f)
    (hg : UpperTheory.Reformulated.B.BoundedSums.BddS V g) : UpperTheory.Reformulated.B.BoundedSums.BddS V fun n ↦ f n * g n := by
  classical
  intro μ
  have h := UpperTheory.Reformulated.B.BoundedSums.bdd_sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (fun p n => MvPowerSeries.coeff p.1 (f n) * MvPowerSeries.coeff p.2 (g n)) (fun p _ => by
      obtain ⟨K, hK⟩ := hf p.1
      obtain ⟨L, hL⟩ := hg p.2
      exact ⟨K + L, fun n => (hK n).mul (hL n)⟩)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  show V.Ge K (MvPowerSeries.coeff μ (f n * g n))
  rw [MvPowerSeries.coeff_mul]
  exact hK n
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.BoundedSums
theorem _root_.solution :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by
  intro C _ V σ ι S f h
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ
    refine ⟨0, fun n => ?_⟩
    show V.Ge 0 (MvPowerSeries.coeff μ (∏ i ∈ (∅ : Finset ι), f i n))
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | insert a S ha ih =>
    have h2 := UpperTheory.Reformulated.B.BoundedSums.bddS_mul (h a (Finset.mem_insert_self a S))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.prod_insert ha] using h2
end UpperTheory.Reformulated.B.BoundedSums
