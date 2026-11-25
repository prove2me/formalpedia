-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.common_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:59.077927+00:00
-- url     : https://prove2.me/submissions/f82aad36-836e-4560-84e0-e7cc8f92efd6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_fit_step
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] (T : ℕ → Module.End ℂ U)
    (hT : ∀ i j, Commute (T i) (T j)) (e : U →ₗ[ℂ] ℂ) (s : Finset ℕ) :
    ∀ Z : Submodule ℂ U, FiniteDimensional ℂ Z → (∀ i ∈ s, ∀ z ∈ Z, T i z ∈ Z) →
      (∀ i ∈ s, ∀ z ∈ Z, e (T i z) = 0) → (∃ z ∈ Z, e z ≠ 0) → ∃ z ∈ Z, z ≠ 0 ∧ ∀ i ∈ s, T i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro Z - - - ⟨z, hz, hez⟩
    exact ⟨z, hz, fun h => hez (by rw [h, map_zero]), by simp⟩
  | @insert i0 s hi0 ih =>
    rintro Z hfd hZ he ⟨z0, hz0, hez⟩
    have hZ0 := hZ i0 (Finset.mem_insert_self _ _)
    obtain ⟨N, a, haZ, haN, hea⟩ :=
      fit_step (T i0) e Z hZ0 (he i0 (Finset.mem_insert_self _ _)) z0 hz0 hez
    have hfd' : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker (T i0 ^ N)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨z1, hz1, hz1ne, hz1s⟩ := ih (Z ⊓ LinearMap.ker (T i0 ^ N)) hfd'
      (fun i hi z hz => by
        refine ⟨hZ i (Finset.mem_insert_of_mem hi) z hz.1, ?_⟩
        have hk : (T i0 ^ N) z = 0 := hz.2
        show (T i0 ^ N) (T i z) = 0
        rw [← Module.End.mul_apply, ((hT i i0).pow_right N).eq.symm,
          Module.End.mul_apply, hk, map_zero])
      (fun i hi z hz => he i (Finset.mem_insert_of_mem hi) z hz.1) ⟨a, ⟨haZ, haN⟩, hea⟩
    have hex : ∃ k, (T i0 ^ k) z1 = 0 := ⟨N, hz1.2⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero, Module.End.one_apply] at this
      exact hz1ne this
    refine ⟨(T i0 ^ (Nat.find hex - 1)) z1, pow_mem' _ _ hZ0 _ _ hz1.1, Nat.find_min hex (by omega), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    · rw [← Module.End.mul_apply, ((hT i i0).pow_right _).eq, Module.End.mul_apply, hz1s i hi, map_zero]
end PositivityTheory.Rg.Cz.TF
