-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.halfReps_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:23.636295+00:00
-- url     : https://prove2.me/submissions/8a8c6738-44fb-4bca-9691-e039a3fbc58f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ker_norm
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsExist
import Theorems.Thm_Formalism_L2_Th1_F_pInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by
  obtain ⟨S, hS⟩ := kerRepsExist L α hα hs
  let g : ℂ → ℂ := fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)
  have hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P :=
    fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩
  refine ⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    have hk := hS.1 _ (hg P0 hP0).1
    refine ⟨hk.1, fun h2 => hk.2 ?_⟩
    obtain ⟨k, hk'⟩ := hodd
    have h3 := ker_norm hs hN hk.1
    have e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0)) := by
      rw [hk', zsmul_eq_mul]; push_cast; ring
    rw [e]
    exact sub_mem h3 (zsmul_mem h2 _)
  · intro P hP Q hQ hPQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨Q0, hQ0, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ
    rw [(hg P0 hP0).2, (hg Q0 hQ0).2] at h1
    rw [h1]
  · intro z hz hzL
    obtain ⟨P0, hP0, h0⟩ := hS.2.2 z hz hzL
    refine ⟨g (L.weierstrassP P0),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩
    apply (pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp
    rw [(hg P0 hP0).2]
    exact (pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)
end ReciprocityTheory.ChartRestriction.L1
