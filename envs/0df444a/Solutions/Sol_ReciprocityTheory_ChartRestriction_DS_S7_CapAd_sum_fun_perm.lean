-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapAd.sum_fun_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:10.845099+00:00
-- url     : https://prove2.me/submissions/0b3941bc-fd88-4cca-85f6-6b2eae612fe2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.CapAd
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) : ∑ c, f c = ∑ τ : Equiv.Perm (Fin n), f τ := by
  classical
  have himg : ∑ τ : Equiv.Perm (Fin n), f τ =
      ∑ c ∈ Finset.univ.image (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n)), f c := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact Equiv.ext (congrFun h)
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply hf
  intro hinj
  apply hc
  rw [Finset.mem_image]
  exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
