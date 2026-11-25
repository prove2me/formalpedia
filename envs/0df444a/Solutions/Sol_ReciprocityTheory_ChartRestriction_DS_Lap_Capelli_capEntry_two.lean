-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:56.886411+00:00
-- url     : https://prove2.me/submissions/c42ebd78-ac39-4876-99dc-c0198951ec62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_eq_add_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
private theorem add_smul_one_mul_sub_eq_neg_swap_of_commutator (A B C D : 𝒰) (a b c d x : ℂ)
    (h1 : A * B - B * A = c • D - d • C) (h2 : D * C - C * D = b • A - a • B) :
    (A + (a * x) • (1 : 𝒰)) * (B + (b * (x - 1)) • (1 : 𝒰)) -
        (C + (c * x) • (1 : 𝒰)) * (D + (d * (x - 1)) • (1 : 𝒰)) =
      -((D + (d * x) • (1 : 𝒰)) * (C + (c * (x - 1)) • (1 : 𝒰)) -
        (B + (b * x) • (1 : 𝒰)) * (A + (a * (x - 1)) • (1 : 𝒰))) := by
  have hBA : B * A = A * B - (c • D - d • C) := by rw [← h1]; abel
  have hCD : C * D = D * C - (b • A - a • B) := by rw [← h2]; abel
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hBA, hCD]
  module
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) (i k j l : Fin n) (x : ℂ) :
    capEntry E x i j * capEntry E (x - 1) k l - capEntry E x k j * capEntry E (x - 1) i l =
      -(capEntry E x i l * capEntry E (x - 1) k j - capEntry E x k l * capEntry E (x - 1) i j) := by
  have hs : ∀ (a b : Fin n) (y : ℂ),
      capEntry E y a b = E a b + ((if a = b then (1 : ℂ) else 0) * y) • (1 : 𝒰) := by
    intro a b y
    rw [capEntry_eq_add_smul]
    split_ifs <;> simp
  have hd : ∀ (a b : Fin n) (u : 𝒰), (if b = a then u else 0) = (if a = b then (1 : ℂ) else 0) • u := by
    intro a b u
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h1 := hE i j k l
  have h2 := hE i l k j
  rw [hd, hd] at h1 h2
  simp only [hs]
  exact add_smul_one_mul_sub_eq_neg_swap_of_commutator (E i j) (E k l) (E k j) (E i l) _ _ _ _ x h1 h2
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
