-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntConstPot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:13.677801+00:00
-- url     : https://prove2.me/submissions/62960da0-2b89-49fa-8a37-4dfd83deeb53

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
private lemma sum_neg_one_pow_det_sum_eq_zero_of_eq_zero {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (M : ι → Matrix m m ℂ) (a : ι) (ha : M a = 0) (N : ℕ)
    (hN : Fintype.card ι ≤ N) :
    ∑ S : Finset ι, (-1 : ℂ) ^ (N - S.card) * (∑ k ∈ S, M k).det = 0 := by
  have hU : (Finset.univ : Finset (Finset ι)) = (Finset.univ : Finset ι).powerset :=
    Finset.powerset_univ.symm
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hU, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (by simp : a ∉ (Finset.univ : Finset ι).erase a),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_powerset] at ht
  have hat : a ∉ t := fun h => by simpa using ht h
  have hc : t.card + 1 ≤ N := by
    have h1 := Finset.card_le_card ht
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at h1
    omega
  rw [Finset.sum_insert hat, ha, zero_add, Finset.card_insert_of_notMem hat]
  obtain ⟨d, hd⟩ : ∃ d, N - t.card = d + 1 := ⟨N - (t.card + 1), by omega⟩
  have hd' : N - (t.card + 1) = d := by omega
  rw [hd, hd', pow_succ]
  ring
private lemma mdisc_eq_zero_of_eq_zero' {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) ℂ) (a : Fin n)
    (ha : M a = 0) : mdisc M = 0 := by
  unfold mdisc
  rw [sum_neg_one_pow_det_sum_eq_zero_of_eq_zero M a ha n (by simp)]
  simp
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntConstPotStatement := by
  intro e X _ A c Φ g
  unfold mInt
  split_ifs with h
  · simp only [integralWith, locDens]
    apply Finset.sum_eq_zero
    intro j _
    have h0 : ∀ y : Fin (e + 1) → ℂ, hessC (fun _ : Fin (e + 1) → ℂ => c) y = 0 := by
      intro y
      unfold hessC
      simp
      funext i k
      rfl
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y _ => ?_)
    unfold maDens
    rw [mdisc_eq_zero_of_eq_zero' _ 0]
    · simp
    · simp only [Fin.cons_zero]
      exact h0 y
  · rfl
end ReciprocityTheory.AnForm.M
