-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_big_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:57.029022+00:00
-- url     : https://prove2.me/submissions/d071cce7-e1ff-4125-9679-cc4901b7b07e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_weight_eq_of_irr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_mem

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
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section AlternatingWeights
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
private theorem w_coord_mAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n)
    (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ (mAct E k a b F) = E a b (F κ) := rfl
private theorem w_coord_positionAd (k : ℕ) (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n)
    (F : Big n k M) :
    coord k κ (factorAd k i a b F) =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  change (((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
        Big n k M →ₗ[ℂ] M)) F = _
  split_ifs <;> rfl
private theorem w_coord_bAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n)
    (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ (bAct E k a b F) = E a b (F κ) + ∑ i, ((if (κ i).1 = a then
      F (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0)) := by
  simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, w_coord_mAct,
    w_coord_positionAd]
private theorem w_sum_update (φ : Fin n × Fin n → ℤ) {k : ℕ} (κ : Fin k → Fin n × Fin n) (i : Fin k)
    (p : Fin n × Fin n) :
    ∑ j, φ (Function.update κ i p j) + φ (κ i) = ∑ j, φ (κ j) + φ p := by
  classical
  have hfun : (fun j => φ (Function.update κ i p j)) = Function.update (fun j => φ (κ j)) i (φ p) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_apply, h]
  have h1 : ∑ j, φ (Function.update κ i p j) = φ p + ∑ j ∈ Finset.univ \ {i}, φ (κ j) := by
    rw [show (∑ j, φ (Function.update κ i p j)) = ∑ j, Function.update (fun j => φ (κ j)) i (φ p) j
      from congrArg (fun f => ∑ j, f j) hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h2 : ∑ j, φ (κ j) = φ (κ i) + ∑ j ∈ Finset.univ \ {i}, φ (κ j) :=
by
    rw [Finset.sdiff_singleton_eq_erase, Finset.add_sum_erase _ (fun j => φ (κ j)) (Finset.mem_univ i)]
  rw [h1, h2]
  ring
end AlternatingWeights
section Weights
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {Λ : Fin n → ℝ}
end Weights
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKIrrHW ε E Λ V) {k : ℕ} {F : Big n k M}
    (hF : F ∈ ncV ε V k) (hF0 : F ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E k) ν F) :
    IsNCSum ε k (ν - Λ) := by
  classical
  have hcoord : ∀ (a b : Fin n) (κ : Fin k → Fin n × Fin n), (bAct E k a b F) κ = E a b (F κ) +
      ∑ i, ((if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0)) :=
    fun a b κ => w_coord_bAct E k a b κ F

  have hwt : ∀ (κ : Fin k → Fin n × Fin n) (a : Fin n),
      E a a (F κ) = (((ν - ∑ j, root (κ j).1 (κ j).2) a : ℝ) : ℂ) • F κ := by
    intro κ a
    have h0 := congrArg (fun G : Big n k M => G κ) (hν.1 a)
    simp only at h0
    rw [hcoord, PiLp.smul_apply] at h0
    have hterm : ∀ i, ((if (κ i).1 = a then F (Function.update κ i (a, (κ i).2)) else 0) -
        (if (κ i).2 = a then F (Function.update κ i ((κ i).1, a)) else 0)) =
        ((root (κ i).1 (κ i).2 a : ℝ) : ℂ) • F κ := by
      intro i
      have e1 : (κ i).1 = a → Function.update κ i (a, (κ i).2) = κ := fun h => by
        rw [← h, Prod.mk.eta, Function.update_eq_self]
      have e2 : (κ i).2 = a → Function.update κ i ((κ i).1, a) = κ := fun h => by
        rw [← h, Prod.mk.eta, Function.update_eq_self]
      simp only [root, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : (κ i).1 = a <;> by_cases h2 : (κ i).2 = a
      · rw [if_pos h1, if_pos h2, e1 h1, e2 h2, if_pos h1.symm, if_pos h2.symm]; simp
      · rw [if_pos h1, if_neg h2, e1 h1, if_pos h1.symm, if_neg (Ne.symm h2)]; simp
      · rw [if_neg h1, if_pos h2, e2 h2, if_neg (Ne.symm h1), if_pos h2.symm]; simp
      · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_smul] at h0
    rw [eq_sub_of_add_eq h0, ← sub_smul]
    congr 1
    simp [Finset.sum_apply]
  set φ : Fin n × Fin n → ℤ := fun p => ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ) with hφ
  have hne : (Finset.univ.filter (fun κ : Fin k → Fin n × Fin n => F κ ≠ 0)).Nonempty := by
    by_contra h
    apply hF0
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact PiLp.ext fun κ => by simpa using h (Finset.mem_univ κ)
  obtain ⟨κ, hκmem, hκmax⟩ := Finset.exists_max_image _ (fun κ => ∑ j, φ (κ j)) hne
  have hκ0 : F κ ≠ 0 := (Finset.mem_filter.mp hκmem).2
  have hzero : ∀ κ' : Fin k → Fin n × Fin n, ∑ j, φ (κ j) < ∑ j, φ (κ' j) → F κ' = 0 := by
    intro κ' h
    by_contra h'
    exact absurd (hκmax κ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)) (not_le.mpr h)

  have hK : IsKHWVec ε E (ν - ∑ j, root (κ j).1 (κ j).2) (F κ) := by
    refine ⟨fun a => hwt κ a, fun a b hab hεab => ?_⟩
    have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by
      have : (a : ℕ) < b := hab
      omega
    have h0 := congrArg (fun G : Big n k M => G κ) (hν.2 a b hab hεab)
    simp only at h0
    rw [hcoord] at h0
    have hterm : ∀ i, ((if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0)) = 0 := by
      intro i
      have u1 : (κ i).1 = a → F (Function.update κ i (b, (κ i).2)) = 0 := fun h => by
        apply hzero
        have hs := w_sum_update φ κ i (b, (κ i).2)
        have hp : φ (b, (κ i).2) - φ (κ i) = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) := by
          simp only [hφ, h]; ring
        linarith
      have u2 : (κ i).2 = b → F (Function.update κ i ((κ i).1, a)) = 0 := fun h => by
        apply hzero
        have hs := w_sum_update φ κ i ((κ i).1, a)
        have hp : φ ((κ i).1, a) - φ (κ i) = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) := by
          simp only [hφ, h]; ring
        linarith
      by_cases h1 : (κ i).1 = a <;> by_cases h2 : (κ i).2 = b <;> simp [h1, h2, u1, u2]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const_zero, add_zero] at h0
    simpa using h0
  have hΛ := khw_weight_eq_of_irr hE hV (ncV_mem hF κ) hκ0 hK
  refine ⟨κ, fun i h => hκ0 (ncV_eq_zero hF i h), ?_⟩
  rw [← hΛ, sub_sub_cancel]
end ReciprocityTheory.ChartRestriction.DS
