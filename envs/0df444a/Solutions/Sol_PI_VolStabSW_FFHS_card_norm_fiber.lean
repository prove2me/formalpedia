-- Prove2me | solution 1 for PI.VolStabSW.FFHS.card_norm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:13.586417+00:00
-- url     : https://prove2.me/submissions/ed798d77-3af5-4456-b01c-1067fc8fc648

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
private theorem card_le_natDegree_of_eval_eq_zero {L : Type} [Field L] (P : L[X]) (hP : P ≠ 0)
    (Z : Finset L) (hZ : ∀ z ∈ Z, P.eval z = 0) : Z.card ≤ P.natDegree := by
  have hsub : Z.val ⊆ P.roots := fun z hz =>
    (Polynomial.mem_roots hP).mpr (hZ z (Finset.mem_val.mp hz))
  exact (Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr hsub)).trans
    (Polynomial.card_roots' P)
private theorem card_le_of_pow_eq_mul_add {L : Type} [Field L] (n : ℕ) (hn : 1 < n) (b c : L)
    (Z : Finset L) (hZ : ∀ z ∈ Z, z ^ n = b * z + c) : Z.card ≤ n := by
  have hlt : (C b * X + C c : L[X]).natDegree < (X ^ n : L[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le hn
  have hdeg : (X ^ n - (C b * X + C c) : L[X]).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP0 : (X ^ n - (C b * X + C c) : L[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have := card_le_natDegree_of_eval_eq_zero _ hP0 Z fun z hz => by simp [hZ z hz]
  rwa [hdeg] at this
end field
end PI.VolStabSW.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabSW.FFHS
theorem _root_.solution (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hKcard' : Fintype.card K = Fintype.card k ^ finrank k K := Module.card_eq_pow_finrank
  have hKcard : Fintype.card K = Fintype.card k ^ 2 := by rw [hKcard', h2]
  have hσσ : ∀ t, σ (σ t) = t := by
    intro t
    rw [hfrob (σ t), hfrob t, ← pow_mul, ← sq, ← hKcard, FiniteField.pow_card]
  let c : K → ℕ := fun y => (Finset.univ.filter fun t : K => t * σ t = y).card
  let F : Finset K := Finset.univ.filter fun y : K => y ^ Fintype.card k = y
  have hsum : Fintype.card K = ∑ y ∈ F, c y := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := fun t => t * σ t) fun t _ => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, map_mul, hσσ, mul_comm]
  have hF : F.card ≤ Fintype.card k :=
    card_le_of_pow_eq_mul_add _ hq1 1 0 F fun z hz => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hz, one_mul, add_zero]
  have hfib : ∀ y, c y ≤ Fintype.card k + 1 := fun y =>
    card_le_of_pow_eq_mul_add _ (by omega) 0 y (Finset.univ.filter fun t : K => t * σ t = y)
      fun t ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [pow_succ', ← hfrob, ht, zero_mul, zero_add]
  have hc0 : c 0 = 1 := by
    show (Finset.univ.filter fun t : K => t * σ t = 0).card = 1
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  split_ifs with hd0
  · subst hd0
    exact hc0
  · have hdF : d ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, hd]
    have h0F : (0 : K) ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact zero_pow (by omega)
    refine le_antisymm (hfib d) ?_
    by_contra hlt
    push_neg at hlt
    have key : ∑ y ∈ F.erase 0, c y < ∑ _y ∈ F.erase 0, (Fintype.card k + 1) :=
      Finset.sum_lt_sum (fun y _ => hfib y) ⟨d, Finset.mem_erase.mpr ⟨hd0, hdF⟩, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0F] at key
    have hs := Finset.add_sum_erase F c h0F
    rw [hc0] at hs
    have hn : 1 ≤ F.card := Finset.card_pos.mpr ⟨0, h0F⟩
    have h3 : (F.card - 1) * (Fintype.card k + 1) ≤
        (Fintype.card k - 1) * (Fintype.card k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (Fintype.card k - 1) * (Fintype.card k + 1) + 1 = Fintype.card k ^ 2 := by
      obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      ring
    omega
end PI.VolStabSW.FFHS
