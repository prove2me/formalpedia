-- Prove2me | solution 1 for PhiDivRobust.Counterpart.dualFunction_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:14:17.713933+00:00
-- url     : https://prove2.me/submissions/a65efc61-ee8f-40c1-bfe9-a8d2f9ef3cf6

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

theorem aux_dfe_sup_sum {ι : Type*} [DecidableEq ι] (F : ι → ℝ → EReal) (s : Finset ι) :
    ⨆ p ∈ {p : ι → ℝ | 0 ≤ p}, ∑ i ∈ s, F i (p i) = ∑ i ∈ s, ⨆ t ∈ Set.Ici (0:ℝ), F i t := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact biSup_const ⟨0, fun _ => le_refl (0:ℝ)⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    apply le_antisymm
    · refine iSup₂_le fun p hp => ?_
      rw [Finset.sum_insert ha]
      exact add_le_add (le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => F a t) (p a) (hp a))
        (le_iSup₂ (f := fun p (_ : p ∈ {p : ι → ℝ | 0 ≤ p}) => ∑ i ∈ s, F i (p i)) p hp)
    · refine EReal.add_le_of_forall_lt fun a' ha' b' hb' => ?_
      obtain ⟨t, ht, hat⟩ := lt_biSup_iff.mp ha'
      obtain ⟨p, hp, hbp⟩ := lt_biSup_iff.mp hb'
      have hp' : Function.update p a t ∈ {p : ι → ℝ | 0 ≤ p} := by
        intro i
        by_cases hi : i = a
        · subst hi; simpa using ht
        · simpa [Function.update_of_ne hi] using hp i
      refine le_trans ?_ (le_iSup₂
        (f := fun p (_ : p ∈ {p : ι → ℝ | 0 ≤ p}) => ∑ i ∈ insert a s, F i (p i)) _ hp')
      simp only [Finset.sum_insert ha, Function.update_self]
      have : ∑ i ∈ s, F i (Function.update p a t i) = ∑ i ∈ s, F i (p i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact ha hi)]
      rw [this]
      exact add_le_add hat.le hbp.le

theorem aux_dfe_add_sup {α : Type*} (S : Set α) (R : ℝ) (G : α → EReal) :
    ⨆ p ∈ S, ((R : EReal) + G p) = (R : EReal) + ⨆ p ∈ S, G p := by
  apply le_antisymm
  · exact iSup₂_le fun p hp => add_le_add le_rfl (le_iSup₂ (f := fun p (_ : p ∈ S) => G p) p hp)
  · refine EReal.add_le_of_forall_lt fun a' ha' b' hb' => ?_
    obtain ⟨p, hp, hbp⟩ := lt_biSup_iff.mp hb'
    exact le_trans (add_le_add ha'.le hbp.le)
      (le_iSup₂ (f := fun p (_ : p ∈ S) => (R : EReal) + G p) p hp)

theorem aux_dfe_mul_sup_le {α : Type*} (S : Set α) (c : ℝ) (hc : 0 ≤ c) (G : α → EReal) :
    ⨆ p ∈ S, (c : EReal) * G p ≤ (c : EReal) * ⨆ p ∈ S, G p :=
  iSup₂_le fun p hp => mul_le_mul_of_nonneg_left
    (le_iSup₂ (f := fun p (_ : p ∈ S) => G p) p hp) (by exact_mod_cast hc)

theorem aux_dfe_mul_sup {α : Type*} (S : Set α) (c : ℝ) (hc : 0 < c) (G : α → EReal) :
    (c : EReal) * ⨆ p ∈ S, G p = ⨆ p ∈ S, (c : EReal) * G p := by
  apply le_antisymm _ (aux_dfe_mul_sup_le S c hc.le G)
  have h1 : ⨆ p ∈ S, G p ≤ ((c⁻¹ : ℝ) : EReal) * ⨆ p ∈ S, (c : EReal) * G p := by
    have := aux_dfe_mul_sup_le S c⁻¹ (inv_nonneg.mpr hc.le) (fun p => (c : EReal) * G p)
    refine le_trans (le_of_eq ?_) this
    refine iSup_congr fun p => iSup_congr fun _ => ?_
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  calc (c : EReal) * ⨆ p ∈ S, G p
      ≤ (c : EReal) * (((c⁻¹ : ℝ) : EReal) * ⨆ p ∈ S, (c : EReal) * G p) :=
        mul_le_mul_of_nonneg_left h1 (by exact_mod_cast hc.le)
    _ = _ := by rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]

theorem aux_dfe_subst (G : ℝ → EReal) (c : ℝ) (hc : 0 < c) :
    ⨆ u ∈ Set.Ici (0:ℝ), G (c * u) = ⨆ t ∈ Set.Ici (0:ℝ), G t := by
  apply le_antisymm
  · exact iSup₂_le fun u hu =>
      le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) => G t) (c * u) (mul_nonneg hc.le hu)
  · refine iSup₂_le fun t ht => ?_
    have : G t = G (c * (t / c)) := by rw [mul_div_cancel₀ t hc.ne']
    rw [this]
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Ici (0:ℝ)) => G (c * u)) (t / c)
      (div_nonneg ht hc.le)

theorem aux_dfe_mul_sum {ι : Type*} (c : ℝ) (hc : 0 ≤ c) (Y : ι → EReal) (s : Finset ι) :
    (c : EReal) * ∑ i ∈ s, Y i = ∑ i ∈ s, (c : EReal) * Y i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc) (EReal.coe_ne_top c), ih]

theorem aux_dfe_sub2 (x y : ℝ) (A B : EReal) (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    ((x + y : ℝ) : EReal) - (A + B) = ((x : EReal) - A) + ((y : EReal) - B) := by
  induction A using EReal.rec with
  | bot => exact absurd rfl hA
  | top => rw [EReal.top_add_of_ne_bot hB, EReal.sub_top, EReal.sub_top, EReal.bot_add]
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd rfl hB
    | top => rw [EReal.coe_add_top, EReal.sub_top, EReal.sub_top, EReal.add_bot]
    | coe b =>
      rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
      congr 1; ring

theorem aux_dfe_sum_ne_bot {ι : Type*} (Y : ι → EReal) (hY : ∀ i, Y i ≠ ⊥) (s : Finset ι) :
    ∑ i ∈ s, Y i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact EReal.add_ne_bot_iff.mpr ⟨hY a, ih⟩

theorem aux_dfe_sub_sum {ι : Type*} (r : ι → ℝ) (Y : ι → EReal) (hY : ∀ i, Y i ≠ ⊥)
    (s : Finset ι) :
    ((∑ i ∈ s, r i : ℝ) : EReal) - ∑ i ∈ s, Y i = ∑ i ∈ s, ((r i : EReal) - Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      aux_dfe_sub2 _ _ _ _ (hY a) (aux_dfe_sum_ne_bot Y hY s), ih]

theorem aux_dfe_mul_ne_bot (c : ℝ) (hc : 0 ≤ c) (y : EReal) (hy : y ≠ ⊥) :
    (c : EReal) * y ≠ ⊥ := by
  induction y using EReal.rec with
  | bot => exact absurd rfl hy
  | top =>
    rcases hc.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [EReal.coe_mul_top_of_pos h]; simp
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

theorem aux_dfe_real {n m k : ℕ} (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ) (ρ : ℝ) (x : Fin n → ℝ) (lam : ℝ)
    (η : Fin k → ℝ) (p : Fin m → ℝ) :
    (a + B *ᵥ p) ⬝ᵥ x + ρ * lam + η ⬝ᵥ (d - C *ᵥ p) = (a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam) +
      ∑ i, p i * ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) := by
  rw [add_dotProduct, dotProduct_sub, dotProduct_comm (B *ᵥ p) x, dotProduct_mulVec,
    dotProduct_mulVec]
  have hs : ∀ i, (fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η = (x ᵥ* B) i - (η ᵥ* C) i := by
    intro i; simp only [vecMul, dotProduct_comm]
  simp only [hs]
  rw [dotProduct_comm η d]
  simp only [dotProduct, mul_comm (p _), sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

end PhiDivRobust.Counterpart

open PhiDivRobust.Counterpart
open Matrix

theorem solution {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (x : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : Fin k → ℝ) :
    dualFunction φ a B C d q ρ x lam η =
      ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) +
        ∑ i, (q i : EReal) *
          scaledConj φ lam ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) := by
  obtain ⟨F, hFdef⟩ : ∃ F : Fin m → ℝ → EReal, F = fun i t =>
      ((t * ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) : ℝ) : EReal) -
        (lam : EReal) * ((q i : EReal) * φ (t / q i)) := ⟨_, rfl⟩
  have hL : ∀ p : Fin m → ℝ, lagrangian φ a B C d q ρ x p lam η =
      ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) + ∑ i, F i (p i) := by
    intro p
    unfold lagrangian phiDiv
    rw [aux_dfe_real a B C d ρ x lam η p, EReal.coe_add, sub_eq_add_neg, add_assoc,
      ← sub_eq_add_neg, aux_dfe_mul_sum lam hlam, aux_dfe_sub_sum, hFdef]
    intro i
    exact aux_dfe_mul_ne_bot lam hlam _ (aux_dfe_mul_ne_bot (q i) (hq i).le _ (hφ.ne_bot _))
  unfold dualFunction
  simp_rw [hL]
  rw [aux_dfe_add_sup, aux_dfe_sup_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold scaledConj
  rw [aux_dfe_mul_sup _ _ (hq i), ← aux_dfe_subst (F i) (q i) (hq i)]
  refine iSup_congr fun u => iSup_congr fun _ => ?_
  rw [hFdef]
  simp only
  rw [mul_div_cancel_left₀ u (hq i).ne',
    EReal.mul_sub_of_nonneg_of_ne_top (by exact_mod_cast (hq i).le) (EReal.coe_ne_top _),
    ← EReal.coe_mul, mul_left_comm (q i : EReal)]
  congr 2
  ring
