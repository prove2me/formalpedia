-- Prove2me | solution 1 for SaglamGV.expect_oddCircuitCount_le
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T12:23:25.880061+00:00
-- url     : https://prove2.me/submissions/086398b7-8f68-4350-a7d0-cd60e8af11e6

import Theorems.Thm_SaglamGV_circuit_sum_rank
import Theorems.Thm_SaglamGV_card_circuits_le
import Theorems.Thm_SaglamGV_prob_subset_ker
set_option autoImplicit false
open Finset Matrix SaglamGV

private lemma avg_sum {α : Type*} (C : Finset α) (n m : ℕ)
    (f : α → Matrix (Fin m) (Fin n) (ZMod 2) → ℝ) :
    avgM (fun M ↦ ∑ S ∈ C, f S M) = ∑ S ∈ C, avgM (f S) := by
  unfold avgM
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

private lemma first_moment (n d m : ℕ) :
    avgM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦ (oddCircuitCount d M : ℝ)) =
      ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
        ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) := by
  classical
  let O := (allCircuits n d).filter (fun S ↦ Odd S.card)
  let L := (Finset.Icc 3 (n + 1)).filter Odd
  let I := fun (S : Finset (Fin n → ZMod 2)) (M : Matrix (Fin m) (Fin n) (ZMod 2)) ↦
    @ite ℝ (∀ x ∈ S, M *ᵥ x = 0) (Classical.propDecidable _) 1 0
  have hc (S : Finset (Fin n → ZMod 2)) (hS : S ∈ O) : S ∈ circuits n d S.card := by
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1, rfl⟩
  have hsub (S : Finset (Fin n → ZMod 2)) (hS : S ∈ allCircuits n d) : S ⊆ ballP n d :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hpoint (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
      (oddCircuitCount d M : ℝ) = ∑ S ∈ O, I S M := by
    dsimp [O, I]
    rw [oddCircuitCount, Finset.natCast_card_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    have hker : S ⊆ kerSet d M ↔ ∀ x ∈ S, M *ᵥ x = 0 := by
      constructor
      · intro h x hx
        exact (Finset.mem_filter.mp (h hx)).2
      · intro h x hx
        exact Finset.mem_filter.mpr ⟨hsub S hS hx, h x hx⟩
    by_cases ho : Odd S.card <;> by_cases hk : ∀ x ∈ S, M *ᵥ x = 0 <;>
      simp [hker, ho, hk]
  have hmaps : ∀ S ∈ O, S.card ∈ L := by
    intro S hS
    have hstr := SaglamGV.circuit_sum_rank n d S.card S (hc S hS)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hstr.2.2.1, hstr.2.2.2⟩,
      (Finset.mem_filter.mp hS).2⟩
  calc
    _ = avgM (fun M ↦ ∑ S ∈ O, I S M) := congrArg avgM (funext hpoint)
    _ = ∑ S ∈ O, probM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦
        ∀ x ∈ S, M *ᵥ x = 0) := avg_sum O n m I
    _ = ∑ S ∈ O, (tau n d m / (vol n d : ℝ)) ^ (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (SaglamGV.prob_subset_ker n d m S.card S (hc S hS)).1.trans
        (SaglamGV.prob_subset_ker n d m S.card S (hc S hS)).2
    _ = ∑ ℓ ∈ L, ∑ S ∈ O.filter (fun S ↦ S.card = ℓ),
        (tau n d m / (vol n d : ℝ)) ^ (S.card - 1) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have ho : Odd ℓ := (Finset.mem_filter.mp hℓ).2
      have hf : O.filter (fun S ↦ S.card = ℓ) = circuits n d ℓ := by
        ext S
        simp only [O, circuits, Finset.mem_filter]
        aesop
      rw [hf]
      calc
        _ = ∑ _S ∈ circuits n d ℓ, (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [(Finset.mem_filter.mp hS).2]
        _ = _ := by simp


private lemma prob_bounds (n d ℓ : ℕ) : 0 ≤ zeroSumProb n d ℓ ∧ zeroSumProb n d ℓ ≤ 1 := by
  classical
  have hnat : (Finset.univ.filter (fun t : Fin ℓ → (Fin n → ZMod 2) ↦
      (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)).card ≤ (vol n d) ^ ℓ := by
    calc
      _ ≤ (Fintype.piFinset (fun _ : Fin ℓ ↦ ballP n d)).card := by
        apply Finset.card_le_card
        intro t ht
        exact Fintype.mem_piFinset.mpr (Finset.mem_filter.mp ht).2.1
      _ = _ := Fintype.card_piFinset_const _ _
  unfold zeroSumProb
  constructor
  · positivity
  · apply div_le_one_of_le₀
    · exact_mod_cast hnat
    · positivity

private lemma series_bound (n d m : ℕ) :
    ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
        ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ≤
      (vol n d : ℝ) / tau n d m *
        ∑' ℓ : ℕ, (if 3 ≤ ℓ ∧ Odd ℓ then
          tau n d m ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) := by
  classical
  by_cases hV : vol n d = 0
  · have hball : ballP n d = ∅ := Finset.card_eq_zero.mp hV
    have hall : allCircuits n d = ∅ := by
      simp [allCircuits, hball, IsCircuit]
    simp [circuits, hall, hV]
  · have hv : (vol n d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hV
    have hvp : (0 : ℝ) < vol n d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hV)
    have ht : 0 < tau n d m := by unfold tau; positivity
    let L := (Finset.Icc 3 (n + 1)).filter Odd
    let g := fun ℓ : ℕ ↦ if 3 ≤ ℓ ∧ Odd ℓ then
      tau n d m ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0
    have hg (ℓ : ℕ) : 0 ≤ g ℓ := by
      dsimp [g]
      split_ifs
      · exact mul_nonneg (by positivity) (prob_bounds n d ℓ).1
      · rfl
    have hmajor (ℓ : ℕ) : g ℓ ≤ tau n d m ^ ℓ / (ℓ.factorial : ℝ) := by
      dsimp [g]
      split_ifs
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left (prob_bounds n d ℓ).2
          (show 0 ≤ tau n d m ^ ℓ / (ℓ.factorial : ℝ) by positivity)
      · positivity
    have hsum : Summable g :=
      Summable.of_nonneg_of_le hg hmajor (Real.summable_pow_div_factorial (tau n d m))
    have hterm (ℓ : ℕ) (hℓ : ℓ ∈ L) :
        ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ≤
          (vol n d : ℝ) / tau n d m * g ℓ := by
      have hcond : 3 ≤ ℓ ∧ Odd ℓ :=
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hℓ).1).1, (Finset.mem_filter.mp hℓ).2⟩
      have hℓ1 : 1 ≤ ℓ := by omega
      have hVp : (vol n d : ℝ) ^ ℓ = (vol n d : ℝ) ^ (ℓ - 1) * (vol n d : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel hℓ1]
      have htp : tau n d m ^ ℓ = tau n d m ^ (ℓ - 1) * tau n d m := by
        rw [← pow_succ, Nat.sub_add_cancel hℓ1]
      calc
        _ ≤ ((vol n d : ℝ) ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ) *
            (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) :=
          mul_le_mul_of_nonneg_right (SaglamGV.card_circuits_le n d ℓ) (by positivity)
        _ = _ := by
          dsimp [g]
          rw [if_pos hcond, hVp, htp, div_pow]
          field_simp
    calc
      _ ≤ ∑ ℓ ∈ L, (vol n d : ℝ) / tau n d m * g ℓ := Finset.sum_le_sum hterm
      _ = (vol n d : ℝ) / tau n d m * ∑ ℓ ∈ L, g ℓ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum L (fun ℓ _ ↦ hg ℓ)) (by positivity)

theorem solution (n d m : ℕ) (_hd : 2 ≤ d) :
    avgM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) ↦ (oddCircuitCount d M : ℝ)) =
        ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
          ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ∧
      ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
          ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ≤
        (vol n d : ℝ) / tau n d m *
          ∑' ℓ : ℕ, (if 3 ≤ ℓ ∧ Odd ℓ then
            tau n d m ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) := by
  exact ⟨first_moment n d m, series_bound n d m⟩
