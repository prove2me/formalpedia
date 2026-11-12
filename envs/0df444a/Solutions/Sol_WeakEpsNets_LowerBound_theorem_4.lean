-- Prove2me | solution 1 for WeakEpsNets.LowerBound.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:10:18.180118+00:00
-- url     : https://prove2.me/submissions/d42816ec-4e30-4dad-9178-091355073f06

import Mathlib
import Theorems.Thm_WeakEpsNets_LowerBound_counting_bound

section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace WeakEpsNets.Dev.T4
open WeakEpsNets.LowerBound

lemma weakNet_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P X : Finset E) {r r0 : ℝ}
    (hr : 0 < r0) (hle : r0 ≤ r) (h : IsWeakNet P r X) : IsWeakNet P r0 X := by
  classical
  intro C hC hcard
  apply h C hC
  refine le_trans ?_ hcard
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr hle

lemma weakNet_transport {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [DecidableEq E] [DecidableEq F]
    (L : F ≃ₗ[ℝ] E) (P : Finset E) (r : ℝ) (X : Finset F)
    (h : IsWeakNet (P.image L.symm) r X) : IsWeakNet P r (X.image L) := by
  classical
  intro C hC hcard
  have hC' : Convex ℝ (L ⁻¹' C) := hC.linear_preimage (L : F →ₗ[ℝ] E)
  have hP : (P.image L.symm).card = P.card :=
    Finset.card_image_of_injective _ L.symm.injective
  have hF : ((P.image L.symm).filter (fun p => p ∈ L ⁻¹' C)).card = (P.filter (fun p => p ∈ C)).card := by
    have : (P.image L.symm).filter (fun p => p ∈ L ⁻¹' C) = (P.filter (fun p => p ∈ C)).image L.symm := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, ⟨hx, by simpa using hy⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, by simpa using hy⟩
    rw [this]; exact Finset.card_image_of_injective _ L.symm.injective
  obtain ⟨x, hx, hxC⟩ := h (L ⁻¹' C) hC' (by rw [hP, hF]; exact hcard)
  exact ⟨L x, Finset.mem_image_of_mem _ hx, hxC⟩

lemma card_quad (n : ℕ) : Fintype.card {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≤ ij.2} = (n + 1) * (n + 2) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have : ∀ i : Fin (n + 1), (∑ j : Fin (n + 1), if i ≤ j then 1 else 0) = n + 1 - i.val := by
    intro i
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun j : Fin (n + 1) => i ≤ j)) = Finset.Ici i := by ext; simp
    rw [this, Fin.card_Ici]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => n + 1 - i) (n + 1)]
  have h2 : ∀ m : ℕ, 2 * (∑ i ∈ Finset.range (m + 1), (m + 1 - i)) = (m + 1) * (m + 2) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ', Nat.mul_add, ← Finset.sum_congr rfl (fun i hi => by
        rw [show k + 1 + 1 - (i + 1) = k + 1 - i by omega])]
      rw [ih]; simp; ring
  have := h2 n
  omega

lemma dim_eq (s : ℕ) (hs : 1 ≤ s) :
    Fintype.card (LiftIndex s) = liftDimension s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  unfold LiftIndex liftDimension
  rw [Fintype.card_sum, Fintype.card_fin, card_quad]
  have h : ((t + 1) ^ 2 + 5 * (t + 1)) = (t + 1 + 1) * (t + 1 + 2) + 2 * t := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), Nat.add_sub_cancel]
  ring

end WeakEpsNets.Dev.T4

namespace WeakEpsNets.LowerBound
open WeakEpsNets.Dev.T4

theorem chk_theorem_4 (s : ℕ) (hs : 1 ≤ s) :
    ∃ rₛ : ℝ, 0 < rₛ ∧ ∃ cₛ : ℝ, 0 < cₛ ∧
      ∀ r : ℝ, rₛ ≤ r →
        ∃ P : Finset (Fin (liftDimension s) → ℝ), P.Nonempty ∧
          ∀ X : Finset (Fin (liftDimension s) → ℝ), IsWeakNet P r X →
            cₛ * Real.rpow r (((s : ℝ) + 2) / 2) ≤ (X.card : ℝ) := by
  classical
  have hs' : (0 : ℝ) < 8 * ((s : ℝ) + 1) := by positivity
  refine ⟨8 * ((s : ℝ) + 1), hs', (1 / 8) * Real.rpow (1 / (8 * ((s : ℝ) + 1))) (((s : ℝ) + 2) / 2),
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro r hr
  have hcard : Fintype.card (LiftIndex s) = liftDimension s := dim_eq s hs
  let e : LiftIndex s ≃ Fin (liftDimension s) := Fintype.equivFinOfCardEq hcard
  let L : (Fin (liftDimension s) → ℝ) ≃ₗ[ℝ] (LiftIndex s → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e
  have hr0 : 0 < r := lt_of_lt_of_le hs' hr
  set y : ℝ := Real.sqrt (r / (8 * ((s : ℝ) + 1))) with hy
  have hy2 : y ^ 2 = r / (8 * ((s : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  have hy1 : 1 ≤ y := by
    rw [hy]; apply Real.le_sqrt_of_sq_le
    rw [one_pow, le_div_iff₀ hs']; linarith
  have hy0 : 0 ≤ y := by linarith
  set k : ℕ := ⌊y⌋₊ with hk
  have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hy1)
  have hkle : (k : ℝ) ≤ y := Nat.floor_le hy0
  have hklt : y < (k : ℝ) + 1 := Nat.lt_floor_add_one y
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set q : ℕ := 2 * k with hq
  have hqR : (q : ℝ) = 2 * k := by simp [hq]
  have hq2 : 2 ≤ q := by omega
  have hqe : Even q := ⟨k, by omega⟩
  have hqle : y ≤ q := by rw [hqR]; linarith
  have hq2le : (q : ℝ) ^ 2 ≤ 4 * y ^ 2 := by
    rw [hqR]; nlinarith
  have hq2ge : y ^ 2 ≤ (q : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ hy0 hqle
  have hqpos : (0 : ℝ) < q := by linarith [show (2 : ℝ) ≤ q by exact_mod_cast hq2]
  have hr' : 2 * ((s : ℝ) + 1) * (q : ℝ) ^ 2 ≤ r := by
    have : 2 * ((s : ℝ) + 1) * (q : ℝ) ^ 2 ≤ 2 * ((s : ℝ) + 1) * (4 * y ^ 2) := by gcongr
    refine this.trans ?_
    exact le_of_eq (by rw [hy2]; field_simp; ring)
  have hne : (liftedGrid s q).Nonempty := by
    have : NeZero q := ⟨by omega⟩
    have : NeZero s := ⟨by omega⟩
    unfold liftedGrid shiftedGrid
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.2 ⟨(fun _ => ⟨0, by omega⟩, ⟨0, by positivity⟩)⟩
  refine ⟨(liftedGrid s q).image L.symm, hne.image _, ?_⟩
  intro X hX
  have h1 := weakNet_transport L (liftedGrid s q) r X hX
  have h2 := weakNet_mono _ _ (by positivity) hr' h1
  have h3 := counting_bound s q hs hq2 hqe _ h2
  have h4 : ((X.image L).card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_image_le
  have h5 : (q : ℝ) ^ (s + 2) = ((q : ℝ) ^ 2) ^ (((s : ℝ) + 2) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    congr 1; push_cast; ring
  have h6 : r ^ (((s : ℝ) + 2) / 2) * (1 / (8 * ((s : ℝ) + 1))) ^ (((s : ℝ) + 2) / 2)
      ≤ ((q : ℝ) ^ 2) ^ (((s : ℝ) + 2) / 2) := by
    rw [← Real.mul_rpow hr0.le (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    calc r * (1 / (8 * ((s : ℝ) + 1))) = y ^ 2 := by rw [hy2]; ring
      _ ≤ _ := hq2ge
  have h7 : (0 : ℝ) ≤ (q : ℝ) ^ 2 / 4 := by positivity
  show _ * Real.rpow _ _ ≤ _
  simp only [Real.rpow_eq_pow] at *
  rw [h5] at h3
  nlinarith

end WeakEpsNets.LowerBound
end

theorem solution : type_of% @WeakEpsNets.LowerBound.chk_theorem_4 := @WeakEpsNets.LowerBound.chk_theorem_4
