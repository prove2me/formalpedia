-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P23.systematic_toeplitz_condition1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:06:34.64134+00:00
-- url     : https://prove2.me/submissions/1540bd75-8159-4fcd-b292-87253c8b16ec

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem s110b12_core {K : Type} [Field K] (r l : ℕ) (a : Fin l → K) (jstar : Fin l)
    (hj : a jstar ≠ 0) (hmax : ∀ j, a j ≠ 0 → j ≤ jstar)
    (w : Fin (r + l - 1) → K)
    (hw : ∀ i : Fin r, ∑ j, toeplitz r l w i j * a j = 0)
    (hoff : ∀ k : Fin (r + l - 1), (∀ i : Fin r, k.val ≠ (l - 1 - jstar.val) + i.val) →
      w k = 0) : w = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hex : ∃ i : Fin r, w ⟨(l - 1 - jstar.val) + i.val, by omega⟩ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hk
    by_cases hk2 : ∀ i : Fin r, k.val ≠ (l - 1 - jstar.val) + i.val
    · exact hoff k hk2
    · push_neg at hk2
      obtain ⟨i, hi⟩ := hk2
      have : k = ⟨(l - 1 - jstar.val) + i.val, by omega⟩ := Fin.ext hi
      rw [this]; exact h i
  set F := Finset.univ.filter
    (fun i : Fin r => w ⟨(l - 1 - jstar.val) + i.val, by omega⟩ ≠ 0) with hF
  have hFne : F.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [hF, hi]⟩
  set i0 := F.max' hFne with hi0def
  have hi0 : w ⟨(l - 1 - jstar.val) + i0.val, by omega⟩ ≠ 0 := by
    have := F.max'_mem hFne
    simp only [hF, Finset.mem_filter] at this
    exact this.2
  have hgt : ∀ i : Fin r, i0 < i → w ⟨(l - 1 - jstar.val) + i.val, by omega⟩ = 0 := by
    intro i hi
    by_contra h
    have : i ∈ F := by simp [hF, h]
    have := F.le_max' i this
    exact absurd hi (not_lt.mpr this)
  have heq := hw i0
  rw [Finset.sum_eq_single jstar] at heq
  · apply hi0
    have hidx : (⟨(l - 1 - jstar.val) + i0.val, by omega⟩ : Fin (r + l - 1)) =
        ⟨i0.val + (l - 1 - jstar.val), by omega⟩ := Fin.ext (by simp; omega)
    rw [hidx]
    simpa [toeplitz, hj] using heq
  · intro j _ hjne
    by_cases haj : a j = 0
    · simp [haj]
    · have hle := hmax j haj
      have hlt : j.val < jstar.val := lt_of_le_of_ne hle (fun h => hjne (Fin.ext h))
      have : w ⟨i0.val + (l - 1 - j.val), by omega⟩ = 0 := by
        by_cases hk2 : ∀ i : Fin r, i0.val + (l - 1 - j.val) ≠ (l - 1 - jstar.val) + i.val
        · exact hoff _ hk2
        · push_neg at hk2
          obtain ⟨i, hi⟩ := hk2
          have hii : i0 < i := by
            show i0.val < i.val
            omega
          have := hgt i hii
          have he : (⟨i0.val + (l - 1 - j.val), by omega⟩ : Fin (r + l - 1)) =
              ⟨(l - 1 - jstar.val) + i.val, by omega⟩ := Fin.ext hi
          rw [he]; exact this
      simp [toeplitz, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem s110b12_card {K : Type} [Field K] [Fintype K] (r l : ℕ)
    (z : Fin (r + l - 1) → K) :
    Fintype.card (systematicSubmodule (K := K) r l z) = (Fintype.card K) ^ l := by
  have e : (systematicSubmodule (K := K) r l z) ≃ (Fin l → K) :=
    { toFun := fun v => v.1.1
      invFun := fun a => ⟨(a, fun i => ∑ j, toeplitz r l z i j * a j), fun i => rfl⟩
      left_inv := by
        rintro ⟨⟨v1, v2⟩, hv⟩
        apply Subtype.ext
        simp only
        congr 1
        funext i
        exact (hv i).symm
      right_inv := fun a => rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]

end QAlgorithms.Papers.Independent.Advance50.P23

open QAlgorithms.Papers.Independent.Advance50.P23 in
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw uniform) in
theorem solution {K : Type} [Field K] [Fintype K] (r l : ℕ) :
    Condition1 (uniform : (Fin (r + l - 1) → K) → ℝ)
      (systematicSubmodule (K := K) r l) ((Fintype.card K)^l) := by
  classical
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  refine ⟨⟨fun _ => by simp [uniform], ?_⟩, s110b12_card r l, ?_⟩
  · simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card (Fin (r + l - 1) → K) := by exact_mod_cast Fintype.card_pos
    field_simp
  · rintro ⟨a, y⟩ hx
    have hG : (Fintype.card ((Fin l → K) × (Fin r → K)) : ℝ) =
        (Fintype.card K : ℝ) ^ l * (Fintype.card K : ℝ) ^ r := by
      simp [Fintype.card_prod, Fintype.card_fun]
    have hsum : (∑ z : Fin (r + l - 1) → K,
        if (a, y) ∈ systematicSubmodule (K := K) r l z then uniform z else 0) =
        ((Finset.univ.filter (fun z : Fin (r + l - 1) → K =>
          (a, y) ∈ systematicSubmodule (K := K) r l z)).card : ℝ) *
          ((Fintype.card K : ℝ) ^ (r + l - 1))⁻¹ := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      simp [uniform, Fintype.card_fun]
    rw [hsum, hG]
    by_cases ha : a = 0
    · subst ha
      have hy : y ≠ 0 := by
        intro h; apply hx; simp [h]
      have : ∀ z, ((0 : Fin l → K), y) ∉ systematicSubmodule (K := K) r l z := by
        intro z hz
        apply hy
        funext i
        have := hz i
        simpa using this
      simp [this]
      positivity
    · have hFa : (Finset.univ.filter (fun j : Fin l => a j ≠ 0)).Nonempty := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
        exact ⟨j, by simpa using hj⟩
      set jstar := (Finset.univ.filter (fun j : Fin l => a j ≠ 0)).max' hFa
      have hj : a jstar ≠ 0 := by
        have := Finset.max'_mem _ hFa
        simpa using this
      have hmax : ∀ j, a j ≠ 0 → j ≤ jstar := fun j hj' =>
        Finset.le_max' _ j (by simp [hj'])
      have hl : 1 ≤ l := by have := jstar.isLt; omega
      set m := l - 1 - jstar.val
      let p : Fin (r + l - 1) → Prop := fun k => ∃ i : Fin r, k.val = m + i.val
      have hp : r ≤ Fintype.card {k // p k} := by
        have := Fintype.card_le_of_injective
          (fun i : Fin r => (⟨⟨m + i.val, by omega⟩, i, rfl⟩ : {k // p k}))
          (by intro i i' h; simp at h; exact Fin.ext (by omega))
        simpa using this
      have hnp : Fintype.card {k // ¬ p k} ≤ l - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin]; omega
      have hinj : Function.Injective
          (fun z : {z : Fin (r + l - 1) → K // (a, y) ∈ systematicSubmodule (K := K) r l z} =>
            (fun k : {k // ¬ p k} => z.1 k.1)) := by
        rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
        simp only at h
        apply Subtype.ext
        simp only
        have hw := s110b12_core r l a jstar hj hmax (z - z') ?_ ?_
        · funext k; have := congrFun hw k; simpa [sub_eq_zero] using this
        · intro i
          have e1 := hz i
          have e2 := hz' i
          simp only at e1 e2
          have : ∑ j, toeplitz r l (z - z') i j * a j =
              ∑ j, toeplitz r l z i j * a j - ∑ j, toeplitz r l z' i j * a j := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            simp [toeplitz, sub_mul]
          rw [this, ← e1, ← e2, sub_self]
        · intro k hk
          have hk' : ¬ p k := by
            rintro ⟨i, hi⟩; exact hk i hi
          have := congrFun h ⟨k, hk'⟩
          simp only at this
          simp [this]
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_fun, Fintype.card_subtype] at hcard
      have hcard2 : (Finset.univ.filter (fun z : Fin (r + l - 1) → K =>
          (a, y) ∈ systematicSubmodule (K := K) r l z)).card ≤ (Fintype.card K) ^ (l - 1) :=
        le_trans hcard (Nat.pow_le_pow_right Fintype.card_pos hnp)
      have hcardR : ((Finset.univ.filter (fun z : Fin (r + l - 1) → K =>
          (a, y) ∈ systematicSubmodule (K := K) r l z)).card : ℝ) ≤
          (Fintype.card K : ℝ) ^ (l - 1) := by exact_mod_cast hcard2
      have hn : r + l - 1 = r + (l - 1) := by omega
      have hl' : l = (l - 1) + 1 := by omega
      have key : (Fintype.card K : ℝ) ^ l /
          ((Fintype.card K : ℝ) ^ l * (Fintype.card K : ℝ) ^ r) =
          (Fintype.card K : ℝ) ^ (l - 1) * ((Fintype.card K : ℝ) ^ (r + l - 1))⁻¹ := by
        rw [hn, pow_add]
        have hql : (Fintype.card K : ℝ) ^ l = (Fintype.card K : ℝ) ^ (l - 1) * Fintype.card K := by
          rw [← pow_succ]; congr 1
        rw [hql]
        field_simp
      push_cast
      rw [key]
      gcongr
