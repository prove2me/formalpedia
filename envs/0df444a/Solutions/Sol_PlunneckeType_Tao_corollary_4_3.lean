-- Prove2me | solution 1 for PlunneckeType.Tao.corollary_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:17:23.681316+00:00
-- url     : https://prove2.me/submissions/8293ec4b-165d-4ca2-bf7e-883bdbc75ade

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset


section YPT
variable {G : Type*} [Group G] [DecidableEq G]

/-- a subset of `A` of minimal growth under right multiplication by `B` -/
lemma ypt_min (A B : Finset G) (hA : A.Nonempty) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ Z ⊆ A, Z.Nonempty → (#(S * B) : ℝ) * #Z ≤ #(Z * B) * #S := by
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image (A.powerset.erase ∅)
    (fun Z : Finset G => (#(Z * B) : ℚ) / #Z)
    ⟨A, Finset.mem_erase.mpr ⟨hA.ne_empty, Finset.mem_powerset_self A⟩⟩
  rw [Finset.mem_erase, Finset.mem_powerset, ← Finset.nonempty_iff_ne_empty] at hS
  refine ⟨S, hS.2, hS.1, fun Z hZ hZne => ?_⟩
  have h := hmin Z (Finset.mem_erase.mpr ⟨hZne.ne_empty, Finset.mem_powerset.mpr hZ⟩)
  have hSpos : (0 : ℚ) < #S := by exact_mod_cast hS.1.card_pos
  have hZpos : (0 : ℚ) < #Z := by exact_mod_cast hZne.card_pos
  rw [div_le_div_iff₀ hSpos hZpos] at h
  have h' : ((#(S * B) : ℚ) * #Z : ℚ) ≤ #(Z * B) * #S := h
  exact_mod_cast h'

lemma ypt_ab (A B : Finset G) (α : ℝ) (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A) :
    (#(A * B) : ℝ) ≤ α * #A := by
  have hBpos : 0 < (#B : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hA.mono hAB)
  have h2 := hmin B subset_rfl (hA.mono hAB)
  have h3 : (#(A * B) : ℝ) * #B ≤ (α * #A) * #B := by
    calc (#(A * B) : ℝ) * #B ≤ #(B * B) * #A := h2
      _ ≤ (α * #B) * #A := mul_le_mul_of_nonneg_right hBB (Nat.cast_nonneg _)
      _ = (α * #A) * #B := by ring
  exact le_of_mul_le_mul_right h3 hBpos

lemma ypt_bab (A B : Finset G) (α : ℝ) (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A) :
    (#(B * A * B) : ℝ) ≤ α ^ 2 * #B := by
  have hApos : 0 < (#A : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hAB' := ypt_ab A B α hBB hAB hA hmin
  have hBA : (#(B * A) : ℝ) ≤ α * #B := by
    have : #(B * A) ≤ #(B * B) := Finset.card_le_card (Finset.mul_subset_mul_left hAB)
    exact (Nat.cast_le.mpr this).trans hBB
  have hA' : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A := by
    intro A' hA'A
    rcases A'.eq_empty_or_nonempty with rfl | hne
    · simp
    · have := hmin A' (hA'A.trans hAB) hne
      exact_mod_cast this
  have pp := Finset.pluennecke_petridis_inequality_mul (A := A) (B := B) B hA'
  have pp' : (#(B * A * B) : ℝ) * #A ≤ #(A * B) * #(B * A) := by exact_mod_cast pp
  have hαnn : 0 ≤ α * #A := le_trans (Nat.cast_nonneg _) hAB'
  have h4 : (#(B * A * B) : ℝ) * #A ≤ (α ^ 2 * #B) * #A := by
    calc (#(B * A * B) : ℝ) * #A ≤ #(A * B) * #(B * A) := pp'
      _ ≤ (α * #A) * (α * #B) :=
          mul_le_mul hAB' hBA (Nat.cast_nonneg _) hαnn
      _ = (α ^ 2 * #B) * #A := by ring
  exact le_of_mul_le_mul_right h4 hApos

lemma ypt_c43 (A B : Finset G) (α : ℝ) (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBAB : (#(B * A * B) : ℝ) ≤ α ^ 2 * #B) :
    (#(B * A⁻¹ * A * B⁻¹) : ℝ) ≤ α ^ 6 * #B := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have h1 := Finset.ruzsa_triangle_inequality_mulInv_mul_mul (B * A) B B
  have h1' : (#(B * A * B⁻¹) : ℝ) * #B ≤ #(B * A * B) * #(B * B) := by exact_mod_cast h1
  have hn : (#(B * A * B⁻¹) : ℝ) ≤ α ^ 3 * #B := by
    have : (#(B * A * B⁻¹) : ℝ) * #B ≤ (α ^ 3 * #B) * #B := by
      calc (#(B * A * B⁻¹) : ℝ) * #B ≤ #(B * A * B) * #(B * B) := h1'
        _ ≤ (α ^ 2 * #B) * (α * #B) :=
          mul_le_mul hBAB hBB (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hBAB)
        _ = (α ^ 3 * #B) * #B := by ring
    exact le_of_mul_le_mul_right this hbpos
  have h2 := Finset.ruzsa_triangle_inequality_invMul_mul_mul (A * B⁻¹) B (A * B⁻¹)
  have e1 : (A * B⁻¹)⁻¹ * (A * B⁻¹) = B * A⁻¹ * A * B⁻¹ := by
    simp [mul_inv_rev, mul_assoc]
  have e2 : B * (A * B⁻¹) = B * A * B⁻¹ := by rw [mul_assoc]
  rw [e1, e2] at h2
  have h2' : (#B : ℝ) * #(B * A⁻¹ * A * B⁻¹) ≤ #(B * A * B⁻¹) * #(B * A * B⁻¹) := by exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ #(B * A * B⁻¹) := Nat.cast_nonneg _
  have h5 : (#(B * A * B⁻¹) : ℝ) * #(B * A * B⁻¹) ≤ (α ^ 3 * #B) * (α ^ 3 * #B) :=
    mul_le_mul hn hn hn0 (le_trans hn0 hn)
  have : (#B : ℝ) * #(B * A⁻¹ * A * B⁻¹) ≤ (α ^ 6 * #B) * #B := by
    calc (#B : ℝ) * #(B * A⁻¹ * A * B⁻¹) ≤ _ := h2'
      _ ≤ _ := h5
      _ = (α ^ 6 * #B) * #B := by ring
  rw [mul_comm (α ^ 6 * #B)] at this
  exact le_of_mul_le_mul_left this hbpos

lemma ypt_cover (A B : Finset G) (α : ℝ) (hA : A.Nonempty) (hAB : (#(A * B) : ℝ) ≤ α * #A) :
    ∃ T ⊆ B, (#T : ℝ) ≤ α ∧ B ⊆ A⁻¹ * A * T := by
  have hK : (#(B⁻¹ * A⁻¹) : ℝ) ≤ α * #(A⁻¹) := by
    have : B⁻¹ * A⁻¹ = (A * B)⁻¹ := by rw [mul_inv_rev]
    rw [this, Finset.card_inv, Finset.card_inv]
    exact hAB
  obtain ⟨F, hFB, hFK, hcov⟩ := Finset.ruzsa_covering_mul hA.inv hK
  refine ⟨F⁻¹, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_inv'] at hx
    have := hFB hx
    rw [Finset.mem_inv', inv_inv] at this
    exact this
  · rw [Finset.card_inv]; exact hFK
  · have h1 := Finset.inv_subset_inv hcov
    rw [inv_inv] at h1
    refine h1.trans (le_of_eq ?_)
    simp [mul_inv_rev, div_eq_mul_inv, mul_assoc]

lemma ypt_key (A B T Y : Finset G) (α : ℝ) (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A)
    (hcover : B ⊆ A⁻¹ * A * T) :
    (#(B * B * Y) : ℝ) ≤ α ^ 6 * #(B * T * Y) := by
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast Finset.card_pos.mpr (hA.mono hAB)
  have hc := ypt_c43 A B α hBB (ypt_bab A B α hBB hAB hA hmin)
  have hsub : B * B * Y ⊆ (B * A⁻¹ * A) * (T * Y) := by
    have h1 : B * B * Y ⊆ B * (A⁻¹ * A * T) * Y :=
      Finset.mul_subset_mul_right (Finset.mul_subset_mul_left hcover)
    refine h1.trans (le_of_eq ?_)
    simp [mul_assoc]
  have h2 := Finset.ruzsa_triangle_inequality_mul_mulInv_mul (B * A⁻¹ * A) B (T * Y)
  have e1 : B * (B * A⁻¹ * A)⁻¹ = B * A⁻¹ * A * B⁻¹ := by
    simp [mul_inv_rev, mul_assoc]
  have e2 : B * (T * Y) = B * T * Y := by rw [mul_assoc]
  rw [e1, e2] at h2
  have h3 : (#B : ℝ) * #(B * A⁻¹ * A * (T * Y)) ≤ #(B * A⁻¹ * A * B⁻¹) * #(B * T * Y) := by
    exact_mod_cast h2
  have h4 : (#(B * B * Y) : ℝ) ≤ #(B * A⁻¹ * A * (T * Y)) := by
    exact_mod_cast Finset.card_le_card hsub
  have h5 : (#B : ℝ) * #(B * B * Y) ≤ (α ^ 6 * #B) * #(B * T * Y) := by
    calc (#B : ℝ) * #(B * B * Y) ≤ #B * #(B * A⁻¹ * A * (T * Y)) :=
          mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
      _ ≤ #(B * A⁻¹ * A * B⁻¹) * #(B * T * Y) := h3
      _ ≤ (α ^ 6 * #B) * #(B * T * Y) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  calc (#(B * B * Y) : ℝ) = (#B * #(B * B * Y)) / #B := by field_simp
    _ ≤ ((α ^ 6 * #B) * #(B * T * Y)) / #B := by gcongr
    _ = α ^ 6 * #(B * T * Y) := by field_simp

end YPT

section YPT2
variable {G : Type*} [Group G] [DecidableEq G]

lemma ypt_beta_pos (B : Finset G) (β : ℝ) (hB : B.Nonempty)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B) : 0 < β := by
  obtain ⟨b, hb⟩ := id hB
  have h1 := hBbB b hb
  have hne : (B * {b} * B).Nonempty := ((hB.mul (Finset.singleton_nonempty b)).mul hB)
  have h2 : (1 : ℝ) ≤ #(B * {b} * B) := by exact_mod_cast hne.card_pos
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  by_contra hneg
  push_neg at hneg
  nlinarith

lemma ypt_alpha_ge (B : Finset G) (α : ℝ) (hB : B.Nonempty) (hBB : (#(B * B) : ℝ) ≤ α * #B) :
    1 ≤ α := by
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have h1 : (#B : ℝ) ≤ #(B * B) := by exact_mod_cast Finset.card_le_card_mul_left hB
  by_contra hneg
  push_neg at hneg
  nlinarith

lemma ypt_eq10 (B T : Finset G) (α β : ℝ)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) (k : ℕ) :
    (#(B * T * B ^ k) : ℝ) ≤ α * β * #(B⁻¹ * B ^ k) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have : T = ∅ := Finset.subset_empty.mp hTB
    subst this
    simp only [Finset.empty_mul, Finset.inv_empty, Finset.card_empty, Nat.cast_zero, mul_zero, le_refl]
  have hβ := ypt_beta_pos B β hB hBbB
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hper : ∀ t ∈ T, (#(B * {t} * B ^ k) : ℝ) ≤ β * #(B⁻¹ * B ^ k) := by
    intro t ht
    have h1 := Finset.ruzsa_triangle_inequality_mul_mulInv_mul (B * {t}) B⁻¹ (B ^ k)
    have e : B⁻¹ * (B * {t})⁻¹ = (B * {t} * B)⁻¹ := (mul_inv_rev (B * ({t} : Finset G)) B).symm
    rw [e, Finset.card_inv, Finset.card_inv] at h1
    have h1' : (#B : ℝ) * #(B * {t} * B ^ k) ≤ #(B * {t} * B) * #(B⁻¹ * B ^ k) := by
      exact_mod_cast h1
    have h2 := hBbB t (hTB ht)
    have hy : (0 : ℝ) ≤ #(B⁻¹ * B ^ k) := Nat.cast_nonneg _
    generalize (#(B⁻¹ * B ^ k) : ℝ) = y at hy h1' ⊢
    generalize (#(B * {t} * B ^ k) : ℝ) = x at h1' ⊢
    generalize (#(B * {t} * B) : ℝ) = z at h1' h2
    generalize (#B : ℝ) = b at hbpos h1' h2
    nlinarith [mul_le_mul_of_nonneg_right h2 hy]
  have hsub : B * T * B ^ k ⊆ T.biUnion (fun t => B * {t} * B ^ k) := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
    obtain ⟨b, hb, t, ht, rfl⟩ := Finset.mem_mul.mp hy
    refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
    exact Finset.mul_mem_mul (Finset.mul_mem_mul hb (Finset.mem_singleton_self t)) hz
  have hcard : (#(B * T * B ^ k) : ℝ) ≤ ∑ t ∈ T, (#(B * {t} * B ^ k) : ℝ) := by
    have h0 : #(B * T * B ^ k) ≤ ∑ t ∈ T, #(B * {t} * B ^ k) :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h1 := (Nat.cast_le (α := ℝ)).mpr h0
    rw [Nat.cast_sum] at h1
    exact h1
  have h2 : ∑ t ∈ T, (#(B * {t} * B ^ k) : ℝ) ≤ ∑ t ∈ T, β * (#(B⁻¹ * B ^ k) : ℝ) :=
    Finset.sum_le_sum hper
  have h3 : ∑ t ∈ T, β * (#(B⁻¹ * B ^ k) : ℝ) = (#T : ℝ) * (β * #(B⁻¹ * B ^ k)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : (#T : ℝ) * (β * #(B⁻¹ * B ^ k)) ≤ α * (β * #(B⁻¹ * B ^ k)) :=
    mul_le_mul_of_nonneg_right hT (mul_nonneg hβ.le (Nat.cast_nonneg _))
  linarith

lemma ypt_eq11 (B : Finset G) (α : ℝ) (hBB : (#(B * B) : ℝ) ≤ α * #B) (k : ℕ) (hk : 1 ≤ k) :
    (#(B⁻¹ * B ^ k) : ℝ) ≤ α * #(B ^ (k + 1)) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have : (∅ : Finset G) ^ k = ∅ := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp
    simp [this]
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have h1 := Finset.ruzsa_triangle_inequality_invMul_mul_mul B B (B ^ k)
  rw [← pow_succ'] at h1
  have h1' : (#B : ℝ) * #(B⁻¹ * B ^ k) ≤ #(B * B) * #(B ^ (k + 1)) := by exact_mod_cast h1
  have h3 : (#B : ℝ) * #(B⁻¹ * B ^ k) ≤ (#B : ℝ) * (α * #(B ^ (k + 1))) := by
    calc (#B : ℝ) * #(B⁻¹ * B ^ k) ≤ #(B * B) * #(B ^ (k + 1)) := h1'
      _ ≤ (α * #B) * #(B ^ (k + 1)) := mul_le_mul_of_nonneg_right hBB (Nat.cast_nonneg _)
      _ = (#B : ℝ) * (α * #(B ^ (k + 1))) := by ring
  exact le_of_mul_le_mul_left h3 hbpos

lemma ypt_union (B T Y : Finset G) :
    (#(B * T * Y) : ℝ) ≤ ∑ t ∈ T, (#(B * {t} * Y) : ℝ) := by
  have hsub : B * T * Y ⊆ T.biUnion (fun t => B * {t} * Y) := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
    obtain ⟨b, hb, t, ht, rfl⟩ := Finset.mem_mul.mp hy
    refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
    exact Finset.mul_mem_mul (Finset.mul_mem_mul hb (Finset.mem_singleton_self t)) hz
  have h0 : #(B * T * Y) ≤ ∑ t ∈ T, #(B * {t} * Y) :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h1 := (Nat.cast_le (α := ℝ)).mpr h0
  rw [Nat.cast_sum] at h1
  exact h1

lemma ypt_btb (B T : Finset G) (α β : ℝ)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) (hB : B.Nonempty) :
    (#(B * T * B) : ℝ) ≤ α * β * #B := by
  have hβ := ypt_beta_pos B β hB hBbB
  have hbpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have h1 := ypt_union B T B
  have h2 : ∑ t ∈ T, (#(B * {t} * B) : ℝ) ≤ ∑ t ∈ T, β * (#B : ℝ) :=
    Finset.sum_le_sum (fun t ht => hBbB t (hTB ht))
  have h3 : ∑ t ∈ T, β * (#B : ℝ) = (#T : ℝ) * (β * #B) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : (#T : ℝ) * (β * #B) ≤ α * (β * #B) :=
    mul_le_mul_of_nonneg_right hT (mul_nonneg hβ.le (Nat.cast_nonneg _))
  linarith

end YPT2

theorem solution {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBAB : (#(B * A * B) : ℝ) ≤ α ^ 2 * #B) :
    (#(B * A⁻¹ * A * B⁻¹) : ℝ) ≤ α ^ 6 * #B :=
  ypt_c43 A B α hBB hBAB
