-- Prove2me | solution 1 for TheoryOfGames.Minimax.good_iff_support
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:48:33.699726+00:00
-- url     : https://prove2.me/submissions/24a50a51-e240-4963-b1c9-b78ebf56d1a4

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

set_option autoImplicit false

namespace GoodIffSupport1f5f4bed

open TheoryOfGames.Minimax

lemma K_row {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) :
    K H ξ η = ∑ τ₁, ξ τ₁ * ∑ τ₂, H τ₁ τ₂ * η τ₂ := by
  unfold K
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma K_col {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) :
    K H ξ η = ∑ τ₂, η τ₂ * ∑ τ₁, H τ₁ τ₂ * ξ τ₁ := by
  unfold K
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma K_lin_right {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (a b : Fin β₂ → ℝ)
    (s t : ℝ) : K H ξ (s • a + t • b) = s * K H ξ a + t * K H ξ b := by
  simp only [K, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma K_lin_left {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (a b : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (s t : ℝ) : K H (s • a + t • b) η = s * K H a η + t * K H b η := by
  simp only [K, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma wsum_le {β : ℕ} (w c : Fin β → ℝ) (hw : w ∈ stdSimplex ℝ (Fin β)) (M : ℝ)
    (hc : ∀ i, c i ≤ M) : ∑ i, w i * c i ≤ M := by
  calc ∑ i, w i * c i ≤ ∑ i, w i * M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (hw.1 i)
    _ = M := by rw [← Finset.sum_mul, hw.2, one_mul]

lemma le_wsum {β : ℕ} (w c : Fin β → ℝ) (hw : w ∈ stdSimplex ℝ (Fin β)) (m : ℝ)
    (hc : ∀ i, m ≤ c i) : m ≤ ∑ i, w i * c i := by
  calc m = ∑ i, w i * m := by rw [← Finset.sum_mul, hw.2, one_mul]
    _ ≤ ∑ i, w i * c i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (hw.1 i)

lemma abs_le_sumabs {β : ℕ} (c : Fin β → ℝ) (i : Fin β) : |c i| ≤ ∑ j, |c j| :=
  Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma minK_le {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hη : η ∈ stdSimplex ℝ (Fin β₂)) : minK H ξ ≤ K H ξ η := by
  unfold minK
  refine ciInf_le ⟨-(∑ j, |∑ τ₁, H τ₁ j * ξ τ₁|), ?_⟩ (⟨η, hη⟩ : stdSimplex ℝ (Fin β₂))
  rintro _ ⟨e, rfl⟩
  simp only
  rw [K_col]
  refine le_wsum _ _ e.2 _ fun i => ?_
  have := abs_le_sumabs (fun j => ∑ τ₁, H τ₁ j * ξ τ₁) i
  have := neg_abs_le (∑ τ₁, H τ₁ i * ξ τ₁)
  linarith

lemma le_maxK {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) : K H ξ η ≤ maxK H η := by
  unfold maxK
  refine le_ciSup (f := fun e : stdSimplex ℝ (Fin β₁) => K H e η)
    ⟨∑ j, |∑ τ₂, H j τ₂ * η τ₂|, ?_⟩ (⟨ξ, hξ⟩ : stdSimplex ℝ (Fin β₁))
  rintro _ ⟨e, rfl⟩
  simp only
  rw [K_row]
  refine wsum_le _ _ e.2 _ fun i => ?_
  have := abs_le_sumabs (fun j => ∑ τ₂, H j τ₂ * η τ₂) i
  have := le_abs_self (∑ τ₂, H i τ₂ * η τ₂)
  linarith

lemma le_minK {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η₀ : Fin β₂ → ℝ)
    (hη₀ : η₀ ∈ stdSimplex ℝ (Fin β₂)) (m : ℝ)
    (h : ∀ η ∈ stdSimplex ℝ (Fin β₂), m ≤ K H ξ η) : m ≤ minK H ξ := by
  haveI : Nonempty (stdSimplex ℝ (Fin β₂)) := ⟨⟨η₀, hη₀⟩⟩
  exact le_ciInf fun e => h e e.2

lemma maxK_le {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ₀ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ₀ : ξ₀ ∈ stdSimplex ℝ (Fin β₁)) (M : ℝ)
    (h : ∀ ξ ∈ stdSimplex ℝ (Fin β₁), K H ξ η ≤ M) : maxK H η ≤ M := by
  haveI : Nonempty (stdSimplex ℝ (Fin β₁)) := ⟨⟨ξ₀, hξ₀⟩⟩
  exact ciSup_le fun e => h e e.2

lemma exists_saddle {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    ∃ η₀ ∈ stdSimplex ℝ (Fin β₂), ∃ ξ₀ ∈ stdSimplex ℝ (Fin β₁),
      ∀ η' ∈ stdSimplex ℝ (Fin β₂), ∀ ξ' ∈ stdSimplex ℝ (Fin β₁),
        K H ξ' η₀ ≤ K H ξ₀ η' := by
  have hcont1 : ∀ x : Fin β₁ → ℝ, Continuous (fun e : Fin β₂ → ℝ => K H x e) := by
    intro x; unfold K; fun_prop
  have hcont2 : ∀ e : Fin β₂ → ℝ, Continuous (fun x : Fin β₁ → ℝ => K H x e) := by
    intro e; unfold K; fun_prop
  exact Sion.exists_isSaddlePointOn (f := fun (e : Fin β₂ → ℝ) (x : Fin β₁ → ℝ) => K H x e)
    ⟨η, hη⟩ (convex_stdSimplex ℝ (Fin β₂)) (isCompact_stdSimplex ℝ (Fin β₂))
    (fun y _ => (hcont1 y).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ => (ConvexOn.quasiconvexOn
      ⟨convex_stdSimplex ℝ (Fin β₂), fun a _ b _ s t _ _ _ => by
        simp only [smul_eq_mul]; rw [K_lin_right]⟩))
    (convex_stdSimplex ℝ (Fin β₁)) ⟨ξ, hξ⟩ (isCompact_stdSimplex ℝ (Fin β₁))
    (fun x _ => (hcont2 x).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ => (ConcaveOn.quasiconcaveOn
      ⟨convex_stdSimplex ℝ (Fin β₁), fun a _ b _ s t _ _ _ => by
        simp only [smul_eq_mul]; rw [K_lin_left]⟩))

lemma K_single {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (i : Fin β₁) (η : Fin β₂ → ℝ) :
    K H (Pi.single i 1) η = ∑ τ₂, H i τ₂ * η τ₂ := by
  rw [K_row]
  simp [Pi.single_apply]

lemma K_single' {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (j : Fin β₂) :
    K H ξ (Pi.single j 1) = ∑ τ₁, H τ₁ j * ξ τ₁ := by
  rw [K_col]
  simp [Pi.single_apply]

/-- Saddle point implies the support condition. -/
lemma saddle_to_support {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂))
    (h1 : ∀ ξ' ∈ stdSimplex ℝ (Fin β₁), K H ξ' η ≤ K H ξ η)
    (h2 : ∀ η' ∈ stdSimplex ℝ (Fin β₂), K H ξ η ≤ K H ξ η') :
    ((∀ τ₁, ¬ (∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H τ₁ τ₂ * η τ₂) → ξ τ₁ = 0) ∧
       (∀ τ₂, ¬ (∀ τ₂', ∑ τ₁, H τ₁ τ₂ * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁) → η τ₂ = 0)) := by
  constructor
  · intro τ₁ hn
    push_neg at hn
    obtain ⟨τ₁', hlt⟩ := hn
    by_contra hne
    have hpos : 0 < ξ τ₁ := lt_of_le_of_ne (hξ.1 τ₁) (Ne.symm hne)
    set r : Fin β₁ → ℝ := fun i => ∑ τ₂, H i τ₂ * η τ₂ with hr
    have hall : ∀ i, r i ≤ K H ξ η := fun i => by
      have := h1 _ (single_mem_stdSimplex ℝ i)
      rw [K_single] at this
      exact this
    have hlt' : ∑ i, ξ i * r i < ∑ i, ξ i * K H ξ η := by
      refine Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (hξ.1 i))
        ⟨τ₁, Finset.mem_univ _, ?_⟩
      have : r τ₁ < K H ξ η := lt_of_lt_of_le hlt (hall τ₁')
      exact mul_lt_mul_of_pos_left this hpos
    rw [← Finset.sum_mul, hξ.2, one_mul, hr, ← K_row] at hlt'
    exact lt_irrefl _ hlt'
  · intro τ₂ hn
    push_neg at hn
    obtain ⟨τ₂', hlt⟩ := hn
    by_contra hne
    have hpos : 0 < η τ₂ := lt_of_le_of_ne (hη.1 τ₂) (Ne.symm hne)
    set c : Fin β₂ → ℝ := fun j => ∑ τ₁, H τ₁ j * ξ τ₁ with hc
    have hall : ∀ j, K H ξ η ≤ c j := fun j => by
      have := h2 _ (single_mem_stdSimplex ℝ j)
      rw [K_single'] at this
      exact this
    have hlt' : ∑ j, η j * K H ξ η < ∑ j, η j * c j := by
      refine Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hall j) (hη.1 j))
        ⟨τ₂, Finset.mem_univ _, ?_⟩
      have : K H ξ η < c τ₂ := lt_of_le_of_lt (hall τ₂') hlt
      exact mul_lt_mul_of_pos_left this hpos
    rw [← Finset.sum_mul, hη.2, one_mul, hc, ← K_col] at hlt'
    exact lt_irrefl _ hlt'

/-- The support condition implies a saddle point. -/
lemma support_to_saddle {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂))
    (hs : (∀ τ₁, ¬ (∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H τ₁ τ₂ * η τ₂) → ξ τ₁ = 0) ∧
       (∀ τ₂, ¬ (∀ τ₂', ∑ τ₁, H τ₁ τ₂ * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁) → η τ₂ = 0)) :
    (∀ ξ' ∈ stdSimplex ℝ (Fin β₁), K H ξ' η ≤ K H ξ η) ∧
    (∀ η' ∈ stdSimplex ℝ (Fin β₂), K H ξ η ≤ K H ξ η') := by
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · intro ξ' hξ'
    have hsum : ∑ i, ξ i ≠ 0 := by rw [hξ.2]; exact one_ne_zero
    obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hmax : ∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H i0 τ₂ * η τ₂ := by
      by_contra hc; exact hi0 (hs1 i0 hc)
    have hK : K H ξ η = ∑ τ₂, H i0 τ₂ * η τ₂ := by
      rw [K_row]
      calc ∑ τ₁, ξ τ₁ * ∑ τ₂, H τ₁ τ₂ * η τ₂ = ∑ τ₁, ξ τ₁ * ∑ τ₂, H i0 τ₂ * η τ₂ := by
            refine Finset.sum_congr rfl fun τ₁ _ => ?_
            by_cases h0 : ξ τ₁ = 0
            · rw [h0, zero_mul, zero_mul]
            · have hm : ∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H τ₁ τ₂ * η τ₂ := by
                by_contra hc; exact h0 (hs1 τ₁ hc)
              rw [le_antisymm (hmax τ₁) (hm i0)]
        _ = ∑ τ₂, H i0 τ₂ * η τ₂ := by rw [← Finset.sum_mul, hξ.2, one_mul]
    rw [hK, K_row]
    exact wsum_le _ _ hξ' _ hmax
  · intro η' hη'
    have hsum : ∑ i, η i ≠ 0 := by rw [hη.2]; exact one_ne_zero
    obtain ⟨j0, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hmin : ∀ τ₂', ∑ τ₁, H τ₁ j0 * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁ := by
      by_contra hc; exact hj0 (hs2 j0 hc)
    have hK : K H ξ η = ∑ τ₁, H τ₁ j0 * ξ τ₁ := by
      rw [K_col]
      calc ∑ τ₂, η τ₂ * ∑ τ₁, H τ₁ τ₂ * ξ τ₁ = ∑ τ₂, η τ₂ * ∑ τ₁, H τ₁ j0 * ξ τ₁ := by
            refine Finset.sum_congr rfl fun τ₂ _ => ?_
            by_cases h0 : η τ₂ = 0
            · rw [h0, zero_mul, zero_mul]
            · have hm : ∀ τ₂', ∑ τ₁, H τ₁ τ₂ * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁ := by
                by_contra hc; exact h0 (hs2 τ₂ hc)
              rw [le_antisymm (hm j0) (hmin τ₂)]
        _ = ∑ τ₁, H τ₁ j0 * ξ τ₁ := by rw [← Finset.sum_mul, hη.2, one_mul]
    rw [hK, K_col]
    exact le_wsum _ _ hη' _ hmin

end GoodIffSupport1f5f4bed

open GoodIffSupport1f5f4bed in
open TheoryOfGames.Minimax in
theorem solution {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    (ξ ∈ goodA H ∧ η ∈ goodB H) ↔
      ((∀ τ₁, ¬ (∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H τ₁ τ₂ * η τ₂) → ξ τ₁ = 0) ∧
       (∀ τ₂, ¬ (∀ τ₂', ∑ τ₁, H τ₁ τ₂ * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁) → η τ₂ = 0)) := by
  constructor
  · rintro ⟨⟨-, hA⟩, ⟨-, hB⟩⟩
    obtain ⟨η₀, hη₀, ξ₀, hξ₀, hsad⟩ := exists_saddle H ξ η hξ hη
    have hv1 : K H ξ₀ η₀ ≤ minK H ξ₀ :=
      le_minK H ξ₀ η hη _ fun η' hη' => hsad η' hη' ξ₀ hξ₀
    have hv2 : maxK H η₀ ≤ K H ξ₀ η₀ :=
      maxK_le H ξ η₀ hξ _ fun ξ' hξ' => hsad η₀ hη₀ ξ' hξ'
    have hA' := hA ξ₀ hξ₀
    have hB' := hB η₀ hη₀
    apply saddle_to_support H ξ η hξ hη
    · intro ξ' hξ'
      have a := le_maxK H ξ' η hξ'
      have b := minK_le H ξ η hη
      linarith
    · intro η' hη'
      have a := le_maxK H ξ η hξ
      have b := minK_le H ξ η' hη'
      linarith
  · intro hs
    obtain ⟨hs1, hs2⟩ := support_to_saddle H ξ η hξ hη hs
    refine ⟨⟨hξ, fun ξ' hξ' => ?_⟩, ⟨hη, fun η' hη' => ?_⟩⟩
    · calc minK H ξ' ≤ K H ξ' η := minK_le H ξ' η hη
        _ ≤ K H ξ η := hs1 ξ' hξ'
        _ ≤ minK H ξ := le_minK H ξ η hη _ hs2
    · calc maxK H η ≤ K H ξ η := maxK_le H ξ η hξ _ hs1
        _ ≤ K H ξ η' := hs2 η' hη'
        _ ≤ maxK H η' := le_maxK H ξ η' hξ
