-- Prove2me | solution 1 for ObsCostMDP.WellPosed.theorem_3_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:34:49.068707+00:00
-- url     : https://prove2.me/submissions/5ef538e5-59b2-43d3-beee-b062285911b7

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Theorems.Thm_ObsCostMDP_WellPosed_proposition_3_3

open ObsCostMDP.WellPosed

theorem solution {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β) (hF' : Assumption312 F)
    (hF0 : ∃ K : ℝ, ∀ a n x, |F a n x (fun _ => 0) (fun _ _ => 0)| ≤ K)
    (Q : ℕ → Matrix X X ℝ) (hQ : IsSubstochastic Q)
    (c : A → X → ℝ) (hc : ∀ a x, 0 < c a x) :
    ∃ u : ℕ → X → A → ℝ, IsBounded u ∧ IsSolution F Q c u ∧
      ∀ v : ℕ → X → A → ℝ, IsBounded v → IsSolution F Q c v → v = u := by
  have hFsave := hF
  obtain ⟨hβ, hmono, -, hcont⟩ := hF
  obtain ⟨K, hK⟩ := hF0
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _)
    (hK (Classical.arbitrary A) 0 (Classical.arbitrary X))
  -- basic facts
  have actMax_ge : ∀ (w : A → ℝ) (a : A), w a ≤ actMax w :=
    fun w a => Finset.le_sup' w (Finset.mem_univ a)
  have actMax_mono : ∀ (w w' : A → ℝ), (∀ a, w a ≤ w' a) → actMax w ≤ actMax w' := by
    intro w w' h
    exact Finset.sup'_le _ _ (fun a _ => le_trans (h a) (actMax_ge w' a))
  have insp_mono : ∀ (u w : ℕ → X → A → ℝ), (∀ n x a, u n x a ≤ w n x a) →
      ∀ n x, inspection Q c u n x ≤ inspection Q c w n x := by
    intro u w h n x
    unfold inspection
    exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
      (actMax_mono _ _ (fun a => by linarith [h 1 y a])) ((hQ n).1 x y)
  -- monotonicity with θ = 0
  have mono0 : ∀ (n : ℕ) (x : X) (a : A) (r s : A → ℝ) (φ ψ : ℕ → X → ℝ),
      IsBoundedFn φ → IsBoundedFn ψ → (∀ m y, φ m y ≤ ψ m y) →
      (∀ j, r j - s j ≤ r a - s a) → r a = s a → F a n x s ψ ≤ F a n x r φ := by
    intro n x a r s φ ψ ⟨Kφ, hφ⟩ ⟨Kψ, hψ⟩ hle hj hra
    have := hmono n x (fun m y _ => φ m y) (fun m y _ => ψ m y) ⟨Kφ, fun m y _ => hφ m y⟩
      ⟨Kψ, fun m y _ => hψ m y⟩ (fun m y _ => hle m y) r s a hj (by rw [hra, sub_self])
    rw [hra, sub_self] at this
    simp only [add_zero, mul_zero] at this
    linarith
  -- monotonicity with a uniform shift
  have shift : ∀ (n : ℕ) (x : X) (a : A) (r : A → ℝ) (φ : ℕ → X → ℝ), IsBoundedFn φ →
      ∀ t : ℝ, 0 ≤ t → β * t ≤ F a n x (fun j => r j + t) (fun m y => φ m y + t) - F a n x r φ := by
    intro n x a r φ ⟨Kφ, hφ⟩ t ht
    have := hmono n x (fun m y _ => φ m y) (fun m y _ => φ m y) ⟨Kφ, fun m y _ => hφ m y⟩
      ⟨Kφ, fun m y _ => hφ m y⟩ (fun m y _ => le_rfl) (fun j => r j + t) r a
      (by intro j; ring_nf; exact le_rfl) (by ring_nf; exact ht)
    have h1 : r a + t - r a = t := by ring
    beta_reduce at this
    rw [h1] at this
    exact this
  have hzeroBdd : IsBoundedFn (fun (_ : ℕ) (_ : X) => (0 : ℝ)) := ⟨0, fun _ _ => by simp⟩
  have hconstBdd : ∀ t : ℝ, IsBoundedFn (fun (_ : ℕ) (_ : X) => t) := fun t => ⟨|t|, fun _ _ => le_rfl⟩
  set C : ℝ := K / β + 1 with hCdef
  have hCpos : 0 < C := by have := div_nonneg hK0 hβ.le; linarith
  have hβC : K < β * C := by
    rw [hCdef, mul_add, mul_div_cancel₀ _ hβ.ne']; linarith
  -- F at the constant C is positive
  have hFC : ∀ a n x, 0 < F a n x (fun _ => C) (fun _ _ => C) := by
    intro a n x
    have := shift n x a (fun _ => 0) (fun _ _ => 0) hzeroBdd C hCpos.le
    simp only [zero_add] at this
    have := (abs_le.mp (hK a n x)).1
    linarith
  -- F at the constant -C is negative
  have hFmC : ∀ a n x, F a n x (fun _ => -C) (fun _ _ => -C) < 0 := by
    intro a n x
    have := shift n x a (fun _ => -C) (fun _ _ => -C) (hconstBdd _) C hCpos.le
    simp only [neg_add_cancel] at this
    have := (abs_le.mp (hK a n x)).2
    linarith
  -- the Perron family
  let S := {w : ℕ → X → A → ℝ // IsSubsolution F Q c w ∧ ∀ n x a, |w n x a| ≤ C}
  have hmC : IsSubsolution F Q c (fun _ _ _ => -C) := by
    intro n x a
    unfold ObsCostMDP.WellPosed.residual
    exact min_le_of_left_le (hFmC a n x).le
  let w0 : S := ⟨fun _ _ _ => -C, hmC, fun _ _ _ => by rw [abs_neg, abs_of_pos hCpos]⟩
  haveI : Nonempty S := ⟨w0⟩
  have hbddS : ∀ n x a, BddAbove (Set.range fun w : S => w.1 n x a) :=
    fun n x a => ⟨C, by rintro _ ⟨w, rfl⟩; exact (abs_le.mp (w.2.2 n x a)).2⟩
  set U : ℕ → X → A → ℝ := fun n x a => ⨆ w : S, w.1 n x a with hUdef
  have hleU : ∀ (w : S) n x a, w.1 n x a ≤ U n x a := fun w n x a => le_ciSup (hbddS n x a) w
  have hUle : ∀ n x a, U n x a ≤ C := fun n x a =>
    ciSup_le fun w => (abs_le.mp (w.2.2 n x a)).2
  have hUge : ∀ n x a, -C ≤ U n x a := fun n x a => hleU w0 n x a
  have hUabs : ∀ n x a, |U n x a| ≤ C := fun n x a => abs_le.mpr ⟨hUge n x a, hUle n x a⟩
  have hUbdd : IsBounded U := ⟨C, hUabs⟩
  have hUa : ∀ a, IsBoundedFn (fun m y => U m y a) := fun a => ⟨C, fun m y => hUabs m y a⟩
  -- U is a subsolution
  have hUsub : IsSubsolution F Q c U := by
    intro n x a
    unfold ObsCostMDP.WellPosed.residual
    by_cases hM : U n x a ≤ inspection Q c U n x
    · exact min_le_of_right_le (by linarith)
    apply min_le_of_left_le
    push Not at hM
    by_contra hpos
    push Not at hpos
    obtain ⟨δ, hδ, hδc⟩ := hcont a (fun m y => U m y a) (hUa a) C _ hpos
    set η := min δ (U n x a - inspection Q c U n x) with hη
    have hηpos : 0 < η := lt_min hδ (by linarith)
    obtain ⟨w, hw⟩ := exists_lt_of_lt_ciSup (show U n x a - η < U n x a by linarith)
    have hwle := hleU w
    have hinspw := insp_mono w.1 U hwle n x
    have hFw : F a n x (w.1 n x) (fun m y => w.1 m y a) ≤ 0 := by
      have := w.2.1 n x a
      unfold ObsCostMDP.WellPosed.residual at this
      rcases min_le_iff.mp this with h | h
      · exact h
      · exfalso
        have := min_le_right δ (U n x a - inspection Q c U n x)
        linarith
    set r' : A → ℝ := fun j => if j = a then w.1 n x a else U n x j with hr'
    have h1 : F a n x r' (fun m y => U m y a) ≤ F a n x (w.1 n x) (fun m y => w.1 m y a) := by
      apply mono0 n x a (w.1 n x) r' _ _ ⟨C, fun m y => w.2.2 m y a⟩ (hUa a)
        (fun m y => hwle m y a)
      · intro j
        by_cases hj : j = a
        · subst hj; simp [hr']
        · simp [hr', hj]; linarith [hwle n x j]
      · simp [hr']
    have h2 := hδc n x (U n x) r' (fun j => hUabs n x j)
      (fun j => by
        by_cases hj : j = a
        · subst hj; simp [hr']; exact w.2.2 n x j
        · simp [hr', hj]; exact hUabs n x j)
      (fun j => by
        by_cases hj : j = a
        · subst hj; simp only [hr', if_true]
          rw [abs_of_nonneg (by linarith [hwle n x j])]
          have := min_le_left δ (U n x j - inspection Q c U n x)
          linarith
        · simp [hr', hj]; exact hδ)
    have := (abs_lt.mp h2).2
    linarith
  -- strict inequality U - MU > 0 where U = C
  have hinspC : ∀ n x, inspection Q c U n x < C := by
    intro n x
    set C' := (Finset.univ : Finset X).sup' Finset.univ_nonempty
      (fun y => actMax (fun b => U 1 y b - c b y)) with hC'
    have hC'lt : C' < C := by
      rw [hC', Finset.sup'_lt_iff]
      intro y _
      unfold actMax
      rw [Finset.sup'_lt_iff]
      intro b _
      linarith [hUle 1 y b, hc b y]
    unfold inspection
    calc ∑ y, Q n x y * actMax (fun a => U 1 y a - c a y)
        ≤ ∑ y, Q n x y * max C' 0 := Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (le_trans (Finset.le_sup'
            (fun y => actMax (fun b => U 1 y b - c b y)) (Finset.mem_univ y)) (le_max_left _ _))
            ((hQ n).1 x y)
      _ = (∑ y, Q n x y) * max C' 0 := by rw [Finset.sum_mul]
      _ ≤ max C' 0 := mul_le_of_le_one_left (le_max_right _ _) ((hQ n).2 x)
      _ < C := max_lt hC'lt hCpos
  -- U is a supersolution
  have hUsup : IsSupersolution F Q c U := by
    intro n₀ x₀ a₀
    by_contra hneg
    push Not at hneg
    -- U n₀ x₀ a₀ < C
    have hlt : U n₀ x₀ a₀ < C := by
      by_contra hge
      push Not at hge
      have hEq : U n₀ x₀ a₀ = C := le_antisymm (hUle _ _ _) hge
      have hF1 : F a₀ n₀ x₀ (fun _ => C) (fun _ _ => C) ≤
          F a₀ n₀ x₀ (U n₀ x₀) (fun m y => U m y a₀) :=
        mono0 n₀ x₀ a₀ (U n₀ x₀) (fun _ => C) _ _ (hUa a₀) (hconstBdd C)
          (fun m y => hUle m y a₀) (fun j => by rw [hEq]; linarith [hUle n₀ x₀ j]) hEq
      have := hFC a₀ n₀ x₀
      have := hinspC n₀ x₀
      unfold ObsCostMDP.WellPosed.residual at hneg
      rcases min_lt_iff.mp hneg with h | h <;> linarith
    -- the bump
    let w : ℝ → ℕ → X → A → ℝ := fun η n x a =>
      U n x a + (if n = n₀ ∧ x = x₀ ∧ a = a₀ then η else 0)
    have hwU : ∀ η, 0 ≤ η → ∀ n x a, U n x a ≤ w η n x a := by
      intro η hη n x a
      simp only [w]
      split_ifs <;> linarith
    have bump : ∀ η, 0 < η → η ≤ C - U n₀ x₀ a₀ →
        ObsCostMDP.WellPosed.residual F Q c (w η) n₀ x₀ a₀ ≤ 0 → False := by
      intro η hη hηC hres
      have hwabs : ∀ n x a, |w η n x a| ≤ C := by
        intro n x a
        simp only [w]
        split_ifs with h
        · obtain ⟨rfl, rfl, rfl⟩ := h
          rw [abs_le]; constructor <;> linarith [hUge n x a]
        · simpa using hUabs n x a
      have hwsub : IsSubsolution F Q c (w η) := by
        intro n x a
        by_cases hp : n = n₀ ∧ x = x₀ ∧ a = a₀
        · obtain ⟨rfl, rfl, rfl⟩ := hp; exact hres
        have hwa : w η n x a = U n x a := by simp [w, hp]
        have h1 : F a n x (w η n x) (fun m y => w η m y a) ≤ F a n x (U n x) (fun m y => U m y a) :=
          mono0 n x a (U n x) (w η n x) _ _ (hUa a) ⟨C, fun m y => hwabs m y a⟩
            (fun m y => hwU η hη.le m y a)
            (fun j => by rw [hwa]; simp only [sub_self]; linarith [hwU η hη.le n x j])
            hwa.symm
        have h2 := insp_mono U (w η) (hwU η hη.le) n x
        have := hUsub n x a
        unfold ObsCostMDP.WellPosed.residual at this ⊢
        rw [hwa]
        exact le_trans (min_le_min h1 (by linarith)) this
      have := hleU ⟨w η, hwsub, hwabs⟩ n₀ x₀ a₀
      simp [w] at this
      linarith
    unfold ObsCostMDP.WellPosed.residual at hneg
    rcases min_lt_iff.mp hneg with hFneg | hMneg
    · -- F-branch negative
      set f := F a₀ n₀ x₀ (U n₀ x₀) (fun m y => U m y a₀) with hf
      obtain ⟨δ, hδ, hδc⟩ := hcont a₀ (fun m y => U m y a₀) (hUa a₀) C (-f) (by linarith)
      set η := min (δ / 2) (C - U n₀ x₀ a₀) with hη
      have hηpos : 0 < η := lt_min (by linarith) (by linarith)
      have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      apply bump η hηpos (min_le_right _ _)
      unfold ObsCostMDP.WellPosed.residual
      apply min_le_of_left_le
      have hwabs0 : ∀ j, |w η n₀ x₀ j| ≤ C := by
        intro j
        simp only [w]
        split_ifs with h
        · obtain ⟨-, -, rfl⟩ := h
          rw [abs_le]; constructor <;> linarith [hUge n₀ x₀ j, min_le_right (δ / 2) (C - U n₀ x₀ j)]
        · simpa using hUabs n₀ x₀ j
      have h1 : F a₀ n₀ x₀ (w η n₀ x₀) (fun m y => w η m y a₀) ≤
          F a₀ n₀ x₀ (w η n₀ x₀) (fun m y => U m y a₀) :=
        mono0 n₀ x₀ a₀ (w η n₀ x₀) (w η n₀ x₀) _ _ (hUa a₀)
          ⟨C, fun m y => by
            have : |w η m y a₀| ≤ C := by
              simp only [w]
              split_ifs with h
              · obtain ⟨rfl, rfl, -⟩ := h
                rw [abs_le]; constructor <;> linarith [hUge m y a₀, min_le_right (δ / 2) (C - U m y a₀)]
              · simpa using hUabs m y a₀
            exact this⟩
          (fun m y => hwU η hηpos.le m y a₀) (fun j => by simp) rfl
      have h2 := hδc n₀ x₀ (w η n₀ x₀) (U n₀ x₀) hwabs0 (fun j => hUabs n₀ x₀ j)
        (fun j => by
          simp only [w]
          split_ifs
          · rw [add_sub_cancel_left, abs_of_pos hηpos]; exact hηδ
          · simpa using hδ)
      have := (abs_lt.mp h2).2
      linarith
    · -- inspection branch negative
      set g := U n₀ x₀ a₀ - inspection Q c U n₀ x₀ with hg
      set η := min (-g / 2) (C - U n₀ x₀ a₀) with hη
      have hηpos : 0 < η := lt_min (by linarith) (by linarith)
      apply bump η hηpos (min_le_right _ _)
      unfold ObsCostMDP.WellPosed.residual
      apply min_le_of_right_le
      have h2 := insp_mono U (w η) (hwU η hηpos.le) n₀ x₀
      have : w η n₀ x₀ a₀ = U n₀ x₀ a₀ + η := by simp [w]
      rw [this]
      have := min_le_left (-g / 2) (C - U n₀ x₀ a₀)
      linarith
  have hUsol : IsSolution F Q c U := fun n x a => le_antisymm (hUsub n x a) (hUsup n x a)
  refine ⟨U, hUbdd, hUsol, fun v hv hvsol => ?_⟩
  have hvsub : IsSubsolution F Q c v := fun n x a => (hvsol n x a).le
  have hvsup : IsSupersolution F Q c v := fun n x a => (hvsol n x a).ge
  have h1 := proposition_3_3 F β hFsave Q hQ c hc v U hv hUbdd hvsub hUsup
  have h2 := proposition_3_3 F β hFsave Q hQ c hc U v hUbdd hv hUsub hvsup
  funext n x a
  exact le_antisymm (h1 n x a) (h2 n x a)
