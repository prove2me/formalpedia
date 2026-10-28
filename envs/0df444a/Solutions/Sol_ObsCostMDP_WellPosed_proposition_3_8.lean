-- Prove2me | solution 1 for ObsCostMDP.WellPosed.proposition_3_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:01:38.034305+00:00
-- url     : https://prove2.me/submissions/e5c12402-5c60-42d5-8ff7-abee045ab4e0

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

open ObsCostMDP.WellPosed in
theorem solution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (hc : ∀ a l, 0 < c a l)
    (u v : Fin N → X → A → ℝ)
    (hsub : IsTSubsolution Ft Q c u) (hsup : IsTSupersolution Ft Q c v) :
    ∀ n l a, u n l a ≤ v n l a := by
  intro n l a
  by_contra hlt
  push_neg at hlt
  obtain ⟨⟨n0, l0, a0⟩, hmax⟩ :=
    Finite.exists_max (fun p : Fin N × X × A => u p.1 p.2.1 p.2.2 - v p.1 p.2.1 p.2.2)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = u n0 l0 a0 - v n0 l0 a0 := ⟨_, rfl⟩
  have hm : ∀ n l a, u n l a - v n l a ≤ δ := fun n l a => hδdef ▸ hmax (n, l, a)
  have hδ : 0 < δ := lt_of_lt_of_le (sub_pos.mpr hlt) (hm n l a)
  choose b hb using fun y : X => Finite.exists_max (fun a : A => u 0 y a - c a y)
  have hMu : ∀ y, actMax (fun a => u 0 y a - c a y) = u 0 y (b y) - c (b y) y := fun y =>
    le_antisymm (Finset.sup'_le _ _ fun a _ => hb y a)
      (Finset.le_sup' (fun a => u 0 y a - c a y) (Finset.mem_univ _))
  have hMv : ∀ y, v 0 y (b y) - c (b y) y ≤ actMax (fun a => v 0 y a - c a y) := fun y =>
    Finset.le_sup' (fun a => v 0 y a - c a y) (Finset.mem_univ _)
  have key : ∀ n l a, u n l a - v n l a = δ →
      u n l a ≤ ∑ y, Q n l y * (u 0 y (b y) - c (b y) y) ∧ (∑ y, Q n l y = 1) ∧
        ∀ y, 0 < Q n l y → u 0 y (b y) - v 0 y (b y) = δ := by
    intro n l a hz
    have hs := hsub n l a
    have hv := hsup n l a
    unfold tResidual at hs hv
    have hv1 : 0 ≤ Ft a v n l := (le_min_iff.mp hv).1
    have hv2 : 0 ≤ v n l a - tInspection Q c v n l := (le_min_iff.mp hv).2
    rcases min_le_iff.mp hs with hF | hI
    · exfalso
      have h35 := hFt.2 u v n l a (fun n' l' a' => (hm n' l' a').trans hz.ge) (by linarith)
      have := mul_pos hFt.1 hδ
      rw [hz] at h35
      linarith
    · unfold tInspection at hI hv2
      simp only [hMu] at hI
      have hQ0 := (hQ n).1 l
      have hsumle := (hQ n).2 l
      have hD : ∀ y, u 0 y (b y) - v 0 y (b y) ≤ δ := fun y => hm 0 y (b y)
      have hvb : ∑ y, Q n l y * (v 0 y (b y) - c (b y) y) ≤
          ∑ y, Q n l y * actMax (fun a => v 0 y a - c a y) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hMv y) (hQ0 y)
      have e : ∑ y, Q n l y * (u 0 y (b y) - c (b y) y) -
          ∑ y, Q n l y * (v 0 y (b y) - c (b y) y) =
          ∑ y, Q n l y * (u 0 y (b y) - v 0 y (b y)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      have hineq : δ ≤ ∑ y, Q n l y * (u 0 y (b y) - v 0 y (b y)) := by linarith
      have hub : ∑ y, Q n l y * (u 0 y (b y) - v 0 y (b y)) ≤ δ * ∑ y, Q n l y := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun y _ => by nlinarith [hD y, hQ0 y]
      refine ⟨by linarith, ?_, ?_⟩
      · have : 1 ≤ ∑ y, Q n l y := by
          by_contra h
          push_neg at h
          nlinarith
        linarith
      · intro y hy
        have hterm : ∀ y, 0 ≤ Q n l y * (δ - (u 0 y (b y) - v 0 y (b y))) := fun y =>
          mul_nonneg (hQ0 y) (by linarith [hD y])
        have hsum0 : ∑ y, Q n l y * (δ - (u 0 y (b y) - v 0 y (b y))) ≤ 0 := by
          have : ∑ y, Q n l y * (δ - (u 0 y (b y) - v 0 y (b y))) =
              δ * ∑ y, Q n l y - ∑ y, Q n l y * (u 0 y (b y) - v 0 y (b y)) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
          rw [this]
          nlinarith
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hterm y)).mp
          (le_antisymm hsum0 (Finset.sum_nonneg fun y _ => hterm y)) y (Finset.mem_univ y)
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith [hD y]
  have hexpos : ∀ n l, ∑ y, Q n l y = 1 → ∃ y, 0 < Q n l y := by
    intro n l hS
    by_contra h
    push_neg at h
    have : ∑ y, Q n l y ≤ 0 := Finset.sum_nonpos fun y _ => h y
    linarith
  obtain ⟨-, hS, hpos⟩ := key n0 l0 a0 hδdef.symm
  obtain ⟨y1, hy1⟩ := hexpos n0 l0 hS
  set Z := (Finset.univ : Finset (X × A)).filter (fun p => u 0 p.1 p.2 - v 0 p.1 p.2 = δ) with hZ
  have hZne : Z.Nonempty := ⟨(y1, b y1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos y1 hy1⟩⟩
  obtain ⟨⟨l1, a1⟩, hZ1, hmaxu⟩ := Finset.exists_max_image Z (fun p => u 0 p.1 p.2) hZne
  have hz1 : u 0 l1 a1 - v 0 l1 a1 = δ := (Finset.mem_filter.mp hZ1).2
  obtain ⟨hle, hS1, hpos1⟩ := key 0 l1 a1 hz1
  obtain ⟨y2, hy2⟩ := hexpos 0 l1 hS1
  have hbound : ∀ y, 0 < Q 0 l1 y → u 0 y (b y) ≤ u 0 l1 a1 := fun y hy =>
    hmaxu (y, b y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos1 y hy⟩)
  have hlt2 : ∑ y, Q 0 l1 y * (u 0 y (b y) - c (b y) y) < ∑ y, Q 0 l1 y * u 0 l1 a1 := by
    apply Finset.sum_lt_sum
    · intro y _
      rcases ((hQ 0).1 l1 y).eq_or_lt with h | h
      · rw [← h]; simp
      · have h1 := hbound y h
        have h2 := hc (b y) y
        nlinarith
    · refine ⟨y2, Finset.mem_univ _, ?_⟩
      have h1 := hbound y2 hy2
      have h2 := hc (b y2) y2
      nlinarith
  rw [← Finset.sum_mul, hS1, one_mul] at hlt2
  linarith
