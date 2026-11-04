-- Prove2me | solution 1 for ObsCostMDP.WellPosed.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:31:51.499444+00:00
-- url     : https://prove2.me/submissions/22219d0a-1d0b-4aca-acdb-f8d7d242f945

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI

open ObsCostMDP.WellPosed

theorem solution {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β)
    (Q : ℕ → Matrix X X ℝ) (hQ : IsSubstochastic Q)
    (c : A → X → ℝ) (hc : ∀ a x, 0 < c a x)
    (u v : ℕ → X → A → ℝ) (hu : IsBounded u) (hv : IsBounded v)
    (hsub : IsSubsolution F Q c u) (hsup : IsSupersolution F Q c v) :
    ∀ n x a, u n x a ≤ v n x a := by
  obtain ⟨hβ, hmono, -, hcont⟩ := hF
  have hub := hu
  have hvb0 := hv
  obtain ⟨Ku, hKu⟩ := hu
  obtain ⟨Kv, hKv⟩ := hv
  have actMax_ge : ∀ (w : A → ℝ) (a : A), w a ≤ actMax w :=
    fun w a => Finset.le_sup' w (Finset.mem_univ a)
  have actMax_eq : ∀ (w : A → ℝ), ∃ a, actMax w = w a := by
    intro w
    obtain ⟨a, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty w
    exact ⟨a, h⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨n₀, x₀, a₀, h₀⟩ := hcon
  have hDle : ∀ n x a, u n x a - v n x a ≤ Ku + Kv := by
    intro n x a
    have h1 := (abs_le.mp (hKu n x a)).2
    have h2 := (abs_le.mp (hKv n x a)).1
    linarith
  have hDge : ∀ n x a, -(Ku + Kv) ≤ u n x a - v n x a := by
    intro n x a
    have h1 := (abs_le.mp (hKu n x a)).1
    have h2 := (abs_le.mp (hKv n x a)).2
    linarith
  have hbdd : BddAbove (Set.range fun p : ℕ × X × A => u p.1 p.2.1 p.2.2 - v p.1 p.2.1 p.2.2) :=
    ⟨Ku + Kv, by rintro _ ⟨p, rfl⟩; exact hDle _ _ _⟩
  set M := ⨆ p : ℕ × X × A, (u p.1 p.2.1 p.2.2 - v p.1 p.2.1 p.2.2) with hM
  have hleM : ∀ n x a, u n x a - v n x a ≤ M := fun n x a => le_ciSup hbdd (n, x, a)
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) (hleM n₀ x₀ a₀)
  have hMle : M ≤ Ku + Kv := ciSup_le fun p => hDle _ _ _
  have hKpos : 0 ≤ Ku + Kv := le_trans hMpos.le hMle
  have hKv0 : 0 ≤ Kv := le_trans (abs_nonneg _) (hKv n₀ x₀ a₀)
  have hvb : ∀ a, IsBoundedFn (fun m y => v m y a + M) := by
    intro a
    refine ⟨Kv + |M|, fun m y => ?_⟩
    exact le_trans (abs_add_le _ _) (by linarith [hKv m y a])
  have hvM : IsBounded (fun m y j => v m y j + M) := by
    refine ⟨Kv + |M|, fun m y j => ?_⟩
    exact le_trans (abs_add_le _ _) (by linarith [hKv m y j])
  set R : ℝ := Kv + (Ku + Kv) with hR
  have hδex : ∀ a, ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : X) (r s : A → ℝ),
      (∀ j, |r j| ≤ R) → (∀ j, |s j| ≤ R) → (∀ j, |r j - s j| < δ) →
        |F a n x r (fun m y => v m y a + M) - F a n x s (fun m y => v m y a + M)| < β * M :=
    fun a => hcont a _ (hvb a) R (β * M) (mul_pos hβ hMpos)
  choose δ hδpos hδ using hδex
  set δ0 := Finset.univ.inf' Finset.univ_nonempty δ with hδ0
  have hδ0pos : 0 < δ0 := (Finset.lt_inf'_iff _).2 (fun a _ => hδpos a)
  have hδ0le : ∀ a, δ0 ≤ δ a := fun a => Finset.inf'_le _ (Finset.mem_univ a)
  -- key step
  have key : ∀ n x a, (∀ j, u n x j - v n x j ≤ u n x a - v n x a) →
      M - (u n x a - v n x a) < δ0 → u n x a ≤ inspection Q c u n x := by
    intro n x a hmax hclose
    set Mk := u n x a - v n x a with hMk
    have e1 := hmono n x u (fun m y j => v m y j + M) hub hvM
      (fun m y j => by have := hleM m y j; linarith) (u n x) (fun j => v n x j + Mk) a
      (by intro j; have := hmax j; linarith) (by linarith)
    have h0 : u n x a - (v n x a + Mk) = 0 := by rw [hMk]; ring
    beta_reduce at e1
    rw [h0] at e1
    simp only [add_zero, mul_zero] at e1
    have e2 := hmono n x v v hvb0 hvb0 (fun _ _ _ => le_rfl) (fun j => v n x j + M) (v n x) a
      (by intro j; linarith) (by linarith)
    beta_reduce at e2
    have h1 : v n x a + M - v n x a = M := by ring
    rw [h1] at e2
    have hMkle : Mk ≤ M := hleM n x a
    have e3 := hδ a n x (fun j => v n x j + M) (fun j => v n x j + Mk)
      (fun j => by
        beta_reduce
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_pos hMpos]; linarith [hKv n x j])
      (fun j => by
        beta_reduce
        refine le_trans (abs_add_le _ _) ?_
        have : |Mk| ≤ Ku + Kv := abs_le.mpr ⟨hDge n x a, hDle n x a⟩
        linarith [hKv n x j])
      (fun j => by
        beta_reduce
        rw [show v n x j + M - (v n x j + Mk) = M - Mk by ring, abs_of_nonneg (by linarith)]
        linarith [hδ0le a])
    have e4 := (abs_lt.mp e3).2
    have hFsup : 0 ≤ F a n x (v n x) (fun m y => v m y a) := (le_min_iff.mp (hsup n x a)).1
    have hFpos : 0 < F a n x (u n x) (fun m y => u m y a) := by linarith
    have := hsub n x a
    unfold ObsCostMDP.WellPosed.residual at this
    rcases min_le_iff.mp this with h | h
    · linarith
    · linarith
  -- inspection difference bound
  set M1 := (Finset.univ : Finset (X × A)).sup' Finset.univ_nonempty
    (fun q : X × A => u 1 q.1 q.2 - v 1 q.1 q.2) with hM1
  have hinsp : ∀ n x, inspection Q c u n x - inspection Q c v n x ≤ max M1 0 := by
    intro n x
    unfold inspection
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ y, Q n x y * actMax (fun a => u 1 y a - c a y) -
        Q n x y * actMax (fun a => v 1 y a - c a y) ≤ Q n x y * M1 := by
      intro y
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ ((hQ n).1 x y)
      obtain ⟨b, hb⟩ := actMax_eq (fun a => u 1 y a - c a y)
      rw [hb]
      have := actMax_ge (fun a => v 1 y a - c a y) b
      have h2 : u 1 y b - v 1 y b ≤ M1 :=
        Finset.le_sup' (fun q : X × A => u 1 q.1 q.2 - v 1 q.1 q.2) (Finset.mem_univ (y, b))
      beta_reduce at this
      linarith
    calc _ ≤ ∑ y, Q n x y * M1 := Finset.sum_le_sum fun y _ => hterm y
      _ = (∑ y, Q n x y) * M1 := by rw [Finset.sum_mul]
      _ ≤ (∑ y, Q n x y) * max M1 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _)
            (Finset.sum_nonneg fun y _ => (hQ n).1 x y)
      _ ≤ max M1 0 := mul_le_of_le_one_left (le_max_right _ _) ((hQ n).2 x)
  have hMM1 : M ≤ max M1 0 := by
    by_contra hlt
    push Not at hlt
    set ε := min δ0 (M - max M1 0) with hε
    have hεpos : 0 < ε := lt_min hδ0pos (by linarith)
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup (show M - ε < M by linarith)
    obtain ⟨a', -, ha'⟩ := Finset.exists_max_image Finset.univ
      (fun j => u p.1 p.2.1 j - v p.1 p.2.1 j) Finset.univ_nonempty
    have hge : u p.1 p.2.1 p.2.2 - v p.1 p.2.1 p.2.2 ≤ u p.1 p.2.1 a' - v p.1 p.2.1 a' :=
      ha' p.2.2 (Finset.mem_univ _)
    have hk := key p.1 p.2.1 a' (fun j => ha' j (Finset.mem_univ _))
      (by have := min_le_left δ0 (M - max M1 0); linarith)
    have hv' := (le_min_iff.mp (hsup p.1 p.2.1 a')).2
    have := hinsp p.1 p.2.1
    have := min_le_right δ0 (M - max M1 0)
    linarith
  have hM1M : M1 ≤ M := Finset.sup'_le _ _ (fun q _ => hleM 1 q.1 q.2)
  have hM1eq : M ≤ M1 := by
    rcases le_total M1 0 with h | h
    · rw [max_eq_right h] at hMM1; linarith
    · rwa [max_eq_left h] at hMM1
  obtain ⟨q0, -, hq0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := X × A))
    (fun q : X × A => u 1 q.1 q.2 - v 1 q.1 q.2)
  set T := (Finset.univ : Finset (X × A)).filter (fun q => u 1 q.1 q.2 - v 1 q.1 q.2 = M) with hT
  have hTne : T.Nonempty := ⟨q0, by
    rw [hT, Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
    have : M1 = u 1 q0.1 q0.2 - v 1 q0.1 q0.2 := hq0
    linarith⟩
  obtain ⟨⟨y1, b1⟩, hy1T, hy1max⟩ := Finset.exists_max_image T (fun q => u 1 q.1 q.2) hTne
  have hy1 : u 1 y1 b1 - v 1 y1 b1 = M := (Finset.mem_filter.mp hy1T).2
  have hU := key 1 y1 b1 (fun j => by rw [hy1]; exact hleM 1 y1 j) (by rw [hy1]; simpa using hδ0pos)
  have hV := (le_min_iff.mp (hsup 1 y1 b1)).2
  choose bz hbz using fun z => actMax_eq (fun b => u 1 z b - c b z)
  have hIu : inspection Q c u 1 y1 = ∑ z, Q 1 y1 z * (u 1 z (bz z) - c (bz z) z) := by
    unfold inspection
    exact Finset.sum_congr rfl (fun z _ => by rw [hbz z])
  have hIv : ∑ z, Q 1 y1 z * (v 1 z (bz z) - c (bz z) z) ≤ inspection Q c v 1 y1 := by
    unfold inspection
    exact Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (actMax_ge (fun b => v 1 z b - c b z) (bz z)) ((hQ 1).1 y1 z)
  set s := ∑ z, Q 1 y1 z with hs
  have hs1 : s ≤ 1 := (hQ 1).2 y1
  have hMsum : M ≤ ∑ z, Q 1 y1 z * (u 1 z (bz z) - v 1 z (bz z)) := by
    have : ∑ z, Q 1 y1 z * (u 1 z (bz z) - v 1 z (bz z)) =
        ∑ z, Q 1 y1 z * (u 1 z (bz z) - c (bz z) z) -
          ∑ z, Q 1 y1 z * (v 1 z (bz z) - c (bz z) z) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [this]
    linarith
  have he_nonneg : ∀ z, 0 ≤ Q 1 y1 z * (M - (u 1 z (bz z) - v 1 z (bz z))) :=
    fun z => mul_nonneg ((hQ 1).1 y1 z) (by linarith [hleM 1 z (bz z)])
  have he_sum : ∑ z, Q 1 y1 z * (M - (u 1 z (bz z) - v 1 z (bz z))) =
      s * M - ∑ z, Q 1 y1 z * (u 1 z (bz z) - v 1 z (bz z)) := by
    rw [hs, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  have he_le : ∑ z, Q 1 y1 z * (M - (u 1 z (bz z) - v 1 z (bz z))) ≤ 0 := by
    rw [he_sum]; nlinarith
  have he_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => he_nonneg z)).mp
    (le_antisymm he_le (Finset.sum_nonneg fun z _ => he_nonneg z))
  have hs_ge : 1 ≤ s := by
    have h0 : 0 ≤ s * M - M := by
      have := Finset.sum_nonneg (fun z (_ : z ∈ Finset.univ) => he_nonneg z)
      rw [he_sum] at this; linarith
    by_contra hlt; push Not at hlt
    nlinarith
  have hterm : ∀ z, Q 1 y1 z * (u 1 z (bz z) - c (bz z) z) ≤
      Q 1 y1 z * (u 1 y1 b1 - c (bz z) z) := by
    intro z
    rcases eq_or_lt_of_le ((hQ 1).1 y1 z) with h | h
    · rw [← h]; simp
    · apply mul_le_mul_of_nonneg_left _ h.le
      have hz := he_zero z (Finset.mem_univ _)
      have hzM : u 1 z (bz z) - v 1 z (bz z) = M := by
        rcases mul_eq_zero.mp hz with h' | h'
        · linarith
        · linarith
      have hmemT : (z, bz z) ∈ T := by
        rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hzM⟩
      have := hy1max (z, bz z) hmemT
      beta_reduce at this
      linarith
  have hsumc : 0 < ∑ z, Q 1 y1 z * c (bz z) z := by
    have hex : ∃ z, 0 < Q 1 y1 z := by
      by_contra hne
      push Not at hne
      have : s = 0 := by
        rw [hs]; exact Finset.sum_eq_zero fun z _ => le_antisymm (hne z) ((hQ 1).1 y1 z)
      linarith
    obtain ⟨z, hz⟩ := hex
    exact Finset.sum_pos' (fun i _ => mul_nonneg ((hQ 1).1 y1 i) (hc _ _).le)
      ⟨z, Finset.mem_univ _, mul_pos hz (hc _ _)⟩
  have hfin : ∑ z, Q 1 y1 z * (u 1 y1 b1 - c (bz z) z) =
      s * u 1 y1 b1 - ∑ z, Q 1 y1 z * c (bz z) z := by
    rw [hs, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  have hs_eq : s = 1 := le_antisymm hs1 hs_ge
  have := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hterm z)
  rw [hfin, hs_eq] at this
  rw [hIu] at hU
  linarith
