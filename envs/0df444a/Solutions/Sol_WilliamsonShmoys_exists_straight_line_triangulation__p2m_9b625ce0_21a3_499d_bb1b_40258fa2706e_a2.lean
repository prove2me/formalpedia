-- Prove2me | solution 1 for WilliamsonShmoys.exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:09:51.062222+00:00
-- url     : https://prove2.me/submissions/564229dd-8300-4eae-a57b-569806f26ef7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

private def finAdj (n : ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ (i.val ≤ 1 ∨ j.val ≤ 1 ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val)

private lemma finAdj_symm {n : ℕ} {i j : Fin n} (h : finAdj n i j) : finAdj n j i :=
  ⟨h.1.symm, by rcases h.2 with h1 | h1 | h1 | h1 <;> tauto⟩

private instance instDecidableFinAdj (n : ℕ) : DecidableRel (finAdj n) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private def finGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj := finAdj n
  symm := ⟨fun _ _ h => finAdj_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance instDecidableFinGraphAdj (n : ℕ) : DecidableRel (finGraph n).Adj :=
  instDecidableFinAdj n

private def finPt (n : ℕ) (i : Fin n) : ℝ × ℝ :=
  if i.val = 0 then (0, 1)
  else if i.val = 1 then (0, -1)
  else ((i.val : ℝ) - 1, 0)

private lemma finPt_zero {n : ℕ} {i : Fin n} (h : i.val = 0) : finPt n i = (0, 1) := by
  simp [finPt, h]

private lemma finPt_one {n : ℕ} {i : Fin n} (h : i.val = 1) : finPt n i = (0, -1) := by
  simp [finPt, h]

private lemma finPt_ge {n : ℕ} {i : Fin n} (h : 2 ≤ i.val) :
    finPt n i = ((i.val : ℝ) - 1, 0) := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  simp [finPt, h0, h1]

private def finArc (n : ℕ) (i j : Fin n) (t : ℝ) : ℝ × ℝ :=
  (1 - t) • finPt n i + t • finPt n j

private lemma finArc_01 {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : j.val = 1) (t : ℝ) :
    finArc n i j t = (0, 1 - 2 * t) := by
  rw [finArc, finPt_zero hi, finPt_one hj]
  apply Prod.ext <;> (simp; try ring)

private lemma finArc_0j {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : 2 ≤ j.val) (t : ℝ) :
    finArc n i j t = (t * ((j.val : ℝ) - 1), 1 - t) := by
  rw [finArc, finPt_zero hi, finPt_ge hj]
  apply Prod.ext <;> simp

private lemma finArc_1j {n : ℕ} {i j : Fin n} (hi : i.val = 1) (hj : 2 ≤ j.val) (t : ℝ) :
    finArc n i j t = (t * ((j.val : ℝ) - 1), t - 1) := by
  rw [finArc, finPt_one hi, finPt_ge hj]
  apply Prod.ext <;> simp

private lemma finArc_path {n : ℕ} {i j : Fin n} (hi : 2 ≤ i.val) (hj : j.val = i.val + 1)
    (t : ℝ) : finArc n i j t = ((i.val : ℝ) - 1 + t, 0) := by
  have hj2 : 2 ≤ j.val := by omega
  rw [finArc, finPt_ge hi, finPt_ge hj2, hj]
  apply Prod.ext
  · simp; ring
  · simp

private lemma finPt_inj (n : ℕ) : Function.Injective (finPt n) := by
  intro i j h
  unfold finPt at h
  split_ifs at h with hi0 hi1 hj0 hj1 <;> rw [Prod.ext_iff] at h
  · exact Fin.ext (by omega)
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · exact Fin.ext (by omega)
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · have hval : (i.val : ℝ) = (j.val : ℝ) := by linarith [h.1]
    exact Fin.ext (Nat.cast_injective hval)

private lemma finArc_symm (n : ℕ) (i j : Fin n) (t : ℝ) :
    finArc n i j t = finArc n j i (1 - t) := by
  unfold finArc
  apply Prod.ext <;> simp <;> ring

private lemma finArc_injOn (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Set.InjOn (finArc n i j) (Set.Icc 0 1) := by
  intro t _ s _ hts
  have hneq : finPt n i ≠ finPt n j := fun h => hij (finPt_inj n h)
  by_contra hne
  apply hneq
  unfold finArc at hts
  rw [Prod.ext_iff] at hts
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd] at hts
  have h1 : (t - s) * ((finPt n j).1 - (finPt n i).1) = 0 := by linarith [hts.1]
  have h2 : (t - s) * ((finPt n j).2 - (finPt n i).2) = 0 := by linarith [hts.2]
  have hts0 : t - s ≠ 0 := sub_ne_zero.mpr hne
  rw [mul_eq_zero] at h1 h2
  have hx : (finPt n i).1 = (finPt n j).1 := by
    rcases h1 with h | h
    · exact absurd h hts0
    · linarith
  have hy : (finPt n i).2 = (finPt n j).2 := by
    rcases h2 with h | h
    · exact absurd h hts0
    · linarith
  exact Prod.ext hx hy

private lemma finAdj_lt_cases {n : ℕ} {i j : Fin n} (hlt : i.val < j.val)
    (hadj : finAdj n i j) :
    (i.val = 0 ∧ j.val = 1) ∨
    (i.val = 0 ∧ 2 ≤ j.val) ∨
    (i.val = 1 ∧ 2 ≤ j.val) ∨
    (2 ≤ i.val ∧ j.val = i.val + 1) := by
  rcases hadj.2 with h | h | h | h <;> omega

private lemma finPt_cases {n : ℕ} (k : Fin n) :
    k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega

private lemma finArc_avoid_vertices_lt (n : ℕ) (i j k : Fin n) (hlt : i.val < j.val)
    (hadj : finAdj n i j) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    finArc n i j t ≠ finPt n k := by
  rcases ht with ⟨ht0, ht1⟩
  intro heq
  rcases finAdj_lt_cases hlt hadj with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [finArc_01 hi hj] at heq
    rcases finPt_cases k with hk | hk | hk
    · rw [finPt_zero hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_one hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_ge hk, Prod.ext_iff] at heq
      have hk2 : (2 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast hk
      linarith
  · rw [finArc_0j hi hj] at heq
    rcases finPt_cases k with hk | hk | hk
    · rw [finPt_zero hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_one hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_ge hk, Prod.ext_iff] at heq; linarith
  · rw [finArc_1j hi hj] at heq
    rcases finPt_cases k with hk | hk | hk
    · rw [finPt_zero hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_one hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_ge hk, Prod.ext_iff] at heq; linarith
  · rw [finArc_path hi hj] at heq
    rcases finPt_cases k with hk | hk | hk
    · rw [finPt_zero hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_one hk, Prod.ext_iff] at heq; linarith
    · rw [finPt_ge hk, Prod.ext_iff] at heq
      have hcast : (k.val : ℝ) = (i.val : ℝ) + t := by linarith [heq.1]
      have hn1 : i.val < k.val := (Nat.cast_lt (α := ℝ)).mp (by linarith)
      have hlt2 : ((k.val : ℕ) : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hn2 : k.val < i.val + 1 := (Nat.cast_lt (α := ℝ)).mp hlt2
      omega

private lemma finArc_avoid_vertices (n : ℕ) (i j k : Fin n) (hadj : finAdj n i j)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    finArc n i j t ≠ finPt n k := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact finArc_avoid_vertices_lt n i j k h hadj t ht
  · exact absurd (Fin.ext h) hadj.1
  · rw [finArc_symm]
    exact finArc_avoid_vertices_lt n j i k h (finAdj_symm hadj) (1 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩

private lemma finArc_interior_disjoint_lt (n : ℕ) (i j a b : Fin n)
    (hlt1 : i.val < j.val) (hlt2 : a.val < b.val)
    (hadj1 : finAdj n i j) (hadj2 : finAdj n a b)
    (hne : (i, j) ≠ (a, b))
    (t s : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    finArc n i j t ≠ finArc n a b s := by
  rcases ht with ⟨ht0, ht1⟩
  rcases hs with ⟨hs0, hs1⟩
  intro heq
  rcases finAdj_lt_cases hlt1 hadj1 with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
    rcases finAdj_lt_cases hlt2 hadj2 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hne (Prod.ext (Fin.ext (hi.trans ha.symm)) (Fin.ext (hj.trans hb.symm)))
  · rw [finArc_01 hi hj, finArc_0j ha hb, Prod.ext_iff] at heq
    have hb2 : (1 : ℝ) ≤ (b.val : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (b.val : ℝ) := by exact_mod_cast hb
      linarith
    nlinarith
  · rw [finArc_01 hi hj, finArc_1j ha hb, Prod.ext_iff] at heq
    have hb2 : (1 : ℝ) ≤ (b.val : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (b.val : ℝ) := by exact_mod_cast hb
      linarith
    nlinarith
  · rw [finArc_01 hi hj, finArc_path ha hb, Prod.ext_iff] at heq
    have ha2 : (2 : ℝ) ≤ (a.val : ℝ) := by exact_mod_cast ha
    linarith
  · rw [finArc_0j hi hj, finArc_01 ha hb, Prod.ext_iff] at heq
    have hj2 : (1 : ℝ) ≤ (j.val : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
      linarith
    nlinarith
  · rw [finArc_0j hi hj, finArc_0j ha hb, Prod.ext_iff] at heq
    have hts : t = s := by linarith [heq.2]
    subst hts
    have hx : t * ((j.val : ℝ) - 1) = t * ((b.val : ℝ) - 1) := heq.1
    have hjb : (j.val : ℝ) - 1 = (b.val : ℝ) - 1 := mul_left_cancel₀ (ne_of_gt ht0) hx
    have hjb' : j.val = b.val := (Nat.cast_injective (R := ℝ)) (by linarith)
    exact hne (Prod.ext (Fin.ext (hi.trans ha.symm)) (Fin.ext hjb'))
  · rw [finArc_0j hi hj, finArc_1j ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_0j hi hj, finArc_path ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_1j hi hj, finArc_01 ha hb, Prod.ext_iff] at heq
    have hj2 : (1 : ℝ) ≤ (j.val : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
      linarith
    nlinarith
  · rw [finArc_1j hi hj, finArc_0j ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_1j hi hj, finArc_1j ha hb, Prod.ext_iff] at heq
    have hts : t = s := by linarith [heq.2]
    subst hts
    have hx : t * ((j.val : ℝ) - 1) = t * ((b.val : ℝ) - 1) := heq.1
    have hjb : (j.val : ℝ) - 1 = (b.val : ℝ) - 1 := mul_left_cancel₀ (ne_of_gt ht0) hx
    have hjb' : j.val = b.val := (Nat.cast_injective (R := ℝ)) (by linarith)
    exact hne (Prod.ext (Fin.ext (hi.trans ha.symm)) (Fin.ext hjb'))
  · rw [finArc_1j hi hj, finArc_path ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_path hi hj, finArc_01 ha hb, Prod.ext_iff] at heq
    have hi2 : (2 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hi
    linarith
  · rw [finArc_path hi hj, finArc_0j ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_path hi hj, finArc_1j ha hb, Prod.ext_iff] at heq; linarith
  · rw [finArc_path hi hj, finArc_path ha hb, Prod.ext_iff] at heq
    have hia : i.val ≠ a.val := fun h =>
      hne (Prod.ext (Fin.ext h) (Fin.ext (by dsimp; omega)))
    have hx : (i.val : ℝ) + t = (a.val : ℝ) + s := by linarith [heq.1]
    rcases lt_or_gt_of_ne hia with h | h
    · have hle : ((i.val + 1 : ℕ) : ℝ) ≤ (a.val : ℝ) := by exact_mod_cast h
      push_cast at hle
      linarith
    · have hle : ((a.val + 1 : ℕ) : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast h
      push_cast at hle
      linarith

private lemma finArc_endpoints_only (n : ℕ) (i j a b : Fin n)
    (hadj1 : finAdj n i j) (hadj2 : finAdj n a b)
    (hne : ¬ ((i = a ∧ j = b) ∨ (i = b ∧ j = a)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : finArc n i j t = finArc n a b s) :
    (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  have finArc_0 : ∀ x y, finArc n x y 0 = finPt n x := by
    intro x y; unfold finArc; simp
  have finArc_1 : ∀ x y, finArc n x y 1 = finPt n y := by
    intro x y; unfold finArc; simp
  have h1 : t = 0 ∨ t = 1 ∨ t ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · left; rfl
    · rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · right; left; rfl
      · right; right; exact ⟨ht0, ht1⟩
  have h2 : s = 0 ∨ s = 1 ∨ s ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · left; rfl
    · rcases eq_or_lt_of_le hs.2 with rfl | hs1
      · right; left; rfl
      · right; right; exact ⟨hs0, hs1⟩
  rcases h1 with rfl | rfl | ht_oo
  · refine ⟨Or.inl rfl, ?_⟩
    rcases h2 with rfl | rfl | hs_oo
    · left; rfl
    · right; rfl
    · exfalso; rw [finArc_0] at heq
      exact finArc_avoid_vertices n a b i hadj2 s hs_oo heq.symm
  · refine ⟨Or.inr rfl, ?_⟩
    rcases h2 with rfl | rfl | hs_oo
    · left; rfl
    · right; rfl
    · exfalso; rw [finArc_1] at heq
      exact finArc_avoid_vertices n a b j hadj2 s hs_oo heq.symm
  · rcases h2 with rfl | rfl | hs_oo
    · exfalso; rw [finArc_0] at heq
      exact finArc_avoid_vertices n i j a hadj1 t ht_oo heq
    · exfalso; rw [finArc_1] at heq
      exact finArc_avoid_vertices n i j b hadj1 t ht_oo heq
    · exfalso
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · rcases lt_trichotomy a.val b.val with hab | hab | hab
        · refine finArc_interior_disjoint_lt n i j a b hij hab hadj1 hadj2 ?_ t s ht_oo hs_oo heq
          intro h; simp only [Prod.mk.injEq] at h; exact hne (Or.inl h)
        · exact absurd (Fin.ext hab) hadj2.1
        · rw [finArc_symm n a b s] at heq
          refine finArc_interior_disjoint_lt n i j b a hij hab hadj1 (finAdj_symm hadj2)
            ?_ t (1 - s) ht_oo ⟨by linarith [hs_oo.2], by linarith [hs_oo.1]⟩ heq
          intro h; simp only [Prod.mk.injEq] at h; exact hne (Or.inr h)
      · exact absurd (Fin.ext hij) hadj1.1
      · rw [finArc_symm n i j t] at heq
        rcases lt_trichotomy a.val b.val with hab | hab | hab
        · refine finArc_interior_disjoint_lt n j i a b hij hab (finAdj_symm hadj1) hadj2
            ?_ (1 - t) s ⟨by linarith [ht_oo.2], by linarith [ht_oo.1]⟩ hs_oo heq
          intro h; simp only [Prod.mk.injEq] at h
          exact hne (Or.inr ⟨h.2, h.1⟩)
        · exact absurd (Fin.ext hab) hadj2.1
        · rw [finArc_symm n a b s] at heq
          refine finArc_interior_disjoint_lt n j i b a hij hab (finAdj_symm hadj1)
            (finAdj_symm hadj2) ?_ (1 - t) (1 - s)
            ⟨by linarith [ht_oo.2], by linarith [ht_oo.1]⟩
            ⟨by linarith [hs_oo.2], by linarith [hs_oo.1]⟩ heq
          intro h; simp only [Prod.mk.injEq] at h
          exact hne (Or.inl ⟨h.2, h.1⟩)

private lemma finGraph_edgeFinset_card (n : ℕ) (hn : 3 ≤ n) :
    (finGraph n).edgeFinset.card + 6 = 3 * n := by
  let f₀ : Fin (n - 1) → Sym2 (Fin n) := fun k => s(⟨0, by omega⟩, ⟨k.val + 1, by omega⟩)
  let f₁ : Fin (n - 2) → Sym2 (Fin n) := fun k => s(⟨1, by omega⟩, ⟨k.val + 2, by omega⟩)
  let f₂ : Fin (n - 3) → Sym2 (Fin n) := fun k => s(⟨k.val + 2, by omega⟩, ⟨k.val + 3, by omega⟩)
  let E₀ : Finset (Sym2 (Fin n)) := Finset.univ.image f₀
  let E₁ : Finset (Sym2 (Fin n)) := Finset.univ.image f₁
  let E₂ : Finset (Sym2 (Fin n)) := Finset.univ.image f₂
  have hf₀ : Function.Injective f₀ := by
    intro k₁ k₂ h
    simp only [f₀, Sym2.eq_iff, Fin.ext_iff] at h
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact Fin.ext (by omega); omega]
  have hf₁ : Function.Injective f₁ := by
    intro k₁ k₂ h
    simp only [f₁, Sym2.eq_iff, Fin.ext_iff] at h
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact Fin.ext (by omega); omega]
  have hf₂ : Function.Injective f₂ := by
    intro k₁ k₂ h
    simp only [f₂, Sym2.eq_iff, Fin.ext_iff] at h
    rcases h with ⟨h, _⟩ | ⟨h₁, h₂⟩ <;> [exact Fin.ext (by omega); omega]
  have hE₀ : E₀.card = n - 1 := by
    rw [Finset.card_image_of_injective _ hf₀, Finset.card_fin]
  have hE₁ : E₁.card = n - 2 := by
    rw [Finset.card_image_of_injective _ hf₁, Finset.card_fin]
  have hE₂ : E₂.card = n - 3 := by
    rw [Finset.card_image_of_injective _ hf₂, Finset.card_fin]
  have hd₀₁ : Disjoint E₀ E₁ := by
    rw [Finset.disjoint_left]
    intro e he₀ he₁
    rcases Finset.mem_image.mp he₀ with ⟨k₀, _, rfl⟩
    rcases Finset.mem_image.mp he₁ with ⟨k₁, _, hk⟩
    simp only [f₀, f₁, Sym2.eq_iff, Fin.ext_iff] at hk
    omega
  have hd₀₂ : Disjoint E₀ E₂ := by
    rw [Finset.disjoint_left]
    intro e he₀ he₂
    rcases Finset.mem_image.mp he₀ with ⟨k₀, _, rfl⟩
    rcases Finset.mem_image.mp he₂ with ⟨k₂, _, hk⟩
    simp only [f₀, f₂, Sym2.eq_iff, Fin.ext_iff] at hk
    omega
  have hd₁₂ : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rcases Finset.mem_image.mp he₁ with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp he₂ with ⟨k₂, _, hk⟩
    simp only [f₁, f₂, Sym2.eq_iff, Fin.ext_iff] at hk
    omega
  have h_eq : (finGraph n).edgeFinset = E₀ ∪ E₁ ∪ E₂ := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      have hi_lt : i.val < n := i.isLt
      have hj_lt : j.val < n := j.isLt
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change finAdj n i j ↔ _
      dsimp only [E₀, E₁, E₂, f₀, f₁, f₂]
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Sym2.eq_iff, Fin.ext_iff, finAdj, ne_eq]
      constructor
      · rintro ⟨hij, h⟩
        rcases h with h | h | h | h
        · by_cases hi0 : i.val = 0
          · left; left; exact ⟨⟨j.val - 1, by omega⟩, Or.inl ⟨hi0.symm, by dsimp; omega⟩⟩
          · by_cases hj0 : j.val = 0
            · left; left; exact ⟨⟨i.val - 1, by omega⟩, Or.inr ⟨hj0.symm, by dsimp; omega⟩⟩
            · left; right; exact ⟨⟨j.val - 2, by omega⟩, Or.inl ⟨by omega, by dsimp; omega⟩⟩
        · by_cases hj0 : j.val = 0
          · left; left; exact ⟨⟨i.val - 1, by omega⟩, Or.inr ⟨hj0.symm, by dsimp; omega⟩⟩
          · by_cases hi0 : i.val = 0
            · left; left; exact ⟨⟨j.val - 1, by omega⟩, Or.inl ⟨hi0.symm, by dsimp; omega⟩⟩
            · left; right; exact ⟨⟨i.val - 2, by omega⟩, Or.inr ⟨by omega, by dsimp; omega⟩⟩
        · by_cases hi0 : i.val = 0
          · left; left; exact ⟨⟨j.val - 1, by omega⟩, Or.inl ⟨hi0.symm, by dsimp; omega⟩⟩
          · by_cases hi1 : i.val = 1
            · left; right; exact ⟨⟨j.val - 2, by omega⟩, Or.inl ⟨hi1.symm, by dsimp; omega⟩⟩
            · right; exact ⟨⟨i.val - 2, by omega⟩, Or.inl ⟨by dsimp; omega, by dsimp; omega⟩⟩
        · by_cases hj0 : j.val = 0
          · left; left; exact ⟨⟨i.val - 1, by omega⟩, Or.inr ⟨hj0.symm, by dsimp; omega⟩⟩
          · by_cases hj1 : j.val = 1
            · left; right; exact ⟨⟨i.val - 2, by omega⟩, Or.inr ⟨hj1.symm, by dsimp; omega⟩⟩
            · right; exact ⟨⟨j.val - 2, by omega⟩, Or.inr ⟨by dsimp; omega, by dsimp; omega⟩⟩
      · rintro ((⟨k, hk⟩ | ⟨k, hk⟩) | ⟨k, hk⟩)
        · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by omega, Or.inl (by omega)⟩
          · exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
        · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by omega, Or.inl (by omega)⟩
          · exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
        · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by omega, Or.inr (Or.inr (Or.inl (by omega)))⟩
          · exact ⟨by omega, Or.inr (Or.inr (Or.inr (by omega)))⟩
  rw [h_eq, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩),
    Finset.card_union_of_disjoint hd₀₁, hE₀, hE₁, hE₂]
  omega

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj)
      (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ u v, u < v → L.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧
        arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → L.Adj u v → L.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (∀ u v t, arc u v t = (1 - t) • p u + t • p v) ∧
      L.edgeFinset.card + 6 = 3 * Fintype.card V := by
  let n : ℕ := Fintype.card V
  let e : V ≃ Fin n := Fintype.equivFin V
  let L : SimpleGraph V :=
    { Adj := fun u v => finAdj n (e u) (e v)
      symm := ⟨fun _ _ h => finAdj_symm h⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  let dL : DecidableRel L.Adj := fun u v => instDecidableFinAdj n (e u) (e v)
  let p : V → ℝ × ℝ := fun u => finPt n (e u)
  let arc : V → V → ℝ → ℝ × ℝ := fun u v t => finArc n (e u) (e v) t
  refine ⟨L, dL, p, arc, ?_, ?_, ?_, ?_, ?_⟩
  · exact (finPt_inj n).comp e.injective
  · intro u v huv hadj
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold arc finArc
      fun_prop
    · exact finArc_injOn n (e u) (e v) (fun h => ne_of_lt huv (e.injective h))
    · simp [arc, finArc, p]
    · simp [arc, finArc, p]
    · intro t ht w
      exact finArc_avoid_vertices n (e u) (e v) (e w) hadj t ht
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
    apply finArc_endpoints_only n (e u) (e v) (e x) (e y) hadj1 hadj2 _ t ht s hs heq
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · apply hne; ext <;> [exact e.injective h1; exact e.injective h2]
    · have hux : u = y := e.injective h1
      have hvx : v = x := e.injective h2
      subst hux; subst hvx
      exact absurd (huv.trans hxy) (lt_irrefl u)
  · intro u v t; rfl
  · have h_equiv : L.edgeSet ≃ (finGraph n).edgeSet :=
      { toFun := fun ⟨x, hx⟩ => ⟨x.map e, by
          induction x using Sym2.ind with
          | _ u v => exact hx⟩
        invFun := fun ⟨y, hy⟩ => ⟨y.map e.symm, by
          induction y using Sym2.ind with
          | _ i j =>
            change finAdj n (e (e.symm i)) (e (e.symm j))
            change finAdj n i j at hy
            simpa using hy⟩
        left_inv := fun ⟨x, _⟩ => by
          ext : 1
          induction x using Sym2.ind with
          | _ u v => simp
        right_inv := fun ⟨y, _⟩ => by
          ext : 1
          induction y using Sym2.ind with
          | _ i j => simp }
    have hcard_eq : L.edgeFinset.card = (finGraph n).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
      exact Fintype.card_congr h_equiv
    rw [hcard_eq]
    exact finGraph_edgeFinset_card n hcard
