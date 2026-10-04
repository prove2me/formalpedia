-- Prove2me | solution 1 for TheoryOfGames.Minimax.good_iff_saddlePoint
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:03:31.451679+00:00
-- url     : https://prove2.me/submissions/1283cab0-27dd-4508-9490-deedb5d5cc1f

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

namespace MinimaxAux

open Finset TheoryOfGames.Minimax

/-- The two alternatives cannot hold simultaneously. -/
lemma not_both {n m : ℕ} (a : Fin n → Fin m → ℝ) (x : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n))
    (h1 : ∀ i, ∑ j, a i j * x j ≤ 0) (h2 : ∀ j, 0 < ∑ i, a i j * w i) : False := by
  have e : ∑ i, w i * ∑ j, a i j * x j = ∑ j, x j * ∑ i, a i j * w i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hA : ∑ i, w i * ∑ j, a i j * x j ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw.1 i) (h1 i)
  have hB : 0 < ∑ j, x j * ∑ i, a i j * w i := by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := x) (by rw [hx.2]; exact one_ne_zero)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hx.1 j) (h2 j).le) ⟨j, mem_univ _, ?_⟩
    exact mul_pos (lt_of_le_of_ne (hx.1 j) (Ne.symm hj)) (h2 j)
  linarith

/-- If the first alternative fails, the second holds (separation of the compact convex set
`A(S_m)` from the closed negative orthant). -/
lemma exists_of_not {n m : ℕ} (hn : 0 < n) (a : Fin n → Fin m → ℝ)
    (h : ¬ ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) :
    ∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 < ∑ i, a i j * w i := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · refine ⟨fun _ => 1 / (n : ℝ), ⟨fun _ => by positivity, ?_⟩, fun j => isEmptyElim j⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of a)
  have hA : ∀ x i, A x i = ∑ j, a i j * x j := by
    intro x i; simp [A, Matrix.mulVec, dotProduct]
  set S : Set (Fin n → ℝ) := A '' stdSimplex ℝ (Fin m) with hS
  have hSc : IsCompact S :=
    (isCompact_stdSimplex ℝ (Fin m)).image (LinearMap.continuous_of_finiteDimensional A)
  have hSv : Convex ℝ S := (convex_stdSimplex ℝ (Fin m)).linear_image A
  set T : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Iic (0 : ℝ)) with hT
  have hTv : Convex ℝ T := convex_pi fun i _ => convex_Iic 0
  have hTc : IsClosed T := isClosed_set_pi fun i _ => isClosed_Iic
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hmem
    exact h ⟨x, hx, fun i => by rw [← hA]; exact hmem i (Set.mem_univ i)⟩
  obtain ⟨f, u, v, hf1, huv, hf2⟩ := geometric_hahn_banach_compact_closed hSv hSc hTv hTc hdisj
  have h0 : v < 0 := by
    have h00 : (0 : Fin n → ℝ) ∈ T := by
      rw [hT, Set.mem_univ_pi]
      intro i
      exact (le_refl (0 : ℝ))
    have := hf2 0 h00
    simpa using this
  let e : Fin n → (Fin n → ℝ) := fun i j => if i = j then 1 else 0
  have hrep : ∀ y : Fin n → ℝ, f y = ∑ i, y i * f (e i) := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
    simpa [e] using this
  -- the functional is nonpositive on the coordinate vectors
  have hneg : ∀ i, f (e i) ≤ 0 := by
    intro i
    by_contra hpos
    rw [not_le] at hpos
    set p := f (e i) with hp
    set t : ℝ := (-v + 1) / p with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have hb : (fun j => -t * e i j) ∈ T := by
      intro j _
      simp only [Set.mem_Iic, e]
      split_ifs <;> linarith
    have := hf2 _ hb
    rw [hrep] at this
    have hsum : ∑ j, (-t * e i j) * f (e j) = -t * p := by
      rw [Finset.sum_eq_single i]
      · simp [e, hp]
      · intro j _ hj
        simp [e, Ne.symm hj]
      · intro hi; exact absurd (mem_univ i) hi
    rw [hsum, ht] at this
    have : -((-v + 1) / p) * p = v - 1 := by field_simp; ring
    linarith
  set w' : Fin n → ℝ := fun i => - f (e i) with hw'
  have hw'nn : ∀ i, 0 ≤ w' i := fun i => by simp only [hw']; linarith [hneg i]
  have hpos : ∀ j, 0 < ∑ i, a i j * w' i := by
    intro j
    have hmem : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ stdSimplex ℝ (Fin m) := single_mem_stdSimplex ℝ j
    have h1 := hf1 _ ⟨_, hmem, rfl⟩
    rw [hrep] at h1
    have hcol : ∀ i, A (Pi.single j (1 : ℝ)) i = a i j := by
      intro i; rw [hA]; simp [Pi.single_apply]
    simp only [hcol] at h1
    have : ∑ i, a i j * w' i = - ∑ i, a i j * f (e i) := by
      simp only [hw', mul_neg, Finset.sum_neg_distrib]
    rw [this]
    linarith
  have hs : 0 < ∑ i, w' i := by
    by_contra hle
    rw [not_lt] at hle
    have hz : ∀ i, w' i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw'nn i)).1
        (le_antisymm hle (Finset.sum_nonneg fun i _ => hw'nn i))
      exact this i (mem_univ i)
    obtain ⟨j⟩ := hm
    have := hpos j
    simp [hz] at this
  refine ⟨fun i => w' i / ∑ k, w' k, ⟨fun i => div_nonneg (hw'nn i) hs.le, ?_⟩, fun j => ?_⟩
  · rw [← Finset.sum_div, div_self hs.ne']
  · have : ∑ i, a i j * (w' i / ∑ k, w' k) = (∑ i, a i j * w' i) / ∑ k, w' k := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact div_pos (hpos j) hs


/-- The theorem of the alternative (16:C), in disjunctive form. -/
lemma alt {n m : ℕ} (hn : 0 < n) (a : Fin n → Fin m → ℝ) :
    (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) ∨
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 < ∑ i, a i j * w i) := by
  by_cases h : ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0
  · exact Or.inl h
  · exact Or.inr (exists_of_not hn a h)

lemma pos_of_mem {β : ℕ} {ξ : Fin β → ℝ} (h : ξ ∈ stdSimplex ℝ (Fin β)) : 0 < β := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  have := h.2
  simp at this

lemma pureVec_mem {β : ℕ} (τ : Fin β) : pureVec τ ∈ stdSimplex ℝ (Fin β) := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold pureVec; split_ifs <;> norm_num
  · simp [pureVec]

lemma simplex_le_one {β : ℕ} {ξ : Fin β → ℝ} (h : ξ ∈ stdSimplex ℝ (Fin β)) (i : Fin β) :
    ξ i ≤ 1 := by
  have := Finset.single_le_sum (f := ξ) (fun j _ => h.1 j) (Finset.mem_univ i)
  rwa [h.2] at this

lemma K_row {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) :
    K H ξ η = ∑ i, ξ i * ∑ j, H i j * η j := by
  unfold K
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma K_col {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) :
    K H ξ η = ∑ j, η j * ∑ i, H i j * ξ i := by
  unfold K
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma K_abs_le {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) {ξ : Fin β₁ → ℝ} {η : Fin β₂ → ℝ}
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    |K H ξ η| ≤ ∑ i, ∑ j, |H i j| := by
  unfold K
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hξ.1 i), abs_of_nonneg (hη.1 j)]
  have h1 : |H i j| * ξ i ≤ |H i j| := mul_le_of_le_one_right (abs_nonneg _) (simplex_le_one hξ i)
  have h2 : |H i j| * ξ i * η j ≤ |H i j| * ξ i :=
    mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (hξ.1 i)) (simplex_le_one hη j)
  linarith

lemma minK_le {β₁ β₂ : ℕ} {H : Fin β₁ → Fin β₂ → ℝ} {ξ : Fin β₁ → ℝ} {η : Fin β₂ → ℝ}
    (hη : η ∈ stdSimplex ℝ (Fin β₂)) (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) :
    minK H ξ ≤ K H ξ η := by
  unfold minK
  refine ciInf_le ⟨-(∑ i, ∑ j, |H i j|), ?_⟩ (⟨η, hη⟩ : stdSimplex ℝ (Fin β₂))
  rintro _ ⟨η', rfl⟩
  exact (abs_le.1 (K_abs_le H hξ η'.2)).1

lemma le_minK {β₁ β₂ : ℕ} {H : Fin β₁ → Fin β₂ → ℝ} {ξ : Fin β₁ → ℝ} {c : ℝ}
    (hne : (stdSimplex ℝ (Fin β₂)).Nonempty)
    (h : ∀ η ∈ stdSimplex ℝ (Fin β₂), c ≤ K H ξ η) : c ≤ minK H ξ := by
  unfold minK
  have : Nonempty (stdSimplex ℝ (Fin β₂)) := hne.to_subtype
  exact le_ciInf fun η => h η.1 η.2

lemma le_maxK {β₁ β₂ : ℕ} {H : Fin β₁ → Fin β₂ → ℝ} {ξ : Fin β₁ → ℝ} {η : Fin β₂ → ℝ}
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    K H ξ η ≤ maxK H η := by
  unfold maxK
  refine le_ciSup (f := fun ξ' : stdSimplex ℝ (Fin β₁) => K H ξ' η)
    ⟨∑ i, ∑ j, |H i j|, ?_⟩ (⟨ξ, hξ⟩ : stdSimplex ℝ (Fin β₁))
  rintro _ ⟨ξ', rfl⟩
  exact (abs_le.1 (K_abs_le H ξ'.2 hη)).2

lemma maxK_le {β₁ β₂ : ℕ} {H : Fin β₁ → Fin β₂ → ℝ} {η : Fin β₂ → ℝ} {c : ℝ}
    (hne : (stdSimplex ℝ (Fin β₁)).Nonempty)
    (h : ∀ ξ ∈ stdSimplex ℝ (Fin β₁), K H ξ η ≤ c) : maxK H η ≤ c := by
  unfold maxK
  have : Nonempty (stdSimplex ℝ (Fin β₁)) := hne.to_subtype
  exact ciSup_le fun ξ => h ξ.1 ξ.2

lemma sum_sub_mul {β : ℕ} (u : Fin β → ℝ) (x : Fin β → ℝ) (c : ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin β)) :
    ∑ j, (u j - c) * x j = ∑ j, u j * x j - c := by
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx.2, mul_one]

lemma sum_sub_mul' {β : ℕ} (u : Fin β → ℝ) (x : Fin β → ℝ) (c : ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin β)) :
    ∑ j, (c - u j) * x j = c - ∑ j, u j * x j := by
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx.2, mul_one]

/-- Existence of a mixed saddle point (the minimax theorem), derived from the alternative. -/
lemma saddle_exists {β₁ β₂ : ℕ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (H : Fin β₁ → Fin β₂ → ℝ) :
    ∃ ξ η, IsMixedSaddlePoint H ξ η := by
  classical
  have hne₁ : (stdSimplex ℝ (Fin β₁)).Nonempty := ⟨pureVec ⟨0, hβ₁⟩, pureVec_mem _⟩
  have hne₂ : (stdSimplex ℝ (Fin β₂)).Nonempty := ⟨pureVec ⟨0, hβ₂⟩, pureVec_mem _⟩
  have : Nonempty (stdSimplex ℝ (Fin β₂)) := hne₂.to_subtype
  set c : ℝ := ⨅ η : stdSimplex ℝ (Fin β₂), maxK H η with hc
  have hc_le : ∀ η ∈ stdSimplex ℝ (Fin β₂), c ≤ maxK H η := by
    intro η hη
    refine ciInf_le ⟨-(∑ i, ∑ j, |H i j|), ?_⟩ (⟨η, hη⟩ : stdSimplex ℝ (Fin β₂))
    rintro _ ⟨η', rfl⟩
    obtain ⟨ξ0, hξ0⟩ := hne₁
    have h1 : K H ξ0 η'.1 ≤ maxK H η'.1 := le_maxK hξ0 η'.2
    exact le_trans (abs_le.1 (K_abs_le H hξ0 η'.2)).1 h1
  have hc_ge : ∀ ε : ℝ, (∀ η ∈ stdSimplex ℝ (Fin β₂), ε ≤ maxK H η) → ε ≤ c :=
    fun ε h => le_ciInf fun η => h η.1 η.2
  have hA : ∃ η0 ∈ stdSimplex ℝ (Fin β₂), maxK H η0 ≤ c := by
    rcases alt hβ₁ (fun i j => H i j - c) with ⟨x, hx, hx2⟩ | ⟨w, hw, hw2⟩
    · refine ⟨x, hx, maxK_le hne₁ fun ξ hξ => ?_⟩
      rw [K_row]
      have hrow : ∀ i, ∑ j, H i j * x j ≤ c := by
        intro i
        have := hx2 i
        rw [sum_sub_mul _ _ _ hx] at this
        linarith
      calc ∑ i, ξ i * ∑ j, H i j * x j ≤ ∑ i, ξ i * c :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hξ.1 i)
        _ = c := by rw [← Finset.sum_mul, hξ.2, one_mul]
    · exfalso
      obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ
        (fun j => ∑ i, (H i j - c) * w i) ⟨⟨0, hβ₂⟩, Finset.mem_univ _⟩
      set ε := ∑ i, (H i j0 - c) * w i with hε
      have hεpos : 0 < ε := hw2 j0
      have hcol : ∀ j, c + ε ≤ ∑ i, H i j * w i := by
        intro j
        have h1 := hj0 j (Finset.mem_univ j)
        rw [sum_sub_mul (fun i => H i j) w c hw] at h1
        rw [hε]
        linarith
      have hle : c + ε ≤ c := by
        refine hc_ge _ fun η hη => ?_
        have hKw : c + ε ≤ K H w η := by
          rw [K_col]
          calc c + ε = ∑ j, η j * (c + ε) := by rw [← Finset.sum_mul, hη.2, one_mul]
            _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (hη.1 j)
        exact hKw.trans (le_maxK hw hη)
      linarith
  have hB : ∃ ξ0 ∈ stdSimplex ℝ (Fin β₁), c ≤ minK H ξ0 := by
    rcases alt hβ₂ (fun j i => c - H i j) with ⟨x, hx, hx2⟩ | ⟨w, hw, hw2⟩
    · refine ⟨x, hx, le_minK hne₂ fun η hη => ?_⟩
      rw [K_col]
      have hcol : ∀ j, c ≤ ∑ i, H i j * x i := by
        intro j
        have := hx2 j
        rw [sum_sub_mul' (fun i => H i j) x c hx] at this
        linarith
      calc c = ∑ j, η j * c := by rw [← Finset.sum_mul, hη.2, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (hη.1 j)
    · exfalso
      obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ
        (fun i => ∑ j, (c - H i j) * w j) ⟨⟨0, hβ₁⟩, Finset.mem_univ _⟩
      set ε := ∑ j, (c - H i0 j) * w j with hε
      have hεpos : 0 < ε := hw2 i0
      have hrow : ∀ i, ∑ j, H i j * w j ≤ c - ε := by
        intro i
        have h1 := hi0 i (Finset.mem_univ i)
        rw [sum_sub_mul' (fun j => H i j) w c hw] at h1
        rw [hε]
        linarith
      have hmax : maxK H w ≤ c - ε := by
        refine maxK_le hne₁ fun ξ hξ => ?_
        rw [K_row]
        calc ∑ i, ξ i * ∑ j, H i j * w j ≤ ∑ i, ξ i * (c - ε) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hξ.1 i)
          _ = c - ε := by rw [← Finset.sum_mul, hξ.2, one_mul]
      have := hc_le w hw
      linarith
  obtain ⟨η0, hη0, hmax0⟩ := hA
  obtain ⟨ξ0, hξ0, hmin0⟩ := hB
  refine ⟨ξ0, η0, hξ0, hη0, fun ξ' hξ' => ?_, fun η' hη' => ?_⟩
  · have h1 : K H ξ' η0 ≤ c := (le_maxK hξ' hη0).trans hmax0
    have h2 : c ≤ K H ξ0 η0 := hmin0.trans (minK_le hη0 hξ0)
    linarith
  · have h1 : K H ξ0 η0 ≤ c := (le_maxK hξ0 hη0).trans hmax0
    have h2 : c ≤ K H ξ0 η' := hmin0.trans (minK_le hη' hξ0)
    linarith

/-- A saddle point consists of good strategies, and `minK`, `maxK` equal the saddle value. -/
lemma saddle_good {β₁ β₂ : ℕ} {H : Fin β₁ → Fin β₂ → ℝ} {ξ : Fin β₁ → ℝ} {η : Fin β₂ → ℝ}
    (h : IsMixedSaddlePoint H ξ η) :
    ξ ∈ goodA H ∧ η ∈ goodB H ∧ minK H ξ = K H ξ η ∧ maxK H η = K H ξ η := by
  obtain ⟨hξ, hη, hmax, hmin⟩ := h
  have hmin' : minK H ξ = K H ξ η :=
    le_antisymm (minK_le hη hξ) (le_minK ⟨η, hη⟩ hmin)
  have hmax' : maxK H η = K H ξ η :=
    le_antisymm (maxK_le ⟨ξ, hξ⟩ hmax) (le_maxK hξ hη)
  refine ⟨⟨hξ, fun ξ' hξ' => ?_⟩, ⟨hη, fun η' hη' => ?_⟩, hmin', hmax'⟩
  · rw [hmin']
    exact (minK_le hη hξ').trans (hmax ξ' hξ')
  · rw [hmax']
    exact (hmin η' hη').trans (le_maxK hξ hη')

end MinimaxAux

open MinimaxAux TheoryOfGames.Minimax in
theorem solution {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    (ξ ∈ goodA H ∧ η ∈ goodB H) ↔ IsMixedSaddlePoint H ξ η := by
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨ξs, ηs, hs⟩ := saddle_exists (pos_of_mem hξ) (pos_of_mem hη) H
    obtain ⟨hAs, hBs, hmins, hmaxs⟩ := saddle_good hs
    have e1 : minK H ξ = minK H ξs := le_antisymm (hAs.2 ξ hξ) (hA.2 ξs hs.1)
    have e2 : maxK H η = maxK H ηs := le_antisymm (hB.2 ηs hs.2.1) (hBs.2 η hη)
    have h1 : ∀ ξ' ∈ stdSimplex ℝ (Fin β₁), K H ξ' η ≤ K H ξs ηs := fun ξ' hξ' => by
      rw [← hmaxs, ← e2]; exact le_maxK hξ' hη
    have h2 : ∀ η' ∈ stdSimplex ℝ (Fin β₂), K H ξs ηs ≤ K H ξ η' := fun η' hη' => by
      rw [← hmins, ← e1]; exact minK_le hη' hξ
    have h3 : K H ξ η = K H ξs ηs := le_antisymm (h1 ξ hξ) (h2 η hη)
    refine ⟨hξ, hη, fun ξ' hξ' => ?_, fun η' hη' => ?_⟩
    · rw [h3]; exact h1 ξ' hξ'
    · rw [h3]; exact h2 η' hη'
  · intro h
    obtain ⟨hA, hB, -, -⟩ := saddle_good h
    exact ⟨hA, hB⟩
