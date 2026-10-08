-- Prove2me | solution 1 for TalagrandConc.BinPacking.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:30:20.800107+00:00
-- url     : https://prove2.me/submissions/89a37583-149f-4520-868f-180573b087b1

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

open scoped ENNReal

namespace TalagrandConc.BinPacking

/-- A packing of the items in `I` only. -/
def PackingOn {N : ℕ} (I : Finset (Fin N)) (x : Fin N → unitInterval) (k : ℕ) : Prop :=
  ∃ σ : Fin N → Fin k, ∀ j : Fin k,
    ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) ≤ 1

lemma packingOn_univ_iff {N : ℕ} (x : Fin N → unitInterval) (k : ℕ) :
    PackingOn Finset.univ x k ↔ IsPacking x k := Iff.rfl

lemma sum_filter_insert {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) (a : Fin N)
    (ha : a ∉ I) (σ : Fin N → Fin k) (j : Fin k) :
    ∑ i ∈ (insert a I).filter (fun i => σ i = j), (x i : ℝ) =
      (if σ a = j then (x a : ℝ) else 0) + ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
  classical
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert]
    simp only [Finset.mem_filter, not_and]; intro h'; exact absurd h' ha
  · rw [zero_add]

lemma sum_filter_congr {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N))
    (σ σ' : Fin N → Fin k) (h : ∀ i ∈ I, σ' i = σ i) (j : Fin k) :
    ∑ i ∈ I.filter (fun i => σ' i = j), (x i : ℝ) = ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
  classical
  congr 1
  apply Finset.filter_congr; intro i hi; rw [h i hi]

/-- Key greedy lemma: there is a packing of the items of `I` into `k` bins whose pairwise
bin sums exceed one. -/
lemma exists_packingOn_pairwise {N : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) :
    ∃ k : ℕ, ∃ σ : Fin N → Fin k,
      (∀ j : Fin k, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) ≤ 1) ∧
      (∀ j j' : Fin k, j ≠ j' →
        1 < ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) +
            ∑ i ∈ I.filter (fun i => σ i = j'), (x i : ℝ)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 0, fun j => by simp, fun j j' hjj' => absurd (Subsingleton.elim j j') hjj'⟩
  | insert a I ha ih =>
    obtain ⟨k, σ, hσ1, hσ2⟩ := ih
    have hx0 : 0 ≤ (x a : ℝ) := (x a).2.1
    have hx1 : (x a : ℝ) ≤ 1 := (x a).2.2
    by_cases hfit : ∃ j : Fin k, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) + (x a : ℝ) ≤ 1
    · obtain ⟨j₀, hj₀⟩ := hfit
      have hupd : ∀ i ∈ I, Function.update σ a j₀ i = σ i :=
        fun i hi => Function.update_of_ne (fun h : i = a => ha (h ▸ hi)) _ _
      refine ⟨k, Function.update σ a j₀, ?_, ?_⟩
      · intro j
        rw [sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd]
        simp only [Function.update_self]
        split_ifs with h
        · subst h; linarith
        · simpa using hσ1 j
      · intro j j' hjj'
        rw [sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd,
          sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd]
        have := hσ2 j j' hjj'
        simp only [Function.update_self]
        split_ifs <;> linarith
    · push_neg at hfit
      -- new bin
      set σ' : Fin N → Fin (k + 1) := fun i => if i = a then Fin.last k else Fin.castSucc (σ i)
        with hσ'
      have hσ'a : σ' a = Fin.last k := by simp [hσ']
      have hcast : ∀ j : Fin k, ∑ i ∈ I.filter (fun i => σ' i = Fin.castSucc j), (x i : ℝ) =
          ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
        intro j
        congr 1
        apply Finset.filter_congr
        intro i hi
        have : i ≠ a := fun h => ha (h ▸ hi)
        simp [hσ', this, Fin.castSucc_inj]
      have hlast : ∑ i ∈ I.filter (fun i => σ' i = Fin.last k), (x i : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_filter] at hi
        exfalso
        have : i ≠ a := fun h => ha (h ▸ hi.1)
        have h2 := hi.2
        simp only [hσ', this, if_false] at h2
        exact Fin.castSucc_ne_last _ h2
      refine ⟨k + 1, σ', ?_, ?_⟩
      · intro j
        rw [sum_filter_insert x I a ha, hσ'a]
        induction j using Fin.lastCases with
        | last => rw [hlast]; simp [hx1]
        | cast j => rw [hcast, if_neg (Fin.castSucc_ne_last j).symm, zero_add]; exact hσ1 j
      · intro j j' hjj'
        rw [sum_filter_insert x I a ha, sum_filter_insert x I a ha, hσ'a]
        induction j using Fin.lastCases with
        | last =>
          rw [hlast]
          induction j' using Fin.lastCases with
          | last => exact absurd rfl hjj'
          | cast j' =>
            rw [hcast, if_neg (Fin.castSucc_ne_last j').symm, if_pos rfl]
            have := hfit j'; linarith
        | cast j =>
          rw [hcast, if_neg (Fin.castSucc_ne_last j).symm]
          induction j' using Fin.lastCases with
          | last =>
            rw [hlast, if_pos rfl]
            have := hfit j; linarith
          | cast j' =>
            rw [hcast, if_neg (Fin.castSucc_ne_last j').symm]
            have : j ≠ j' := fun h => hjj' (by rw [h])
            have := hσ2 j j' this; linarith

/-- Sum of pairwise-large bins: `k ≤ 2 S + 1`. -/
lemma card_le_of_pairwise {k : ℕ} (b : Fin k → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ j j', j ≠ j' → 1 < b j + b j') : (k : ℝ) ≤ 2 * ∑ j, b j + 1 := by
  classical
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    have : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
    linarith
  · -- choose a minimal bin
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ b hne
    have hhalf : ∀ j, j ≠ j₀ → 1 / 2 < b j := by
      intro j hj
      have h1 := h j j₀ hj
      have h2 := hj₀ j (Finset.mem_univ _)
      linarith
    have hsum : ∑ j, b j = b j₀ + ∑ j ∈ Finset.univ.erase j₀, b j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    have hcard : ((Finset.univ.erase j₀).card : ℝ) = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by omega)]; simp
    have hlow : ((Finset.univ.erase j₀).card : ℝ) * (1 / 2) ≤ ∑ j ∈ Finset.univ.erase j₀, b j := by
      have := Finset.card_nsmul_le_sum (Finset.univ.erase j₀) b (1 / 2)
        (fun j hj => le_of_lt (hhalf j (Finset.ne_of_mem_erase hj)))
      simpa [nsmul_eq_mul] using this
    have := hb j₀
    rw [hcard] at hlow
    linarith


lemma sum_bins {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) (σ : Fin N → Fin k) :
    ∑ j, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) = ∑ i ∈ I, (x i : ℝ) := by
  classical
  exact Finset.sum_fiberwise I σ (fun i => (x i : ℝ))

/-- Greedy packing of the items of `I`: `k ≤ 2 ∑_{i ∈ I} x_i + 1`. -/
lemma exists_packingOn_le {N : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) :
    ∃ k : ℕ, PackingOn I x k ∧ (k : ℝ) ≤ 2 * ∑ i ∈ I, (x i : ℝ) + 1 := by
  classical
  obtain ⟨k, σ, h1, h2⟩ := exists_packingOn_pairwise x I
  refine ⟨k, ⟨σ, h1⟩, ?_⟩
  have := card_le_of_pairwise (fun j => ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ))
    (fun j => Finset.sum_nonneg (fun i _ => (x i).2.1)) h2
  rwa [sum_bins] at this

lemma binNumber_le_of_isPacking {N : ℕ} (x : Fin N → unitInterval) {k : ℕ} (h : IsPacking x k) :
    binNumber x ≤ k := Nat.sInf_le h

theorem lemma_6_1_core {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by
  obtain ⟨k, hk, hle⟩ := exists_packingOn_le x Finset.univ
  have : binNumber x ≤ k := binNumber_le_of_isPacking x ((packingOn_univ_iff x k).mp hk)
  calc (binNumber x : ℝ) ≤ k := by exact_mod_cast this
    _ ≤ _ := hle


/-- Every `y` admits a packing (one item per bin). -/
lemma isPacking_self {N : ℕ} (y : Fin N → unitInterval) : IsPacking y N := by
  classical
  refine ⟨id, fun j => ?_⟩
  have : (Finset.univ.filter fun i : Fin N => id i = j) = {j} := by
    ext i; simp
  rw [this, Finset.sum_singleton]
  exact (y j).2.2

lemma isPacking_binNumber {N : ℕ} (y : Fin N → unitInterval) : IsPacking y (binNumber y) := by
  have : binNumber y ∈ {k : ℕ | IsPacking y k} := Nat.sInf_mem ⟨N, isPacking_self y⟩
  exact this

/-- Restricting a full packing of `y` to the items where `x = y`. -/
lemma packingOn_restrict {N : ℕ} (x y : Fin N → unitInterval) (I : Finset (Fin N))
    (hxy : ∀ i, i ∉ I → x i = y i) {k : ℕ} (h : IsPacking y k) : PackingOn Iᶜ x k := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun j => ?_⟩
  calc ∑ i ∈ Iᶜ.filter (fun i => σ i = j), (x i : ℝ)
      = ∑ i ∈ Iᶜ.filter (fun i => σ i = j), (y i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter, Finset.mem_compl] at hi
        rw [hxy i hi.1]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (y i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.subset_univ _)) (fun i _ _ => (y i).2.1)
    _ ≤ 1 := hσ j

/-- Union of packings. -/
lemma packingOn_union {N : ℕ} (x : Fin N → unitInterval) (I J : Finset (Fin N)) {k₁ k₂ : ℕ}
    (h₁ : PackingOn I x k₁) (h₂ : PackingOn J x k₂) : PackingOn (I ∪ J) x (k₁ + k₂) := by
  classical
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  refine ⟨fun i => if i ∈ I then Fin.castAdd k₂ (σ₁ i) else Fin.natAdd k₁ (σ₂ i), fun j => ?_⟩
  induction j using Fin.addCases with
  | left j =>
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (x i).2.1)) (hσ₁ j)
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    by_cases hiI : i ∈ I
    · refine ⟨hiI, ?_⟩
      simp only [hiI, if_true] at hi
      exact Fin.castAdd_inj.mp hi.2
    · exfalso
      simp only [hiI, if_false] at hi
      have h2 := hi.2
      rw [Fin.ext_iff] at h2
      simp at h2; omega
  | right j =>
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (x i).2.1)) (hσ₂ j)
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    by_cases hiI : i ∈ I
    · exfalso
      simp only [hiI, if_true] at hi
      have h2 := hi.2
      rw [Fin.ext_iff] at h2
      simp at h2; omega
    · simp only [hiI, if_false] at hi
      refine ⟨?_, (Fin.natAdd_inj _).mp hi.2⟩
      rcases Finset.mem_union.mp hi.1 with h | h
      · exact absurd h hiI
      · exact h

/-- `B_N(x) ≤ B_N(y) + 2 ∑_{i : x_i ≠ y_i} x_i + 1`. -/
lemma binNumber_le_of_ne {N : ℕ} (x y : Fin N → unitInterval) (I : Finset (Fin N))
    (hxy : ∀ i, i ∉ I → x i = y i) :
    (binNumber x : ℝ) ≤ binNumber y + (2 * ∑ i ∈ I, (x i : ℝ) + 1) := by
  classical
  obtain ⟨k, hk, hle⟩ := exists_packingOn_le x I
  have h1 := packingOn_restrict x y I hxy (isPacking_binNumber y)
  have h2 := packingOn_union x Iᶜ I h1 hk
  have hu : Iᶜ ∪ I = Finset.univ := by ext i; by_cases h : i ∈ I <;> simp [h]
  rw [hu] at h2
  have h3 : binNumber x ≤ binNumber y + k :=
    binNumber_le_of_isPacking x ((packingOn_univ_iff x _).mp h2)
  calc (binNumber x : ℝ) ≤ ((binNumber y + k : ℕ) : ℝ) := by exact_mod_cast h3
    _ = binNumber y + (k : ℝ) := by push_cast; ring
    _ ≤ _ := by linarith

/-- For `s ∈ U_{A(a)}(x)`: `B_N(x) ≤ a + 2 ∑ x_i s_i + 1`. -/
lemma binNumber_le_of_mem_U {N : ℕ} (a : ℝ) (x : Fin N → unitInterval) (s : Fin N → ℝ)
    (hs : s ∈ TalagrandConc.ConvexHull.U (levelSet N a) x) :
    (binNumber x : ℝ) ≤ a + 2 * ∑ i, (x i : ℝ) * s i + 1 := by
  classical
  obtain ⟨hs01, y, hy, hxy⟩ := hs
  have hyA : (binNumber y : ℝ) ≤ a := hy
  let I : Finset (Fin N) := Finset.univ.filter (fun i => x i ≠ y i)
  have hI : ∀ i, i ∉ I → x i = y i := by
    intro i hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  have h1 := binNumber_le_of_ne x y I hI
  have h2 : ∑ i ∈ I, (x i : ℝ) ≤ ∑ i, (x i : ℝ) * s i := by
    calc ∑ i ∈ I, (x i : ℝ) = ∑ i ∈ I, (x i : ℝ) * s i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hs01 i with h | h
          · exact absurd (hxy i h) hi
          · rw [h, mul_one]
      _ ≤ ∑ i, (x i : ℝ) * s i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          rcases hs01 i with h | h
          · rw [h]; simp
          · rw [h]; simpa using (x i).2.1
  linarith

/-- For `s ∈ V_{A(a)}(x)`: `B_N(x) ≤ a + 2 ∑ x_i s_i + 1`. -/
lemma binNumber_le_of_mem_V {N : ℕ} (a : ℝ) (x : Fin N → unitInterval) (s : Fin N → ℝ)
    (hs : s ∈ TalagrandConc.ConvexHull.V (levelSet N a) x) :
    (binNumber x : ℝ) ≤ a + 2 * ∑ i, (x i : ℝ) * s i + 1 := by
  let C : Set (Fin N → ℝ) := {s | (binNumber x : ℝ) - a - 1 ≤ ∑ i, 2 * (x i : ℝ) * s i}
  have hlin : IsLinearMap ℝ (fun s : Fin N → ℝ => ∑ i, 2 * (x i : ℝ) * s i) :=
    ⟨fun u v => by simp [mul_add, Finset.sum_add_distrib],
     fun c u => by simp [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring⟩
  have hC : Convex ℝ C := convex_halfSpace_ge hlin _
  have hUC : TalagrandConc.ConvexHull.U (levelSet N a) x ⊆ C := by
    intro s hs
    have := binNumber_le_of_mem_U a x s hs
    show (binNumber x : ℝ) - a - 1 ≤ ∑ i, 2 * (x i : ℝ) * s i
    have e : ∑ i, 2 * (x i : ℝ) * s i = 2 * ∑ i, (x i : ℝ) * s i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    linarith
  have := convexHull_min hUC hC hs
  have e : ∑ i, 2 * (x i : ℝ) * s i = 2 * ∑ i, (x i : ℝ) * s i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have h' : (binNumber x : ℝ) - a - 1 ≤ ∑ i, 2 * (x i : ℝ) * s i := this
  linarith

/-- Real form of Lemma 6.2. -/
lemma binNumber_le_real {N : ℕ} (a : ℝ) (x : Fin N → unitInterval) (s : Fin N → ℝ)
    (hs : s ∈ TalagrandConc.ConvexHull.V (levelSet N a) x) :
    (binNumber x : ℝ) ≤ a + 2 * l2Norm x * Real.sqrt (∑ i, s i ^ 2) + 1 := by
  have h1 := binNumber_le_of_mem_V a x s hs
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => (x i : ℝ)) s
  unfold l2Norm
  linarith

theorem lemma_6_2_core {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    (binNumber x : ℝ≥0∞) ≤
      ENNReal.ofReal a + 2 * ENNReal.ofReal (l2Norm x) * convexDist (levelSet N a) x + 1 := by
  have hnorm0 : 0 ≤ l2Norm x := Real.sqrt_nonneg _
  by_cases hB : (binNumber x : ℝ) ≤ a + 1
  · -- trivial case
    calc (binNumber x : ℝ≥0∞) = ENNReal.ofReal (binNumber x : ℝ) := by
          rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (a + 1) := ENNReal.ofReal_le_ofReal hB
      _ = ENNReal.ofReal a + 1 := by
          rw [ENNReal.ofReal_add ha.le zero_le_one, ENNReal.ofReal_one]
      _ ≤ _ := by
          rw [add_right_comm]
          exact le_add_right le_rfl
  · push_neg at hB
    have hnorm : 0 < l2Norm x := by
      by_contra h
      have h0 : l2Norm x = 0 := le_antisymm (not_lt.mp h) hnorm0
      have hsum : ∑ i, ((x i : ℝ)) ^ 2 = 0 := by
        unfold l2Norm at h0
        exact (Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ => sq_nonneg _))).mp h0
      have hzero : ∀ i, (x i : ℝ) = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((x i : ℝ)))).mp hsum i
          (Finset.mem_univ _)
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have := lemma_6_1_core x
      simp only [hzero, Finset.sum_const_zero, mul_zero, zero_add] at this
      linarith
    -- lower bound on the convex distance
    set L : ℝ := ((binNumber x : ℝ) - a - 1) / (2 * l2Norm x) with hL
    have hL0 : 0 ≤ L := by
      apply div_nonneg <;> linarith
    have hLle : ENNReal.ofReal L ≤ convexDist (levelSet N a) x := by
      unfold convexDist TalagrandConc.ConvexHull.fc
      apply le_iInf₂
      intro s hs
      apply ENNReal.ofReal_le_ofReal
      rw [hL, div_le_iff₀ (by linarith)]
      have := binNumber_le_real a x s hs
      linarith
    calc (binNumber x : ℝ≥0∞) = ENNReal.ofReal (binNumber x : ℝ) := by
          rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (a + 2 * l2Norm x * L + 1) := by
          congr 1
          rw [hL]; field_simp; ring
      _ = ENNReal.ofReal a + 2 * ENNReal.ofReal (l2Norm x) * ENNReal.ofReal L + 1 := by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
            ENNReal.ofReal_add ha.le (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ _ := by
          gcongr

end TalagrandConc.BinPacking

open TalagrandConc.BinPacking


theorem solution {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    (binNumber x : ℝ≥0∞) ≤
      ENNReal.ofReal a + 2 * ENNReal.ofReal (l2Norm x) * convexDist (levelSet N a) x + 1 := by
  exact lemma_6_2_core a ha x
