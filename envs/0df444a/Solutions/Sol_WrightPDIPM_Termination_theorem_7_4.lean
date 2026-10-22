-- Prove2me | solution 1 for WrightPDIPM.Termination.theorem_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:57:45.005589+00:00
-- url     : https://prove2.me/submissions/79fa02d0-3f7b-49d2-8d6b-24b98f246499

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

open WrightPDIPM.Termination

open Matrix
theorem g69a1_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (t : Finset ι) : ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → ∃ s ⊆ t, ∃ l' : ι → ℝ, (∀ i, 0 ≤ l' i) ∧
      LinearIndepOn ℝ v (s : Set ι) ∧ ∑ i ∈ s, l' i • v i = ∑ i ∈ t, l i • v i := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro l hl
  by_cases hli : LinearIndepOn ℝ v (t : Set ι)
  · exact ⟨t, subset_rfl, l, hl, hli, rfl⟩
  rw [not_linearIndepOn_finset_iffₛ] at hli
  obtain ⟨f, g, hfg, i0, hi0t, hi0⟩ := hli
  have hsum0 : ∑ i ∈ t, (f i - g i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  -- get ν supported on t with positive entry
  obtain ⟨ν, hνsum, hνsupp, i1, hi1t, hi1⟩ : ∃ ν : ι → ℝ, ∑ i ∈ t, ν i • v i = 0 ∧
      (∀ i, i ∉ t → ν i = 0) ∧ ∃ i ∈ t, 0 < ν i := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi0) with h | h
    · refine ⟨fun i => if i ∈ t then -(f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then -(f i - g i) else 0) • v i = -((f i - g i) • v i) := by
          intro i hi; rw [if_pos hi, neg_smul]
        beta_reduce
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib, hsum0, neg_zero]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
    · refine ⟨fun i => if i ∈ t then (f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then (f i - g i) else 0) • v i = (f i - g i) • v i := by
          intro i hi; rw [if_pos hi]
        beta_reduce
        rw [Finset.sum_congr rfl hc, hsum0]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
  set P := t.filter (fun i => 0 < ν i) with hP
  have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1t, hi1]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / ν i) hPne
  have hjt : j ∈ t := (Finset.mem_filter.mp hjP).1
  have hjpos : 0 < ν j := (Finset.mem_filter.mp hjP).2
  set θ := l j / ν j with hθ
  have hθnn : 0 ≤ θ := div_nonneg (hl j) hjpos.le
  set l' : ι → ℝ := fun i => l i - θ * ν i with hl'
  have hl'nn : ∀ i, 0 ≤ l' i := by
    intro i
    simp only [hl']
    by_cases hit : i ∈ t
    · by_cases hνi : 0 < ν i
      · have hiP : i ∈ P := by simp [hP, hit, hνi]
        have := hjmin i hiP
        rw [le_div_iff₀ hνi] at this
        linarith
      · push Not at hνi
        nlinarith [hl i]
    · rw [hνsupp i hit]; simp [hl i]
  have hl'j : l' j = 0 := by
    simp only [hl', hθ]; field_simp; ring
  have hsum' : ∑ i ∈ t.erase j, l' i • v i = ∑ i ∈ t, l i • v i := by
    rw [Finset.sum_erase _ (by rw [hl'j, zero_smul])]
    simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hνsum,
      smul_zero, sub_zero]
  obtain ⟨s, hs, l'', hl'', hli, hs'⟩ := ih (t.erase j) (Finset.erase_ssubset hjt) l' hl'nn
  exact ⟨s, hs.trans (Finset.erase_subset _ _), l'', hl'', hli, hs'.trans hsum'⟩

theorem g69a1_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g69a1_cara v Finset.univ l hl
      refine ⟨s, hli, fun i => l' i, fun i => hl' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hs]
      exact (Finset.sum_coe_sort s (fun i => l' i • v i))
    · rintro ⟨s, -, m, hm, rfl⟩
      refine ⟨fun i => if h : i ∈ s then m ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i; by_cases h : i ∈ s <;> simp [h, hm]
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · rw [← Finset.sum_coe_sort s]
          apply Finset.sum_congr rfl
          intro i _
          simp
        · intro i _ hi; simp [hi]
  rw [heq]
  apply Set.Finite.isClosed_biUnion (Set.toFinite _)
  intro s hs
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hs
  apply (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem g69a1_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g69a1_cone_closed v) ha
  have hu : u < 0 := by
    have := hfC 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hfnn : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨l, hl, rfl⟩ := hy
    set t : ℝ := u / f (∑ i, l i • v i) with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hu hneg
    have hmem : t • (∑ i, l i • v i) ∈ C :=
      ⟨fun i => t * l i, fun i => mul_nonneg htpos.le (hl i), by
        simp only [Finset.smul_sum, mul_smul]⟩
    have := hfC _ hmem
    rw [map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  let x : κ → ℝ := fun j => f (Pi.single j 1)
  have hfx : ∀ y : κ → ℝ, f y = y ⬝ᵥ x := by
    intro y
    conv_lhs => rw [show y = ∑ j, y j • Pi.single j (1:ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, dotProduct, x]
  refine ⟨x, ?_, ?_⟩
  · rw [← hfx]; linarith
  · intro i
    rw [← hfx]
    apply hfnn
    refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · simp [Pi.single_apply]


theorem g69a1_lp_dualG {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ)
    (hfeas : ∃ x0, b ≤ A *ᵥ x0) (a : ℝ) (hlb : ∀ x, b ≤ A *ᵥ x → a ≤ c ⬝ᵥ x) :
    ∃ y : ι → ℝ, 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ a ≤ b ⬝ᵥ y := by
  classical
  obtain ⟨x0, hx0⟩ := hfeas
  let w : Option ι → (κ ⊕ Unit → ℝ) := fun o =>
    match o with
    | none => Sum.elim 0 (fun _ => 1)
    | some i => Sum.elim (fun j => A i j) (fun _ => -b i)
  let q : κ ⊕ Unit → ℝ := Sum.elim c (fun _ => -a)
  have hno : ¬ ∃ z : κ ⊕ Unit → ℝ, q ⬝ᵥ z < 0 ∧ ∀ o, 0 ≤ w o ⬝ᵥ z := by
    rintro ⟨z, hz, hw⟩
    set x : κ → ℝ := fun j => z (Sum.inl j) with hxdef
    set t : ℝ := z (Sum.inr ()) with htdef
    have hqz : q ⬝ᵥ z = c ⬝ᵥ x - a * t := by
      simp [q, dotProduct, Fintype.sum_sum_type, x, t]; ring
    have ht0 : 0 ≤ t := by
      have := hw none
      simpa [w, dotProduct, Fintype.sum_sum_type, t] using this
    have hAx : ∀ i, b i * t ≤ (A *ᵥ x) i := by
      intro i
      have := hw (some i)
      simp [w, dotProduct, Fintype.sum_sum_type, t] at this
      simp only [mulVec, dotProduct, x]
      linarith
    rcases ht0.lt_or_eq with htpos | htz
    · have hfe : b ≤ A *ᵥ (t⁻¹ • x) := by
        intro i
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ htpos]
        linarith [hAx i]
      have := hlb _ hfe
      rw [dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ htpos] at this
      linarith
    · have hcx : c ⬝ᵥ x < 0 := by rw [← htz] at hqz; linarith
      have hAx0 : ∀ i, 0 ≤ (A *ᵥ x) i := by
        intro i; have := hAx i; rw [← htz] at this; simpa using this
      have hca := hlb x0 hx0
      set s : ℝ := (c ⬝ᵥ x0 - a + 1) / (-(c ⬝ᵥ x)) with hs
      have hspos : 0 ≤ s := div_nonneg (by linarith) (by linarith)
      have hfe : b ≤ A *ᵥ (x0 + s • x) := by
        intro i
        rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx0 i
        nlinarith [hAx0 i]
      have := hlb _ hfe
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hs, div_mul_eq_mul_div,
        div_neg, mul_div_assoc, div_self hcx.ne, mul_one] at this
      linarith
  have hmem : ∃ l : Option ι → ℝ, (∀ o, 0 ≤ l o) ∧ q = ∑ o, l o • w o := by
    by_contra hne
    exact hno (g69a1_farkas w q hne)
  obtain ⟨l, hl, hq⟩ := hmem
  refine ⟨fun i => l (some i), fun i => hl (some i), ?_, ?_⟩
  · funext j
    have := congrFun hq (Sum.inl j)
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    rw [this]
    simp [mulVec, dotProduct, mul_comm]
  · have := congrFun hq (Sum.inr ())
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    have h1 := hl none
    simp only [dotProduct]
    have h2 : ∑ x, l (some x) * b x = ∑ x, b x * l (some x) := by
      apply Finset.sum_congr rfl; intro i _; ring
    linarith

theorem g70wr_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c d : Fin n → ℝ)
    (δ a : ℝ)
    (hfeas : ∃ x0 : Fin n → ℝ, A *ᵥ x0 = b ∧ (∀ j, 0 ≤ x0 j) ∧ d ⬝ᵥ x0 ≤ δ)
    (hlb : ∀ x : Fin n → ℝ, A *ᵥ x = b → (∀ j, 0 ≤ x j) → d ⬝ᵥ x ≤ δ → a ≤ c ⬝ᵥ x) :
    ∃ (y : Fin m → ℝ) (w : Fin n → ℝ) (t : ℝ), (∀ j, 0 ≤ w j) ∧ 0 ≤ t ∧
      Aᵀ *ᵥ y + w - t • d = c ∧ a ≤ b ⬝ᵥ y - t * δ := by
  classical
  let A' : Matrix (Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit) (Fin n) ℝ :=
    Matrix.of (Sum.elim (fun i j => A i j) (Sum.elim (fun i j => -A i j)
      (Sum.elim (fun i j => if i = j then 1 else 0) (fun _ j => -d j))))
  let b' : Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit → ℝ :=
    Sum.elim b (Sum.elim (-b) (Sum.elim 0 (fun _ => -δ)))
  have key : ∀ x : Fin n → ℝ, b' ≤ A' *ᵥ x ↔ (A *ᵥ x = b ∧ (∀ j, 0 ≤ x j) ∧ d ⬝ᵥ x ≤ δ) := by
    intro x
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · funext i
        have h1 := h (Sum.inl i)
        have h2 := h (Sum.inr (Sum.inl i))
        simp [A', b', mulVec, dotProduct] at h1 h2
        simp only [mulVec, dotProduct]
        linarith
      · intro j
        have h1 := h (Sum.inr (Sum.inr (Sum.inl j)))
        simpa [A', b', mulVec, dotProduct] using h1
      · have h1 := h (Sum.inr (Sum.inr (Sum.inr ())))
        simp [A', b', mulVec, dotProduct] at h1
        simp only [dotProduct]
        linarith
    · rintro ⟨h1, h2, h3⟩ r
      rcases r with i | i | j | u
      · have := congrFun h1 i
        simp [A', b', mulVec, dotProduct] at this ⊢
        linarith
      · have := congrFun h1 i
        simp [A', b', mulVec, dotProduct] at this ⊢
        linarith
      · simpa [A', b', mulVec, dotProduct] using h2 j
      · simp [A', b', mulVec, dotProduct] at h3 ⊢
        linarith
  obtain ⟨x0, hx0⟩ := hfeas
  obtain ⟨Y, hY0, hYA, hYb⟩ := g69a1_lp_dualG A' b' c ⟨x0, (key x0).2 hx0⟩ a
    (fun x hx => by obtain ⟨h1, h2, h3⟩ := (key x).1 hx; exact hlb x h1 h2 h3)
  refine ⟨fun i => Y (Sum.inl i) - Y (Sum.inr (Sum.inl i)),
    fun j => Y (Sum.inr (Sum.inr (Sum.inl j))), Y (Sum.inr (Sum.inr (Sum.inr ()))),
    fun j => hY0 _, hY0 _, ?_, ?_⟩
  · funext j
    have := congrFun hYA j
    simp [A', mulVec, dotProduct, Fintype.sum_sum_type] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      transpose_apply]
    rw [← this]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [b', dotProduct, Fintype.sum_sum_type] at hYb
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    linarith


theorem g70wr_wd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hd : Aᵀ *ᵥ lam + s = c) : c ⬝ᵥ x = b ⬝ᵥ lam + s ⬝ᵥ x := by
  rw [← hd, ← hx, add_dotProduct, mulVec_transpose, dotProduct_comm (A *ᵥ x) lam, dotProduct_mulVec]

theorem g70wr_nn {n : ℕ} (s x : Fin n → ℝ) (hs : ∀ j, 0 ≤ s j) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ s ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (hx j)

/-- dual optimal → primal feasible with equal value -/
theorem g70wr_fromD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ OmegaD A b c) :
    ∃ x, PrimalFeasible A b x ∧ c ⬝ᵥ x = b ⬝ᵥ p.1 := by
  obtain ⟨⟨hd, hs⟩, hopt⟩ := hp
  obtain ⟨x, hx0, hxA, hxb⟩ := g69a1_lp_dualG (-Aᵀ) (-c) (-b) ⟨p.1, by
      intro j; have := congrFun hd j; simp [neg_mulVec] at this ⊢; linarith [hs j]⟩ (-(b ⬝ᵥ p.1))
    (fun lam hl => by
      have := hopt lam (c - Aᵀ *ᵥ lam) ⟨by abel, fun j => by
        have := hl j; simp [neg_mulVec] at this ⊢; linarith⟩
      simp; linarith)
  have hAx : A *ᵥ x = b := by
    have : -(A *ᵥ x) = -b := by simpa [transpose_neg, neg_mulVec] using hxA
    exact neg_inj.mp this
  refine ⟨x, ⟨hAx, fun j => hx0 j⟩, ?_⟩
  have hw := g70wr_wd A b c x p.1 p.2 hAx hd
  have := g70wr_nn p.2 x hs (fun j => hx0 j)
  simp at hxb
  linarith

/-- primal optimal → dual feasible with equal value -/
theorem g70wr_fromP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ OmegaP A b c) :
    ∃ lam s, DualFeasible A c lam s ∧ c ⬝ᵥ x = b ⬝ᵥ lam := by
  obtain ⟨⟨hA, hx0⟩, hopt⟩ := hx
  obtain ⟨y, w, t, hw, ht, hy, hyb⟩ := g70wr_dual A b c 0 0 (c ⬝ᵥ x) ⟨x, hA, hx0, by simp⟩
    (fun x' h1 h2 _ => hopt x' ⟨h1, h2⟩)
  refine ⟨y, w, ⟨by simpa using hy, hw⟩, ?_⟩
  have hd : Aᵀ *ᵥ y + w = c := by simpa using hy
  have := g70wr_wd A b c x y w hA hd
  have := g70wr_nn w x hw hx0
  simp at hyb
  linarith

theorem g70wr_feas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (l0 : Fin m → ℝ) (s0 : Fin n → ℝ) (hx0A : A *ᵥ x0 = b)
    (hx00 : ∀ j, 0 ≤ x0 j) (hd0 : Aᵀ *ᵥ l0 + s0 = c) (hs0 : ∀ j, 0 ≤ s0 j) :
    (Omega A b c).Nonempty := by
  set S : Set ℝ := {v | ∃ x, PrimalFeasible A b x ∧ v = c ⬝ᵥ x} with hS
  have hbdd : BddBelow S := ⟨b ⬝ᵥ l0, by
    rintro v ⟨x, ⟨h1, h2⟩, rfl⟩
    have := g70wr_wd A b c x l0 s0 h1 hd0
    have := g70wr_nn s0 x hs0 h2
    linarith⟩
  have hne : S.Nonempty := ⟨_, x0, ⟨hx0A, hx00⟩, rfl⟩
  obtain ⟨y, w, t, hw, ht, hy, hyb⟩ := g70wr_dual A b c 0 0 (sInf S) ⟨x0, hx0A, hx00, by simp⟩
    (fun x' h1 h2 _ => csInf_le hbdd ⟨x', ⟨h1, h2⟩, rfl⟩)
  have hd : Aᵀ *ᵥ y + w = c := by simpa using hy
  simp at hyb
  have hyopt : (y, w) ∈ OmegaD A b c := by
    refine ⟨⟨hd, hw⟩, fun lam' s' ⟨h1, h2⟩ => ?_⟩
    have : b ⬝ᵥ lam' ≤ sInf S := le_csInf hne (by
      rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have := g70wr_wd A b c x lam' s' hx1 h1
      have := g70wr_nn s' x h2 hx2
      linarith)
    simp; linarith
  obtain ⟨x, ⟨hxA, hx0⟩, hxv⟩ := g70wr_fromD A b c _ hyopt
  refine ⟨(x, y, w), ⟨⟨hxA, hx0⟩, fun x' ⟨h1, h2⟩ => ?_⟩, hyopt⟩
  have := g70wr_wd A b c x' y w h1 hd
  have := g70wr_nn w x' hw h2
  simp at hxv
  linarith

theorem g70wr_PD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ OmegaP A b c) (p : (Fin m → ℝ) × (Fin n → ℝ))
    (hp : p ∈ OmegaD A b c) : c ⬝ᵥ x = b ⬝ᵥ p.1 := by
  obtain ⟨lam, s, ⟨hd, hs⟩, hv⟩ := g70wr_fromP A b c x hx
  have h1 := hp.2 lam s ⟨hd, hs⟩
  have h2 := g70wr_wd A b c x p.1 p.2 hx.1.1 hp.1.1
  have h3 := g70wr_nn p.2 x hp.1.2 hx.1.2
  linarith

/-- Goldman–Tucker, one index. -/
theorem g70wr_gtj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xs : Fin n → ℝ) (hxs : xs ∈ OmegaP A b c) (ps : (Fin m → ℝ) × (Fin n → ℝ))
    (hps : ps ∈ OmegaD A b c) (j : Fin n) :
    ∃ x ∈ OmegaP A b c, ∃ p ∈ OmegaD A b c, 0 < x j + p.2 j := by
  classical
  by_cases h : ∃ x ∈ OmegaP A b c, 0 < x j
  · obtain ⟨x, hx, hxj⟩ := h
    exact ⟨x, hx, ps, hps, by linarith [hps.1.2 j]⟩
  push Not at h
  set e : Fin n → ℝ := fun i => if i = j then -1 else 0 with he
  obtain ⟨y, w, t, hw, ht, hy, hyb⟩ := g70wr_dual A b e c (c ⬝ᵥ xs) 0
    ⟨xs, hxs.1.1, hxs.1.2, le_rfl⟩ (fun x h1 h2 h3 => by
      have hxo : x ∈ OmegaP A b c := ⟨⟨h1, h2⟩, fun x' hx' => le_trans h3 (hxs.2 x' hx')⟩
      have := h x hxo
      simp [he, dotProduct]
      linarith)
  have hval : c ⬝ᵥ xs = b ⬝ᵥ ps.1 := g70wr_PD A b c xs hxs ps hps
  have hcomp : ∀ i, (Aᵀ *ᵥ y) i + w i - t * c i = e i := fun i => by
    have := congrFun hy i; simpa using this
  rcases ht.lt_or_eq with htp | ht0
  · -- λ = y / t
    refine ⟨xs, hxs, (t⁻¹ • y, c - Aᵀ *ᵥ (t⁻¹ • y)), ⟨⟨add_sub_cancel _ _, fun i => ?_⟩, ?_⟩, ?_⟩
    · have := hcomp i
      have hei : e i ≤ 0 := by simp only [he]; split_ifs <;> norm_num
      simp only [Pi.sub_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : c i - t⁻¹ * (Aᵀ *ᵥ y) i = t⁻¹ * (w i - e i) := by
        field_simp; linarith
      rw [this]; exact mul_nonneg (inv_nonneg.mpr ht) (by linarith [hw i])
    · intro lam' s' hd'
      have h1 := g70wr_wd A b c xs lam' s' hxs.1.1 hd'.1
      have h2 := g70wr_nn s' xs hd'.2 hxs.1.2
      simp only [dotProduct_smul, smul_eq_mul]
      rw [le_inv_mul_iff₀ htp]
      have := mul_le_mul_of_nonneg_left (show b ⬝ᵥ lam' ≤ c ⬝ᵥ xs by linarith) ht
      linarith
    · have := hcomp j
      have hej : e j = -1 := by simp [he]
      simp only [Pi.sub_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : c j - t⁻¹ * (Aᵀ *ᵥ y) j = t⁻¹ * (w j + 1) := by
        field_simp; linarith
      rw [this]
      have := mul_pos (inv_pos.mpr htp) (show 0 < w j + 1 by linarith [hw j])
      linarith [hxs.1.2 j]
  · subst ht0
    refine ⟨xs, hxs, (ps.1 + y, ps.2 + w - e), ⟨⟨?_, fun i => ?_⟩, ?_⟩, ?_⟩
    · funext i
      have := hcomp i
      have := congrFun hps.1.1 i
      simp only [Pi.add_apply, Pi.sub_apply, mulVec_add] at *
      linarith
    · have hei : e i ≤ 0 := by simp only [he]; split_ifs <;> norm_num
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith [hps.1.2 i, hw i]
    · intro lam' s' hd'
      have := hps.2 lam' s' hd'
      simp only [dotProduct_add]
      simp at hyb
      linarith
    · have hej : e j = -1 := by simp [he]
      simp only [Pi.add_apply, Pi.sub_apply, hej]
      linarith [hps.1.2 j, hw j, hxs.1.2 j]

theorem g70wr_gt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hΩ : (Omega A b c).Nonempty) :
    indexB A b c ∪ indexN A b c = Set.univ ∧
    ∃ x ∈ OmegaP A b c, ∃ p ∈ OmegaD A b c, ∀ j, 0 < x j + p.2 j := by
  classical
  obtain ⟨⟨xs, ls, ss⟩, hxs, hps⟩ := hΩ
  have main : ∃ x ∈ OmegaP A b c, ∃ p ∈ OmegaD A b c, ∀ j, 0 < x j + p.2 j := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact ⟨xs, hxs, _, hps, fun j => j.elim0⟩
    choose P hP Q hQ hPQ using g70wr_gtj A b c xs hxs (ls, ss) hps
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    set k : ℝ := (n : ℝ)⁻¹ with hk
    have hkp : 0 < k := inv_pos.mpr hnr
    have hksum : ∀ v : ℝ, ∑ _i : Fin n, k * v = v := fun v => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hk]
      field_simp
    refine ⟨k • ∑ i, P i, ⟨⟨?_, fun j => ?_⟩, fun x' hx' => ?_⟩,
      (k • ∑ i, (Q i).1, k • ∑ i, (Q i).2), ⟨⟨?_, fun j => ?_⟩, fun l' s' hd' => ?_⟩, fun j => ?_⟩
    · rw [mulVec_smul, mulVec_sum]
      funext r
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hP _).1.1, Finset.mul_sum]
      exact hksum (b r)
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hP i).1.2 j)
    · rw [dotProduct_smul, dotProduct_sum, smul_eq_mul]
      calc k * ∑ i, c ⬝ᵥ P i ≤ k * ∑ _i : Fin n, c ⬝ᵥ x' :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hP i).2 x' hx') hkp.le
        _ = c ⬝ᵥ x' := by rw [Finset.mul_sum]; exact hksum _
    · rw [mulVec_smul, mulVec_sum, ← smul_add, ← Finset.sum_add_distrib]
      funext r
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hQ _).1.1, Finset.mul_sum]
      exact hksum (c r)
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hQ i).1.2 j)
    · rw [dotProduct_smul, dotProduct_sum, smul_eq_mul]
      calc b ⬝ᵥ l' = k * ∑ _i : Fin n, b ⬝ᵥ l' := by rw [Finset.mul_sum]; exact (hksum _).symm
        _ ≤ k * ∑ i, b ⬝ᵥ (Q i).1 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hQ i).2 l' s' hd') hkp.le
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_pos hkp (lt_of_lt_of_le (hPQ j) ?_)
      exact Finset.single_le_sum (f := fun i => P i j + (Q i).2 j)
        (fun i _ => add_nonneg ((hP i).1.2 j) ((hQ i).1.2 j)) (Finset.mem_univ j)
  refine ⟨?_, main⟩
  obtain ⟨x, hx, p, hp, hj⟩ := main
  ext j
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hxj : x j = 0
  · right; exact ⟨p, hp, by have := hj j; rw [hxj] at this; simp at this; exact this.ne'⟩
  · left; exact ⟨x, hx, hxj⟩

theorem g70wr_PtoD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ OmegaP A b c) : (OmegaD A b c).Nonempty := by
  obtain ⟨lam, s, hd, hv⟩ := g70wr_fromP A b c x hx
  refine ⟨(lam, s), hd, fun l' s' hd' => ?_⟩
  have h1 := g70wr_wd A b c x l' s' hx.1.1 hd'.1
  have h2 := g70wr_nn s' x hd'.2 hx.1.2
  simp only; linarith

theorem g70wr_DtoP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ OmegaD A b c) : (OmegaP A b c).Nonempty := by
  obtain ⟨x, hx, hv⟩ := g70wr_fromD A b c p hp
  refine ⟨x, hx, fun x' hx' => ?_⟩
  have h1 := g70wr_wd A b c x' p.1 p.2 hx'.1 hp.1.1
  have h2 := g70wr_nn p.2 x' hp.1.2 hx'.2
  linarith

theorem g70wr_orth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x x' : Fin n → ℝ) (l l' : Fin m → ℝ) (s s' : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hx' : A *ᵥ x' = b) (hd : Aᵀ *ᵥ l + s = c) (hd' : Aᵀ *ᵥ l' + s' = c) :
    x ⬝ᵥ s' + x' ⬝ᵥ s = x ⬝ᵥ s + x' ⬝ᵥ s' := by
  have h1 := g70wr_wd A b c x l s hx hd
  have h2 := g70wr_wd A b c x l' s' hx hd'
  have h3 := g70wr_wd A b c x' l s hx' hd
  have h4 := g70wr_wd A b c x' l' s' hx' hd'
  rw [dotProduct_comm x s', dotProduct_comm x' s, dotProduct_comm x s, dotProduct_comm x' s']
  linarith

theorem g70wr_single {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, 0 ≤ s i)
    (i : Fin n) : x i * s i ≤ x ⬝ᵥ s :=
  Finset.single_le_sum (f := fun j => x j * s j) (fun j _ => mul_nonneg (hx j) (hs j))
    (Finset.mem_univ i)

set_option maxHeartbeats 1000000 in
theorem g70wr_513 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ₀ γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (xo : Fin n → ℝ) (lo : Fin m → ℝ) (so : Fin n → ℝ) (hFo : (xo, lo, so) ∈ Fo A b c) :
    ∃ C₀ : ℝ, ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ → mu x s ≤ μ₀ →
        norm2Pair x s ≤ C₀ ∧
        (∀ i ∈ indexN A b c, 0 < x i ∧ x i ≤ mu x s / C3 A b c) ∧
        (∀ i ∈ indexB A b c, 0 < s i ∧ s i ≤ mu x s / C3 A b c) ∧
        (∀ i ∈ indexN A b c, C3 A b c * γ ≤ s i) ∧
        (∀ i ∈ indexB A b c, C3 A b c * γ ≤ x i) := by
  classical
  obtain ⟨hA, hd, hxo, hso⟩ := hFo
  simp only at hA hd hxo hso
  obtain ⟨⟨xs, ls, ss⟩, hxs, hps⟩ := g70wr_feas A b c xo lo so hA (fun j => (hxo j).le) hd
    (fun j => (hso j).le)
  simp only at hxs hps
  obtain ⟨hBN, -⟩ := g70wr_gt A b c ⟨(xs, ls, ss), hxs, hps⟩
  have hcomp : ∀ x ∈ OmegaP A b c, ∀ p ∈ OmegaD A b c, x ⬝ᵥ p.2 = 0 := fun x hx p hp => by
    have h1 := g70wr_PD A b c x hx p hp
    have h2 := g70wr_wd A b c x p.1 p.2 hx.1.1 hp.1.1
    rw [dotProduct_comm]; linarith
  have hdisj : ∀ i, i ∈ indexB A b c → i ∉ indexN A b c := by
    rintro i ⟨x, hx, hxi⟩ ⟨p, hp, hpi⟩
    have h := hcomp x hx p hp
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hx.1.2 j) (hp.1.2 j))).1 h i
      (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact hxi h
    · exact hpi h
  have hPb : ∀ x ∈ OmegaP A b c, ∀ i, x i ≤ (c ⬝ᵥ xs - b ⬝ᵥ lo) / so i := fun x hx i => by
    rw [le_div_iff₀ (hso i)]
    have h1 := g70wr_wd A b c x lo so hx.1.1 hd
    have h2 := hx.2 xs hxs.1
    have h3 := hxs.2 x hx.1
    have h4 := g70wr_single so x (fun j => (hso j).le) hx.1.2 i
    rw [mul_comm] at h4; linarith
  have hDb : ∀ p ∈ OmegaD A b c, ∀ i, p.2 i ≤ (c ⬝ᵥ xo - b ⬝ᵥ ls) / xo i := fun p hp i => by
    rw [le_div_iff₀ (hxo i)]
    have h1 := g70wr_wd A b c xo p.1 p.2 hA hp.1.1
    have h2 := hp.2 ls ss hps.1
    have h3 := hps.2 p.1 p.2 hp.1
    have h4 := g70wr_single p.2 xo hp.1.2 (fun j => (hxo j).le) i
    rw [mul_comm] at h4; simp only at h2 h3; linarith
  have hBeq : ∀ i ∈ indexB A b c,
      epsTerm A b c i = sSup ((fun x : Fin n → ℝ => x i) '' OmegaP A b c) := fun i hi => by
    unfold epsTerm; rw [if_pos hi]
  have hNeq : ∀ i ∈ indexN A b c,
      epsTerm A b c i = sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 i) '' OmegaD A b c) :=
    fun i hi => by unfold epsTerm; rw [if_neg (fun h => hdisj i h hi), if_pos hi]
  have hpos : ∀ i, 0 < epsTerm A b c i := fun i => by
    have hi : i ∈ indexB A b c ∪ indexN A b c := by rw [hBN]; trivial
    rcases hi with hi | hi
    · rw [hBeq i hi]
      obtain ⟨x, hx, hxi⟩ := hi
      have : 0 < x i := lt_of_le_of_ne (hx.1.2 i) (Ne.symm hxi)
      refine lt_of_lt_of_le this (le_csSup ⟨(c ⬝ᵥ xs - b ⬝ᵥ lo) / so i, ?_⟩ ⟨x, hx, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩; exact hPb y hy i
    · rw [hNeq i hi]
      obtain ⟨p, hp, hpi⟩ := hi
      have : 0 < p.2 i := lt_of_le_of_ne (hp.1.2 i) (Ne.symm hpi)
      refine lt_of_lt_of_le this (le_csSup ⟨(c ⬝ᵥ xo - b ⬝ᵥ ls) / xo i, ?_⟩ ⟨p, hp, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩; exact hDb y hy i
  have hεle : ∀ i, epsABC A b c ≤ epsTerm A b c i := fun i =>
    ciInf_le (Finite.bddBelow_range _) i
  have hεpos : ∀ i : Fin n, 0 < epsABC A b c := fun i => by
    haveI : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := epsTerm A b c)
    rw [epsABC, ← hj]; exact hpos j
  have hnpos : ∀ i : Fin n, (0 : ℝ) < n := fun i => by
    have := i.pos; exact_mod_cast this
  have hC3 : ∀ i : Fin n, C3 A b c = epsABC A b c / n := fun _ => rfl
  have hmuC : ∀ (x s : Fin n → ℝ) (i : Fin n), mu x s / C3 A b c = x ⬝ᵥ s / epsABC A b c :=
    fun x s i => by
      rw [mu, C3]; have := hnpos i; have := hεpos i; field_simp
  set K := (n : ℝ) * μ₀ + xo ⬝ᵥ so with hK
  refine ⟨Real.sqrt (∑ i, (K / so i) ^ 2 + ∑ i, (K / xo i) ^ 2), ?_⟩
  rintro x lam s ⟨⟨hAx, hdx, hx, hs⟩, hγμ⟩ hμ
  simp only at hAx hdx hx hs hγμ
  have hxs0 : 0 ≤ x ⬝ᵥ s := g70wr_nn x s (fun j => (hx j).le) (fun j => (hs j).le)
  -- N-bound
  have hNb : ∀ i ∈ indexN A b c, x i ≤ mu x s / C3 A b c := fun i hi => by
    rw [hmuC x s i, le_div_iff₀ (hεpos i)]
    have h1 : epsTerm A b c i ≤ x ⬝ᵥ s / x i := by
      rw [hNeq i hi]
      refine csSup_le ⟨_, (ls, ss), hps, rfl⟩ ?_
      rintro _ ⟨p, hp, rfl⟩
      rw [le_div_iff₀ (hx i)]
      have o := g70wr_orth A b c x xs lam p.1 s p.2 hAx hxs.1.1 hdx hp.1.1
      have h0 := hcomp xs hxs p hp
      have hn1 := g70wr_nn xs s hxs.1.2 (fun j => (hs j).le)
      have hn2 := g70wr_single x p.2 (fun j => (hx j).le) hp.1.2 i
      rw [mul_comm]; linarith
    have h2 := (hεle i).trans h1
    rw [le_div_iff₀ (hx i)] at h2
    linarith
  have hBb : ∀ i ∈ indexB A b c, s i ≤ mu x s / C3 A b c := fun i hi => by
    rw [hmuC x s i, le_div_iff₀ (hεpos i)]
    have h1 : epsTerm A b c i ≤ x ⬝ᵥ s / s i := by
      rw [hBeq i hi]
      refine csSup_le ⟨_, xs, hxs, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [le_div_iff₀ (hs i)]
      have o := g70wr_orth A b c y x ls lam ss s hy.1.1 hAx hps.1.1 hdx
      have h0 := hcomp y hy (ls, ss) hps
      have hn1 := g70wr_nn x ss (fun j => (hx j).le) hps.1.2
      rw [dotProduct_comm x ss] at hn1
      have hn2 := g70wr_single y s hy.1.2 (fun j => (hs j).le) i
      simp only at h0
      rw [dotProduct_comm x ss] at o
      linarith
    have h2 := (hεle i).trans h1
    rw [le_div_iff₀ (hs i)] at h2
    linarith
  have hγ0 : 0 < γ := hγ.1
  refine ⟨?_, fun i hi => ⟨hx i, hNb i hi⟩, fun i hi => ⟨hs i, hBb i hi⟩, fun i hi => ?_,
    fun i hi => ?_⟩
  · -- norm bound
    have hxsK : x ⬝ᵥ s ≤ n * μ₀ := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [dotProduct]
      · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
        have : x ⬝ᵥ s = n * mu x s := by rw [mu]; field_simp
        rw [this]; exact mul_le_mul_of_nonneg_left hμ hnr.le
    have o := g70wr_orth A b c x xo lam lo s so hAx hA hdx hd
    have n1 := g70wr_nn x so (fun j => (hx j).le) (fun j => (hso j).le)
    have n2 := g70wr_nn xo s (fun j => (hxo j).le) (fun j => (hs j).le)
    have n3 := g70wr_nn xo so (fun j => (hxo j).le) (fun j => (hso j).le)
    apply Real.sqrt_le_sqrt
    apply add_le_add
    · refine Finset.sum_le_sum fun i _ => ?_
      have h := g70wr_single x so (fun j => (hx j).le) (fun j => (hso j).le) i
      have : x i ≤ K / so i := by rw [le_div_iff₀ (hso i)]; linarith
      exact pow_le_pow_left₀ (hx i).le this 2
    · refine Finset.sum_le_sum fun i _ => ?_
      have h := g70wr_single xo s (fun j => (hxo j).le) (fun j => (hs j).le) i
      have : s i ≤ K / xo i := by rw [le_div_iff₀ (hxo i)]; linarith
      exact pow_le_pow_left₀ (hs i).le this 2
  · have hC : 0 < C3 A b c := div_pos (hεpos i) (hnpos i)
    have h1 := hNb i hi
    rw [le_div_iff₀ hC] at h1
    have h2 := hγμ i
    have : C3 A b c * γ * x i ≤ x i * s i := by nlinarith
    nlinarith [hx i]
  · have hC : 0 < C3 A b c := div_pos (hεpos i) (hnpos i)
    have h1 := hBb i hi
    rw [le_div_iff₀ hC] at h1
    have h2 := hγμ i
    have : C3 A b c * γ * s i ≤ x i * s i := by nlinarith
    nlinarith [hs i]

set_option maxHeartbeats 1000000 in
theorem g70wr_C3pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xo : Fin n → ℝ) (lo : Fin m → ℝ) (so : Fin n → ℝ) (hFo : (xo, lo, so) ∈ Fo A b c)
    (i0 : Fin n) : 0 < C3 A b c := by
  classical
  obtain ⟨hA, hd, hxo, hso⟩ := hFo
  simp only at hA hd hxo hso
  obtain ⟨⟨xs, ls, ss⟩, hxs, hps⟩ := g70wr_feas A b c xo lo so hA (fun j => (hxo j).le) hd
    (fun j => (hso j).le)
  simp only at hxs hps
  obtain ⟨hBN, -⟩ := g70wr_gt A b c ⟨(xs, ls, ss), hxs, hps⟩
  have hcomp : ∀ x ∈ OmegaP A b c, ∀ p ∈ OmegaD A b c, x ⬝ᵥ p.2 = 0 := fun x hx p hp => by
    have h1 := g70wr_PD A b c x hx p hp
    have h2 := g70wr_wd A b c x p.1 p.2 hx.1.1 hp.1.1
    rw [dotProduct_comm]; linarith
  have hdisj : ∀ i, i ∈ indexB A b c → i ∉ indexN A b c := by
    rintro i ⟨x, hx, hxi⟩ ⟨p, hp, hpi⟩
    have h := hcomp x hx p hp
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hx.1.2 j) (hp.1.2 j))).1 h i
      (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact hxi h
    · exact hpi h
  have hPb : ∀ x ∈ OmegaP A b c, ∀ i, x i ≤ (c ⬝ᵥ xs - b ⬝ᵥ lo) / so i := fun x hx i => by
    rw [le_div_iff₀ (hso i)]
    have h1 := g70wr_wd A b c x lo so hx.1.1 hd
    have h2 := hx.2 xs hxs.1
    have h3 := hxs.2 x hx.1
    have h4 := g70wr_single so x (fun j => (hso j).le) hx.1.2 i
    rw [mul_comm] at h4; linarith
  have hDb : ∀ p ∈ OmegaD A b c, ∀ i, p.2 i ≤ (c ⬝ᵥ xo - b ⬝ᵥ ls) / xo i := fun p hp i => by
    rw [le_div_iff₀ (hxo i)]
    have h1 := g70wr_wd A b c xo p.1 p.2 hA hp.1.1
    have h2 := hp.2 ls ss hps.1
    have h3 := hps.2 p.1 p.2 hp.1
    have h4 := g70wr_single p.2 xo hp.1.2 (fun j => (hxo j).le) i
    rw [mul_comm] at h4; simp only at h2 h3; linarith
  have hBeq : ∀ i ∈ indexB A b c,
      epsTerm A b c i = sSup ((fun x : Fin n → ℝ => x i) '' OmegaP A b c) := fun i hi => by
    unfold epsTerm; rw [if_pos hi]
  have hNeq : ∀ i ∈ indexN A b c,
      epsTerm A b c i = sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 i) '' OmegaD A b c) :=
    fun i hi => by unfold epsTerm; rw [if_neg (fun h => hdisj i h hi), if_pos hi]
  have hpos : ∀ i, 0 < epsTerm A b c i := fun i => by
    have hi : i ∈ indexB A b c ∪ indexN A b c := by rw [hBN]; trivial
    rcases hi with hi | hi
    · rw [hBeq i hi]
      obtain ⟨x, hx, hxi⟩ := hi
      have : 0 < x i := lt_of_le_of_ne (hx.1.2 i) (Ne.symm hxi)
      refine lt_of_lt_of_le this (le_csSup ⟨(c ⬝ᵥ xs - b ⬝ᵥ lo) / so i, ?_⟩ ⟨x, hx, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩; exact hPb y hy i
    · rw [hNeq i hi]
      obtain ⟨p, hp, hpi⟩ := hi
      have : 0 < p.2 i := lt_of_le_of_ne (hp.1.2 i) (Ne.symm hpi)
      refine lt_of_lt_of_le this (le_csSup ⟨(c ⬝ᵥ xo - b ⬝ᵥ ls) / xo i, ?_⟩ ⟨p, hp, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩; exact hDb y hy i
  have hεle : ∀ i, epsABC A b c ≤ epsTerm A b c i := fun i =>
    ciInf_le (Finite.bddBelow_range _) i
  have hεpos : ∀ i : Fin n, 0 < epsABC A b c := fun i => by
    haveI : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := epsTerm A b c)
    rw [epsABC, ← hj]; exact hpos j
  have : (0 : ℝ) < n := by have := i0.pos; exact_mod_cast this
  exact div_pos (hεpos i0) this

theorem g70wr_dxds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (h1 : Aᵀ *ᵥ dlam + ds = 0) (h2 : A *ᵥ dx = 0) : dx ⬝ᵥ ds = 0 := by
  have : ds = -(Aᵀ *ᵥ dlam) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
  rw [this, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h2]
  simp

theorem g70wr_n2On {n : ℕ} (S : Set (Fin n)) (v : Fin n → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i ∈ S, v i ^ 2 ≤ T) : norm2On S v ≤ Real.sqrt (n * T) := by
  classical
  unfold norm2On
  apply Real.sqrt_le_sqrt
  have : ∀ i, S.indicator (fun j => v j ^ 2) i ≤ T := fun i => by
    by_cases hi : i ∈ S
    · rw [Set.indicator_of_mem hi]; exact h i hi
    · rw [Set.indicator_of_notMem hi]; exact hT
  calc ∑ i, S.indicator (fun j => v j ^ 2) i ≤ ∑ _i : Fin n, T := Finset.sum_le_sum fun i _ => this i
    _ = n * T := by simp

set_option maxHeartbeats 1000000 in
theorem g70wr_71 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ NegInf A b c γ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsAffineStep A x s dx dlam ds) :
    norm2On (indexN A b c) dx ≤ (n / (Real.sqrt γ * C3 A b c)) * mu x s ∧
      norm2On (indexB A b c) ds ≤ (n / (Real.sqrt γ * C3 A b c)) * mu x s := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [norm2On]
  obtain ⟨hFo, hγμ⟩ := hN
  have hFo' := hFo
  obtain ⟨hAx, hdx, hx, hs⟩ := hFo'
  simp only at hAx hdx hx hs hγμ
  have i0 : Fin n := ⟨0, hn⟩
  have hC := g70wr_C3pos A b c x lam s hFo i0
  obtain ⟨C0, hC0⟩ := g70wr_513 A b c (mu x s) γ hγ x lam s hFo
  obtain ⟨-, hNb, hBb, hNs, hBx⟩ := hC0 x lam s ⟨hFo, hγμ⟩ le_rfl
  obtain ⟨h1, h2, h3⟩ := hstep
  have hdd := g70wr_dxds A dx dlam ds h1 h2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ0 : 0 < γ := hγ.1
  have hxs : x ⬝ᵥ s = n * mu x s := by rw [mu]; field_simp
  have hμ : 0 < mu x s := by
    haveI : Nonempty (Fin n) := ⟨i0⟩
    exact div_pos (Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) Finset.univ_nonempty) hnr
  set μ := mu x s with hμdef
  set C := C3 A b c with hCdef
  -- energy identity
  have hPQ : ∑ i, (dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i) = x ⬝ᵥ s := by
    have e : ∀ i, dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i = x i * s i - 2 * (dx i * ds i) :=
      fun i => by
        have := h3 i
        have hxi := (hx i).ne'; have hsi := (hs i).ne'
        field_simp
        have : (s i * dx i + x i * ds i) ^ 2 = (x i * s i) ^ 2 := by rw [this]; ring
        nlinarith [this]
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∑ i, dx i * ds i = dx ⬝ᵥ ds := rfl
    rw [this, hdd]; simp [dotProduct]
  have hP : ∀ i, dx i ^ 2 * s i / x i ≤ x ⬝ᵥ s := fun i => by
    rw [← hPQ]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i)
      (fun j _ => by have := hx j; have := hs j; positivity) (Finset.mem_univ i))
    have : 0 ≤ ds i ^ 2 * x i / s i := by have := hx i; have := hs i; positivity
    linarith
  have hQ : ∀ i, ds i ^ 2 * x i / s i ≤ x ⬝ᵥ s := fun i => by
    rw [← hPQ]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i)
      (fun j _ => by have := hx j; have := hs j; positivity) (Finset.mem_univ i))
    have : 0 ≤ dx i ^ 2 * s i / x i := by have := hx i; have := hs i; positivity
    linarith
  set T := n * μ ^ 2 / (C ^ 2 * γ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hfinal : Real.sqrt (n * T) = (n / (Real.sqrt γ * C)) * μ := by
    have e : (n : ℝ) * T = ((n / (Real.sqrt γ * C)) * μ) ^ 2 := by
      rw [hT, mul_pow, div_pow, mul_pow, Real.sq_sqrt hγ0.le]; field_simp
    rw [e, Real.sqrt_sq (by positivity)]
  constructor
  · rw [← hfinal]
    refine g70wr_n2On _ _ T hT0 fun i hi => ?_
    have a1 := (hNb i hi).2
    have a2 := hNs i hi
    have hp := hP i
    rw [div_le_iff₀ (hx i)] at hp
    -- dx_i^2 s_i ≤ nμ x_i ≤ nμ * μ / C ;  s_i ≥ Cγ
    have b1 : dx i ^ 2 * s i ≤ n * μ * (μ / C) := by
      rw [hxs] at hp
      have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ n * μ)
      linarith
    have b2 : dx i ^ 2 * (C * γ) ≤ n * μ * (μ / C) := by
      have := mul_le_mul_of_nonneg_left a2 (sq_nonneg (dx i)); linarith
    rw [hT, le_div_iff₀ (by positivity)]
    have : n * μ * (μ / C) = n * μ ^ 2 / C := by ring
    rw [this, le_div_iff₀ hC] at b2
    nlinarith
  · rw [← hfinal]
    refine g70wr_n2On _ _ T hT0 fun i hi => ?_
    have a1 := (hBb i hi).2
    have a2 := hBx i hi
    have hq := hQ i
    rw [div_le_iff₀ (hs i)] at hq
    have b1 : ds i ^ 2 * x i ≤ n * μ * (μ / C) := by
      rw [hxs] at hq
      have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ n * μ)
      linarith
    have b2 : ds i ^ 2 * (C * γ) ≤ n * μ * (μ / C) := by
      have := mul_le_mul_of_nonneg_left a2 (sq_nonneg (ds i)); linarith
    rw [hT, le_div_iff₀ (by positivity)]
    have : n * μ * (μ / C) = n * μ ^ 2 / C := by ring
    rw [this, le_div_iff₀ hC] at b2
    nlinarith


open Matrix


/-- property: no nonzero kernel vector conformal to `w` -/
def g72wyb_NoConf {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (w : Fin q → ℝ) : Prop :=
  ∀ z : Fin q → ℝ, H *ᵥ z = 0 → (∀ j, z j ≠ 0 → 0 < z j * w j) → z = 0

lemma g72wyb_sq_sign (t : SignType) : ((t : ℝ)) ^ 2 = if t = 0 then 0 else 1 := by
  cases t <;> simp

lemma g72wyb_pat {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (τ : Fin q → SignType) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) →
      g72wyb_NoConf H w → ‖w‖ ≤ C * ‖H *ᵥ w‖ := by
  set T : Set (Fin q → ℝ) := (⋂ j, {u : Fin q → ℝ | 0 ≤ (τ j : ℝ) * u j} ∩
      {u | u j = (τ j : ℝ) ^ 2 * u j}) ∩ Metric.sphere 0 1 with hT
  have hTc : IsCompact T := by
    apply (isCompact_sphere (0 : Fin q → ℝ) 1).inter_left
    apply isClosed_iInter
    intro j
    apply IsClosed.inter
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  -- members of T are conformal to w of pattern τ
  have hconf : ∀ u ∈ T, ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) →
      ∀ j, u j ≠ 0 → 0 < u j * w j := by
    intro u hu w hw j hj
    have hu1 := (Set.mem_iInter.mp hu.1 j).1
    have hu2 := (Set.mem_iInter.mp hu.1 j).2
    simp only [Set.mem_setOf_eq] at hu1 hu2
    have hwj := hw j
    rcases lt_trichotomy (w j) 0 with h | h | h
    · rw [sign_neg h] at hwj
      rw [← hwj] at hu1
      simp at hu1
      have : u j < 0 := lt_of_le_of_ne (by linarith) hj
      nlinarith
    · rw [h, sign_zero] at hwj
      rw [← hwj] at hu2
      simp at hu2
      exact absurd hu2 hj
    · rw [sign_pos h] at hwj
      rw [← hwj] at hu1
      simp at hu1
      have : 0 < u j := lt_of_le_of_ne hu1 (Ne.symm hj)
      nlinarith
  have hmemT : ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) → w ≠ 0 →
      ‖w‖⁻¹ • w ∈ T := by
    intro w hw hw0
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨Set.mem_iInter.mpr fun j => ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      rw [← hw j]
      rcases lt_trichotomy (w j) 0 with h | h | h
      · rw [sign_neg h]; simp; have := inv_pos.mpr hn; nlinarith
      · rw [h]; simp
      · rw [sign_pos h]; simp; positivity
    · simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      rw [← hw j]
      rcases lt_trichotomy (w j) 0 with h | h | h
      · rw [sign_neg h]; simp
      · rw [h]; simp
      · rw [sign_pos h]; simp
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  by_cases hbad : ∃ u ∈ T, H *ᵥ u = 0
  · obtain ⟨u, hu, hHu⟩ := hbad
    refine ⟨0, le_rfl, fun w hw hnc => ?_⟩
    exfalso
    have h0 := hnc u hHu (hconf u hu w hw)
    have := hu.2
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  push_neg at hbad
  rcases T.eq_empty_or_nonempty with hE | hNE
  · refine ⟨0, le_rfl, fun w hw _ => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    · have := hmemT w hw hw0
      rw [hE] at this
      exact absurd this (Set.notMem_empty _)
  · obtain ⟨u0, hu0, hmin⟩ := hTc.exists_isMinOn hNE
      (f := fun u => ‖H *ᵥ u‖) (by fun_prop)
    have hc : 0 < ‖H *ᵥ u0‖ := norm_pos_iff.mpr (hbad u0 hu0)
    refine ⟨‖H *ᵥ u0‖⁻¹, by positivity, fun w hw _ => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have h1 := hmin (hmemT w hw hw0)
      simp only [Set.mem_setOf_eq, Matrix.mulVec_smul, norm_smul, norm_inv, norm_norm] at h1
      rw [le_inv_mul_iff₀ hc]
      have h2 : ‖H *ᵥ u0‖ * ‖w‖ ≤ ‖w‖⁻¹ * ‖H *ᵥ w‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right h1 hn.le
      have e : ‖w‖⁻¹ * ‖H *ᵥ w‖ * ‖w‖ = ‖H *ᵥ w‖ := by field_simp
      rw [e] at h2
      linarith

lemma g72wyb_core {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, g72wyb_NoConf H w → ‖w‖ ≤ C * ‖H *ᵥ w‖ := by
  choose C hC0 hC using g72wyb_pat H
  refine ⟨∑ τ, C τ, Finset.sum_nonneg fun τ _ => hC0 τ, fun w hw => ?_⟩
  have h1 := hC (fun j => SignType.sign (w j)) w (fun j => rfl) hw
  have h2 : C (fun j => SignType.sign (w j)) ≤ ∑ τ, C τ :=
    Finset.single_le_sum (fun τ _ => hC0 τ) (Finset.mem_univ _)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- Euclidean norm comparisons. -/
lemma g72wyb_sup_le_e {q : ℕ} (v : Fin q → ℝ) : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))

lemma g72wyb_e_le_sup {q : ℕ} (v : Fin q → ℝ) :
    Real.sqrt (∑ i, v i ^ 2) ≤ Real.sqrt q * ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg q)]
  apply Real.sqrt_le_sqrt
  have : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := fun i => by
    rw [← sq_abs]
    have := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin q, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = q * ‖v‖ ^ 2 := by simp

lemma g72wyb_core2 {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, g72wyb_NoConf H w →
      Real.sqrt (∑ i, w i ^ 2) ≤ C * Real.sqrt (∑ i, (H *ᵥ w) i ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := g72wyb_core H
  refine ⟨Real.sqrt q * C, by positivity, fun w hw => ?_⟩
  calc Real.sqrt (∑ i, w i ^ 2) ≤ Real.sqrt q * ‖w‖ := g72wyb_e_le_sup w
    _ ≤ Real.sqrt q * (C * ‖H *ᵥ w‖) := mul_le_mul_of_nonneg_left (hC w hw) (by positivity)
    _ ≤ Real.sqrt q * (C * Real.sqrt (∑ i, (H *ᵥ w) i ^ 2)) := by
        gcongr; exact g72wyb_sup_le_e _
    _ = _ := by ring


theorem g72wyb_comp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x' : Fin n → ℝ) (hx : x' ∈ OmegaP A b c) (p : (Fin m → ℝ) × (Fin n → ℝ))
    (hp : p ∈ OmegaD A b c) (j : Fin n) : x' j * p.2 j = 0 := by
  have h1 := g70wr_PD A b c x' hx p hp
  have h2 := g70wr_wd A b c x' p.1 p.2 hx.1.1 hp.1.1
  have h3 : p.2 ⬝ᵥ x' = 0 := by linarith
  have h4 := g70wr_single x' p.2 hx.1.2 hp.1.2 j
  rw [dotProduct_comm, h3] at h4
  exact le_antisymm h4 (mul_nonneg (hx.1.2 j) (hp.1.2 j))

theorem g72wyb_opb {r q : ℕ} (M : Matrix (Fin r) (Fin q) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Fin q → ℝ,
      Real.sqrt (∑ i, (M *ᵥ u) i ^ 2) ≤ K * Real.sqrt (∑ i, u i ^ 2) := by
  set f := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M) with hf
  refine ⟨Real.sqrt r * ‖f‖, by positivity, fun u => ?_⟩
  have h1 : ‖M *ᵥ u‖ ≤ ‖f‖ * ‖u‖ := by simpa [hf] using f.le_opNorm u
  calc Real.sqrt (∑ i, (M *ᵥ u) i ^ 2) ≤ Real.sqrt r * ‖M *ᵥ u‖ := g72wyb_e_le_sup _
    _ ≤ Real.sqrt r * (‖f‖ * ‖u‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ Real.sqrt r * (‖f‖ * Real.sqrt (∑ i, u i ^ 2)) := by
        gcongr; exact g72wyb_sup_le_e u
    _ = _ := by ring

theorem g72wyb_neg_n2 {q : ℕ} (v : Fin q → ℝ) :
    Real.sqrt (∑ i, (-v) i ^ 2) = Real.sqrt (∑ i, v i ^ 2) := by
  simp

theorem g72wyb_mask_le {n : ℕ} (S T : Set (Fin n)) [DecidablePred (· ∈ S)]
    (hST : ∀ j, j ∉ S → j ∈ T) (v : Fin n → ℝ) :
    Real.sqrt (∑ i, (if i ∈ S then 0 else v i) ^ 2) ≤ norm2On T v := by
  unfold norm2On
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    have : 0 ≤ T.indicator (fun j => v j ^ 2) i :=
      Set.indicator_nonneg (fun j _ => sq_nonneg (v j)) i
    simpa using this
  · simp only [hi, if_false]
    rw [Set.indicator_of_mem (hST i hi)]

theorem g72wyb_pair {n : ℕ} (u v : Fin n → ℝ) :
    norm2Pair u v ≤ Real.sqrt n * (‖u‖ + ‖v‖) := by
  unfold norm2Pair
  have hu : ∀ i, u i ^ 2 ≤ ‖u‖ ^ 2 := fun i => by
    rw [← sq_abs]; have := norm_le_pi_norm u i; rw [Real.norm_eq_abs] at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hv : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := fun i => by
    rw [← sq_abs]; have := norm_le_pi_norm v i; rw [Real.norm_eq_abs] at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h1 : ∑ i, u i ^ 2 + ∑ i, v i ^ 2 ≤ n * (‖u‖ + ‖v‖) ^ 2 := by
    have a1 : ∑ i, u i ^ 2 ≤ n * ‖u‖ ^ 2 := by
      calc ∑ i, u i ^ 2 ≤ ∑ _i : Fin n, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => hu i
        _ = _ := by simp
    have a2 : ∑ i, v i ^ 2 ≤ n * ‖v‖ ^ 2 := by
      calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hv i
        _ = _ := by simp
    have : (0:ℝ) ≤ n * (2 * ‖u‖ * ‖v‖) := by positivity
    nlinarith
  calc Real.sqrt (∑ i, u i ^ 2 + ∑ i, v i ^ 2) ≤ Real.sqrt (n * (‖u‖ + ‖v‖) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt n * (‖u‖ + ‖v‖) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity)]

set_option maxHeartbeats 1000000 in
/-- Theorem 7.4 (p. 133): for `γ ∈ (0, 1)` there is a constant `C₅`, chosen before the point
(it depends only on `A, b, c, γ`), such that for every `(x, λ, s) ∈ N_{-∞}(γ)` and every
affine-scaling direction `(Δx, Δλ, Δs)` from (7.1), `‖(Δx, Δs)‖ ≤ C₅μ`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C₅ : ℝ, ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ →
        ∀ (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ),
          IsAffineStep A x s dx dlam ds → norm2Pair dx ds ≤ C₅ * mu x s := by
  classical
  set B := indexB A b c with hBdef
  set N := indexN A b c with hNdef
  set dB : Fin n → ℝ := fun i => if i ∈ B then 1 else 0 with hdB
  set dN : Fin n → ℝ := fun i => if i ∈ N then 1 else 0 with hdN
  set H1 := A * diagonal dB with hH1
  obtain ⟨C1, hC10, hC1⟩ := g72wyb_core2 H1
  obtain ⟨KA, hKA0, hKA⟩ := g72wyb_opb A
  -- a matrix whose kernel is the range of Aᵀ
  set V := LinearMap.range (Matrix.mulVecLin Aᵀ) with hV
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  set Q' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := W.subtype ∘ₗ Submodule.projectionOnto W V hW.symm
    with hQ'
  set Qm := LinearMap.toMatrix' Q' with hQm
  have hQ : ∀ v, Qm *ᵥ v = 0 ↔ ∃ u, Aᵀ *ᵥ u = v := by
    intro v
    rw [hQm, LinearMap.toMatrix'_mulVec, hQ', LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.coe_eq_zero, Submodule.projectionOnto_apply_eq_zero_iff, hV, LinearMap.mem_range]
    simp [Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
  set H2 := Qm * diagonal dN with hH2
  obtain ⟨C2, hC20, hC2⟩ := g72wyb_core2 H2
  obtain ⟨KQ, hKQ0, hKQ⟩ := g72wyb_opb Qm
  set C₄ := (n / (Real.sqrt γ * C3 A b c)) with hC₄
  refine ⟨Real.sqrt n * ((C1 * KA + 1) * C₄ + (C2 * KQ + 1) * C₄), ?_⟩
  intro x lam s hNeg dx dlam ds hstep
  have h71 := g70wr_71 A b c γ hγ x lam s hNeg dx dlam ds hstep
  obtain ⟨⟨hAx, hd, hxpos, hspos⟩, -⟩ := hNeg
  simp only at hAx hd hxpos hspos
  rw [← hC₄] at h71
  obtain ⟨hdxN, hdsB⟩ := h71
  have hΩ := g70wr_feas A b c x lam s hAx (fun j => (hxpos j).le) hd (fun j => (hspos j).le)
  obtain ⟨hcov, xs, hxs, ps, hps, -⟩ := g70wr_gt A b c hΩ
  have hcov' : ∀ j, j ∉ B → j ∈ N := by
    intro j hj
    have : j ∈ B ∪ N := by rw [hBdef, hNdef, hcov]; trivial
    rcases this with h | h
    · exact absurd h hj
    · exact h
  have hcov'' : ∀ j, j ∉ N → j ∈ B := by
    intro j hj
    have : j ∈ B ∪ N := by rw [hBdef, hNdef, hcov]; trivial
    rcases this with h | h
    · exact h
    · exact absurd h hj
  have sB : ∀ j ∈ B, ps.2 j = 0 := by
    intro j hj
    obtain ⟨x', hx', hx'j⟩ := hj
    have := g72wyb_comp A b c x' hx' ps hps j
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx'j
    · exact h
  have xN : ∀ j ∈ N, xs j = 0 := by
    intro j hj
    obtain ⟨p, hp, hpj⟩ := hj
    have := g72wyb_comp A b c xs hxs p hp j
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hpj
  obtain ⟨hst1, hst2, hst3⟩ := hstep
  have hds : ds = -(Aᵀ *ᵥ dlam) := by
    ext j; have := congrFun hst1 j; simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.neg_apply]; linarith
  have hmu0 : 0 ≤ C₄ * mu x s := le_trans (Real.sqrt_nonneg _) hdxN
  ------------------------------------------------------------------ part 1
  set w1 := diagonal dB *ᵥ dx with hw1
  have hw1j : ∀ j, w1 j = if j ∈ B then dx j else 0 := by
    intro j; rw [hw1, mulVec_diagonal, hdB]; by_cases hj : j ∈ B <;> simp [hj]
  set r1 := dx - w1 with hr1
  have hr1j : ∀ j, r1 j = if j ∈ B then 0 else dx j := by
    intro j; rw [hr1, Pi.sub_apply, hw1j]; by_cases hj : j ∈ B <;> simp [hj]
  have hH1w : H1 *ᵥ w1 = -(A *ᵥ r1) := by
    have e1 : diagonal dB *ᵥ w1 = w1 := by
      ext j; rw [mulVec_diagonal, hw1j, hdB]; by_cases hj : j ∈ B <;> simp [hj]
    rw [hH1, ← Matrix.mulVec_mulVec, e1, hr1, Matrix.mulVec_sub, hst2]; simp
  have hnc1 : g72wyb_NoConf H1 w1 := by
    intro z hz hconf
    have hsupp : ∀ j, j ∉ B → z j = 0 := by
      intro j hj
      by_contra hzj
      have := hconf j hzj
      rw [hw1j, if_neg hj, mul_zero] at this
      exact lt_irrefl _ this
    have hdz : diagonal dB *ᵥ z = z := by
      ext j; rw [mulVec_diagonal, hdB]
      by_cases hj : j ∈ B
      · simp [hj]
      · simp [hj, hsupp j hj]
    have hAz : A *ᵥ z = 0 := by
      rw [hH1, ← Matrix.mulVec_mulVec, hdz] at hz; exact hz
    have hzAt : ∀ u, z ⬝ᵥ (Aᵀ *ᵥ u) = 0 := by
      intro u; rw [dotProduct_mulVec, vecMul_transpose, hAz, zero_dotProduct]
    by_contra hne
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hne
    have hterm : ∀ j, 0 ≤ z j * w1 j * (s j / x j) := by
      intro j
      by_cases hzj : z j = 0
      · simp [hzj]
      · exact mul_nonneg (hconf j hzj).le (div_pos (hspos j) (hxpos j)).le
    have hpos : 0 < ∑ j, z j * w1 j * (s j / x j) :=
      Finset.sum_pos' (fun j _ => hterm j)
        ⟨j0, Finset.mem_univ _, mul_pos (hconf j0 hj0) (div_pos (hspos j0) (hxpos j0))⟩
    have hsum : ∑ j, z j * w1 j * (s j / x j) = ∑ j, (-(z j * s j) - z j * ds j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ B
      · rw [hw1j, if_pos hj]
        have h3 := hst3 j
        have hx0 := (hxpos j).ne'
        rw [show z j * dx j * (s j / x j) = z j * (s j * dx j) / x j by ring,
          show s j * dx j = -(x j * s j) - x j * ds j by linarith]
        field_simp
      · rw [hsupp j hj]; ring
    have hs_eq : s = Aᵀ *ᵥ (ps.1 - lam) + ps.2 := by
      have hp1 := hps.1.1
      rw [Matrix.mulVec_sub]
      ext j
      have e1 := congrFun hp1 j
      have e2 := congrFun hd j
      simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 ⊢
      linarith
    have hzps : z ⬝ᵥ ps.2 = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ B
      · simp [sB j hj]
      · simp [hsupp j hj]
    have hzs : z ⬝ᵥ s = 0 := by
      rw [hs_eq, dotProduct_add, hzAt, hzps, add_zero]
    have hzds : z ⬝ᵥ ds = 0 := by
      rw [hds, dotProduct_neg, hzAt, neg_zero]
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hpos
    have e1 : ∑ j, z j * s j = z ⬝ᵥ s := rfl
    have e2 : ∑ j, z j * ds j = z ⬝ᵥ ds := rfl
    rw [e1, e2, hzs, hzds] at hpos
    simp at hpos
  have hr1b : Real.sqrt (∑ i, r1 i ^ 2) ≤ C₄ * mu x s := by
    have := g72wyb_mask_le B N hcov' dx
    simp_rw [hr1j]
    exact this.trans hdxN
  have hw1b : Real.sqrt (∑ i, w1 i ^ 2) ≤ C1 * KA * (C₄ * mu x s) := by
    calc Real.sqrt (∑ i, w1 i ^ 2) ≤ C1 * Real.sqrt (∑ i, (H1 *ᵥ w1) i ^ 2) := hC1 w1 hnc1
      _ = C1 * Real.sqrt (∑ i, (A *ᵥ r1) i ^ 2) := by rw [hH1w, g72wyb_neg_n2]
      _ ≤ C1 * (KA * Real.sqrt (∑ i, r1 i ^ 2)) := mul_le_mul_of_nonneg_left (hKA r1) hC10
      _ ≤ C1 * (KA * (C₄ * mu x s)) := by gcongr
      _ = _ := by ring
  have hdx : ‖dx‖ ≤ (C1 * KA + 1) * (C₄ * mu x s) := by
    have e : dx = w1 + r1 := by rw [hr1]; abel
    calc ‖dx‖ = ‖w1 + r1‖ := by rw [← e]
      _ ≤ ‖w1‖ + ‖r1‖ := norm_add_le _ _
      _ ≤ Real.sqrt (∑ i, w1 i ^ 2) + Real.sqrt (∑ i, r1 i ^ 2) :=
          add_le_add (g72wyb_sup_le_e _) (g72wyb_sup_le_e _)
      _ ≤ C1 * KA * (C₄ * mu x s) + C₄ * mu x s := add_le_add hw1b hr1b
      _ = _ := by ring
  ------------------------------------------------------------------ part 2
  set w2 := diagonal dN *ᵥ ds with hw2
  have hw2j : ∀ j, w2 j = if j ∈ N then ds j else 0 := by
    intro j; rw [hw2, mulVec_diagonal, hdN]; by_cases hj : j ∈ N <;> simp [hj]
  set r2 := ds - w2 with hr2
  have hr2j : ∀ j, r2 j = if j ∈ N then 0 else ds j := by
    intro j; rw [hr2, Pi.sub_apply, hw2j]; by_cases hj : j ∈ N <;> simp [hj]
  have hQds : Qm *ᵥ ds = 0 := by
    rw [hQ]; refine ⟨-dlam, ?_⟩; rw [Matrix.mulVec_neg, hds]
  have hH2w : H2 *ᵥ w2 = -(Qm *ᵥ r2) := by
    have e1 : diagonal dN *ᵥ w2 = w2 := by
      ext j; rw [mulVec_diagonal, hw2j, hdN]; by_cases hj : j ∈ N <;> simp [hj]
    rw [hH2, ← Matrix.mulVec_mulVec, e1, hr2, Matrix.mulVec_sub, hQds]; simp
  have hnc2 : g72wyb_NoConf H2 w2 := by
    intro z hz hconf
    have hsupp : ∀ j, j ∉ N → z j = 0 := by
      intro j hj
      by_contra hzj
      have := hconf j hzj
      rw [hw2j, if_neg hj, mul_zero] at this
      exact lt_irrefl _ this
    have hdz : diagonal dN *ᵥ z = z := by
      ext j; rw [mulVec_diagonal, hdN]
      by_cases hj : j ∈ N
      · simp [hj]
      · simp [hj, hsupp j hj]
    have hQz : Qm *ᵥ z = 0 := by
      rw [hH2, ← Matrix.mulVec_mulVec, hdz] at hz; exact hz
    obtain ⟨u, hu⟩ := (hQ z).mp hQz
    have hzAv : ∀ v, z ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
      intro v; rw [← hu, dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    by_contra hne
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hne
    have hterm : ∀ j, 0 ≤ z j * w2 j * (x j / s j) := by
      intro j
      by_cases hzj : z j = 0
      · simp [hzj]
      · exact mul_nonneg (hconf j hzj).le (div_pos (hxpos j) (hspos j)).le
    have hpos : 0 < ∑ j, z j * w2 j * (x j / s j) :=
      Finset.sum_pos' (fun j _ => hterm j)
        ⟨j0, Finset.mem_univ _, mul_pos (hconf j0 hj0) (div_pos (hxpos j0) (hspos j0))⟩
    have hsum : ∑ j, z j * w2 j * (x j / s j) = ∑ j, (-(z j * (x j - xs j)) - z j * dx j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ N
      · rw [hw2j, if_pos hj, xN j hj]
        have h3 := hst3 j
        have hs0 := (hspos j).ne'
        rw [show z j * ds j * (x j / s j) = z j * (x j * ds j) / s j by ring,
          show x j * ds j = -(x j * s j) - s j * dx j by linarith]
        field_simp
        ring
      · rw [hsupp j hj]; ring
    have hzdx : z ⬝ᵥ dx = 0 := by rw [hzAv, hst2, dotProduct_zero]
    have hzx : z ⬝ᵥ (x - xs) = 0 := by
      rw [hzAv, Matrix.mulVec_sub, hAx, hxs.1.1, sub_self, dotProduct_zero]
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hpos
    have e1 : ∑ j, z j * (x j - xs j) = z ⬝ᵥ (x - xs) := rfl
    have e2 : ∑ j, z j * dx j = z ⬝ᵥ dx := rfl
    rw [e1, e2, hzx, hzdx] at hpos
    simp at hpos
  have hr2b : Real.sqrt (∑ i, r2 i ^ 2) ≤ C₄ * mu x s := by
    have := g72wyb_mask_le N B hcov'' ds
    simp_rw [hr2j]
    exact this.trans hdsB
  have hw2b : Real.sqrt (∑ i, w2 i ^ 2) ≤ C2 * KQ * (C₄ * mu x s) := by
    calc Real.sqrt (∑ i, w2 i ^ 2) ≤ C2 * Real.sqrt (∑ i, (H2 *ᵥ w2) i ^ 2) := hC2 w2 hnc2
      _ = C2 * Real.sqrt (∑ i, (Qm *ᵥ r2) i ^ 2) := by rw [hH2w, g72wyb_neg_n2]
      _ ≤ C2 * (KQ * Real.sqrt (∑ i, r2 i ^ 2)) := mul_le_mul_of_nonneg_left (hKQ r2) hC20
      _ ≤ C2 * (KQ * (C₄ * mu x s)) := by gcongr
      _ = _ := by ring
  have hds' : ‖ds‖ ≤ (C2 * KQ + 1) * (C₄ * mu x s) := by
    have e : ds = w2 + r2 := by rw [hr2]; abel
    calc ‖ds‖ = ‖w2 + r2‖ := by rw [← e]
      _ ≤ ‖w2‖ + ‖r2‖ := norm_add_le _ _
      _ ≤ Real.sqrt (∑ i, w2 i ^ 2) + Real.sqrt (∑ i, r2 i ^ 2) :=
          add_le_add (g72wyb_sup_le_e _) (g72wyb_sup_le_e _)
      _ ≤ C2 * KQ * (C₄ * mu x s) + C₄ * mu x s := add_le_add hw2b hr2b
      _ = _ := by ring
  calc norm2Pair dx ds ≤ Real.sqrt n * (‖dx‖ + ‖ds‖) := g72wyb_pair dx ds
    _ ≤ Real.sqrt n * ((C1 * KA + 1) * (C₄ * mu x s) + (C2 * KQ + 1) * (C₄ * mu x s)) := by
        gcongr
    _ = _ := by ring
