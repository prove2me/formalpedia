-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:35:13.379001+00:00
-- url     : https://prove2.me/submissions/ffcd651a-8921-4696-9d11-12f53b0410dd

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup
open WrightPDIPM.SelfDual

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

theorem g70wr_mcert {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M11 : Matrix ι ι ℝ) (M12 : Matrix ι κ ℝ) (M22 : Matrix κ κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (d1 : ι → ℝ) (d2 : κ → ℝ) (δ : ℝ) (o1 : ι → ℝ) (o2 : κ → ℝ) (a : ℝ)
    (hfeas : ∃ (u : ι → ℝ) (w : κ → ℝ), (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 ∧ d1 ⬝ᵥ u + d2 ⬝ᵥ w ≤ δ)
    (hlb : ∀ (u : ι → ℝ) (w : κ → ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) →
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 → d1 ⬝ᵥ u + d2 ⬝ᵥ w ≤ δ → a ≤ o1 ⬝ᵥ u + o2 ⬝ᵥ w) :
    ∃ (y1 : ι → ℝ) (y2 : κ → ℝ) (r : ι → ℝ) (t : ℝ), (∀ i, 0 ≤ y1 i) ∧ (∀ i, 0 ≤ r i) ∧ 0 ≤ t ∧
      M11ᵀ *ᵥ y1 - M12 *ᵥ y2 + r - t • d1 = o1 ∧
      M12ᵀ *ᵥ y1 + M22ᵀ *ᵥ y2 - t • d2 = o2 ∧
      a ≤ -(f ⬝ᵥ y1) - g ⬝ᵥ y2 - t * δ := by
  classical
  let A' : Matrix (ι ⊕ κ ⊕ κ ⊕ ι ⊕ Unit) (ι ⊕ κ) ℝ :=
    Matrix.of (Sum.elim (fun i => Sum.elim (fun j => M11 i j) (fun k => M12 i k))
      (Sum.elim (fun k => Sum.elim (fun j => -M12 j k) (fun k' => M22 k k'))
      (Sum.elim (fun k => Sum.elim (fun j => M12 j k) (fun k' => -M22 k k'))
      (Sum.elim (fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0))
        (fun _ => Sum.elim (fun j => -d1 j) (fun k => -d2 k))))))
  let b' : ι ⊕ κ ⊕ κ ⊕ ι ⊕ Unit → ℝ :=
    Sum.elim (-f) (Sum.elim (-g) (Sum.elim g (Sum.elim 0 (fun _ => -δ))))
  let c' : ι ⊕ κ → ℝ := Sum.elim o1 o2
  have key : ∀ z : ι ⊕ κ → ℝ, b' ≤ A' *ᵥ z ↔
      ((∀ i, 0 ≤ z (Sum.inl i)) ∧
        (∀ i, 0 ≤ (M11 *ᵥ (fun i => z (Sum.inl i)) + M12 *ᵥ (fun k => z (Sum.inr k)) + f) i) ∧
        -(M12ᵀ *ᵥ (fun i => z (Sum.inl i))) + M22 *ᵥ (fun k => z (Sum.inr k)) + g = 0 ∧
        d1 ⬝ᵥ (fun i => z (Sum.inl i)) + d2 ⬝ᵥ (fun k => z (Sum.inr k)) ≤ δ) := by
    intro z
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
      · have := h (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
        simpa [A', b', mulVec, dotProduct, Fintype.sum_sum_type] using this
      · have := h (Sum.inl i)
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type] at this
        simp only [Pi.add_apply, mulVec, dotProduct]
        linarith
      · funext k
        have h1 := h (Sum.inr (Sum.inl k))
        have h2 := h (Sum.inr (Sum.inr (Sum.inl k)))
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type] at h1 h2
        simp only [Pi.add_apply, Pi.neg_apply, mulVec, dotProduct, transpose_apply, Pi.zero_apply]
        linarith
      · have := h (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type] at this
        simp only [dotProduct]
        linarith
    · rintro ⟨h1, h2, h3, h4⟩ r
      rcases r with i | k | k | i | u
      · have := h2 i
        simp only [Pi.add_apply, mulVec, dotProduct] at this
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type]
        linarith
      · have := congrFun h3 k
        simp only [Pi.add_apply, Pi.neg_apply, mulVec, dotProduct, transpose_apply,
          Pi.zero_apply] at this
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type]
        linarith
      · have := congrFun h3 k
        simp only [Pi.add_apply, Pi.neg_apply, mulVec, dotProduct, transpose_apply,
          Pi.zero_apply] at this
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type]
        linarith
      · simpa [A', b', mulVec, dotProduct, Fintype.sum_sum_type] using h1 i
      · simp only [dotProduct] at h4
        simp [A', b', mulVec, dotProduct, Fintype.sum_sum_type]
        linarith
  obtain ⟨u0, w0, hu0⟩ := hfeas
  obtain ⟨Y, hY0, hYA, hYb⟩ := g69a1_lp_dualG A' b' c' ⟨Sum.elim u0 w0, (key _).2 (by simpa using hu0)⟩ a
    (fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := (key z).1 hz
      have := hlb _ _ h1 h2 h3 h4
      simpa [c', dotProduct, Fintype.sum_sum_type] using this)
  refine ⟨fun i => Y (Sum.inl i), fun k => Y (Sum.inr (Sum.inl k)) - Y (Sum.inr (Sum.inr (Sum.inl k))),
    fun i => Y (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))), Y (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))),
    fun i => hY0 _, fun i => hY0 _, hY0 _, ?_, ?_, ?_⟩
  · funext j
    have := congrFun hYA (Sum.inl j)
    simp [A', c', mulVec, dotProduct, Fintype.sum_sum_type] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      transpose_apply]
    rw [← this]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · funext j
    have := congrFun hYA (Sum.inr j)
    simp [A', c', mulVec, dotProduct, Fintype.sum_sum_type] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      transpose_apply]
    rw [← this]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [b', dotProduct, Fintype.sum_sum_type] at hYb
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    linarith

theorem g70wr_skew {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (hM : M = -Mᵀ) (x : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = 0 := by
  have hT : Mᵀ = -M := by conv_rhs => rw [hM]
                          simp
  have h1 : x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (Mᵀ *ᵥ x) := by
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  rw [hT, neg_mulVec, dotProduct_neg] at h1
  linarith

theorem g70wr_mid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M11 : Matrix ι ι ℝ) (M12 : Matrix ι κ ℝ) (M22 : Matrix κ κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hM11 : M11 = -M11ᵀ) (hM22 : M22 = -M22ᵀ) (u : ι → ℝ) (w : κ → ℝ)
    (heq : -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0) :
    f ⬝ᵥ u + g ⬝ᵥ w = u ⬝ᵥ (M11 *ᵥ u + M12 *ᵥ w + f) := by
  have hg : g = M12ᵀ *ᵥ u - M22 *ᵥ w := by
    rw [← sub_eq_zero, ← heq]; abel
  subst hg
  have h1 := g70wr_skew M11 hM11 u
  have h2 := g70wr_skew M22 hM22 w
  have h3 : (M12ᵀ *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (M12 *ᵥ w) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  rw [sub_dotProduct, h3, dotProduct_add, dotProduct_add, h1, dotProduct_comm (M22 *ᵥ w), h2,
    dotProduct_comm f]
  ring

theorem g70wr_mexist {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M11 : Matrix ι ι ℝ) (M12 : Matrix ι κ ℝ) (M22 : Matrix κ κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hM11 : M11 = -M11ᵀ) (hM22 : M22 = -M22ᵀ)
    (hfeas : ∃ (u : ι → ℝ) (w : κ → ℝ), (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0) :
    ∃ (u : ι → ℝ) (w : κ → ℝ), (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 ∧ f ⬝ᵥ u + g ⬝ᵥ w ≤ 0 := by
  have hT11 : M11ᵀ = -M11 := by conv_rhs => rw [hM11]
                                simp
  have hT22 : M22ᵀ = -M22 := by conv_rhs => rw [hM22]
                                simp
  obtain ⟨u0, w0, h1, h2, h3⟩ := hfeas
  obtain ⟨y1, y2, r, t, hy1, hr, ht, hc1, hc2, hcb⟩ := g70wr_mcert M11 M12 M22 f g 0 0 0 f g 0
    ⟨u0, w0, h1, h2, h3, by simp⟩ (fun u w hu hv heq _ => by
      rw [g70wr_mid M11 M12 M22 f g hM11 hM22 u w heq]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hv i))
  rw [hT11] at hc1
  rw [hT22] at hc2
  refine ⟨y1, y2, hy1, fun i => ?_, ?_, by simp at hcb; linarith⟩
  · have := congrFun hc1 i
    simp [neg_mulVec] at this
    simp only [Pi.add_apply]
    linarith [hr i]
  · funext k
    have := congrFun hc2 k
    simp [neg_mulVec] at this
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    linarith

theorem g70wr_mj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M11 : Matrix ι ι ℝ) (M12 : Matrix ι κ ℝ) (M22 : Matrix κ κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hM11 : M11 = -M11ᵀ) (hM22 : M22 = -M22ᵀ) (us : ι → ℝ) (ws : κ → ℝ)
    (hs : (∀ i, 0 ≤ us i) ∧ (∀ i, 0 ≤ (M11 *ᵥ us + M12 *ᵥ ws + f) i) ∧
      -(M12ᵀ *ᵥ us) + M22 *ᵥ ws + g = 0 ∧ f ⬝ᵥ us + g ⬝ᵥ ws ≤ 0) (i : ι) :
    ∃ (u : ι → ℝ) (w : κ → ℝ), ((∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 ∧ f ⬝ᵥ u + g ⬝ᵥ w ≤ 0) ∧
      0 < u i + (M11 *ᵥ u + M12 *ᵥ w + f) i := by
  classical
  by_cases h : ∃ (u : ι → ℝ) (w : κ → ℝ), ((∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 ∧ f ⬝ᵥ u + g ⬝ᵥ w ≤ 0) ∧ 0 < u i
  · obtain ⟨u, w, hS, hp⟩ := h
    exact ⟨u, w, hS, by linarith [hS.2.1 i]⟩
  have hT11 : M11ᵀ = -M11 := by conv_rhs => rw [hM11]
                                simp
  have hT22 : M22ᵀ = -M22 := by conv_rhs => rw [hM22]
                                simp
  set e : ι → ℝ := fun j => if j = i then -1 else 0 with he
  obtain ⟨y1, y2, r, t, hy1, hr, ht, hc1, hc2, hcb⟩ := g70wr_mcert M11 M12 M22 f g f g 0 e 0 0
    ⟨us, ws, hs⟩ (fun u w hu hv heq hd => by
      have : ¬ 0 < u i := fun hp => h ⟨u, w, ⟨hu, hv, heq, hd⟩, hp⟩
      simp [he, dotProduct]
      linarith)
  rw [hT11] at hc1
  rw [hT22] at hc2
  have hc1' : ∀ j, (M11 *ᵥ y1) j + (M12 *ᵥ y2) j + t * f j = r j - e j := fun j => by
    have := congrFun hc1 j
    simp [neg_mulVec] at this
    linarith
  have hc2' : ∀ k, -(M12ᵀ *ᵥ y1) k + (M22 *ᵥ y2) k + t * g k = 0 := fun k => by
    have := congrFun hc2 k
    simp [neg_mulVec] at this
    linarith
  simp at hcb
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  have ht1 : 0 < t + 1 := by linarith
  set k := (t + 1)⁻¹ with hk
  have hkp : 0 < k := inv_pos.mpr ht1
  have hv : ∀ j, (M11 *ᵥ (k • (y1 + us)) + M12 *ᵥ (k • (y2 + ws)) + f) j =
      k * (r j - e j + (M11 *ᵥ us + M12 *ᵥ ws + f) j) := fun j => by
    simp only [mulVec_smul, mulVec_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hc1' j
    rw [hk]; field_simp; linarith
  refine ⟨k • (y1 + us), k • (y2 + ws), ⟨fun j => ?_, fun j => ?_, ?_, ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact mul_nonneg hkp.le (add_nonneg (hy1 j) (hs1 j))
  · rw [hv j]
    have hej : e j ≤ 0 := by simp only [he]; split_ifs <;> norm_num
    exact mul_nonneg hkp.le (by linarith [hr j, hs2 j])
  · funext q
    have := hc2' q
    have h3 := congrFun hs3 q
    simp only [mulVec_smul, mulVec_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.zero_apply] at h3 ⊢
    rw [hk]; field_simp; linarith
  · simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]
    have : k * (f ⬝ᵥ y1 + f ⬝ᵥ us) + k * (g ⬝ᵥ y2 + g ⬝ᵥ ws) =
        k * ((f ⬝ᵥ y1 + g ⬝ᵥ y2) + (f ⬝ᵥ us + g ⬝ᵥ ws)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hkp.le (by linarith)
  · rw [hv i]
    have hei : e i = -1 := by simp [he]
    have h0 : 0 ≤ (k • (y1 + us)) i := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact mul_nonneg hkp.le (add_nonneg (hy1 i) (hs1 i))
    have := mul_pos hkp (show 0 < r i - e i + (M11 *ᵥ us + M12 *ᵥ ws + f) i by
      rw [hei]; linarith [hr i, hs2 i])
    linarith

theorem g70wr_msc {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M11 : Matrix ι ι ℝ) (M12 : Matrix ι κ ℝ) (M22 : Matrix κ κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hM11 : M11 = -M11ᵀ) (hM22 : M22 = -M22ᵀ)
    (hfeas : ∃ (u : ι → ℝ) (w : κ → ℝ), (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0) :
    ∃ (u : ι → ℝ) (w : κ → ℝ), ((∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ (M11 *ᵥ u + M12 *ᵥ w + f) i) ∧
      -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g = 0 ∧ f ⬝ᵥ u + g ⬝ᵥ w ≤ 0) ∧
      ∀ i, 0 < u i + (M11 *ᵥ u + M12 *ᵥ w + f) i := by
  classical
  obtain ⟨us, ws, hs⟩ := g70wr_mexist M11 M12 M22 f g hM11 hM22 hfeas
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨us, ws, hs, fun i => (IsEmpty.false i).elim⟩
  choose U W hUW hpos using g70wr_mj M11 M12 M22 f g hM11 hM22 us ws hs
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set k : ℝ := ((Fintype.card ι : ℕ) : ℝ)⁻¹ with hk
  have hkp : 0 < k := inv_pos.mpr hcard
  have hksum : ∀ v : ℝ, ∑ _i : ι, k * v = v := fun v => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hk]
    field_simp
  have hv : ∀ j, (M11 *ᵥ (k • ∑ i, U i) + M12 *ᵥ (k • ∑ i, W i) + f) j =
      k * ∑ i, (M11 *ᵥ U i + M12 *ᵥ W i + f) j := fun j => by
    simp only [mulVec_smul, mulVec_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.sum_add_distrib, mul_add]
    rw [Finset.mul_sum (s := Finset.univ) (f := fun _ => f j), hksum]
  refine ⟨k • ∑ i, U i, k • ∑ i, W i, ⟨fun j => ?_, fun j => ?_, ?_, ?_⟩, fun j => ?_⟩
  · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hUW i).1 j)
  · rw [hv j]
    exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hUW i).2.1 j)
  · funext q
    have hq : ∀ i, -(M12ᵀ *ᵥ U i) q + (M22 *ᵥ W i) q + g q = 0 := fun i => by
      have := congrFun (hUW i).2.2.1 q; simpa using this
    simp only [mulVec_smul, mulVec_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Pi.neg_apply, Pi.zero_apply]
    have : -(k * ∑ i, (M12ᵀ *ᵥ U i) q) + k * ∑ i, (M22 *ᵥ W i) q + g q =
        k * ∑ i, (-(M12ᵀ *ᵥ U i) q + (M22 *ᵥ W i) q + g q) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_add, mul_add,
        Finset.mul_sum (s := Finset.univ) (f := fun _ => g q), hksum]; ring
    rw [this, Finset.sum_congr rfl (fun i _ => hq i)]; simp
  · simp only [dotProduct_smul, dotProduct_sum, smul_eq_mul]
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact mul_nonpos_of_nonneg_of_nonpos hkp.le (Finset.sum_nonpos fun i _ => (hUW i).2.2.2)
  · rw [hv j]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine mul_pos hkp (lt_of_lt_of_le (hpos j) ?_)
    exact Finset.single_le_sum (f := fun i => U i j + (M11 *ᵥ U i + M12 *ᵥ W i + f) j)
      (fun i _ => add_nonneg ((hUW i).1 j) ((hUW i).2.1 j)) (Finset.mem_univ j)

theorem g70wr_theta {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hκ : κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam + zbar b c x0 lam0 * θ)
    (hs : s = τ • c - Aᵀ *ᵥ lam - θ • cbar A c lam0 s0)
    (hb : (0 : Fin m → ℝ) = -(τ • b) + A *ᵥ x + θ • bbar A b x0)
    (hz : (0 : ℝ) = -(zbar b c x0 lam0 * τ) + cbar A c lam0 s0 ⬝ᵥ x - bbar A b x0 ⬝ᵥ lam
      + (x0 ⬝ᵥ s0 + 1)) :
    τ * κ + x ⬝ᵥ s = θ * (x0 ⬝ᵥ s0 + 1) := by
  have hAx : A *ᵥ x = τ • b - θ • bbar A b x0 := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, hb]; abel
  have h1 : x ⬝ᵥ (Aᵀ *ᵥ lam) = τ * (b ⬝ᵥ lam) - θ * (bbar A b x0 ⬝ᵥ lam) := by
    have : x ⬝ᵥ (Aᵀ *ᵥ lam) = (A *ᵥ x) ⬝ᵥ lam := by
      rw [mulVec_transpose, dotProduct_comm (A *ᵥ x), dotProduct_mulVec, dotProduct_comm]
    rw [this, hAx, sub_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hxs : x ⬝ᵥ s = τ * (c ⬝ᵥ x) - x ⬝ᵥ (Aᵀ *ᵥ lam) - θ * (cbar A c lam0 s0 ⬝ᵥ x) := by
    rw [hs, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dotProduct_comm x c, dotProduct_comm x (cbar A c lam0 s0)]
  rw [hxs, h1, hκ]
  linear_combination θ * hz

theorem g70wr_95fwd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) (hΩ : (Omega A b c).Nonempty)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (h : IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s) : 0 < τ ∧ κ = 0 := by
  obtain ⟨⟨hκ, hs, hb, hz, hτ, hx, hκ0, hs0', hc⟩, hpos, -⟩ := h
  obtain ⟨⟨xs, ls, ss⟩, hxs, hps⟩ := hΩ
  have hK : 0 < x0 ⬝ᵥ s0 + 1 := by
    have := g70wr_nn x0 s0 (fun j => (hx0 j).le) (fun j => (hs0 j).le); linarith
  have hθ : θ = 0 := by
    have := g70wr_theta A b c x0 lam0 s0 τ x lam θ κ s hκ hs hb hz
    rw [hc] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · linarith
  subst hθ
  simp only [zero_smul, sub_zero, add_zero, mul_zero] at hκ hs hb
  have hAx : A *ᵥ x = τ • b := by
    rw [← sub_eq_zero, ← neg_add_eq_sub]; exact hb.symm
  have hval : c ⬝ᵥ xs = b ⬝ᵥ ls := g70wr_PD A b c xs hxs (ls, ss) hps
  have hT : ∀ (y : Fin n → ℝ) (l : Fin m → ℝ), y ⬝ᵥ (Aᵀ *ᵥ l) = (A *ᵥ y) ⬝ᵥ l := fun y l => by
    rw [mulVec_transpose, dotProduct_comm (A *ᵥ y), dotProduct_mulVec, dotProduct_comm]
  have e1 : xs ⬝ᵥ s = τ * (c ⬝ᵥ xs) - b ⬝ᵥ lam := by
    rw [hs, dotProduct_sub, dotProduct_smul, smul_eq_mul, hT, hxs.1.1, dotProduct_comm xs c]
  have hss : ss = c - Aᵀ *ᵥ ls := by rw [← hps.1.1]; abel
  have e2 : x ⬝ᵥ ss = c ⬝ᵥ x - τ * (b ⬝ᵥ ls) := by
    rw [hss, dotProduct_sub, hT, hAx, smul_dotProduct, smul_eq_mul, dotProduct_comm x c]
  have n1 := g70wr_nn xs s hxs.1.2 hs0'
  have n2 := g70wr_nn x ss hx hps.1.2
  rw [dotProduct_comm] at n1
  have hk : κ = 0 := by
    have : xs ⬝ᵥ s + x ⬝ᵥ ss = -κ := by
      rw [e1, e2, hκ, hval]; ring
    rw [dotProduct_comm] at n1
    linarith
  exact ⟨by linarith, hk⟩

theorem g70wr_95bwd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    ∃ (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ),
      IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s := by
  classical
  set zb := zbar b c x0 lam0 with hzb
  set cb := cbar A c lam0 s0 with hcb
  set bb := bbar A b x0 with hbb
  set K := x0 ⬝ᵥ s0 + 1 with hK
  let M11 : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
    Matrix.of (Sum.elim (fun _ => Sum.elim (fun _ => 0) (fun j => -c j))
      (fun i => Sum.elim (fun _ => c i) (fun _ => 0)))
  let M12 : Matrix (Unit ⊕ Fin n) (Fin m ⊕ Unit) ℝ :=
    Matrix.of (Sum.elim (fun _ => Sum.elim (fun k => b k) (fun _ => zb))
      (fun i => Sum.elim (fun k => -A k i) (fun _ => -cb i)))
  let M22 : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℝ :=
    Matrix.of (Sum.elim (fun k => Sum.elim (fun _ => 0) (fun _ => bb k))
      (fun _ => Sum.elim (fun k => -bb k) (fun _ => 0)))
  let g : Fin m ⊕ Unit → ℝ := Sum.elim 0 (fun _ => K)
  have hM11 : M11 = -M11ᵀ := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [M11]
  have hM22 : M22 = -M22ᵀ := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [M22]
  have F11 : ∀ (τ : ℝ) (x : Fin n → ℝ), M11 *ᵥ Sum.elim (fun _ => τ) x =
      Sum.elim (fun _ => -(c ⬝ᵥ x)) (fun i => c i * τ) := by
    intro τ x; funext r; rcases r with r | r <;>
      simp [M11, mulVec, dotProduct, Fintype.sum_sum_type]
  have F12 : ∀ (l : Fin m → ℝ) (θ : ℝ), M12 *ᵥ Sum.elim l (fun _ => θ) =
      Sum.elim (fun _ => b ⬝ᵥ l + zb * θ) (fun i => -(Aᵀ *ᵥ l) i - cb i * θ) := by
    intro l θ; funext r; rcases r with r | r <;>
      simp [M12, mulVec, dotProduct, Fintype.sum_sum_type] <;> ring
  have F12T : ∀ (τ : ℝ) (x : Fin n → ℝ), M12ᵀ *ᵥ Sum.elim (fun _ => τ) x =
      Sum.elim (fun k => b k * τ - (A *ᵥ x) k) (fun _ => zb * τ - cb ⬝ᵥ x) := by
    intro τ x; funext r; rcases r with r | r <;>
      simp [M12, mulVec, dotProduct, Fintype.sum_sum_type] <;> ring
  have F22 : ∀ (l : Fin m → ℝ) (θ : ℝ), M22 *ᵥ Sum.elim l (fun _ => θ) =
      Sum.elim (fun k => bb k * θ) (fun _ => -(bb ⬝ᵥ l)) := by
    intro l θ; funext r; rcases r with r | r <;>
      simp [M22, mulVec, dotProduct, Fintype.sum_sum_type]
  have hT : ∀ (y : Fin n → ℝ) (l : Fin m → ℝ), y ⬝ᵥ (Aᵀ *ᵥ l) = (A *ᵥ y) ⬝ᵥ l := fun y l => by
    rw [mulVec_transpose, dotProduct_comm (A *ᵥ y), dotProduct_mulVec, dotProduct_comm]
  have hscal : -(zb * 1 - cb ⬝ᵥ x0) + -(bb ⬝ᵥ lam0) + K = 0 := by
    have e1 : cb ⬝ᵥ x0 = c ⬝ᵥ x0 - (A *ᵥ x0) ⬝ᵥ lam0 - x0 ⬝ᵥ s0 := by
      rw [hcb, cbar, sub_dotProduct, sub_dotProduct, dotProduct_comm (Aᵀ *ᵥ lam0), hT,
        dotProduct_comm s0]
    have e2 : bb ⬝ᵥ lam0 = b ⬝ᵥ lam0 - (A *ᵥ x0) ⬝ᵥ lam0 := by
      rw [hbb, bbar, sub_dotProduct]
    rw [e1, e2, hK, hzb, zbar]; ring
  obtain ⟨u, w, ⟨hu0, hv0, heq, hfg⟩, hpos⟩ := g70wr_msc M11 M12 M22 0 g hM11 hM22
    ⟨Sum.elim (fun _ => 1) x0, Sum.elim lam0 (fun _ => 1), fun r => by
      rcases r with r | r
      · simp
      · simpa using (hx0 r).le, fun r => by
      rw [F11, F12]
      rcases r with r | r
      · simp [hzb, zbar]
      · have := hs0 r
        simp [hcb, cbar]
        linarith, by
      rw [F12T, F22]
      funext r
      rcases r with r | r
      · simp [g, hbb, bbar]
      · simpa [g] using hscal⟩
  set τ := u (Sum.inl ()) with hτ
  set x : Fin n → ℝ := fun i => u (Sum.inr i) with hx
  set lam : Fin m → ℝ := fun k => w (Sum.inl k) with hlam
  set θ := w (Sum.inr ()) with hθ
  have hu : u = Sum.elim (fun _ => τ) x := by funext r; rcases r with r | r <;> rfl
  have hw : w = Sum.elim lam (fun _ => θ) := by funext r; rcases r with r | r <;> rfl
  rw [hu, hw] at hv0 heq hfg hpos
  rw [hu] at hu0
  rw [F11, F12] at hv0 hpos
  rw [F12T, F22] at heq
  have hτ0 : 0 ≤ τ := by simpa using hu0 (Sum.inl ())
  have hx0' : ∀ j, 0 ≤ x j := fun j => by simpa using hu0 (Sum.inr j)
  have hκ0 : 0 ≤ -(c ⬝ᵥ x) + (b ⬝ᵥ lam + zb * θ) := by simpa using hv0 (Sum.inl ())
  have hs0' : ∀ j, 0 ≤ c j * τ + (-(Aᵀ *ᵥ lam) j - cb j * θ) := fun j => by
    simpa using hv0 (Sum.inr j)
  have hgw : θ * K ≤ 0 := by
    simpa [g, dotProduct, Fintype.sum_sum_type, mul_comm] using hfg
  have heq1 : ∀ k, -(b k * τ - (A *ᵥ x) k) + bb k * θ = 0 := fun k => by
    have := congrFun heq (Sum.inl k); simpa [g] using this
  have heq2 : -(zb * τ - cb ⬝ᵥ x) + -(bb ⬝ᵥ lam) + K = 0 := by
    have := congrFun heq (Sum.inr ()); simpa [g] using this
  set κ := -(c ⬝ᵥ x) + (b ⬝ᵥ lam + zb * θ) with hκ
  set s : Fin n → ℝ := fun j => c j * τ + (-(Aᵀ *ᵥ lam) j - cb j * θ) with hs
  have H1 : κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam + zbar b c x0 lam0 * θ := by rw [hκ]; ring
  have H2 : s = τ • c - Aᵀ *ᵥ lam - θ • cbar A c lam0 s0 := by
    funext j; simp only [hs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcb]; ring
  have H3 : (0 : Fin m → ℝ) = -(τ • b) + A *ᵥ x + θ • bbar A b x0 := by
    funext k; have := heq1 k
    simp only [Pi.zero_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hbb] at this ⊢
    linarith
  have H4 : (0 : ℝ) = -(zbar b c x0 lam0 * τ) + cbar A c lam0 s0 ⬝ᵥ x - bbar A b x0 ⬝ᵥ lam
      + (x0 ⬝ᵥ s0 + 1) := by
    rw [← hzb, ← hcb, ← hbb, ← hK]; linarith
  have Hth := g70wr_theta A b c x0 lam0 s0 τ x lam θ κ s H1 H2 H3 H4
  have hnn : 0 ≤ τ * κ + x ⬝ᵥ s :=
    add_nonneg (mul_nonneg hτ0 hκ0) (g70wr_nn x s hx0' hs0')
  refine ⟨τ, x, lam, θ, κ, s, ⟨H1, H2, H3, H4, hτ0, hx0', hκ0, hs0', ?_⟩, ?_, fun j => ?_⟩
  · rw [← hK] at Hth; linarith
  · simpa using hpos (Sum.inl ())
  · simpa using hpos (Sum.inr j)


open Matrix

/-- Theorem 9.5 (p. 185): for an initial point `(x⁰, λ⁰, s⁰)` with `x⁰ > 0`, `s⁰ > 0` (p. 183),
the primal-dual solution set `Ω` for (9.3) is nonempty if and only if all strictly
complementary solutions `(τ*, x*, λ*, θ*, κ*, s*)` of (9.8) have `τ* > 0` and `κ* = 0`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (Omega A b c).Nonempty ↔
      ∀ (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ),
        IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s → 0 < τ ∧ κ = 0 := by
  constructor
  · intro hΩ τ x lam θ κ s h
    exact g70wr_95fwd A b c x0 lam0 s0 hx0 hs0 hΩ τ x lam θ κ s h
  · intro H
    obtain ⟨τ, x, lam, θ, κ, s, h⟩ := g70wr_95bwd A b c x0 lam0 s0 hx0 hs0
    obtain ⟨hτ, hκ⟩ := H τ x lam θ κ s h
    obtain ⟨⟨h1, h2, h3, h4, -, hx, -, hs, hc⟩, -, -⟩ := h
    have hθ : θ = 0 := by
      have := g70wr_theta A b c x0 lam0 s0 τ x lam θ κ s h1 h2 h3 h4
      have hK : 0 < x0 ⬝ᵥ s0 + 1 := by
        have := g70wr_nn x0 s0 (fun j => (hx0 j).le) (fun j => (hs0 j).le); linarith
      rw [hc] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact h
      · linarith
    subst hθ
    subst hκ
    simp only [zero_smul, sub_zero, add_zero, mul_zero] at h1 h2 h3
    have hAx : A *ᵥ (τ⁻¹ • x) = b := by
      have : A *ᵥ x = τ • b := by rw [← sub_eq_zero, ← neg_add_eq_sub]; exact h3.symm
      rw [mulVec_smul, this, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    have hd : Aᵀ *ᵥ (τ⁻¹ • lam) + τ⁻¹ • s = c := by
      rw [mulVec_smul, ← smul_add, h2, add_sub_cancel, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    have hxn : ∀ j, 0 ≤ (τ⁻¹ • x) j := fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hτ.le) (hx j)
    have hsn : ∀ j, 0 ≤ (τ⁻¹ • s) j := fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hτ.le) (hs j)
    have hval : c ⬝ᵥ (τ⁻¹ • x) = b ⬝ᵥ (τ⁻¹ • lam) := by
      simp only [dotProduct_smul, smul_eq_mul]; rw [mul_eq_mul_left_iff]; left; linarith
    refine ⟨(τ⁻¹ • x, τ⁻¹ • lam, τ⁻¹ • s), ⟨⟨hAx, hxn⟩, fun x' hx' => ?_⟩, ⟨hd, hsn⟩, fun l' s' hd' => ?_⟩
    · have := g70wr_wd A b c x' _ _ hx'.1 hd
      have := g70wr_nn _ x' hsn hx'.2
      linarith
    · have := g70wr_wd A b c _ l' s' hAx hd'.1
      have := g70wr_nn s' _ hd'.2 hxn
      simp only at *
      linarith

