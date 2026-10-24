-- Prove2me | solution 1 for WrightPDIPM.Termination.theorem_7_12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:50:55.158354+00:00
-- url     : https://prove2.me/submissions/4c57a981-e77f-47e7-970e-38c0a831cb48

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup
import Theorems.Thm_WrightPDIPM_Termination_lemma_7_2
import Theorems.Thm_WrightPDIPM_Termination_lemma_5_13

open WrightPDIPM.Termination
open Matrix

namespace WT97

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
theorem wt_setup {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xo : Fin n → ℝ) (lo : Fin m → ℝ) (so : Fin n → ℝ) (hFo : (xo, lo, so) ∈ Fo A b c)
    (hn : 0 < n) :
    0 < C3 A b c ∧ indexB A b c ∪ indexN A b c = Set.univ ∧
      (∀ i, i ∈ indexB A b c → i ∉ indexN A b c) ∧
      (OmegaP A b c).Nonempty ∧ (OmegaD A b c).Nonempty := by
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
  have hεpos : 0 < epsABC A b c := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := epsTerm A b c)
    rw [epsABC, ← hj]; exact hpos j
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact ⟨div_pos hεpos hnpos, hBN, hdisj, ⟨xs, hxs⟩, ⟨(ls, ss), hps⟩⟩

end WT97



namespace WT97

theorem exists_ker_mat {q : ℕ} (K : Submodule ℝ (Fin q → ℝ)) :
    ∃ k : ℕ, ∃ L : (Fin q → ℝ) →ₗ[ℝ] (Fin k → ℝ), LinearMap.ker L = K := by
  let e := (Module.finBasis ℝ ((Fin q → ℝ) ⧸ K)).equivFun
  exact ⟨_, e.toLinearMap.comp K.mkQ, by rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]⟩

theorem wls_sub {q : ℕ} (K : Submodule ℝ (Fin q → ℝ)) (S : Set (Fin q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin q → ℝ, (∃ w₀ ∈ K, ∀ i ∈ S, w₀ i = v i) →
      ∃ w ∈ K, (∀ i ∈ S, w i = v i) ∧
        (∀ w' ∈ K, (∀ i ∈ S, w' i = v i) → ∑ i, w i ^ 2 ≤ ∑ i, w' i ^ 2) ∧
        (∀ w' ∈ K, (∀ i ∈ S, w' i = v i) → ∑ i, w' i ^ 2 ≤ ∑ i, w i ^ 2 → w' = w) ∧
        norm2 w ≤ C * Real.sqrt (∑ i, S.indicator (fun j => v j ^ 2) i) := by
  classical
  obtain ⟨k, L, hL⟩ := exists_ker_mat K
  let M : (Fin q → ℝ) →ₗ[ℝ] (Fin (k + q) → ℝ) :=
    LinearMap.pi (fun j => Fin.addCases (motive := fun _ => (Fin q → ℝ) →ₗ[ℝ] ℝ)
      (fun a => (LinearMap.proj a).comp L)
      (fun i => if i ∈ S then (LinearMap.proj i : (Fin q → ℝ) →ₗ[ℝ] ℝ) else 0) j)
  let H := LinearMap.toMatrix' M
  obtain ⟨C, hC0, hC⟩ := lemma_7_2 H
  refine ⟨C, hC0, fun v hv => ?_⟩
  let h : Fin (k + q) → ℝ := fun j => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0)
    (fun i => if i ∈ S then v i else 0) j
  have hH : ∀ w, H *ᵥ w = h ↔ w ∈ K ∧ ∀ i ∈ S, w i = v i := by
    intro w
    rw [LinearMap.toMatrix'_mulVec, funext_iff, Fin.forall_fin_add, ← hL, LinearMap.mem_ker,
      funext_iff]
    simp only [M, h, LinearMap.pi_apply, Fin.addCases_left, Fin.addCases_right,
      LinearMap.comp_apply, LinearMap.proj_apply, Pi.zero_apply]
    refine and_congr Iff.rfl ⟨fun H i hi => ?_, fun H i => ?_⟩
    · have := H i; simpa [hi] using this
    · by_cases hi : i ∈ S
      · simp [hi, H i hi]
      · simp [hi]
  have hnh : norm2 h = Real.sqrt (∑ i, S.indicator (fun j => v j ^ 2) i) := by
    unfold norm2; congr 1
    rw [Fin.sum_univ_add]
    simp only [h, Fin.addCases_left, Fin.addCases_right]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  obtain ⟨w₀, hw₀K, hw₀S⟩ := hv
  have hr : ∃ w₀ : Fin q → ℝ, H *ᵥ w₀ = h := ⟨w₀, (hH w₀).2 ⟨hw₀K, hw₀S⟩⟩
  obtain ⟨⟨w, hw, huniq⟩, hbd⟩ := hC h hr (fun _ => 1) (fun _ => one_ne_zero)
  have hw' := hw
  obtain ⟨hwH, hwmin⟩ := hw
  simp only [one_mul] at hwmin
  obtain ⟨hwK, hwS⟩ := (hH w).1 hwH
  refine ⟨w, hwK, hwS, fun w' hK hS => hwmin w' ((hH w').2 ⟨hK, hS⟩), fun w' hK hS hle => ?_,
    by rw [← hnh]; exact hbd w hw'⟩
  apply huniq
  refine ⟨(hH w').2 ⟨hK, hS⟩, fun w'' hw'' => ?_⟩
  simp only [one_mul]
  exact hle.trans (hwmin w'' hw'')

end WT97



namespace WT97

theorem abs_le_norm2 {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : |w i| ≤ norm2 w :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => w j ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i))

theorem sqrt_ind_le {n : ℕ} (S : Set (Fin n)) (v : Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i ∈ S, |v i| ≤ M) :
    Real.sqrt (∑ i, S.indicator (fun j => v j ^ 2) i) ≤ n * M := by
  classical
  have h1 : ∑ i, S.indicator (fun j => v j ^ 2) i ≤ ((n : ℝ) * M) ^ 2 := by
    calc ∑ i, S.indicator (fun j => v j ^ 2) i ≤ ∑ _i : Fin n, M ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Set.indicator_apply]
          split_ifs with hi
          · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i hi) 2
          · positivity
      _ = (n : ℝ) * M ^ 2 := by simp
      _ ≤ ((n : ℝ) * M) ^ 2 := by
          rw [mul_pow]
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn; simp
          · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_right this (sq_nonneg M)
  exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))

theorem main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ μbar : ℝ, 0 < μbar ∧ ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ → 0 < mu x s → mu x s ≤ μbar →
        (Bset x s = indexB A b c ∧ Nset x s = indexN A b c) ∧
        (∃ p, IsFTMinimizer A b c x s p) ∧
        ∀ p, IsFTMinimizer A b c x s p → IsStrictlyComplementary A b c p := by
  classical
  by_cases hex : ∃ x lam s, (x, lam, s) ∈ NegInf A b c γ ∧ 0 < mu x s
  swap
  · exact ⟨1, one_pos, fun x lam s hN hμ _ => absurd ⟨x, lam, s, hN, hμ⟩ hex⟩
  obtain ⟨xo, lo, so, hNo, hμo⟩ := hex
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [mu] at hμo
    · exact h
  obtain ⟨hC3, hBN, hdisj, ⟨xs, hxs⟩, ⟨ps, hps⟩⟩ := wt_setup A b c xo lo so hNo.1 hn
  obtain ⟨Cx, hCx0, hCx⟩ := wls_sub (LinearMap.ker A.mulVecLin) (indexN A b c)
  obtain ⟨Cs, hCs0, hCs⟩ := wls_sub (LinearMap.range Aᵀ.mulVecLin) (indexB A b c)
  have hγ0 := hγ.1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set C := C3 A b c with hCdef
  set T := Cx + Cs + 1 with hT
  have hT0 : 0 < T := by positivity
  set μbar := C ^ 2 * γ / (2 * T * n) with hμbar_def
  have hμbar : 0 < μbar := by positivity
  obtain ⟨C₀, h513⟩ := lemma_5_13 A b c μbar γ hμbar hγ
  refine ⟨μbar, hμbar, ?_⟩
  intro x lam s hN hμ hμle
  obtain ⟨-, hxN, hsB, hsN, hxB⟩ := h513 x lam s hN hμle
  obtain ⟨⟨hAx, hdx, hx, hs⟩, -⟩ := hN
  simp only at hAx hdx hx hs
  set r := mu x s / C with hr
  have hnr_le : (n : ℝ) * r ≤ C * γ / (2 * T) := by
    rw [hr, hμbar_def] at *
    rw [mul_div_assoc', div_le_div_iff₀ hC3 (by positivity)]
    have := mul_le_mul_of_nonneg_left hμle hnr.le
    rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
    nlinarith
  have hr0 : 0 ≤ r := div_nonneg hμ.le hC3.le
  have hr1 : r < C * γ := by
    have h1 : r ≤ (n : ℝ) * r := le_mul_of_one_le_left hr0 (by exact_mod_cast hn)
    have h2 : C * γ / (2 * T) < C * γ := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_pos hC3 hγ0]
    linarith
  have hCxb : Cx * ((n : ℝ) * r) < C * γ := by
    calc Cx * ((n : ℝ) * r) ≤ Cx * (C * γ / (2 * T)) := mul_le_mul_of_nonneg_left hnr_le hCx0
      _ < C * γ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [mul_pos hC3 hγ0]
  have hCsb : Cs * ((n : ℝ) * r) < C * γ := by
    calc Cs * ((n : ℝ) * r) ≤ Cs * (C * γ / (2 * T)) := mul_le_mul_of_nonneg_left hnr_le hCs0
      _ < C * γ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [mul_pos hC3 hγ0]
  -- part (a)
  have hBeq : Bset x s = indexB A b c := by
    ext i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · have hi' : i ∈ indexB A b c ∪ indexN A b c := by rw [hBN]; trivial
      rcases hi' with h | h
      · exact h
      · exfalso
        have h1 := (hxN i h).2; have h2 := hsN i h
        change s i ≤ x i at hi
        linarith
    · have h1 := (hsB i hi).2; have h2 := hxB i hi
      change s i ≤ x i
      linarith
  have hNeq : Nset x s = indexN A b c := by
    ext i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · have hi' : i ∈ indexB A b c ∪ indexN A b c := by rw [hBN]; trivial
      rcases hi' with h | h
      · exact absurd (hBeq ▸ h) hi
      · exact h
    · have h1 := (hxN i hi).2; have h2 := hsN i hi
      change ¬ (s i ≤ x i)
      intro h; linarith
  refine ⟨⟨hBeq, hNeq⟩, ?_⟩
  -- zero patterns of optimal points
  have hxs0 : ∀ i ∈ indexN A b c, xs i = 0 := fun i hi => by
    by_contra h; exact hdisj i ⟨xs, hxs, h⟩ hi
  have hps0 : ∀ i ∈ indexB A b c, ps.2 i = 0 := fun i hi => by
    by_contra h; exact hdisj i hi ⟨ps, hps, h⟩
  -- x-part
  obtain ⟨wx, hwxK, hwxS, hwxmin, hwxu, hwxb⟩ := hCx (-x) ⟨xs - x, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_sub, hxs.1.1, hAx, sub_self],
    fun i hi => by simp [hxs0 i hi]⟩
  -- s-part
  obtain ⟨ws, hwsK, hwsS, hwsmin, hwsu, hwsb⟩ := hCs (-s) ⟨ps.2 - s, by
    refine ⟨lam - ps.1, ?_⟩
    rw [Matrix.mulVecLin_apply, mulVec_sub]
    have := hps.1.1
    rw [← this] at hdx
    linear_combination hdx,
    fun i hi => by simp [hps0 i hi]⟩
  obtain ⟨u, hu⟩ := hwsK
  rw [Matrix.mulVecLin_apply] at hu
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hwxK
  -- feasibility translation
  have hfeas : ∀ q : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
      (A *ᵥ q.1 = b ∧ Aᵀ *ᵥ q.2.1 + q.2.2 = c ∧
        (∀ i ∈ Nset x s, q.1 i = 0) ∧ (∀ i ∈ Bset x s, q.2.2 i = 0)) →
      (q.1 - x ∈ LinearMap.ker A.mulVecLin ∧ ∀ i ∈ indexN A b c, (q.1 - x) i = (-x) i) ∧
      (q.2.2 - s ∈ LinearMap.range Aᵀ.mulVecLin ∧ ∀ i ∈ indexB A b c, (q.2.2 - s) i = (-s) i) := by
    rintro q ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, fun i hi => ?_⟩, ⟨⟨lam - q.2.1, ?_⟩, fun i hi => ?_⟩⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_sub, h1, hAx, sub_self]
    · simp [h3 i (hNeq ▸ hi)]
    · rw [Matrix.mulVecLin_apply, mulVec_sub]
      rw [← h2] at hdx
      linear_combination hdx
    · simp [h4 i (hBeq ▸ hi)]
  have hobj : ∀ q : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
      (1 / 2 : ℝ) * ∑ i, (q.1 i - x i) ^ 2 + (1 / 2) * ∑ i, (q.2.2 i - s i) ^ 2 =
        (1 / 2 : ℝ) * ∑ i, (q.1 - x) i ^ 2 + (1 / 2) * ∑ i, (q.2.2 - s) i ^ 2 := by
    intro q; simp [Pi.sub_apply]
  -- the minimizer
  have hpfeas : A *ᵥ (x + wx) = b ∧ Aᵀ *ᵥ (lam - u) + (s + ws) = c ∧
      (∀ i ∈ Nset x s, (x + wx) i = 0) ∧ (∀ i ∈ Bset x s, (s + ws) i = 0) := by
    refine ⟨by rw [mulVec_add, hwxK, hAx, add_zero], ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [mulVec_sub, hu, ← hdx]; abel
    · rw [hNeq] at hi; simp [hwxS i hi]
    · rw [hBeq] at hi; simp [hwsS i hi]
  refine ⟨⟨(x + wx, lam - u, s + ws), hpfeas, fun q hq => ?_⟩, ?_⟩
  · obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hfeas q hq
    have e1 := hwxmin _ hq1 hq2
    have e2 := hwsmin _ hq3 hq4
    beta_reduce
    rw [hobj q]
    simp only [Pi.add_apply, add_sub_cancel_left]
    linarith
  · rintro q ⟨hq, hqmin⟩
    obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hfeas q hq
    have e1 := hwxmin _ hq1 hq2
    have e2 := hwsmin _ hq3 hq4
    have hle := hqmin (x + wx, lam - u, s + ws) hpfeas
    simp only at hle
    rw [hobj q] at hle
    simp only [Pi.add_apply, add_sub_cancel_left] at hle
    have hx1 : q.1 - x = wx := hwxu _ hq1 hq2 (by linarith)
    have hs1 : q.2.2 - s = ws := hwsu _ hq3 hq4 (by linarith)
    obtain ⟨h1, h2, h3, h4⟩ := hq
    have hq1e : ∀ i, q.1 i = x i + wx i := fun i => by
      rw [← hx1]; simp
    have hq2e : ∀ i, q.2.2 i = s i + ws i := fun i => by
      rw [← hs1]; simp
    -- positivity on B and N
    have hposB : ∀ i ∈ indexB A b c, 0 < q.1 i := fun i hi => by
      have a1 := abs_le_norm2 wx i
      have a2 := sqrt_ind_le (indexN A b c) (-x) r hr0
        (fun j hj => by simp only [Pi.neg_apply, abs_neg]; rw [abs_of_pos (hxN j hj).1];
                        exact (hxN j hj).2)
      have a3 := mul_le_mul_of_nonneg_left a2 hCx0
      have a4 := neg_abs_le (wx i)
      rw [hq1e i]; have := hxB i hi; linarith
    have hposN : ∀ i ∈ indexN A b c, 0 < q.2.2 i := fun i hi => by
      have a1 := abs_le_norm2 ws i
      have a2 := sqrt_ind_le (indexB A b c) (-s) r hr0
        (fun j hj => by simp only [Pi.neg_apply, abs_neg]; rw [abs_of_pos (hsB j hj).1];
                        exact (hsB j hj).2)
      have a3 := mul_le_mul_of_nonneg_left a2 hCs0
      have a4 := neg_abs_le (ws i)
      rw [hq2e i]; have := hsN i hi; linarith
    have hmem : ∀ i, i ∈ indexB A b c ∨ i ∈ indexN A b c := fun i => by
      have hi' : i ∈ indexB A b c ∪ indexN A b c := by rw [hBN]; trivial
      exact hi'
    have hq1nn : ∀ i, 0 ≤ q.1 i := fun i => by
      rcases hmem i with h | h
      · exact (hposB i h).le
      · rw [h3 i (hNeq ▸ h)]
    have hq2nn : ∀ i, 0 ≤ q.2.2 i := fun i => by
      rcases hmem i with h | h
      · rw [h4 i (hBeq ▸ h)]
      · exact (hposN i h).le
    have hcomp : q.2.2 ⬝ᵥ q.1 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hmem i with h | h
      · rw [h4 i (hBeq ▸ h), zero_mul]
      · rw [h3 i (hNeq ▸ h), mul_zero]
    have hcq := g70wr_wd A b c q.1 q.2.1 q.2.2 h1 h2
    refine ⟨⟨⟨⟨h1, hq1nn⟩, fun x' hx' => ?_⟩, ⟨⟨h2, hq2nn⟩, fun lam' s' hd' => ?_⟩⟩, hposB,
      hposN⟩
    · have := g70wr_wd A b c x' q.2.1 q.2.2 hx'.1 h2
      have := g70wr_nn q.2.2 x' hq2nn hx'.2
      linarith
    · have := g70wr_wd A b c q.1 lam' s' h1 hd'.1
      have := g70wr_nn s' q.1 hd'.2 hq1nn
      simp only
      linarith

end WT97

open WrightPDIPM.Termination in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ μbar : ℝ, 0 < μbar ∧ ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ → 0 < mu x s → mu x s ≤ μbar →
        (Bset x s = indexB A b c ∧ Nset x s = indexN A b c) ∧
        (∃ p, IsFTMinimizer A b c x s p) ∧
        ∀ p, IsFTMinimizer A b c x s p → IsStrictlyComplementary A b c p :=
  WT97.main A b c γ hγ
