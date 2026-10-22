-- Prove2me | solution 1 for WrightPDIPM.Potential.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:55:31.815548+00:00
-- url     : https://prove2.me/submissions/f838c4fd-bb28-4c2b-bcc5-f2510a3b0baf

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix
open WrightPDIPM.Potential

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

namespace g70wrCP

open Matrix

/-- Primal feasibility for (2.1): `Ax = b`, `x ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- Dual feasibility for (2.2): `Aᵀλ + s = c`, `s ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 ≤ s j

/-- Strict primal feasibility (p. 26): `Ax = b`, `x > 0`. -/
def StrictlyPrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- Strict dual feasibility (p. 26): `Aᵀλ + s = c`, `s > 0`. -/
def StrictlyDualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 < s j

/-- The primal-dual feasible set `F` (1.7a): `(x, λ, s)` with `Ax = b`, `Aᵀλ + s = c`,
`(x, s) ≥ 0`. -/
def F {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | PrimalFeasible A b p.1 ∧ DualFeasible A c p.2.1 p.2.2}

/-- The strictly feasible set `F°` (1.7b): `(x, λ, s)` with `Ax = b`, `Aᵀλ + s = c`,
`(x, s) > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | StrictlyPrimalFeasible A b p.1 ∧ StrictlyDualFeasible A c p.2.1 p.2.2}

/-- The primal solution set `Ω_P = {x* | x* solves (2.1)}` (p. 24): feasible points whose
objective `cᵀx*` is no larger than that of any feasible point. -/
def OmegaP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'}

/-- The dual solution set `Ω_D = {(λ*, s*) | (λ*, s*) solves (2.2)}` (p. 24): feasible points
whose objective `bᵀλ*` is no smaller than that of any feasible point. -/
def OmegaD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | DualFeasible A c p.1 p.2 ∧
    ∀ lam' s', DualFeasible A c lam' s' → b ⬝ᵥ lam' ≤ b ⬝ᵥ p.1}

/-- The primal-dual solution set `Ω = Ω_P × Ω_D` (p. 24), as triples `(x*, λ*, s*)`. -/
def Omega {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ OmegaP A b c ∧ (p.2.1, p.2.2) ∈ OmegaD A b c}

/-- The index set `B` (2.11a): `j` with `x*_j ≠ 0` for some `x* ∈ Ω_P`. -/
def indexB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ x ∈ OmegaP A b c, x j ≠ 0}

/-- The index set `N` (2.11b): `j` with `s*_j ≠ 0` for some `(λ*, s*) ∈ Ω_D`. -/
def indexN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ OmegaD A b c, p.2 j ≠ 0}

/-- The reduced strictly feasible set `H° = {(x, s) | (x, λ, s) ∈ F° for some λ ∈ ℝᵐ}`
(p. 37). -/
def Hcirc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {q | ∃ lam : Fin m → ℝ, (q.1, lam, q.2) ∈ Fo A b c}

/-- The primal-dual barrier `f_τ(x, s) = (1/τ) xᵀs − ∑_{j=1}^n log(x_j s_j)` (p. 37). It is
meant on `H°`, where every `x_j s_j > 0`; off `H°` `Real.log` takes its junk values, so every
statement about `f_τ` restricts to `H°`. -/
noncomputable def ftau {n : ℕ} (τ : ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / τ) * (q.1 ⬝ᵥ q.2) - ∑ j, Real.log (q.1 j * q.2 j)

/-- The central path conditions (2.25a)–(2.25d) (p. 36) for the parameter `τ`:
`Aᵀλ + s = c`, `Ax = b`, `XSe = τe` (i.e. `x_j s_j = τ` for every `j`), `(x, s) > 0`. -/
def CentralPathConditions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ A *ᵥ x = b ∧ (∀ j, x j * s j = τ) ∧ (∀ j, 0 < x j) ∧ (∀ j, 0 < s j)


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
    (hF : (F A b c).Nonempty) : (Omega A b c).Nonempty := by
  obtain ⟨⟨x0, l0, s0⟩, ⟨hx0A, hx00⟩, hd0, hs0⟩ := hF
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

end g70wrCP

open WrightPDIPM.Potential

theorem g70wr_ii {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ) : mu x s ≤ Real.exp (Phi ρ x s / (ρ - n)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hxs : 0 < x ⬝ᵥ s := Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) Finset.univ_nonempty
  have hμ : 0 < mu x s := div_pos hxs hnr
  have hsum : ∑ i, Real.log (x i * s i) ≤ n * Real.log (mu x s) := by
    have h1 : ∀ i, Real.log (x i * s i) - Real.log (mu x s) ≤ x i * s i / mu x s - 1 := fun i => by
      rw [← Real.log_div (mul_pos (hx i) (hs i)).ne' hμ.ne']
      exact Real.log_le_sub_one_of_pos (div_pos (mul_pos (hx i) (hs i)) hμ)
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at h2
    have h3 : (∑ i, x i * s i) / mu x s = n := by
      rw [mu, dotProduct]; field_simp; exact div_self (ne_of_gt (by simpa [dotProduct] using hxs))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
    rw [h3] at h2
    linarith
  have hlogxs : Real.log (mu x s) ≤ Real.log (x ⬝ᵥ s) := by
    apply Real.log_le_log hμ
    rw [mu, div_le_iff₀ hnr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [← Real.log_le_iff_le_exp hμ, le_div_iff₀ (by linarith), Phi]
  have : 0 ≤ ρ := by linarith
  have := mul_le_mul_of_nonneg_left hlogxs this
  nlinarith

theorem g70wr_i {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) < ρ) (hF : (Fo A b c).Nonempty) (M : ℝ) :
    ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ Fo A b c ∧ Phi ρ x s < M := by
  obtain ⟨⟨xo, lo, so⟩, hA, hd, hxo, hso⟩ := hF
  simp only at hA hd hxo hso
  have hFcp : (g70wrCP.F A b c).Nonempty :=
    ⟨(xo, lo, so), ⟨hA, fun j => (hxo j).le⟩, hd, fun j => (hso j).le⟩
  obtain ⟨-, xb, hxb, p, hp, hpos⟩ := g70wrCP.g70wr_gt A b c (g70wrCP.g70wr_feas A b c hFcp)
  have hcomp : p.2 ⬝ᵥ xb = 0 := by
    have h1 := g70wrCP.g70wr_PD A b c xb hxb p hp
    have h2 := g70wrCP.g70wr_wd A b c xb p.1 p.2 hxb.1.1 hp.1.1
    linarith
  have hxb0 : ∀ i, 0 ≤ xb i := hxb.1.2
  have hsb0 : ∀ i, 0 ≤ p.2 i := hp.1.2
  have hcomp' : ∀ i, xb i * p.2 i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hsb0 j) (hxb0 j))).1 hcomp i
      (Finset.mem_univ i)
    simpa [mul_comm] using this
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set cc : Fin n → ℝ := fun i => (xb i * so i + xo i * p.2 i) / 2 with hcc
  have hcc0 : ∀ i, 0 < cc i := fun i => by
    have := hpos i
    rcases (hxb0 i).lt_or_eq with h | h
    · have := mul_pos h (hso i); have := mul_nonneg (hxo i).le (hsb0 i); simp only [hcc]; linarith
    · have : 0 < p.2 i := by rw [← h] at this; linarith
      have := mul_pos (hxo i) this; have := mul_nonneg (hxb0 i) (hso i).le; simp only [hcc]; linarith
  set K : ℝ := ∑ i, (xb i * so i + xo i * p.2 i + xo i * so i) with hK
  have hK0 : 0 < K := Finset.sum_pos (fun i _ => by
    have := mul_pos (hxo i) (hso i); have := mul_nonneg (hxb0 i) (hso i).le
    have := mul_nonneg (hxo i).le (hsb0 i); linarith) Finset.univ_nonempty
  set L : ℝ := ρ * Real.log K - ∑ i, Real.log (cc i) with hL
  set t : ℝ := min (1 / 2) (Real.exp ((M - 1 - L) / (ρ - n))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (Real.exp_pos _)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htl : Real.log t ≤ (M - 1 - L) / (ρ - n) := by
    rw [Real.log_le_iff_le_exp ht0]; exact min_le_right _ _
  set x : Fin n → ℝ := fun i => (1 - t) * xb i + t * xo i with hx
  set s : Fin n → ℝ := fun i => (1 - t) * p.2 i + t * so i with hs
  set lam : Fin m → ℝ := (1 - t) • p.1 + t • lo with hlam
  have hxv : x = (1 - t) • xb + t • xo := by funext i; simp [hx]
  have hsv : s = (1 - t) • p.2 + t • so := by funext i; simp [hs]
  have hx0 : ∀ i, 0 < x i := fun i => by
    have := mul_pos ht0 (hxo i); have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (hxb0 i)
    simp only [hx]; linarith
  have hs0 : ∀ i, 0 < s i := fun i => by
    have := mul_pos ht0 (hso i); have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (hsb0 i)
    simp only [hs]; linarith
  have hlow : ∀ i, t * cc i ≤ x i * s i := fun i => by
    simp only [hx, hs, hcc]
    have e : ((1 - t) * xb i + t * xo i) * ((1 - t) * p.2 i + t * so i) =
        (1 - t) ^ 2 * (xb i * p.2 i) + t * (1 - t) * (xb i * so i + xo i * p.2 i)
          + t ^ 2 * (xo i * so i) := by ring
    rw [e, hcomp' i]
    have h1 : t * (1 / 2) * (xb i * so i + xo i * p.2 i) ≤
        t * (1 - t) * (xb i * so i + xo i * p.2 i) := by
      apply mul_le_mul_of_nonneg_right _ (by
        have := mul_nonneg (hxb0 i) (hso i).le; have := mul_nonneg (hxo i).le (hsb0 i); linarith)
      apply mul_le_mul_of_nonneg_left (by linarith) ht0.le
    have h2 : 0 ≤ t ^ 2 * (xo i * so i) := by have := mul_pos (hxo i) (hso i); positivity
    nlinarith
  have hup : ∀ i, x i * s i ≤ t * (xb i * so i + xo i * p.2 i + xo i * so i) := fun i => by
    simp only [hx, hs]
    have e : ((1 - t) * xb i + t * xo i) * ((1 - t) * p.2 i + t * so i) =
        (1 - t) ^ 2 * (xb i * p.2 i) + t * (1 - t) * (xb i * so i + xo i * p.2 i)
          + t ^ 2 * (xo i * so i) := by ring
    rw [e, hcomp' i]
    have hq : 0 ≤ xb i * so i + xo i * p.2 i := by
      have := mul_nonneg (hxb0 i) (hso i).le; have := mul_nonneg (hxo i).le (hsb0 i); linarith
    have hr : 0 < xo i * so i := mul_pos (hxo i) (hso i)
    have h1 : t * (1 - t) * (xb i * so i + xo i * p.2 i) ≤ t * (xb i * so i + xo i * p.2 i) := by
      have : t * (1 - t) ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_right this hq
    have h2 : t ^ 2 * (xo i * so i) ≤ t * (xo i * so i) := by
      have : t ^ 2 ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_right this hr.le
    nlinarith
  refine ⟨x, lam, s, ⟨?_, ?_, hx0, hs0⟩, ?_⟩
  · rw [hxv, mulVec_add, mulVec_smul, mulVec_smul, hA, hxb.1.1, ← add_smul]; simp
  · rw [hlam, hsv, mulVec_add, mulVec_smul, mulVec_smul]
    have := hp.1.1
    calc (1 - t) • (Aᵀ *ᵥ p.1) + t • (Aᵀ *ᵥ lo) + ((1 - t) • p.2 + t • so)
        = (1 - t) • (Aᵀ *ᵥ p.1 + p.2) + t • (Aᵀ *ᵥ lo + so) := by
          simp only [smul_add]; abel
      _ = c := by rw [this, hd, ← add_smul]; simp
  · have hxs_pos : 0 < x ⬝ᵥ s :=
      Finset.sum_pos (fun i _ => mul_pos (hx0 i) (hs0 i)) Finset.univ_nonempty
    have hxsK : x ⬝ᵥ s ≤ t * K := by
      rw [dotProduct, hK, Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hup i
    have hlog1 : Real.log (x ⬝ᵥ s) ≤ Real.log t + Real.log K := by
      rw [← Real.log_mul ht0.ne' hK0.ne']; exact Real.log_le_log hxs_pos hxsK
    have hlog2 : ∑ i, (Real.log t + Real.log (cc i)) ≤ ∑ i, Real.log (x i * s i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Real.log_mul ht0.ne' (hcc0 i).ne']
      exact Real.log_le_log (mul_pos ht0 (hcc0 i)) (hlow i)
    rw [Finset.sum_add_distrib] at hlog2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlog2
    have hρ0 : 0 ≤ ρ := by linarith
    have hA1 := mul_le_mul_of_nonneg_left hlog1 hρ0
    have hB : (ρ - n) * Real.log t ≤ M - 1 - L := by
      rw [le_div_iff₀ (by linarith)] at htl; linarith
    rw [Phi]
    rw [hL] at hB
    nlinarith


/-- **Lemma 4.3** (Wright, p. 69), for `ρ > n` (the range of the parameter in (4.2)) and
`n ≥ 1`.
(i) If `F° ≠ ∅`, `Φ_ρ` is unbounded below on its domain (4.3), the pairs `(x, s)` with
`(x, λ, s) ∈ F°` for some `λ`. (The proof uses the central path, which exists when
`F° ≠ ∅`.)
(ii) For any `(x, λ, s) ∈ F°`, `μ ≤ exp(Φ_ρ(x, s)/(ρ − n))` (4.7), where `μ = xᵀs/n`. -/
theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) < ρ) :
    ((Fo A b c).Nonempty →
      ∀ M : ℝ, ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
        (x, lam, s) ∈ Fo A b c ∧ Phi ρ x s < M) ∧
    (∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ), (x, lam, s) ∈ Fo A b c →
      mu x s ≤ Real.exp (Phi ρ x s / (ρ - n))) := by
  exact ⟨fun hF M => g70wr_i hn A b c ρ hρ hF M, fun x lam s h => g70wr_ii hn x s h.2.2.1 h.2.2.2 ρ hρ⟩


