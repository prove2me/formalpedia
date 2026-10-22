-- Prove2me | solution 1 for YeIPA.Asymptotic.lemma_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:28:54.356564+00:00
-- url     : https://prove2.me/submissions/7535e21f-eec3-4223-82e7-d9997accceb4

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix
open YeIPA.Asymptotic

theorem g70ye_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
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

theorem g70ye_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g70ye_cara v Finset.univ l hl
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

theorem g70ye_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g70ye_cone_closed v) ha
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


theorem g70ye_lp_dualG {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ)
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
    exact hno (g70ye_farkas w q hne)
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

open YeIPA.Asymptotic

theorem g70ye_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hs : Aᵀ *ᵥ y + s = c) : c ⬝ᵥ x = b ⬝ᵥ y + x ⬝ᵥ s := by
  rw [← hs, ← hx, add_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm s x,
    dotProduct_comm (A *ᵥ x) y]

theorem g70ye_single_le {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j)
    (j : Fin n) : x j * s j ≤ x ⬝ᵥ s := by
  unfold dotProduct
  exact Finset.single_le_sum (f := fun i => x i * s i) (fun i _ => mul_nonneg (hx i) (hs i))
    (Finset.mem_univ j)

theorem g70ye_dot_nonneg {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j) :
    0 ≤ x ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))

theorem g70ye_L {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : Fin n → ℝ) (v a : ℝ) (x0 : Fin n → ℝ) (hx0 : A *ᵥ x0 = b) (hx0n : ∀ j, 0 ≤ x0 j)
    (hx0v : c ⬝ᵥ x0 ≤ v)
    (h : ∀ x, A *ᵥ x = b → (∀ j, 0 ≤ x j) → c ⬝ᵥ x ≤ v → a ≤ d ⬝ᵥ x) :
    ∃ u : Fin m → ℝ, ∃ w : Fin n → ℝ, ∃ t : ℝ, 0 ≤ t ∧ (∀ j, 0 ≤ w j) ∧
      Aᵀ *ᵥ u + w - t • c = d ∧ a ≤ b ⬝ᵥ u - t * v := by
  classical
  let M : Matrix ((Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Unit)) (Fin n) ℝ := Matrix.of fun i k =>
    match i with
    | Sum.inl (Sum.inl r) => A r k
    | Sum.inl (Sum.inr r) => -A r k
    | Sum.inr (Sum.inl j) => if j = k then 1 else 0
    | Sum.inr (Sum.inr _) => -c k
  let bb : ((Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Unit)) → ℝ :=
    Sum.elim (Sum.elim b (-b)) (Sum.elim 0 (fun _ => -v))
  have hM : ∀ x : Fin n → ℝ, (∀ r, (M *ᵥ x) (Sum.inl (Sum.inl r)) = (A *ᵥ x) r) ∧
      (∀ r, (M *ᵥ x) (Sum.inl (Sum.inr r)) = -(A *ᵥ x) r) ∧
      (∀ j, (M *ᵥ x) (Sum.inr (Sum.inl j)) = x j) ∧
      (∀ u, (M *ᵥ x) (Sum.inr (Sum.inr u)) = -(c ⬝ᵥ x)) := by
    intro x
    refine ⟨fun r => ?_, fun r => ?_, fun j => ?_, fun u => ?_⟩ <;>
      simp [M, mulVec, dotProduct]
  have hfeasM : ∀ x : Fin n → ℝ, bb ≤ M *ᵥ x ↔
      (A *ᵥ x = b ∧ (∀ j, 0 ≤ x j) ∧ c ⬝ᵥ x ≤ v) := by
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := hM x
    constructor
    · intro hle
      refine ⟨funext fun r => ?_, fun j => ?_, ?_⟩
      · have e1 := hle (Sum.inl (Sum.inl r)); have e2 := hle (Sum.inl (Sum.inr r))
        simp only [bb, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, h1, h2] at e1 e2
        linarith
      · have e := hle (Sum.inr (Sum.inl j))
        simp only [bb, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, h3] at e
        exact e
      · have e := hle (Sum.inr (Sum.inr ()))
        simp only [bb, Sum.elim_inr, h4] at e
        linarith
    · rintro ⟨e1, e2, e3⟩ i
      rcases i with (r | r) | (j | u)
      · simp only [bb, Sum.elim_inl, h1, e1]; exact le_refl _
      · simp only [bb, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, h2, e1]; exact le_refl _
      · simp only [bb, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, h3]; exact e2 j
      · simp only [bb, Sum.elim_inr, h4]; linarith
  obtain ⟨y, hy0, hyM, hyb⟩ := g70ye_lp_dualG M bb d ⟨x0, (hfeasM x0).2 ⟨hx0, hx0n, hx0v⟩⟩ a
    (fun x hx => by obtain ⟨e1, e2, e3⟩ := (hfeasM x).1 hx; exact h x e1 e2 e3)
  refine ⟨fun r => y (Sum.inl (Sum.inl r)) - y (Sum.inl (Sum.inr r)),
    fun j => y (Sum.inr (Sum.inl j)), y (Sum.inr (Sum.inr ())), hy0 _, fun j => hy0 _, ?_, ?_⟩
  · rw [← hyM]
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      transpose_apply, Fintype.sum_sum_type, M, of_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_mul, Finset.sum_neg_distrib, mul_sub,
      Finset.sum_sub_distrib]
    have : (default : Unit) = () := rfl
    ring_nf
  · simp only [dotProduct, Fintype.sum_sum_type, bb, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, Finset.univ_unique, Finset.sum_singleton,
      mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib] at hyb ⊢
    have : (default : Unit) = () := rfl
    rw [this] at hyb
    linarith

/-- strong duality data -/
theorem g70ye_strong {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk) :
    ∃ q : ℝ, (∃ z, IsPrimalOptimal A b c z ∧ c ⬝ᵥ z = q) ∧
      (∃ y s, IsDualOptimal A b c y s ∧ b ⬝ᵥ y = q) ∧
      (∀ x, PrimalFeasible A b x → q ≤ c ⬝ᵥ x) ∧ (∀ y s, DualFeasible A c y s → b ⬝ᵥ y ≤ q) := by
  obtain ⟨hAx, hxp, hAy, hsp⟩ := hint
  have weak : ∀ x y s, PrimalFeasible A b x → DualFeasible A c y s → b ⬝ᵥ y ≤ c ⬝ᵥ x := by
    rintro x y s ⟨h1, h2⟩ ⟨h3, h4⟩
    rw [g70ye_gap A b c x y s h1 h3]; linarith [g70ye_dot_nonneg x s h2 h4]
  set S := {r : ℝ | ∃ y s, DualFeasible A c y s ∧ r = b ⬝ᵥ y} with hS
  have hne : S.Nonempty := ⟨_, yk, sk, ⟨hAy, fun j => (hsp j).le⟩, rfl⟩
  have hbdd : ∀ x, PrimalFeasible A b x → ∀ r ∈ S, r ≤ c ⬝ᵥ x := by
    rintro x hx r ⟨y, s, hd, rfl⟩; exact weak x y s hx hd
  have hbdd' : BddAbove S := ⟨_, hbdd xk ⟨hAx, fun j => (hxp j).le⟩⟩
  set q := sSup S
  have hq_le : ∀ x, PrimalFeasible A b x → q ≤ c ⬝ᵥ x := fun x hx => csSup_le hne (hbdd x hx)
  have hle_q : ∀ y s, DualFeasible A c y s → b ⬝ᵥ y ≤ q :=
    fun y s hd => le_csSup hbdd' ⟨y, s, hd, rfl⟩
  -- primal attainment
  obtain ⟨z, hz0, hzA, hzc⟩ := g70ye_lp_dualG (-Aᵀ) (-c) (-b) ⟨yk, by
      intro j; have := congrFun hAy j; simp only [Pi.add_apply] at this
      simp only [Pi.neg_apply, neg_mulVec]; linarith [hsp j]⟩ (-q) (by
      intro y hy
      have hd : DualFeasible A c y (c - Aᵀ *ᵥ y) := ⟨by abel, fun j => by
        have := hy j; simp only [Pi.neg_apply, neg_mulVec] at this
        simp only [Pi.sub_apply]; linarith⟩
      have := hle_q _ _ hd
      simp only [neg_dotProduct]; linarith)
  have hzA' : A *ᵥ z = b := by
    rw [transpose_neg, transpose_transpose, neg_mulVec] at hzA; exact neg_injective hzA
  have hzf : PrimalFeasible A b z := ⟨hzA', fun j => hz0 j⟩
  rw [neg_dotProduct] at hzc
  have hzq : c ⬝ᵥ z = q := le_antisymm (by linarith) (hq_le z hzf)
  refine ⟨q, ⟨z, ⟨hzf, fun x' hx' => hzq ▸ hq_le x' hx'⟩, hzq⟩, ?_, hq_le, hle_q⟩
  -- dual attainment
  obtain ⟨u, w, t, ht, hw, huw, hub⟩ := g70ye_L A b c c q q z hzA' hz0 hzq.le
    (fun x h1 h2 _ => hq_le x ⟨h1, h2⟩)
  have h1t : 0 < 1 + t := by linarith
  have hd : DualFeasible A c ((1 + t)⁻¹ • u) ((1 + t)⁻¹ • w) := by
    refine ⟨?_, fun j => ?_⟩
    · funext k
      have hk := congrFun huw k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk
      rw [mulVec_smul]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← mul_add]
      have : (Aᵀ *ᵥ u) k + w k = (1 + t) * c k := by linear_combination hk
      rw [this, ← mul_assoc, inv_mul_cancel₀ h1t.ne', one_mul]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 h1t.le) (hw j)
  have hby : q ≤ b ⬝ᵥ ((1 + t)⁻¹ • u) := by
    rw [dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ h1t]; linarith
  have := hle_q _ _ hd
  exact ⟨_, _, ⟨hd, fun y' s' hd' => by linarith [hle_q y' s' hd']⟩, le_antisymm this hby⟩

theorem g70ye_cs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (x : Fin n → ℝ) (hx : IsPrimalOptimal A b c x) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hs : IsDualOptimal A b c y s) : ∀ j, x j * s j = 0 := by
  obtain ⟨q, ⟨z, hz, hzq⟩, ⟨y0, s0, hd0, hy0⟩, hq1, hq2⟩ := g70ye_strong A b c xk yk sk hint
  have e1 : c ⬝ᵥ x = q := le_antisymm (hzq ▸ hx.2 z hz.1) (hq1 x hx.1)
  have e2 : b ⬝ᵥ y = q := le_antisymm (hq2 y s hs.1) (hy0 ▸ hs.2 y0 s0 hd0.1)
  have := g70ye_gap A b c x y s hx.1.1 hs.1.1
  have h0 : x ⬝ᵥ s = 0 := by linarith
  intro j
  have := g70ye_single_le x s hx.1.2 hs.1.2 j
  exact le_antisymm (by linarith) (mul_nonneg (hx.1.2 j) (hs.1.2 j))

theorem g70ye_cover {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) : j ∈ Pstar A b c ∨ j ∈ Zstar A b c := by
  classical
  obtain ⟨q, ⟨z, hz, hzq⟩, ⟨y0, s0, hd0, hy0⟩, hq1, hq2⟩ := g70ye_strong A b c xk yk sk hint
  by_cases hP : j ∈ Pstar A b c
  · exact Or.inl hP
  right
  have hP' : ∀ x, IsPrimalOptimal A b c x → x j ≤ 0 := fun x hx => not_lt.1 fun h => hP ⟨x, hx, h⟩
  let e : Fin n → ℝ := fun k => if k = j then 1 else 0
  obtain ⟨u, w, t, ht, hw, huw, hub⟩ := g70ye_L A b c (-e) q 0 z hz.1.1 hz.1.2 hzq.le
    (fun x h1 h2 h3 => by
      have hopt : IsPrimalOptimal A b c x := ⟨⟨h1, h2⟩, fun x' hx' => by linarith [hq1 x' hx']⟩
      have := hP' x hopt
      simp [e, neg_dotProduct, dotProduct]; linarith)
  have h1t : 0 < 1 + t := by linarith
  have he0 : ∀ k, 0 ≤ e k := fun k => by simp only [e]; split_ifs <;> norm_num
  refine ⟨(1 + t)⁻¹ • (y0 + u), (1 + t)⁻¹ • (s0 + w + e), ⟨⟨?_, fun k => ?_⟩, fun y' s' hd' => ?_⟩, ?_⟩
  · funext k
    have hk := congrFun huw k
    have hk0 := congrFun hd0.1.1 k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hk hk0
    rw [mulVec_smul]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_add]
    rw [← mul_add]
    have : (Aᵀ *ᵥ y0) k + (Aᵀ *ᵥ u) k + (s0 k + w k + e k) = (1 + t) * c k := by
      linear_combination hk + hk0
    rw [this, ← mul_assoc, inv_mul_cancel₀ h1t.ne', one_mul]
  · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 h1t.le) (add_nonneg (add_nonneg (hd0.1.2 k) (hw k)) (he0 k))
  · have := hq2 y' s' hd'
    rw [dotProduct_smul, smul_eq_mul, dotProduct_add, le_inv_mul_iff₀ h1t]; nlinarith
  · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, e, if_true]
    exact mul_pos (inv_pos.2 h1t) (by linarith [hd0.1.2 j, hw j])

theorem g70ye_disj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) (hP : j ∈ Pstar A b c) (hZ : j ∈ Zstar A b c) : False := by
  obtain ⟨x, hx, hxj⟩ := hP
  obtain ⟨y, s, hs, hsj⟩ := hZ
  have := g70ye_cs A b c xk yk sk hint x hx y s hs j
  have := mul_pos hxj hsj; linarith


theorem g70ye_xs_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (hx0 : A *ᵥ x0 = b)
    (hx0p : ∀ j, 0 < x0 j) (hs0 : Aᵀ *ᵥ y0 + s0 = c) (hs0p : ∀ j, 0 < s0 j) (K : ℝ) :
    ∃ R, 0 ≤ R ∧ ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), A *ᵥ x = b →
      (∀ j, 0 ≤ x j) → Aᵀ *ᵥ y + s = c → (∀ j, 0 ≤ s j) → x ⬝ᵥ s ≤ K →
      ∀ j, |x j| ≤ R ∧ |s j| ≤ R := by
  set L := |K| + x0 ⬝ᵥ s0
  have hL : 0 ≤ L := add_nonneg (abs_nonneg K)
    (g70ye_dot_nonneg x0 s0 (fun j => (hx0p j).le) (fun j => (hs0p j).le))
  set T := ∑ j, (1 / s0 j + 1 / x0 j)
  have hT : ∀ j, 1 / s0 j ≤ T ∧ 1 / x0 j ≤ T := by
    intro j
    have h1 : 1 / s0 j + 1 / x0 j ≤ T :=
      Finset.single_le_sum (f := fun j => 1 / s0 j + 1 / x0 j)
        (fun i _ => add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
        (Finset.mem_univ j)
    have := hs0p j; have := hx0p j
    have a1 : 0 ≤ 1 / s0 j := by positivity
    have a2 : 0 ≤ 1 / x0 j := by positivity
    constructor <;> linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ =>
    add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
  refine ⟨L * T, mul_nonneg hL hT0, ?_⟩
  intro x y s hx hxn hs hsn hK j
  have e1 := g70ye_gap A b c x y s hx hs
  have e2 := g70ye_gap A b c x0 y0 s0 hx0 hs0
  have e3 := g70ye_gap A b c x y0 s0 hx hs0
  have e4 := g70ye_gap A b c x0 y s hx0 hs
  have hid : x ⬝ᵥ s0 + x0 ⬝ᵥ s = x ⬝ᵥ s + x0 ⬝ᵥ s0 := by linarith
  have d1 := g70ye_dot_nonneg x0 s (fun j => (hx0p j).le) hsn
  have d2 := g70ye_dot_nonneg x s0 hxn (fun j => (hs0p j).le)
  have hKa := le_abs_self K
  have b1 := g70ye_single_le x s0 hxn (fun j => (hs0p j).le) j
  have b2 := g70ye_single_le x0 s (fun j => (hx0p j).le) hsn j
  have hx1 : x j * s0 j ≤ L := by linarith
  have hs1 : x0 j * s j ≤ L := by linarith
  have hsj := hs0p j
  have hxj := hx0p j
  obtain ⟨t1, t2⟩ := hT j
  rw [abs_of_nonneg (hxn j), abs_of_nonneg (hsn j)]
  constructor
  · have : x j ≤ L * (1 / s0 j) := by
      rw [mul_one_div, le_div_iff₀ hsj]; exact hx1
    exact this.trans (mul_le_mul_of_nonneg_left t1 hL)
  · have : s j ≤ L * (1 / x0 j) := by
      rw [mul_one_div, le_div_iff₀ hxj]; linarith
    exact this.trans (mul_le_mul_of_nonneg_left t2 hL)


theorem g70ye_lowP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hint : IsInterior A b c x y s)
    (xs : Fin n → ℝ) (hxs : IsPrimalOptimal A b c xs) (j : Fin n) : xs j * s j ≤ x ⬝ᵥ s := by
  obtain ⟨q, -, ⟨y0, s0, hd0, -⟩, -, -⟩ := g70ye_strong A b c x y s hint
  have h0 : xs ⬝ᵥ s0 = 0 := Finset.sum_eq_zero fun i _ =>
    g70ye_cs A b c x y s hint xs hxs y0 s0 hd0 i
  have e1 := g70ye_gap A b c x y s hint.1 hint.2.2.1
  have e2 := g70ye_gap A b c xs y0 s0 hxs.1.1 hd0.1.1
  have e3 := g70ye_gap A b c x y0 s0 hint.1 hd0.1.1
  have e4 := g70ye_gap A b c xs y s hxs.1.1 hint.2.2.1
  have := g70ye_single_le xs s hxs.1.2 (fun i => (hint.2.2.2 i).le) j
  have := g70ye_dot_nonneg x s0 (fun i => (hint.2.1 i).le) hd0.1.2
  linarith

theorem g70ye_lowZ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hint : IsInterior A b c x y s)
    (ys : Fin m → ℝ) (ss : Fin n → ℝ) (hss : IsDualOptimal A b c ys ss) (j : Fin n) :
    ss j * x j ≤ x ⬝ᵥ s := by
  obtain ⟨q, ⟨z, hz, -⟩, -, -, -⟩ := g70ye_strong A b c x y s hint
  have h0 : z ⬝ᵥ ss = 0 := Finset.sum_eq_zero fun i _ =>
    g70ye_cs A b c x y s hint z hz ys ss hss i
  have e1 := g70ye_gap A b c x y s hint.1 hint.2.2.1
  have e2 := g70ye_gap A b c z ys ss hz.1.1 hss.1.1
  have e3 := g70ye_gap A b c x ys ss hint.1 hss.1.1
  have e4 := g70ye_gap A b c z y s hz.1.1 hint.2.2.1
  have := g70ye_single_le x ss (fun i => (hint.2.1 i).le) hss.1.2 j
  have := g70ye_dot_nonneg z s hz.1.2 (fun i => (hint.2.2.2 i).le)
  linarith [mul_comm (ss j) (x j)]

theorem g70ye_n2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (h : InN2 A b c (1 / 4) x y s) (j : Fin n) :
    3 / 4 * mu x s ≤ x j * s j := by
  have h1 : |x j * s j - mu x s| ≤ Real.sqrt (∑ i, (x i * s i - mu x s) ^ 2) :=
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => (x i * s i - mu x s) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have h2 := h.2
  have := neg_abs_le (x j * s j - mu x s)
  linarith


/-- Lemma 7.4 (pp. 215–216). Let `(x, y, s)` be an interior feasible point, `rank A = m`,
`(P, Z) = (P*, Z*)`, `Dⱼ = √(xⱼ/sⱼ)`, and let `(d_x, d_y, d_s)` solve the predictor system
(7.4). Then
1. `(d_x)_P` is the unique solution of the weighted least-squares problem
   `min_u (1/2)‖D_P⁻¹ u‖²` s.t. `A_P u = −A_Z (d_x)_Z` (vectors `u` written as full vectors
   vanishing off `P`, so `A_P u = A u`);
2. `d_y` solves the weighted least-squares problem `min_v (1/2)‖D_Z A_Zᵀ v‖²` s.t.
   `A_Pᵀ v = −(d_s)_P`, and every solution `v` of it gives `(d_s)_Z = −A_Zᵀ v`.
Part 2 is the page's second problem with its misprints corrected (the page prints the
objective `‖D_Z v‖²` and `(d_s)_Z = A_Zᵀ v`; see the natural-language statement). -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hint : IsInterior A b c x y s) (hdir : IsPredictorDirection A x s dx dy ds) :
    -- part 1: the feasible set of the first problem, and its objective
    (let U : Set (Fin n → ℝ) := {u | (∀ j, j ∉ Pstar A b c → u j = 0) ∧
          A *ᵥ u = -(A *ᵥ (Zstar A b c).indicator dx)}
     let f : (Fin n → ℝ) → ℝ := fun u => (1 / 2) * ∑ j, (u j / scaling x s j) ^ 2
     (Pstar A b c).indicator dx ∈ U ∧
       ∀ u ∈ U, u ≠ (Pstar A b c).indicator dx → f ((Pstar A b c).indicator dx) < f u) ∧
    -- part 2: the feasible set of the second problem, and its objective
    (let V : Set (Fin m → ℝ) := {v | ∀ j ∈ Pstar A b c, (Aᵀ *ᵥ v) j = -ds j}
     let g : (Fin m → ℝ) → ℝ := fun v =>
       (1 / 2) * ∑ j, ((Zstar A b c).indicator (fun i => scaling x s i * (Aᵀ *ᵥ v) i) j) ^ 2
     dy ∈ V ∧ (∀ v ∈ V, g dy ≤ g v) ∧
       ∀ v ∈ V, g v = g dy → ∀ j ∈ Zstar A b c, ds j = -(Aᵀ *ᵥ v) j) := by
  classical
  obtain ⟨hdir1, hdir2, hdir3⟩ := hdir
  have hds : ds = -(Aᵀ *ᵥ dy) := (sub_eq_zero.1 hdir3).symm
  have hx := hint.2.1
  have hs := hint.2.2.2
  obtain ⟨q, ⟨z, hz, -⟩, ⟨y0, s0, hd0, -⟩, -, -⟩ := g70ye_strong A b c x y s hint
  have hzZ : ∀ j ∈ Zstar A b c, z j = 0 := by
    rintro j ⟨y', s', hs', hsj⟩
    rcases mul_eq_zero.1 (g70ye_cs A b c x y s hint z hz y' s' hs' j) with h | h
    · exact h
    · linarith
  have hs0P : ∀ j ∈ Pstar A b c, s0 j = 0 := by
    rintro j ⟨x', hx', hxj⟩
    rcases mul_eq_zero.1 (g70ye_cs A b c x y s hint x' hx' y0 s0 hd0 j) with h | h
    · linarith
    · exact h
  have cover := g70ye_cover A b c x y s hint
  have disj := g70ye_disj A b c x y s hint
  have hD : ∀ j, scaling x s j ^ 2 = x j / s j := fun j => by
    unfold scaling; rw [Real.sq_sqrt (div_nonneg (hx j).le (hs j).le)]
  have hDp : ∀ j, 0 < scaling x s j := fun j => Real.sqrt_pos.2 (div_pos (hx j) (hs j))
  have orth : ∀ (w : Fin n → ℝ) (v : Fin m → ℝ), w ⬝ᵥ (Aᵀ *ᵥ v) = (A *ᵥ w) ⬝ᵥ v := by
    intro w v; rw [mulVec_transpose, dotProduct_comm, dotProduct_comm (A *ᵥ w), dotProduct_mulVec]
  -- the direction equation solved for dx_j s_j/x_j
  have key : ∀ j, dx j * (s j / x j) = -s j - ds j := by
    intro j; rw [mul_div_assoc', div_eq_iff (hx j).ne']; linear_combination hdir1 j
  have key2 : ∀ j, x j / s j * ds j = -x j - dx j := by
    intro j; rw [div_mul_eq_mul_div, div_eq_iff (hs j).ne']; linear_combination hdir1 j
  constructor
  · intro U f
    set dP := (Pstar A b c).indicator dx
    set dZ := (Zstar A b c).indicator dx
    have hsplit : dP + dZ = dx := by
      funext j
      simp only [Pi.add_apply, dP, dZ]
      rcases cover j with h | h
      · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (fun h' => disj j h h')]; ring
      · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (fun h' => disj j h' h)]; ring
    have hmem : dP ∈ U := by
      refine ⟨fun j hj => Set.indicator_of_notMem hj _, ?_⟩
      have : A *ᵥ dP + A *ᵥ dZ = 0 := by rw [← mulVec_add, hsplit, hdir2]
      linear_combination this
    have hf : ∀ u, f u = 1 / 2 * ∑ j, u j ^ 2 * (s j / x j) := by
      intro u; simp only [f]; congr 1; apply Finset.sum_congr rfl; intro j _
      rw [div_pow, hD]; field_simp
    refine ⟨hmem, fun u hu hne => ?_⟩
    set w := u - dP
    have hwP : ∀ j, j ∉ Pstar A b c → w j = 0 := fun j hj => by
      simp only [w, Pi.sub_apply, hu.1 j hj, hmem.1 j hj, sub_zero]
    have hAw : A *ᵥ w = 0 := by
      simp only [w, mulVec_sub, hu.2, hmem.2, sub_self]
    have hws : w ⬝ᵥ s = 0 := by
      have e1 : w ⬝ᵥ c = w ⬝ᵥ s := by
        rw [← hint.2.2.1, dotProduct_add, orth, hAw, zero_dotProduct, zero_add]
      have e2 : w ⬝ᵥ c = 0 := by
        rw [← hd0.1.1, dotProduct_add, orth, hAw, zero_dotProduct, zero_add]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ∈ Pstar A b c
        · rw [hs0P j hj, mul_zero]
        · rw [hwP j hj, zero_mul]
      linarith
    have hwds : w ⬝ᵥ ds = 0 := by rw [hds, dotProduct_neg, orth, hAw, zero_dotProduct, neg_zero]
    have hcross : ∑ j, w j * (dP j * (s j / x j)) = 0 := by
      have : ∀ j, w j * (dP j * (s j / x j)) = -(w j * s j) - w j * ds j := by
        intro j
        by_cases hj : j ∈ Pstar A b c
        · simp only [dP, Set.indicator_of_mem hj]; rw [key j]; ring
        · rw [hwP j hj]; ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      have h1 : ∑ j, w j * s j = 0 := hws
      have h2 : ∑ j, w j * ds j = 0 := hwds
      rw [h1, h2]; ring
    have hu' : u = dP + w := by simp [w]
    have hpos : 0 < ∑ j, w j ^ 2 * (s j / x j) := by
      obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
        by_contra hc; push_neg at hc; apply hne; rw [hu']; funext i; simp [hc i]
      exact Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (div_pos (hs i) (hx i)).le)
        ⟨j, Finset.mem_univ j, mul_pos (by positivity) (div_pos (hs j) (hx j))⟩
    rw [hf, hf, hu']
    have : ∑ j, (dP + w) j ^ 2 * (s j / x j) = ∑ j, dP j ^ 2 * (s j / x j) +
        2 * ∑ j, w j * (dP j * (s j / x j)) + ∑ j, w j ^ 2 * (s j / x j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; simp only [Pi.add_apply]; ring
    rw [this, hcross]; linarith
  · intro V g
    have hg : ∀ v, g v = 1 / 2 * ∑ j, (if j ∈ Zstar A b c then
        x j / s j * (Aᵀ *ᵥ v) j ^ 2 else 0) := by
      intro v; simp only [g]; congr 1; apply Finset.sum_congr rfl; intro j _
      by_cases hj : j ∈ Zstar A b c
      · rw [Set.indicator_of_mem hj, if_pos hj, mul_pow, hD]
      · rw [Set.indicator_of_notMem hj, if_neg hj]; ring
    have hdyV : dy ∈ V := fun j _ => by rw [hds]; simp
    -- decomposition
    have hdec : ∀ v ∈ V, g v = g dy + 1 / 2 * ∑ j, (if j ∈ Zstar A b c then
        x j / s j * (Aᵀ *ᵥ (v - dy)) j ^ 2 else 0) := by
      intro v hv
      set e := Aᵀ *ᵥ (v - dy)
      have heP : ∀ j ∈ Pstar A b c, e j = 0 := fun j hj => by
        simp only [e, mulVec_sub, Pi.sub_apply, hv j hj, hds, Pi.neg_apply, neg_neg, sub_self]
      have hcr : ∑ j, (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ dy) j * e j else 0) = 0 := by
        have : ∀ j, (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ dy) j * e j else 0) =
            (x j + dx j - z j) * e j := by
          intro j
          by_cases hj : j ∈ Zstar A b c
          · rw [if_pos hj, hzZ j hj]
            have h1 : (Aᵀ *ᵥ dy) j = -ds j := by rw [hds]; simp
            rw [h1]
            have := key2 j
            linear_combination (-e j) * this
          · rw [if_neg hj, heP j ((cover j).resolve_right hj)]; ring
        rw [Finset.sum_congr rfl (fun j _ => this j)]
        have : (x + dx - z) ⬝ᵥ e = 0 := by
          simp only [e]; rw [orth, mulVec_sub, mulVec_add, hint.1, hdir2, hz.1.1]; simp
        exact this
      have hv' : Aᵀ *ᵥ v = Aᵀ *ᵥ dy + e := by simp [e, mulVec_sub]
      rw [hg, hg, hv']
      have : ∀ j, (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ dy + e) j ^ 2 else 0) =
          (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ dy) j ^ 2 else 0) +
          2 * (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ dy) j * e j else 0) +
          (if j ∈ Zstar A b c then x j / s j * e j ^ 2 else 0) := by
        intro j; rw [Pi.add_apply]; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, hcr]
      ring
    have hnn : ∀ v : Fin m → ℝ, ∀ j, 0 ≤ (if j ∈ Zstar A b c then
        x j / s j * (Aᵀ *ᵥ v) j ^ 2 else 0) := by
      intro v j; split_ifs
      · exact mul_nonneg (div_pos (hx j) (hs j)).le (sq_nonneg _)
      · exact le_refl 0
    refine ⟨hdyV, fun v hv => ?_, fun v hv hgv j hj => ?_⟩
    · rw [hdec v hv]
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hnn (v - dy) j)
      linarith
    · rw [hdec v hv] at hgv
      have h0 : ∑ j, (if j ∈ Zstar A b c then x j / s j * (Aᵀ *ᵥ (v - dy)) j ^ 2 else 0) = 0 := by
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn (v - dy) j)).1 h0 j
        (Finset.mem_univ j)
      rw [if_pos hj] at this
      have h2 : (Aᵀ *ᵥ (v - dy)) j = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (div_pos (hx j) (hs j)).ne'
        · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
      rw [mulVec_sub, Pi.sub_apply, sub_eq_zero] at h2
      rw [h2, hds]; simp



