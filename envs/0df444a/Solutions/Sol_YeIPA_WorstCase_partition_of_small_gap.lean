-- Prove2me | solution 1 for YeIPA.WorstCase.partition_of_small_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:10:37.134122+00:00
-- url     : https://prove2.me/submissions/901b840c-af3e-480d-baa9-8004d70d892f

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix
open YeIPA.WorstCase

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

open YeIPA.WorstCase

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
    ∃ q : ℝ, (∃ z, PrimalOptimal A b c z ∧ c ⬝ᵥ z = q) ∧
      (∃ y s, DualOptimal A b c y s ∧ b ⬝ᵥ y = q) ∧
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
    (x : Fin n → ℝ) (hx : PrimalOptimal A b c x) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hs : DualOptimal A b c y s) : ∀ j, x j * s j = 0 := by
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
  have hP' : ∀ x, PrimalOptimal A b c x → x j ≤ 0 := fun x hx => not_lt.1 fun h => hP ⟨x, hx, h⟩
  let e : Fin n → ℝ := fun k => if k = j then 1 else 0
  obtain ⟨u, w, t, ht, hw, huw, hub⟩ := g70ye_L A b c (-e) q 0 z hz.1.1 hz.1.2 hzq.le
    (fun x h1 h2 h3 => by
      have hopt : PrimalOptimal A b c x := ⟨⟨h1, h2⟩, fun x' hx' => by linarith [hq1 x' hx']⟩
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

theorem g70ye_omegaP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (x : Fin n → ℝ) : x ∈ OmegaP A b c ↔ PrimalOptimal A b c x := by
  obtain ⟨q, ⟨z, hz, hzq⟩, ⟨y0, s0, hd0, hy0⟩, hq1, hq2⟩ := g70ye_strong A b c xk yk sk hint
  constructor
  · rintro ⟨hf, hZ⟩
    have h0 : x ⬝ᵥ s0 = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (hd0.1.2 i).lt_or_eq with h | h
      · rw [hZ i ⟨y0, s0, hd0, h⟩, zero_mul]
      · rw [← h, mul_zero]
    have := g70ye_gap A b c x y0 s0 hf.1 hd0.1.1
    exact ⟨hf, fun x' hx' => by linarith [hq1 x' hx']⟩
  · intro hx
    refine ⟨hx.1, fun j ⟨y, s, hs, hsj⟩ => ?_⟩
    have := g70ye_cs A b c xk yk sk hint x hx y s hs j
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith

theorem g70ye_omegaD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) : p ∈ OmegaD A b c ↔ DualOptimal A b c p.1 p.2 := by
  obtain ⟨q, ⟨z, hz, hzq⟩, ⟨y0, s0, hd0, hy0⟩, hq1, hq2⟩ := g70ye_strong A b c xk yk sk hint
  constructor
  · rintro ⟨hf, hP⟩
    have h0 : z ⬝ᵥ p.2 = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (hz.1.2 i).lt_or_eq with h | h
      · rw [hP i ⟨z, hz, h⟩, mul_zero]
      · rw [← h, zero_mul]
    have := g70ye_gap A b c z p.1 p.2 hz.1.1 hf.1
    exact ⟨hf, fun y' s' hd' => by linarith [hq2 y' s' hd']⟩
  · intro hp
    refine ⟨hp.1, fun j ⟨x, hx, hxj⟩ => ?_⟩
    have := g70ye_cs A b c xk yk sk hint x hx p.1 p.2 hp j
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h

theorem g70ye_split {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (xs : Fin n → ℝ) (ys : Fin m → ℝ) (ss : Fin n → ℝ)
    (hxs : xs ∈ OmegaP A b c) (hss : (ys, ss) ∈ OmegaD A b c) :
    (xk - xs) ⬝ᵥ (sk - ss) = 0 ∧ xs ⬝ᵥ ss = 0 ∧ xk ⬝ᵥ sk = xs ⬝ᵥ sk + xk ⬝ᵥ ss := by
  have e1 := g70ye_gap A b c xk yk sk hint.1 hint.2.2.1
  have e2 := g70ye_gap A b c xs ys ss hxs.1.1 hss.1.1
  have e3 := g70ye_gap A b c xk ys ss hint.1 hss.1.1
  have e4 := g70ye_gap A b c xs yk sk hxs.1.1 hint.2.2.1
  have h0 : xs ⬝ᵥ ss = 0 := Finset.sum_eq_zero fun i _ => by
    rcases g70ye_cover A b c xk yk sk hint i with h | h
    · rw [show ss i = 0 from hss.2 i h, mul_zero]
    · rw [hxs.2 i h, zero_mul]
  refine ⟨?_, h0, ?_⟩
  · rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]; linarith
  · linarith

theorem g70ye_xsk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (xs : Fin n → ℝ) (hxs : xs ∈ OmegaP A b c) (j : Fin n) : xs j * sk j ≤ xk ⬝ᵥ sk := by
  obtain ⟨q, -, ⟨y0, s0, hd0, -⟩, -, -⟩ := g70ye_strong A b c xk yk sk hint
  have hm := (g70ye_omegaD A b c xk yk sk hint (y0, s0)).2 hd0
  obtain ⟨-, -, h⟩ := g70ye_split A b c xk yk sk hint xs y0 s0 hxs hm
  have := g70ye_single_le xs sk hxs.1.2 (fun i => (hint.2.2.2 i).le) j
  have := g70ye_dot_nonneg xk s0 (fun i => (hint.2.1 i).le) hd0.1.2
  linarith

theorem g70ye_ssk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ OmegaD A b c) (j : Fin n) :
    p.2 j * xk j ≤ xk ⬝ᵥ sk := by
  obtain ⟨q, ⟨z, hz, -⟩, -, -, -⟩ := g70ye_strong A b c xk yk sk hint
  have hm := (g70ye_omegaP A b c xk yk sk hint z).2 hz
  obtain ⟨-, -, h⟩ := g70ye_split A b c xk yk sk hint z p.1 p.2 hm hp
  have := g70ye_single_le xk p.2 (fun i => (hint.2.1 i).le) hp.1.2 j
  have := g70ye_dot_nonneg z sk hz.1.2 (fun i => (hint.2.2.2 i).le)
  linarith [mul_comm (p.2 j) (xk j)]

theorem g70ye_maxP_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) : maxPrimalCoord A b c j ≤ xk ⬝ᵥ sk / sk j := by
  have hs := hint.2.2.2 j
  have hpos : 0 ≤ xk ⬝ᵥ sk := g70ye_dot_nonneg xk sk (fun i => (hint.2.1 i).le)
    (fun i => (hint.2.2.2 i).le)
  apply Real.sSup_le _ (div_nonneg hpos hs.le)
  rintro _ ⟨xs, hxs, rfl⟩
  rw [le_div_iff₀ hs]; exact g70ye_xsk A b c xk yk sk hint xs hxs j

theorem g70ye_maxD_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) : maxDualCoord A b c j ≤ xk ⬝ᵥ sk / xk j := by
  have hs := hint.2.1 j
  have hpos : 0 ≤ xk ⬝ᵥ sk := g70ye_dot_nonneg xk sk (fun i => (hint.2.1 i).le)
    (fun i => (hint.2.2.2 i).le)
  apply Real.sSup_le _ (div_nonneg hpos hs.le)
  rintro _ ⟨p, hp, rfl⟩
  rw [le_div_iff₀ hs]; exact g70ye_ssk A b c xk yk sk hint p hp j

theorem g70ye_maxP_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) (hj : j ∈ Pstar A b c) : 0 < maxPrimalCoord A b c j := by
  obtain ⟨x, hx, hxj⟩ := hj
  have hm := (g70ye_omegaP A b c xk yk sk hint x).2 hx
  refine lt_of_lt_of_le hxj (le_csSup ⟨xk ⬝ᵥ sk / sk j, ?_⟩ ⟨x, hm, rfl⟩)
  rintro _ ⟨xs, hxs, rfl⟩
  rw [le_div_iff₀ (hint.2.2.2 j)]; exact g70ye_xsk A b c xk yk sk hint xs hxs j

theorem g70ye_maxD_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) (hj : j ∈ Zstar A b c) : 0 < maxDualCoord A b c j := by
  obtain ⟨y, s, hs, hsj⟩ := hj
  have hm := (g70ye_omegaD A b c xk yk sk hint (y, s)).2 hs
  refine lt_of_lt_of_le hsj (le_csSup ⟨xk ⬝ᵥ sk / xk j, ?_⟩ ⟨(y, s), hm, rfl⟩)
  rintro _ ⟨p, hp, rfl⟩
  rw [le_div_iff₀ (hint.2.1 j)]; exact g70ye_ssk A b c xk yk sk hint p hp j

theorem g70ye_xi_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) :
    (j ∈ Pstar A b c → xi A b c ≤ maxPrimalCoord A b c j) ∧
    (j ∈ Zstar A b c → xi A b c ≤ maxDualCoord A b c j) := by
  classical
  have h := ciInf_le (Set.finite_range (fun j : Fin n =>
    haveI := Classical.propDecidable (j ∈ Pstar A b c)
    if j ∈ Pstar A b c then maxPrimalCoord A b c j else maxDualCoord A b c j)).bddBelow j
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · exact h.trans_eq (if_pos hj)
  · have hnP : j ∉ Pstar A b c := fun hP => g70ye_disj A b c xk yk sk hint j hP hj
    exact h.trans_eq (if_neg hnP)

theorem g70ye_xi_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hn : 0 < n) (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ)
    (hint : IsInterior A b c xk yk sk) : 0 < xi A b c := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold xi
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin n =>
    haveI := Classical.propDecidable (j ∈ Pstar A b c)
    if j ∈ Pstar A b c then maxPrimalCoord A b c j else maxDualCoord A b c j)
  rw [← hj]
  split_ifs with h
  · exact g70ye_maxP_pos A b c xk yk sk hint j h
  · exact g70ye_maxD_pos A b c xk yk sk hint j
      ((g70ye_cover A b c xk yk sk hint j).resolve_left h)

theorem g70ye_xi_sk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) (hj : j ∈ Pstar A b c) : xi A b c * sk j ≤ xk ⬝ᵥ sk := by
  have h1 := (g70ye_xi_le A b c xk yk sk hint j).1 hj
  have h2 := g70ye_maxP_le A b c xk yk sk hint j
  rw [← le_div_iff₀ (hint.2.2.2 j)]; linarith

theorem g70ye_xi_xk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ) (hint : IsInterior A b c xk yk sk)
    (j : Fin n) (hj : j ∈ Zstar A b c) : xi A b c * xk j ≤ xk ⬝ᵥ sk := by
  have h1 := (g70ye_xi_le A b c xk yk sk hint j).2 hj
  have h2 := g70ye_maxD_le A b c xk yk sk hint j
  rw [← le_div_iff₀ (hint.2.1 j)]; linarith

/-- from property 5.7: if v * s_j ≤ xᵀs then n^{-η} v < x_j -/
theorem g70ye_p57 {n : ℕ} (hn : 0 < n) (η : ℝ) (xk sk : Fin n → ℝ) (hx : ∀ j, 0 < xk j)
    (hs : ∀ j, 0 < sk j) (h57 : Property57 η xk sk) (j : Fin n) (v : ℝ)
    (hv : v * sk j ≤ xk ⬝ᵥ sk) : (n : ℝ) ^ (-η) * v < xk j := by
  have hdot : 0 < xk ⬝ᵥ sk := lt_of_lt_of_le (mul_pos (hx j) (hs j))
    (g70ye_single_le xk sk (fun i => (hx i).le) (fun i => (hs i).le) j)
  have h := h57 j
  rw [lt_div_iff₀ hdot] at h
  have hr : 0 < (n : ℝ) ^ (-η) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have : (n : ℝ) ^ (-η) * v * sk j < xk j * sk j := by
    calc (n : ℝ) ^ (-η) * v * sk j = (n : ℝ) ^ (-η) * (v * sk j) := by ring
      _ ≤ (n : ℝ) ^ (-η) * (xk ⬝ᵥ sk) := mul_le_mul_of_nonneg_left hv hr.le
      _ < _ := h
  exact lt_of_mul_lt_mul_right this (hs j).le


/-- Proof of Theorem 5.3 (Ye 1997, pp. 154–155), the deterministic core. Let `(xᵏ, yᵏ, sᵏ)` be
an interior point of (LP)/(LD), `n ≥ 1`, satisfying property (5.7) with a constant `η > 0`,
and let `ξ = ξ(A, b, c)`. If `(xᵏ)ᵀsᵏ ≤ n^{-η} ξ²`, then `s_jᵏ < x_jᵏ` for every `j ∈ P*`,
`x_jᵏ < s_jᵏ` for every `j ∈ Z*`, and `σᵏ = {j : x_jᵏ ≥ s_jᵏ} = P*`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (xk : Fin n → ℝ) (yk : Fin m → ℝ) (sk : Fin n → ℝ)
    (hint : IsInterior A b c xk yk sk) (h57 : Property57 η xk sk)
    (hgap : xk ⬝ᵥ sk ≤ (n : ℝ) ^ (-η) * xi A b c ^ 2) :
    (∀ j ∈ Pstar A b c, sk j < xk j) ∧ (∀ j ∈ Zstar A b c, xk j < sk j) ∧
    sigma xk sk = Pstar A b c := by
  have hξ := g70ye_xi_pos A b c hn xk yk sk hint
  have h57' : Property57 η sk xk := by
    intro j; rw [dotProduct_comm, mul_comm]; exact h57 j
  have hP : ∀ j ∈ Pstar A b c, sk j < xk j := by
    intro j hj
    have h1 := g70ye_xi_sk A b c xk yk sk hint j hj
    have h2 := g70ye_p57 hn η xk sk hint.2.1 hint.2.2.2 h57 j _ h1
    have h3 : sk j * xi A b c ≤ ((n : ℝ) ^ (-η) * xi A b c) * xi A b c := by
      rw [sq] at hgap; linarith
    have := le_of_mul_le_mul_right h3 hξ
    linarith
  have hZ : ∀ j ∈ Zstar A b c, xk j < sk j := by
    intro j hj
    have h1 := g70ye_xi_xk A b c xk yk sk hint j hj
    have h2 := g70ye_p57 hn η sk xk hint.2.2.2 hint.2.1 h57' j (xi A b c)
      (by rw [dotProduct_comm]; exact h1)
    have h3 : xk j * xi A b c ≤ ((n : ℝ) ^ (-η) * xi A b c) * xi A b c := by
      rw [sq] at hgap; linarith
    have := le_of_mul_le_mul_right h3 hξ
    linarith
  refine ⟨hP, hZ, ?_⟩
  ext j
  constructor
  · intro hj
    by_contra hnP
    have := hZ j ((g70ye_cover A b c xk yk sk hint j).resolve_left hnP)
    exact absurd hj (not_le.2 this)
  · intro hj; exact (hP j hj).le



