-- Prove2me | solution 1 for SWSSNet.Diffusion.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:03:47.189199+00:00
-- url     : https://prove2.me/submissions/b6f25bb5-f9be-4f83-9f81-2760fce8f316

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network
import Theorems.Thm_SWSSNet_Diffusion_atar_prop_A_2

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSProp2Aux

open SWSSNet.Diffusion

variable {I J : ℕ}

theorem bip_adj_iff (adj : Fin I → Fin J → Prop) (a b : Fin I ⊕ Fin J) :
    (bipGraph adj).Adj a b ↔
      (∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ adj i j) ∨
      (∃ i j, b = Sum.inl i ∧ a = Sum.inr j ∧ adj i j) := by
  unfold bipGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨i, j, rfl, rfl, _⟩ | ⟨i, j, rfl, rfl, _⟩ <;> simp

/-- `flowMap` is the unique flow on `D`. -/
theorem flowMap_eq (N : TreeNetwork I J) {α : Fin I → ℝ} {β : Fin J → ℝ} (hD : ∑ i, α i = ∑ j, β j)
    {z : Fin I → Fin J → ℝ} (hz : IsFlow N α β z) : flowMap N α β = z := by
  classical
  have h := atar_prop_A_2 N α β hD
  unfold flowMap
  rw [dif_pos h]
  exact h.unique h.exists.choose_spec hz

theorem flowMap_isFlow (N : TreeNetwork I J) {α : Fin I → ℝ} {β : Fin J → ℝ}
    (hD : ∑ i, α i = ∑ j, β j) : IsFlow N α β (flowMap N α β) := by
  obtain ⟨z, hz, -⟩ := atar_prop_A_2 N α β hD
  rw [flowMap_eq N hD hz]; exact hz

/-- Elementary flow along one step of a walk. -/
def ed (x y : Fin I ⊕ Fin J) (i : Fin I) (j : Fin J) : ℝ :=
  (if x = Sum.inl i ∧ y = Sum.inr j then 1 else 0) - (if x = Sum.inr j ∧ y = Sum.inl i then 1 else 0)

/-- The flow carried by a walk. -/
def pfw (adj : Fin I → Fin J → Prop) :
    {a b : Fin I ⊕ Fin J} → (bipGraph adj).Walk a b → Fin I → Fin J → ℝ
  | _, _, .nil => 0
  | a, _, .cons (v := c) _ p => ed a c + pfw adj p

theorem ed_supp (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (i : Fin I) (j : Fin J) (hn : ¬ adj i j) : ed x y i j = 0 := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, h⟩ | ⟨i', j', rfl, rfl, h⟩
  · unfold ed
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij; exact absurd h hn
    · simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, sub_zero]
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hij ⟨rfl, rfl⟩
  · unfold ed
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij; exact absurd h hn
    · simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, zero_sub,
        neg_eq_zero]
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hij ⟨rfl, rfl⟩

theorem ed_row (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (i : Fin I) :
    ∑ j, ed x y i j = (if x = Sum.inl i then 1 else 0) - (if y = Sum.inl i then 1 else 0) := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, _⟩ | ⟨i', j', rfl, rfl, _⟩
  · by_cases hi : i' = i
    · subst hi; simp [ed]
    · simp [ed, hi]
  · by_cases hi : i' = i
    · subst hi; simp [ed]
    · simp [ed, hi]

theorem ed_col (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (j : Fin J) :
    ∑ i, ed x y i j = (if y = Sum.inr j then 1 else 0) - (if x = Sum.inr j then 1 else 0) := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, _⟩ | ⟨i', j', rfl, rfl, _⟩
  · by_cases hj : j' = j
    · subst hj; simp [ed]
    · simp [ed, hj]
  · by_cases hj : j' = j
    · subst hj; simp [ed]
    · simp [ed, hj]

theorem pfw_supp (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (i : Fin I) (j : Fin J) (hn : ¬ adj i j) : pfw adj w i j = 0 := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, ih, add_zero]
    exact ed_supp adj h i j hn

theorem pfw_row (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (i : Fin I) :
    ∑ j, pfw adj w i j = (if a = Sum.inl i then 1 else 0) - (if b = Sum.inl i then 1 else 0) := by
  induction w with
  | nil => simp [pfw]
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, Finset.sum_add_distrib, ih, ed_row adj h]
    ring

theorem pfw_col (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (j : Fin J) :
    ∑ i, pfw adj w i j = (if b = Sum.inr j then 1 else 0) - (if a = Sum.inr j then 1 else 0) := by
  induction w with
  | nil => simp [pfw]
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, Finset.sum_add_distrib, ih, ed_col adj h]
    ring

theorem pfw_not_mem (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J}
    (w : (bipGraph adj).Walk a b) (i : Fin I) (hi : Sum.inl i ∉ w.support) (j : Fin J) :
    pfw adj w i j = 0 := by
  induction w with
  | nil => rfl
  | @cons x c y h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hi
    simp only [pfw, Pi.add_apply, ih hi.2, add_zero]
    have hc : c ≠ Sum.inl i := fun hc => hi.2 (hc ▸ p.start_mem_support)
    unfold ed
    rw [if_neg (fun hh => hi.1 hh.1.symm), if_neg (fun hh => hc hh.2)]
    simp

/-- The flow of a walk from class `k` to pool `ĵ` solves (37) for `(e_k, e_ĵ)`. -/
theorem pfw_isFlow (N : TreeNetwork I J) (k : Fin I) (ĵ : Fin J)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) :
    IsFlow N (Pi.single k 1) (Pi.single ĵ 1) (pfw N.adj w) := by
  refine ⟨fun i j hn => pfw_supp N.adj w i j hn, fun i => ?_, fun j => ?_⟩
  · rw [pfw_row]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [pfw_col]
    by_cases h : j = ĵ
    · subst h; simp
    · simp [h, Ne.symm h]

theorem flowMap_single (N : TreeNetwork I J) (k : Fin I) (ĵ : Fin J)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) :
    flowMap N (Pi.single k 1) (Pi.single ĵ 1) = pfw N.adj w :=
  flowMap_eq N (by simp) (pfw_isFlow N k ĵ w)


theorem alg (μ : Fin J → ℝ) (Ψ : Fin I → Fin J → ℝ) (Φ : Fin J → Fin J → ℝ) (a : Fin I → ℝ)
    (b : Fin J → ℝ) :
    ∑ j, μ j * (∑ k, a k * Ψ k j + ∑ l, b l * Φ l j) =
      ∑ k, (∑ j, μ j * Ψ k j) * a k + ∑ l, (∑ j, μ j * Φ l j) * b l := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Linear representation of `Ψ` on `D` in the basis `(α, (β)_{−ĵ})`. -/
theorem flowMap_lin (N : TreeNetwork I J) (ĵ : Fin J) {a : Fin I → ℝ} {b : Fin J → ℝ}
    (hD : ∑ i, a i = ∑ j, b j) :
    flowMap N a b = fun i j => ∑ k, a k * flowMap N (Pi.single k 1) (Pi.single ĵ 1) i j
      + ∑ l, b l * flowMap N 0 (Pi.single l 1 - Pi.single ĵ 1) i j := by
  have hΨ : ∀ k, IsFlow N (Pi.single k 1) (Pi.single ĵ 1)
      (flowMap N (Pi.single k 1) (Pi.single ĵ 1)) := fun k => flowMap_isFlow N (by simp)
  have hΦ : ∀ l, IsFlow N 0 (Pi.single l 1 - Pi.single ĵ 1)
      (flowMap N 0 (Pi.single l 1 - Pi.single ĵ 1)) := fun l => flowMap_isFlow N (by
        simp [Finset.sum_sub_distrib])
  apply flowMap_eq N hD
  refine ⟨fun i j hn => ?_, fun i => ?_, fun j => ?_⟩
  · simp [(hΨ _).1 i j hn, (hΦ _).1 i j hn]
  · rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := fun x y => b y * _)]
    simp only [← Finset.mul_sum, (hΨ _).2.1 i, (hΦ _).2.1 i]
    simp [Pi.single_apply]
  · rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := fun x y => b y * _)]
    simp only [← Finset.mul_sum, (hΨ _).2.2 j, (hΦ _).2.2 j]
    simp only [Pi.single_apply, Pi.sub_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    by_cases hj : j = ĵ
    · simp only [hj, if_true, hD]; ring
    · simp [hj]


/-- The tree path from class `k` to pool `ĵ`. -/
noncomputable def tp (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I) :
    (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ) :=
  (N.isTree.existsUnique_path (Sum.inl k) (Sum.inr ĵ)).exists.choose

theorem tp_isPath (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I) : (tp N ĵ k).IsPath :=
  (N.isTree.existsUnique_path (Sum.inl k) (Sum.inr ĵ)).exists.choose_spec

theorem tp_unique (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) (hw : w.IsPath) : w = tp N ĵ k :=
  (N.isTree.existsUnique_path (Sum.inl k) (Sum.inr ĵ)).unique hw (tp_isPath N ĵ k)

/-- Depth of a class: the length of its tree path to `ĵ`. -/
noncomputable def depth (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I) : ℕ := (tp N ĵ k).length

theorem B1_eq (N : TreeNetwork I J) (ĵ : Fin J) (i k : Fin I) :
    B1 N ĵ i k = ∑ j, N.mu i j * pfw N.adj (tp N ĵ k) i j := by
  unfold B1
  rw [flowMap_single N k ĵ (tp N ĵ k)]

theorem diag_path (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) (hw : w.IsPath) :
    ∃ j1, N.adj k j1 ∧ ∑ j, N.mu k j * pfw N.adj w k j = N.mu k j1 := by
  cases w with
  | @cons _ c _ h p =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw
    have hp0 : ∀ j, pfw N.adj p k j = 0 := pfw_not_mem N.adj p k hw.2
    have h' := h
    rw [bip_adj_iff] at h'
    rcases h' with ⟨i', j1, hi', rfl, hadj⟩ | ⟨i', j1, _, hk, _⟩
    · cases hi'
      refine ⟨j1, hadj, ?_⟩
      simp only [pfw, Pi.add_apply, hp0, add_zero, ed]
      simp
    · cases hk

theorem depth_pos (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I) : 1 ≤ depth N ĵ k := by
  unfold depth
  by_contra h
  have h0 : (tp N ĵ k).length = 0 := by omega
  have := SimpleGraph.Walk.eq_of_length_eq_zero h0
  cases this

theorem depth_hat (N : TreeNetwork I J) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ) :
    depth N ĵ î = 1 := by
  have hadj : (bipGraph N.adj).Adj (Sum.inl î) (Sum.inr ĵ) := by
    rw [bip_adj_iff]; exact Or.inl ⟨î, ĵ, rfl, rfl, hedge⟩
  have hw : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath := by
    simp [SimpleGraph.Walk.cons_isPath_iff]
  unfold depth
  rw [← tp_unique N ĵ î _ hw]
  rfl

theorem depth_lt (N : TreeNetwork I J) (ĵ : Fin J) (i k : Fin I) (hik : i ≠ k)
    (hB : B1 N ĵ i k ≠ 0) : depth N ĵ i < depth N ĵ k := by
  rw [B1_eq] at hB
  have hmem : Sum.inl i ∈ (tp N ĵ k).support := by
    by_contra hn
    apply hB
    simp [pfw_not_mem N.adj (tp N ĵ k) i hn]
  set q := (tp N ĵ k).dropUntil (Sum.inl i) hmem with hq
  have hqp : q.IsPath := (tp_isPath N ĵ k).dropUntil hmem
  have hqe : q = tp N ĵ i := tp_unique N ĵ i q hqp
  have hlen : ((tp N ĵ k).takeUntil (Sum.inl i) hmem).length + q.length = (tp N ĵ k).length := by
    rw [← SimpleGraph.Walk.length_append, hq, SimpleGraph.Walk.take_spec]
  have hpos : ((tp N ĵ k).takeUntil (Sum.inl i) hmem).length ≠ 0 := by
    intro h0
    have := SimpleGraph.Walk.eq_of_length_eq_zero h0
    cases this
    exact hik rfl
  unfold depth
  rw [← hqe]
  omega

/-- An ordering of the classes that sorts them by a score, decreasing. -/
theorem exists_rank (s : Fin I → ℕ) :
    ∃ rk : Fin I ≃ Fin I, ∀ k l, s k < s l → rk l < rk k := by
  classical
  set M := ∑ l, s l with hM
  have hsM : ∀ k, s k ≤ M := fun k =>
    Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  set f : Fin I → ℕ := fun k => (M - s k) * I + k.val with hf
  have hfinj : Function.Injective f := by
    intro k l h
    simp only [hf] at h
    have hk := k.isLt
    have hl := l.isLt
    have h1 : (M - s k) = (M - s l) := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · have : (M - s k + 1) * I ≤ (M - s l) * I := Nat.mul_le_mul_right _ h2
        nlinarith
      · have : (M - s l + 1) * I ≤ (M - s k) * I := Nat.mul_le_mul_right _ h2
        nlinarith
    rw [h1] at h
    exact Fin.ext (by omega)
  have hmono : ∀ k l, s k < s l → f l < f k := by
    intro k l h
    simp only [hf]
    have hl := l.isLt
    have h2 : M - s l + 1 ≤ M - s k := by have := hsM l; omega
    have : (M - s l + 1) * I ≤ (M - s k) * I := Nat.mul_le_mul_right _ h2
    nlinarith
  let g : Fin I → Fin I := fun k =>
    ⟨(Finset.univ.filter (fun l => f l < f k)).card, by
      have : (Finset.univ.filter (fun l => f l < f k)).card < (Finset.univ : Finset (Fin I)).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨k, by simp, by simp⟩
      simpa using this⟩
  have hgmono : ∀ k l, f k < f l → g k < g l := by
    intro k l h
    show (Finset.univ.filter (fun m => f m < f k)).card < (Finset.univ.filter (fun m => f m < f l)).card
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨k, by simp [h], by simp⟩
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega
  have hginj : Function.Injective g := by
    intro k l h
    by_contra hne
    rcases lt_or_gt_of_ne (hfinj.ne hne) with h2 | h2
    · exact absurd h (hgmono k l h2).ne
    · exact absurd h (hgmono l k h2).ne'
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj), fun k l h => ?_⟩
  exact hgmono l k (hmono k l h)

end SWSSProp2Aux

open SWSSNet.Diffusion SWSSProp2Aux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ) :
    (∀ (hv : Fin I → ℝ) (u : (Fin I → ℝ) × (Fin J → ℝ)) (x : EthierKurtz.SDEState I),
      IsControlValue u →
      driftH N hv u x = WithLp.toLp 2 (hv - B1 N ĵ *ᵥ (fun k => x k - max (∑ l, x l) 0 * u.1 k)
        + max (-(∑ k, x k)) 0 • (B2 N ĵ *ᵥ u.2))) ∧
    (∃ rk : Fin I ≃ Fin I, (∀ k, rk k ≤ rk î) ∧ ∀ k l, rk k < rk l → B1 N ĵ k l = 0) ∧
    (∀ i, 0 < B1 N ĵ i i) ∧
    B1 N ĵ î î = N.mu î ĵ ∧
    ∀ i, B2 N ĵ i ĵ = 0 := by
  have hadj : (bipGraph N.adj).Adj (Sum.inl î) (Sum.inr ĵ) := by
    rw [bip_adj_iff]; exact Or.inl ⟨î, ĵ, rfl, rfl, hedge⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (43)
    intro hv u x hu
    have hs1 : ∑ k, u.1 k = 1 := hu.1.2
    have hs2 : ∑ l, u.2 l = 1 := hu.2.2
    set m := ∑ l, x l with hm
    have hD : ∑ k, (x k - max m 0 * u.1 k) = ∑ l, -(max (-m) 0 * u.2 l) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, Finset.sum_neg_distrib, ← Finset.mul_sum,
        hs2, ← hm]
      rcases le_total m 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    unfold driftH
    rw [flowMap_lin N ĵ hD]
    congr 1
    funext i
    simp only []
    rw [alg]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, B1, B2]
    have h3 : ∀ X : Fin J → ℝ, ∑ l, X l * -(max (-m) 0 * u.2 l) = -(max (-m) 0 * ∑ l, X l * u.2 l) := by
      intro X
      simp only [mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h3]
    ring
  · -- triangular structure
    classical
    set sc : Fin I → ℕ := fun k => 2 * depth N ĵ k + (if k = î then 0 else 1) with hsc
    obtain ⟨rk, hrk⟩ := exists_rank sc
    refine ⟨rk, fun k => ?_, fun k l hkl => ?_⟩
    · by_cases hk : k = î
      · rw [hk]
      · apply le_of_lt
        apply hrk
        simp only [hsc, if_neg hk, depth_hat N î ĵ hedge, if_true]
        have := depth_pos N ĵ k
        omega
    · by_contra hB
      have hne : k ≠ l := by rintro rfl; exact lt_irrefl _ hkl
      have hd := depth_lt N ĵ k l hne hB
      have : sc k < sc l := by
        simp only [hsc]
        split_ifs <;> omega
      exact absurd (hrk k l this) (not_lt.mpr hkl.le)
  · -- positive diagonal
    intro i
    obtain ⟨j1, hj1, he⟩ := diag_path N ĵ i (tp N ĵ i) (tp_isPath N ĵ i)
    rw [B1_eq, he]
    exact N.mu_pos i j1 hj1
  · -- (B₁)_{îî} = µ_{îĵ}
    have hw : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath := by
      simp [SimpleGraph.Walk.cons_isPath_iff]
    unfold B1
    rw [flowMap_single N î ĵ (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)]
    simp [pfw, ed]
  · -- column `ĵ` of `B₂`
    intro i
    unfold B2
    have h0 : flowMap N 0 0 = 0 := by
      apply flowMap_eq N (by simp)
      refine ⟨fun _ _ _ => rfl, fun i => ?_, fun j => ?_⟩ <;> simp
    simp [sub_self, h0]
