-- Prove2me | solution 1 for PolylogKServer.HST.exists_hst_embedding_distribution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T09:32:48.734881+00:00
-- url     : https://prove2.me/submissions/17fd126e-a43d-41c6-8e01-ebae8c4b5837

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

/-! K1 part A: the prefix tree of a family of center sequences `s x` (all of length `D`). -/

set_option autoImplicit false

namespace B5077a04K1

open PolylogKServer.HST

variable {M : Type} [Fintype M] [DecidableEq M]

/-- Nodes: prefixes of length `≤ D` of the sequences `s x`. -/
def nodes (s : M → List M) (D : ℕ) : Finset (List M) :=
  Finset.univ.biUnion (fun x => (Finset.range (D + 1)).image (fun i => (s x).take i))

theorem mem_nodes {s : M → List M} {D : ℕ} {l : List M} :
    l ∈ nodes s D ↔ ∃ x i, i ≤ D ∧ (s x).take i = l := by
  simp [nodes]

theorem take_mem (s : M → List M) (D : ℕ) (x : M) (i : ℕ) (hi : i ≤ D) :
    (s x).take i ∈ nodes s D := mem_nodes.2 ⟨x, i, hi, rfl⟩

theorem dropLast_mem {s : M → List M} {D : ℕ} {l : List M} (h : l ∈ nodes s D) :
    l.dropLast ∈ nodes s D := by
  obtain ⟨x, i, hi, rfl⟩ := mem_nodes.1 h
  rw [List.dropLast_eq_take, List.take_take]
  exact take_mem s D x _ (le_trans (min_le_right _ _) hi)

theorem length_le_of_mem {s : M → List M} {D : ℕ} (hs : ∀ x, (s x).length = D) {l : List M}
    (h : l ∈ nodes s D) : l.length ≤ D := by
  obtain ⟨x, i, hi, rfl⟩ := mem_nodes.1 h
  rw [List.length_take, hs]; omega

/-- The prefix tree; `W` of a node of length `j + 1` is `L / σ ^ j`. -/
noncomputable def tree (s : M → List M) (D : ℕ) (x0 : M) (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) :
    WTree (nodes s D) where
  root := ⟨[], take_mem s D x0 0 (Nat.zero_le _)⟩
  parent v := ⟨v.1.dropLast, dropLast_mem v.2⟩
  depth v := v.1.length
  parent_root := rfl
  depth_root := rfl
  depth_parent v hv := by
    have hne : v.1 ≠ [] := fun h => hv (Subtype.ext h)
    have := List.length_pos_of_ne_nil hne
    show v.1.dropLast.length + 1 = v.1.length
    rw [List.length_dropLast]; omega
  W v := L / σ ^ (v.1.length - 1)
  W_pos v _ := by positivity

variable (s : M → List M) (D : ℕ) (x0 : M) (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ)

theorem iter_parent (v : nodes s D) (i : ℕ) :
    ((tree s D x0 L σ hL hσ).parent^[i] v).1 = v.1.take (v.1.length - i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    show (((tree s D x0 L σ hL hσ).parent^[i] v).1).dropLast = _
    rw [ih, List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1
    omega

theorem anc_iff (a v : nodes s D) :
    (tree s D x0 L σ hL hσ).IsAnc a v ↔ a.1 <+: v.1 := by
  constructor
  · rintro ⟨i, hi⟩
    have := iter_parent s D x0 L σ hL hσ v i
    rw [hi] at this
    rw [this]; exact List.take_prefix _ _
  · intro h
    refine ⟨v.1.length - a.1.length, Subtype.ext ?_⟩
    rw [iter_parent]
    have hl := h.length_le
    have h' := List.prefix_iff_eq_take.1 h
    rw [show v.1.length - (v.1.length - a.1.length) = a.1.length by omega]
    exact h'.symm

variable (hs : ∀ x, (s x).length = D)
include hs

/-- The leaf node of `x`. -/
def leafNode (x : M) : nodes s D :=
  ⟨s x, by have := take_mem s D x D le_rfl; rwa [List.take_of_length_le (by rw [hs])] at this⟩

theorem leafNode_isLeaf (x : M) : (tree s D x0 L σ hL hσ).IsLeaf (leafNode s D hs x) := by
  intro u hne hu
  have h1 := congrArg Subtype.val hu
  change u.1.dropLast = s x at h1
  have h2 := congrArg List.length h1
  rw [List.length_dropLast, hs] at h2
  have h3 := length_le_of_mem hs u.2
  have h4 : u.1 ≠ [] := fun h => hne (Subtype.ext h)
  have := List.length_pos_of_ne_nil h4
  omega

theorem take_mem' (x : M) (i : ℕ) : (s x).take i ∈ nodes s D := by
  rcases le_or_gt i D with h | h
  · exact take_mem s D x i h
  · have := take_mem s D x D le_rfl
    rwa [List.take_of_length_le (by rw [hs]), ← List.take_of_length_le (l := s x) (i := i)
      (by rw [hs]; omega)] at this

theorem isLeaf_iff (v : nodes s D) :
    (tree s D x0 L σ hL hσ).IsLeaf v ↔ ∃ x, v.1 = s x := by
  constructor
  · intro h
    obtain ⟨x, i, hi, hv⟩ := mem_nodes.1 v.2
    refine ⟨x, ?_⟩
    by_contra hne
    have hiD : i < D := by
      rcases lt_or_eq_of_le hi with h' | h'
      · exact h'
      · exfalso; apply hne; rw [← hv, h', List.take_of_length_le (by rw [hs])]
    refine h ⟨(s x).take (i + 1), take_mem s D x (i + 1) hiD⟩ ?_ ?_
    · intro he
      have h1 : (s x).take (i + 1) = [] := congrArg Subtype.val he
      have := congrArg List.length h1
      rw [List.length_take, hs] at this
      simp at this; omega
    · apply Subtype.ext
      show ((s x).take (i + 1)).dropLast = v.1
      rw [List.dropLast_eq_take, List.take_take, List.length_take, ← hv, hs]
      congr 1; omega
  · rintro ⟨x, hx⟩
    have : v = leafNode s D hs x := Subtype.ext hx
    rw [this]; exact leafNode_isLeaf s D x0 L σ hL hσ hs x

/-- The bijection `M ≃ leaves`. -/
noncomputable def leafEquiv (hinj : Function.Injective s) : M ≃ (tree s D x0 L σ hL hσ).Leaf :=
  Equiv.ofBijective (fun x => ⟨leafNode s D hs x, leafNode_isLeaf s D x0 L σ hL hσ hs x⟩)
    ⟨fun x y h => hinj (congrArg (fun a => a.1.1) h), fun v => by
      obtain ⟨x, hx⟩ := (isLeaf_iff s D x0 L σ hL hσ hs v.1).1 v.2
      exact ⟨x, Subtype.ext (Subtype.ext hx.symm)⟩⟩

theorem leafEquiv_apply (hinj : Function.Injective s) (x : M) :
    ((leafEquiv s D x0 L σ hL hσ hs hinj x : (tree s D x0 L σ hL hσ).Leaf) : nodes s D) =
      leafNode s D hs x := rfl

/-- The depth-`(j+1)` ancestor of the leaf of `x`. -/
def nodeOf (x : M) (j : ℕ) : nodes s D := ⟨(s x).take (j + 1), take_mem' s D hs x (j + 1)⟩

open Classical in
theorem sum_anc (x : M) (g : nodes s D → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => a ≠ (tree s D x0 L σ hL hσ).root),
      (if (tree s D x0 L σ hL hσ).IsAnc a (leafNode s D hs x) then g a else 0) =
    ∑ j ∈ Finset.range D, g (nodeOf s D hs x j) := by
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hset : Finset.univ.filter (fun a => a ≠ (tree s D x0 L σ hL hσ).root ∧
      (tree s D x0 L σ hL hσ).IsAnc a (leafNode s D hs x)) =
      (Finset.range D).image (nodeOf s D hs x) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    rw [anc_iff]
    constructor
    · rintro ⟨hne, hp⟩
      have hne' : a.1 ≠ [] := fun h => hne (Subtype.ext h)
      have hpos := List.length_pos_of_ne_nil hne'
      have hle := hp.length_le
      change a.1 <+: s x at hp
      have hle' : a.1.length ≤ D := by have := hp.length_le; rw [hs x] at this; exact this
      refine ⟨a.1.length - 1, by omega, Subtype.ext ?_⟩
      show (s x).take (a.1.length - 1 + 1) = a.1
      rw [show a.1.length - 1 + 1 = a.1.length by omega]
      exact (List.prefix_iff_eq_take.1 hp).symm
    · rintro ⟨j, hj, rfl⟩
      refine ⟨fun he => ?_, List.take_prefix _ _⟩
      have h1 : (s x).take (j + 1) = [] := congrArg Subtype.val he
      have := congrArg List.length h1
      rw [List.length_take, hs] at this
      simp at this; omega
  rw [hset, Finset.sum_image]
  intro i hi j hj hij
  have := congrArg (fun a => (Subtype.val a).length) hij
  simp only [nodeOf, List.length_take, hs] at this
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  omega

theorem W_nodeOf (x : M) (j : ℕ) (hj : j < D) :
    (tree s D x0 L σ hL hσ).W (nodeOf s D hs x j) = L / σ ^ j := by
  show L / σ ^ (((s x).take (j + 1)).length - 1) = _
  rw [List.length_take, hs]; congr 2; omega

theorem anc_nodeOf (x y : M) (j : ℕ) (hj : j < D) :
    (tree s D x0 L σ hL hσ).IsAnc (nodeOf s D hs x j) (leafNode s D hs y) ↔
      (s x).take (j + 1) = (s y).take (j + 1) := by
  rw [anc_iff]
  change (s x).take (j + 1) <+: s y ↔ _
  rw [List.prefix_iff_eq_take, List.length_take, hs, min_eq_left (by omega)]

theorem treeDist_le (x y : M) :
    (tree s D x0 L σ hL hσ).treeDist (leafNode s D hs x) (leafNode s D hs y) ≤
      2 * ∑ j ∈ Finset.range D,
        (if (s x).take (j + 1) = (s y).take (j + 1) then 0 else L / σ ^ j) := by
  classical
  unfold WTree.treeDist
  set T := tree s D x0 L σ hL hσ
  calc _ ≤ ∑ a ∈ Finset.univ.filter (fun a => a ≠ T.root),
        ((if T.IsAnc a (leafNode s D hs x) then (if T.IsAnc a (leafNode s D hs y) then 0 else T.W a)
          else 0) +
         (if T.IsAnc a (leafNode s D hs y) then (if T.IsAnc a (leafNode s D hs x) then 0 else T.W a)
          else 0)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases h1 : T.IsAnc a (leafNode s D hs x) <;>
          by_cases h2 : T.IsAnc a (leafNode s D hs y) <;> simp [h1, h2]
    _ = _ := by
        rw [Finset.sum_add_distrib, sum_anc, sum_anc, two_mul]
        congr 1
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [anc_nodeOf s D x0 L σ hL hσ hs x y j hj', W_nodeOf s D x0 L σ hL hσ hs x j hj']
          split_ifs with h1 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h1.symm h2 | exact absurd h2 h1 | exact absurd h2.symm h1
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [anc_nodeOf s D x0 L σ hL hσ hs y x j hj', W_nodeOf s D x0 L σ hL hσ hs y j hj']
          by_cases h : (s x).take (j + 1) = (s y).take (j + 1)
          · rw [if_pos h.symm, if_pos h]
          · rw [if_neg (Ne.symm h), if_neg h]

theorem le_treeDist (x y : M) (j : ℕ) (hj : j < D)
    (hne : (s x).take (j + 1) ≠ (s y).take (j + 1)) :
    L / σ ^ j ≤ (tree s D x0 L σ hL hσ).treeDist (leafNode s D hs x) (leafNode s D hs y) := by
  classical
  unfold WTree.treeDist
  set T := tree s D x0 L σ hL hσ
  have hmem : nodeOf s D hs x j ∈ Finset.univ.filter (fun a => a ≠ T.root) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro he
    have h1 : (s x).take (j + 1) = [] := congrArg Subtype.val he
    have := congrArg List.length h1
    rw [List.length_take, hs] at this
    simp at this; omega
  have hterm : (if (T.IsAnc (nodeOf s D hs x j) (leafNode s D hs x) ↔
      T.IsAnc (nodeOf s D hs x j) (leafNode s D hs y)) then 0 else T.W (nodeOf s D hs x j)) =
      L / σ ^ j := by
    rw [anc_nodeOf s D x0 L σ hL hσ hs x y j hj, anc_nodeOf s D x0 L σ hL hσ hs x x j hj,
      W_nodeOf s D x0 L σ hL hσ hs x j hj]
    simp [hne]
  rw [← hterm]
  refine Finset.single_le_sum (f := fun a => if (T.IsAnc a (leafNode s D hs x) ↔
      T.IsAnc a (leafNode s D hs y)) then 0 else T.W a) (fun a _ => ?_) hmem
  have : 0 < T.W a := by show 0 < L / σ ^ (a.1.length - 1); positivity
  split_ifs <;> linarith

end B5077a04K1

/-! K1 parts B-E: random-rank ball centres, injectivity, dominance, upper bound, cut lemma. -/

namespace B5077a04K1

open PolylogKServer.HST

section Centers

variable {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M] {n : ℕ}

/-- The closed ball as a finset. -/
noncomputable def ballF (x : M) (R : ℝ) : Finset M := Finset.univ.filter (fun w => dist x w ≤ R)

theorem self_mem_ballF (x : M) {R : ℝ} (hR : 0 ≤ R) : x ∈ ballF x R := by
  simp [ballF, hR]

/-- The `π`-first point of the ball of radius `R` around `x`. -/
noncomputable def center (π : M ≃ Fin n) (R : ℝ) (x : M) : M :=
  if h : (ballF x R).Nonempty then Classical.choose (Finset.exists_min_image _ (fun w => π w) h)
  else x

theorem center_spec (π : M ≃ Fin n) {R : ℝ} (hR : 0 ≤ R) (x : M) :
    dist x (center π R x) ≤ R ∧ ∀ v, dist x v ≤ R → π (center π R x) ≤ π v := by
  have h : (ballF x R).Nonempty := ⟨x, self_mem_ballF x hR⟩
  have hs := Classical.choose_spec (Finset.exists_min_image _ (fun w => π w) h)
  rw [center, dif_pos h]
  refine ⟨?_, fun v hv => hs.2 v ?_⟩
  · exact (Finset.mem_filter.1 hs.1).2
  · simp [ballF, hv]

theorem center_eq (π : M ≃ Fin n) {R : ℝ} (hR : 0 ≤ R) (x w : M) (hw : dist x w ≤ R)
    (hmin : ∀ v, dist x v ≤ R → π w ≤ π v) : center π R x = w := by
  obtain ⟨h1, h2⟩ := center_spec π hR x
  exact π.injective (le_antisymm (h2 w hw) (hmin _ h1))

theorem center_self (π : M ≃ Fin n) {R δ : ℝ} (hR : 0 ≤ R) (hRδ : R < δ)
    (hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y) (x : M) : center π R x = x := by
  by_contra h
  have h1 := (center_spec π hR x).1
  have h2 := hδ x _ (Ne.symm h)
  linarith

/-- `w` is `π`-first among the points at least as close to `{x, y}` as `w`. -/
def first (π : M ≃ Fin n) (x y w : M) : Prop :=
  ∀ v, min (dist v x) (dist v y) ≤ min (dist w x) (dist w y) → π w ≤ π v

theorem cut (π : M ≃ Fin n) {R : ℝ} (hR : 0 ≤ R) (x y : M)
    (hne : center π R x ≠ center π R y) :
    ∃ w, min (dist w x) (dist w y) ≤ R ∧ R < max (dist w x) (dist w y) ∧ first π x y w := by
  classical
  set T := Finset.univ.filter (fun v : M => min (dist v x) (dist v y) ≤ R) with hT
  have hTn : T.Nonempty := ⟨x, by simp [hT, hR]⟩
  obtain ⟨w, hwT, hwmin⟩ := Finset.exists_min_image T (fun v => π v) hTn
  have hwR : min (dist w x) (dist w y) ≤ R := (Finset.mem_filter.1 hwT).2
  refine ⟨w, hwR, ?_, fun v hv => hwmin v (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_trans hv hwR⟩)⟩
  by_contra hc
  push_neg at hc
  have hx : dist w x ≤ R := le_trans (le_max_left _ _) hc
  have hy : dist w y ≤ R := le_trans (le_max_right _ _) hc
  apply hne
  have e1 : center π R x = w := center_eq π hR x w (by rw [dist_comm]; exact hx)
    (fun v hv => hwmin v (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      le_trans (min_le_left _ _) (by rw [dist_comm]; exact hv)⟩))
  have e2 : center π R y = w := center_eq π hR y w (by rw [dist_comm]; exact hy)
    (fun v hv => hwmin v (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      le_trans (min_le_right _ _) (by rw [dist_comm]; exact hv)⟩))
  rw [e1, e2]

/-- Centre sequence at radii `R0 / σ ^ i`. -/
noncomputable def cseq (π : M ≃ Fin n) (R0 σ : ℝ) (x : M) (i : ℕ) : M := center π (R0 / σ ^ i) x

noncomputable def sq (π : M ≃ Fin n) (R0 σ : ℝ) (D : ℕ) (x : M) : List M :=
  List.ofFn (fun i : Fin D => cseq π R0 σ x i)

theorem sq_length (π : M ≃ Fin n) (R0 σ : ℝ) (D : ℕ) (x : M) : (sq π R0 σ D x).length = D := by
  simp [sq]

theorem take_ofFn_iff {D : ℕ} (f g : ℕ → M) (j : ℕ) (hj : j < D) :
    (List.ofFn (fun i : Fin D => f i)).take (j + 1) = (List.ofFn (fun i : Fin D => g i)).take (j + 1) ↔
      ∀ i ≤ j, f i = g i := by
  constructor
  · intro h i hi
    have h1 := congrArg (fun l : List M => l[i]?) h
    simp only [List.getElem?_take, List.getElem?_ofFn] at h1
    simp [show i < j + 1 by omega, show i < D by omega] at h1
    exact h1
  · intro h
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_ofFn]
    by_cases hi : i < j + 1
    · simp [hi, h i (by omega)]
    · simp [hi]

theorem take_sq_iff (π : M ≃ Fin n) (R0 σ : ℝ) (D : ℕ) (x y : M) (j : ℕ) (hj : j < D) :
    (sq π R0 σ D x).take (j + 1) = (sq π R0 σ D y).take (j + 1) ↔
      ∀ i ≤ j, cseq π R0 σ x i = cseq π R0 σ y i :=
  take_ofFn_iff _ _ j hj

theorem sq_inj (π : M ≃ Fin n) {R0 σ δ : ℝ} {D : ℕ} (hσ : 0 < σ) (hR0 : 0 < R0)
    (hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y) (hD : 0 < D) (hRD : R0 / σ ^ (D - 1) < δ) :
    Function.Injective (sq π R0 σ D) := by
  intro x y h
  have h1 := (take_sq_iff π R0 σ D x y (D - 1) (by omega)).1 (by rw [h]) (D - 1) le_rfl
  have hR : 0 ≤ R0 / σ ^ (D - 1) := div_nonneg hR0.le (pow_nonneg hσ.le _)
  unfold cseq at h1
  rwa [center_self π hR hRD hδ x, center_self π hR hRD hδ y] at h1

theorem dom (π : M ≃ Fin n) {R0 σ Δ δ : ℝ} {D : ℕ} (x0 : M) (hσ : 2 ≤ σ) (hR0 : 0 < R0)
    (hL : 0 < 2 * σ * R0) (hσ0 : 0 < σ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (hΔR : Δ ≤ σ * R0)
    (hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y) (hD : 0 < D) (hRD : R0 / σ ^ (D - 1) < δ)
    (x y : M) :
    dist x y ≤ (tree (sq π R0 σ D) D x0 (2 * σ * R0) σ hL hσ0).treeDist
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) x)
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) y) := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [dist_self]
    simp [WTree.treeDist]
  have hRD0 : 0 ≤ R0 / σ ^ (D - 1) := div_nonneg hR0.le (pow_nonneg hσ0.le _)
  have hlast : cseq π R0 σ x (D - 1) ≠ cseq π R0 σ y (D - 1) := by
    unfold cseq
    rw [center_self π hRD0 hRD hδ x, center_self π hRD0 hRD hδ y]
    exact hxy
  have hex : ∃ i, cseq π R0 σ x i ≠ cseq π R0 σ y i := ⟨D - 1, hlast⟩
  obtain ⟨j, hj, hjmin, hjD1⟩ : ∃ j, cseq π R0 σ x j ≠ cseq π R0 σ y j ∧
      (∀ i < j, cseq π R0 σ x i = cseq π R0 σ y i) ∧ j ≤ D - 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      by_contra h; exact Nat.find_min hex hi h, Nat.find_min' hex hlast⟩
  have hjD : j < D := by omega
  have htake : (sq π R0 σ D x).take (j + 1) ≠ (sq π R0 σ D y).take (j + 1) := by
    intro h; exact hj ((take_sq_iff π R0 σ D x y j hjD).1 h j le_rfl)
  refine le_trans ?_ (le_treeDist (sq π R0 σ D) D x0 (2 * σ * R0) σ hL hσ0
    (sq_length π R0 σ D) x y j hjD htake)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero, div_one]
    have := hΔ x y
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hkeq : cseq π R0 σ x k = cseq π R0 σ y k := hjmin k (by omega)
    have hRk : 0 ≤ R0 / σ ^ k := div_nonneg hR0.le (pow_nonneg hσ0.le _)
    have h1 := (center_spec π hRk x).1
    have h2 := (center_spec π hRk y).1
    unfold cseq at hkeq
    rw [hkeq] at h1
    have h3 : dist x y ≤ 2 * (R0 / σ ^ k) := by
      calc dist x y ≤ dist x (center π (R0 / σ ^ k) y) + dist (center π (R0 / σ ^ k) y) y :=
            dist_triangle _ _ _
        _ ≤ _ := by rw [dist_comm _ y]; linarith
    have hσne : σ ≠ 0 := hσ0.ne'
    rw [hk, pow_succ]
    calc dist x y ≤ 2 * (R0 / σ ^ k) := h3
      _ = 2 * σ * R0 / (σ ^ k * σ) := by field_simp

theorem geom_tail {σ L : ℝ} (hσ : 2 ≤ σ) (hL : 0 ≤ L) (i D : ℕ) :
    ∑ j ∈ Finset.range D, (if i ≤ j then (1 : ℝ) else 0) * (L / σ ^ j) ≤ 2 * (L / σ ^ i) := by
  have hσ0 : 0 < σ := by linarith
  have hA : 0 ≤ L / σ ^ i := div_nonneg hL (pow_nonneg hσ0.le _)
  rcases le_or_gt i D with hiD | hiD
  · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) hiD]
    have hz : ∑ j ∈ Finset.Ico 0 i, (if i ≤ j then (1 : ℝ) else 0) * (L / σ ^ j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [if_neg (by omega), zero_mul]
    rw [hz, zero_add, Finset.sum_Ico_eq_sum_range]
    calc ∑ k ∈ Finset.range (D - i), (if i ≤ i + k then (1 : ℝ) else 0) * (L / σ ^ (i + k))
        ≤ ∑ k ∈ Finset.range (D - i), (L / σ ^ i) * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k _
          rw [if_pos (by omega), one_mul, pow_add, ← div_div, one_div_pow, mul_one_div]
          have h2k : (2 : ℝ) ^ k ≤ σ ^ k := pow_le_pow_left₀ (by norm_num) hσ k
          have h2p : (0 : ℝ) < 2 ^ k := by positivity
          rw [div_le_div_iff₀ (pow_pos hσ0 k) h2p]
          exact mul_le_mul_of_nonneg_left h2k hA
      _ = (L / σ ^ i) * ∑ k ∈ Finset.range (D - i), (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ (L / σ ^ i) * 2 := by gcongr; exact sum_geometric_two_le _
      _ = 2 * (L / σ ^ i) := by ring
  · apply le_trans (le_of_eq (Finset.sum_eq_zero ?_)) (mul_nonneg zero_le_two hA)
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega), zero_mul]

theorem upper (π : M ≃ Fin n) {R0 σ : ℝ} {D : ℕ} (x0 : M) (hσ : 2 ≤ σ) (hR0 : 0 < R0)
    (hL : 0 < 2 * σ * R0) (hσ0 : 0 < σ) (x y : M) :
    (tree (sq π R0 σ D) D x0 (2 * σ * R0) σ hL hσ0).treeDist
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) x)
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) y) ≤
      8 * σ * ∑ i ∈ Finset.range D,
        (if cseq π R0 σ x i = cseq π R0 σ y i then 0 else R0 / σ ^ i) := by
  classical
  refine le_trans (treeDist_le (sq π R0 σ D) D x0 (2 * σ * R0) σ hL hσ0 (sq_length π R0 σ D) x y) ?_
  set e : ℕ → ℝ := fun i => if cseq π R0 σ x i = cseq π R0 σ y i then 0 else 1 with he
  have he01 : ∀ i, 0 ≤ e i := fun i => by simp only [he]; split_ifs <;> norm_num
  have hLj : ∀ j : ℕ, 0 ≤ 2 * σ * R0 / σ ^ j := fun j => div_nonneg hL.le (pow_nonneg hσ0.le _)
  have key : ∀ j ∈ Finset.range D,
      (if (sq π R0 σ D x).take (j + 1) = (sq π R0 σ D y).take (j + 1) then 0
        else 2 * σ * R0 / σ ^ j) ≤
      ∑ i ∈ Finset.range D, e i * ((if i ≤ j then (1 : ℝ) else 0) * (2 * σ * R0 / σ ^ j)) := by
    intro j hj
    have hjD := Finset.mem_range.1 hj
    have hnn : ∀ i ∈ Finset.range D,
        0 ≤ e i * ((if i ≤ j then (1 : ℝ) else 0) * (2 * σ * R0 / σ ^ j)) := by
      intro i _
      refine mul_nonneg (he01 i) (mul_nonneg ?_ (hLj j))
      split_ifs <;> norm_num
    split_ifs with ht
    · exact Finset.sum_nonneg hnn
    · rw [take_sq_iff π R0 σ D x y j hjD] at ht
      push_neg at ht
      obtain ⟨i, hij, hi⟩ := ht
      have hiD : i ∈ Finset.range D := Finset.mem_range.2 (by omega)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn hiD)
      simp only [he, if_neg hi, if_pos hij, one_mul]
  calc 2 * ∑ j ∈ Finset.range D,
        (if (sq π R0 σ D x).take (j + 1) = (sq π R0 σ D y).take (j + 1) then 0
          else 2 * σ * R0 / σ ^ j)
      ≤ 2 * ∑ j ∈ Finset.range D, ∑ i ∈ Finset.range D,
          e i * ((if i ≤ j then (1 : ℝ) else 0) * (2 * σ * R0 / σ ^ j)) := by
        gcongr with j hj
        exact key j hj
    _ = 2 * ∑ i ∈ Finset.range D, e i * ∑ j ∈ Finset.range D,
          ((if i ≤ j then (1 : ℝ) else 0) * (2 * σ * R0 / σ ^ j)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ 2 * ∑ i ∈ Finset.range D, e i * (2 * (2 * σ * R0 / σ ^ i)) := by
        gcongr with i hi
        exact geom_tail hσ hL.le i D
    _ = 8 * σ * ∑ i ∈ Finset.range D,
        (if cseq π R0 σ x i = cseq π R0 σ y i then 0 else R0 / σ ^ i) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [he]
        split_ifs <;> ring

open Classical in
/-- Per-sample bound through the cut lemma. -/
theorem upper_cut (π : M ≃ Fin n) {R0 σ : ℝ} {D : ℕ} (x0 : M) (hσ : 2 ≤ σ) (hR0 : 0 < R0)
    (hL : 0 < 2 * σ * R0) (hσ0 : 0 < σ) (x y : M) :
    (tree (sq π R0 σ D) D x0 (2 * σ * R0) σ hL hσ0).treeDist
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) x)
      (leafNode (sq π R0 σ D) D (sq_length π R0 σ D) y) ≤
      8 * σ * ∑ i ∈ Finset.range D, ∑ w : M,
        (if min (dist w x) (dist w y) ≤ R0 / σ ^ i ∧ R0 / σ ^ i < max (dist w x) (dist w y) ∧
          first π x y w then R0 / σ ^ i else 0) := by
  classical
  refine le_trans (upper π x0 hσ hR0 hL hσ0 x y) ?_
  gcongr with i hi
  have hRi : 0 ≤ R0 / σ ^ i := div_nonneg hR0.le (pow_nonneg hσ0.le _)
  have hnn : ∀ w ∈ (Finset.univ : Finset M), 0 ≤
      (if min (dist w x) (dist w y) ≤ R0 / σ ^ i ∧ R0 / σ ^ i < max (dist w x) (dist w y) ∧
          first π x y w then R0 / σ ^ i else 0) := by
    intro w _; split_ifs <;> first | exact hRi | exact le_rfl
  split_ifs with hc
  · exact Finset.sum_nonneg hnn
  · obtain ⟨w, h1, h2, h3⟩ := cut π hRi x y hc
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn (Finset.mem_univ w))
    rw [if_pos ⟨h1, h2, h3⟩]

end Centers

end B5077a04K1

/-! K1 parts F-G: permutation counting, harmonic bound, geometric window, the grid ratio `ρ`. -/

namespace B5077a04K1

section Counting

variable {M : Type} [Fintype M] [DecidableEq M] {n : ℕ}

/-- Ranks `π` under which `u` is first in `S`. -/
def Afirst (n : ℕ) (S : Finset M) (u : M) : Finset (M ≃ Fin n) :=
  Finset.univ.filter (fun π => ∀ v ∈ S, π u ≤ π v)

theorem swap_mem {S : Finset M} {u w v : M} (hu : u ∈ S) (hw : w ∈ S) (hv : v ∈ S) :
    Equiv.swap w u v ∈ S := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

theorem card_Afirst_eq (S : Finset M) {u w : M} (hu : u ∈ S) (hw : w ∈ S) :
    (Afirst n S u).card = (Afirst n S w).card := by
  refine Finset.card_bij' (fun π _ => (Equiv.swap w u).trans π)
    (fun π _ => (Equiv.swap w u).trans π) ?_ ?_ ?_ ?_
  · intro π hπ
    simp only [Afirst, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro v hv
    simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact hπ _ (swap_mem hu hw hv)
  · intro π hπ
    simp only [Afirst, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro v hv
    simp only [Equiv.trans_apply, Equiv.swap_apply_right]
    exact hπ _ (swap_mem hu hw hv)
  · intro π _
    ext v
    simp [Equiv.swap_apply_self]
  · intro π _
    ext v
    simp [Equiv.swap_apply_self]

theorem card_mul_card_Afirst (S : Finset M) {w : M} (hw : w ∈ S) :
    S.card * (Afirst n S w).card = Fintype.card (M ≃ Fin n) := by
  have hcov : (Finset.univ : Finset (M ≃ Fin n)) = S.biUnion (fun u => Afirst n S u) := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff, Afirst, Finset.mem_filter, true_and]
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image S (fun v => π v) ⟨w, hw⟩
    exact ⟨u, hu, hmin⟩
  rw [← Finset.card_univ, hcov, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun u hu => card_Afirst_eq S hu hw), Finset.sum_const, smul_eq_mul]
  · intro u hu u' hu' hne
    change Disjoint (Afirst n S u) (Afirst n S u')
    rw [Finset.disjoint_left]
    intro π h1 h2
    simp only [Afirst, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (π.injective (le_antisymm (h1 u' hu') (h2 u hu)))

theorem sum_inv_card_le (f : M → ℝ) (A : Finset M) :
    ∑ w ∈ A, (1 : ℝ) / (A.filter (fun v => f v ≤ f w)).card ≤ (harmonic A.card : ℝ) := by
  refine Finset.induction_on_max_value f A ?_ ?_
  · simp
  · intro a s ha hmax ih
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, harmonic_succ]
    have h1 : (insert a s).filter (fun v => f v ≤ f a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact le_rfl
      · exact hmax v hv
    rw [h1, Finset.card_insert_of_notMem ha]
    have h2 : ∑ w ∈ s, (1 : ℝ) / ((insert a s).filter (fun v => f v ≤ f w)).card ≤
        ∑ w ∈ s, (1 : ℝ) / (s.filter (fun v => f v ≤ f w)).card := by
      apply Finset.sum_le_sum
      intro w hw
      have hpos : (0 : ℝ) < ((s.filter (fun v => f v ≤ f w)).card : ℝ) := by
        exact_mod_cast Finset.card_pos.2 ⟨w, (Finset.mem_filter.2 ⟨hw, le_refl (f w)⟩ :
          w ∈ s.filter (fun v => f v ≤ f w))⟩
      apply one_div_le_one_div_of_le hpos
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a s))
    simp only [one_div] at h2 ih ⊢
    push_cast at h2 ih ⊢
    linarith

end Counting

section Grid

theorem geom_window {ρ A a b : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 < A) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (H : Finset ℕ) (hH : ∀ t ∈ H, a ≤ A * ρ ^ t ∧ A * ρ ^ t < b) :
    ∑ t ∈ H, A * ρ ^ t ≤ (b - a) / (1 - ρ) + a := by
  have h1ρ : 0 < 1 - ρ := by linarith
  rcases H.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    have hba : 0 ≤ (b - a) / (1 - ρ) := div_nonneg (by linarith) h1ρ.le
    linarith
  set t0 := H.min' hne with ht0
  set t1 := H.max' hne with ht1
  have h01 : t0 ≤ t1 := Finset.min'_le H t1 (H.max'_mem hne)
  have hsub : H ⊆ Finset.Ico t0 (t1 + 1) := by
    intro t ht
    rw [Finset.mem_Ico]
    exact ⟨H.min'_le t ht, Nat.lt_succ_of_le (H.le_max' t ht)⟩
  have hb : A * ρ ^ t0 < b := (hH t0 (H.min'_mem hne)).2
  have ha : a ≤ A * ρ ^ t1 := (hH t1 (H.max'_mem hne)).1
  have key : A * ρ ^ t0 * ρ ^ (t1 + 1 - t0) = ρ * (A * ρ ^ t1) := by
    rw [mul_assoc, ← pow_add, show t0 + (t1 + 1 - t0) = t1 + 1 by omega, pow_succ]
    ring
  have hρne : ρ - 1 ≠ 0 := by linarith
  calc ∑ t ∈ H, A * ρ ^ t ≤ ∑ t ∈ Finset.Ico t0 (t1 + 1), A * ρ ^ t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)
    _ = ∑ k ∈ Finset.range (t1 + 1 - t0), A * ρ ^ t0 * ρ ^ k := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_add]; ring
    _ = A * ρ ^ t0 * ((ρ ^ (t1 + 1 - t0) - 1) / (ρ - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq hρ1.ne]
    _ = (A * ρ ^ t0 - ρ * (A * ρ ^ t1)) / (1 - ρ) := by
        rw [← key]
        field_simp
        ring
    _ ≤ (b - ρ * a) / (1 - ρ) := by
        apply div_le_div_of_nonneg_right _ h1ρ.le
        nlinarith
    _ = (b - a) / (1 - ρ) + a := by
        field_simp
        ring

/-- The grid ratio `ρ = σ^(-1/N)`. -/
noncomputable def rho (σ : ℝ) (N : ℕ) : ℝ := Real.exp (-(Real.log σ / N))

theorem rho_pos (σ : ℝ) (N : ℕ) : 0 < rho σ N := Real.exp_pos _

theorem rho_lt_one {σ : ℝ} {N : ℕ} (hσ : 1 < σ) (hN : 0 < N) : rho σ N < 1 := by
  unfold rho
  have := Real.log_pos hσ
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 < Real.log σ / N := div_pos this hN'
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.2 (by linarith)

theorem rho_pow_N {σ : ℝ} {N : ℕ} (hσ : 0 < σ) (hN : 0 < N) : rho σ N ^ N = 1 / σ := by
  unfold rho
  rw [← Real.exp_nat_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℝ) * -(Real.log σ / N) = -Real.log σ by field_simp, Real.exp_neg,
    Real.exp_log hσ, one_div]

theorem one_sub_rho {σ : ℝ} {N : ℕ} (hσ : 1 < σ) (hN : 0 < N) (hNl : Real.log σ ≤ N) :
    Real.log σ / (2 * N) ≤ 1 - rho σ N := by
  unfold rho
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set x := Real.log σ / N with hx
  have hx0 : 0 ≤ x := div_nonneg (Real.log_pos hσ).le hN'.le
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hN']; exact hNl
  have h := Real.add_one_le_exp x
  have e : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hE : 0 < Real.exp (-x) := Real.exp_pos _
  have hx2 : Real.log σ / (2 * N) = x / 2 := by rw [hx]; field_simp
  rw [hx2]
  nlinarith [mul_le_mul_of_nonneg_left h hE.le, mul_nonneg hx0 (sub_nonneg.2 hx1)]

end Grid

end B5077a04K1

/-! K1 part H: assembly (constant 72). -/

namespace B5077a04K1

open PolylogKServer.HST

theorem sum_swap3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (B : α → γ → ℝ) (F : β → γ → ℝ) :
    ∑ a, ∑ b, ∑ d, B a d * F b d = ∑ d, (∑ a, B a d) * (∑ b, F b d) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ d, ∑ b, B a d * F b d := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, B a d * F b d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem grid_sum {ρ Δ a b : ℝ} {N D : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hΔ : 0 < Δ)
    (ha0 : 0 ≤ a) (hab : a ≤ b) :
    ∑ u : Fin N, ∑ i ∈ Finset.range D,
      (if a ≤ Δ * ρ ^ (i * N + (u : ℕ)) ∧ Δ * ρ ^ (i * N + (u : ℕ)) < b
        then Δ * ρ ^ (i * N + (u : ℕ)) else 0) ≤ (b - a) / (1 - ρ) + a := by
  classical
  set g : ℕ → ℝ := fun t => if a ≤ Δ * ρ ^ t ∧ Δ * ρ ^ t < b then Δ * ρ ^ t else 0 with hg
  have hinj : Set.InjOn (fun p : Fin N × ℕ => p.2 * N + (p.1 : ℕ))
      ((Finset.univ ×ˢ Finset.range D : Finset (Fin N × ℕ)) : Set (Fin N × ℕ)) := by
    rintro ⟨u, i⟩ _ ⟨u', i'⟩ _ h
    simp only at h
    have hu := u.2
    have hu' := u'.2
    have h1 : i = i' := by
      rcases lt_trichotomy i i' with hl | he | hgt
      · have : (i + 1) * N ≤ i' * N := Nat.mul_le_mul_right N hl
        rw [Nat.add_mul, one_mul] at this
        linarith
      · exact he
      · have : (i' + 1) * N ≤ i * N := Nat.mul_le_mul_right N hgt
        rw [Nat.add_mul, one_mul] at this
        linarith
    subst h1
    have : (u : ℕ) = u' := by omega
    exact Prod.ext (Fin.ext this) rfl
  have e1 : ∑ u : Fin N, ∑ i ∈ Finset.range D, g (i * N + (u : ℕ)) =
      ∑ t ∈ (Finset.univ ×ˢ Finset.range D).image (fun p : Fin N × ℕ => p.2 * N + (p.1 : ℕ)), g t := by
    rw [Finset.sum_image hinj, Finset.sum_product]
  change ∑ u : Fin N, ∑ i ∈ Finset.range D, g (i * N + (u : ℕ)) ≤ _
  rw [e1, hg, ← Finset.sum_filter]
  exact geom_window hρ0 hρ1 hΔ ha0 hab _ (fun t ht => (Finset.mem_filter.1 ht).2)

set_option maxHeartbeats 1000000 in
theorem k1_main (σ : ℝ) (hσ : 2 ≤ σ) (M : Type) [MetricSpace M] [Fintype M]
    (hM : 2 ≤ Fintype.card M) :
    ∃ (r : ℕ) (p : Fin r → ℝ) (V : Fin r → Type) (_ : ∀ i, Fintype (V i))
          (_ : ∀ i, DecidableEq (V i)) (T : (i : Fin r) → WTree (V i))
          (e : (i : Fin r) → M ≃ (T i).Leaf),
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, (T i).IsHST σ) ∧
          (∀ i (x y : M), dist x y ≤ (T i).treeDist (e i x) (e i y)) ∧
          ∀ x y : M, ∑ i, p i * (T i).treeDist (e i x) (e i y) ≤
            72 * σ * Real.log (Fintype.card M) / Real.log σ * dist x y := by
  classical
  set n := Fintype.card M with hn
  have hσ0 : 0 < σ := by linarith
  have hσ1 : 1 < σ := by linarith
  have hlogσ : 0 < Real.log σ := Real.log_pos hσ1
  obtain ⟨x1, y1, hxy1⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card M)
  set Δ : ℝ := ∑ p : M × M, dist p.1 p.2 with hΔdef
  have hΔ : ∀ x y : M, dist x y ≤ Δ := fun x y =>
    Finset.single_le_sum (f := fun p : M × M => dist p.1 p.2) (fun p _ => dist_nonneg)
      (Finset.mem_univ (x, y))
  have hoff : (Finset.univ.offDiag : Finset (M × M)).Nonempty := ⟨(x1, y1), by simp [hxy1]⟩
  obtain ⟨p0, hp0, hp0min⟩ := Finset.exists_min_image _ (fun p : M × M => dist p.1 p.2) hoff
  set δ := dist p0.1 p0.2 with hδdef
  have hδpos : 0 < δ := dist_pos.2 (Finset.mem_offDiag.1 hp0).2.2
  have hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y := fun x y h => hp0min (x, y) (by simp [h])
  have hδΔ : δ ≤ Δ := hΔ _ _
  have hΔpos : 0 < Δ := lt_of_lt_of_le hδpos hδΔ
  set N : ℕ := ⌈Δ * Real.log σ / δ⌉₊ + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hN1 : Δ * Real.log σ / δ ≤ N := by
    have := Nat.le_ceil (Δ * Real.log σ / δ)
    rw [hNdef]; push_cast; linarith
  have hNl : Real.log σ ≤ N := by
    have : Real.log σ ≤ Δ * Real.log σ / δ := by
      rw [le_div_iff₀ hδpos]; nlinarith
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set ρ := rho σ N with hρdef
  have hρ0 : 0 < ρ := rho_pos σ N
  have hρ1 : ρ < 1 := rho_lt_one hσ1 hNpos
  have hρN : ρ ^ N = 1 / σ := rho_pow_N hσ0 hNpos
  have h1ρ : Real.log σ / (2 * N) ≤ 1 - ρ := one_sub_rho hσ1 hNpos hNl
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (Δ / δ) hσ1
  set D := k + 1 with hDdef
  have hE : Nonempty (M ≃ Fin n) := ⟨Fintype.equivFin M⟩
  set r := Fintype.card ((M ≃ Fin n) × Fin N) with hr
  have hrpos : 0 < r := Fintype.card_pos
  set eΩ : Fin r ≃ (M ≃ Fin n) × Fin N := (Fintype.equivFin _).symm with heΩ
  set R0 : (M ≃ Fin n) × Fin N → ℝ := fun ω => Δ * ρ ^ (ω.2 : ℕ) with hR0def
  have hR0 : ∀ ω, 0 < R0 ω := fun ω => mul_pos hΔpos (pow_pos hρ0 _)
  have hL : ∀ ω, 0 < 2 * σ * R0 ω := fun ω => mul_pos (mul_pos two_pos hσ0) (hR0 ω)
  have hΔR : ∀ ω, Δ ≤ σ * R0 ω := by
    intro ω
    have h1 : ρ ^ N ≤ ρ ^ (ω.2 : ℕ) := pow_le_pow_of_le_one hρ0.le hρ1.le ω.2.2.le
    rw [hρN] at h1
    have h2 : σ * Δ * (1 / σ) = Δ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hσ0 hΔpos))
    show Δ ≤ σ * (Δ * ρ ^ (ω.2 : ℕ))
    rw [h2] at h3
    linarith
  have hRD : ∀ ω, R0 ω / σ ^ (D - 1) < δ := by
    intro ω
    have h1 : ρ ^ (ω.2 : ℕ) ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have hk' : Δ / σ ^ k < δ := by
      rw [div_lt_iff₀ (pow_pos hσ0 k)]
      rw [div_lt_iff₀ hδpos] at hk
      linarith
    show Δ * ρ ^ (ω.2 : ℕ) / σ ^ (k + 1 - 1) < δ
    rw [show k + 1 - 1 = k by omega]
    calc Δ * ρ ^ (ω.2 : ℕ) / σ ^ k ≤ Δ / σ ^ k := by
          apply div_le_div_of_nonneg_right _ (pow_pos hσ0 k).le
          nlinarith
      _ < δ := hk'
  have hDpos : 0 < D := Nat.succ_pos k
  refine ⟨r, fun _ => 1 / r, fun i => ↥(nodes (sq (eΩ i).1 (R0 (eΩ i)) σ D) D),
    fun i => inferInstance, fun i => inferInstance,
    fun i => tree (sq (eΩ i).1 (R0 (eΩ i)) σ D) D x1 (2 * σ * R0 (eΩ i)) σ (hL _) hσ0,
    fun i => leafEquiv (sq (eΩ i).1 (R0 (eΩ i)) σ D) D x1 (2 * σ * R0 (eΩ i)) σ (hL _) hσ0
      (sq_length _ _ σ D) (sq_inj (eΩ i).1 hσ0 (hR0 _) hδ hDpos (hRD _)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; positivity
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    field_simp
  · intro i
    exact ⟨2 * σ * R0 (eΩ i), hL _, fun v _ => rfl⟩
  · intro i x y
    exact dom (eΩ i).1 x1 hσ (hR0 _) (hL _) hσ0 hΔ (hΔR _) hδ hDpos (hRD _) x y
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [WTree.treeDist]
    have hd : δ ≤ dist x y := hδ x y hxy
    set d := dist x y with hddef
    set m : M → ℝ := fun v => min (dist v x) (dist v y) with hm
    set Mx : M → ℝ := fun v => max (dist v x) (dist v y) with hMx
    set S : M → Finset M := fun w => Finset.univ.filter (fun v => m v ≤ m w) with hS
    set K : ℝ := (Fintype.card (M ≃ Fin n) : ℝ) with hK
    set Q : ℝ := 3 * N * d / Real.log σ with hQ
    set G : (M ≃ Fin n) × Fin N → ℝ := fun ω =>
      (tree (sq ω.1 (R0 ω) σ D) D x1 (2 * σ * R0 ω) σ (hL ω) hσ0).treeDist
        (leafNode (sq ω.1 (R0 ω) σ D) D (sq_length _ _ σ D) x)
        (leafNode (sq ω.1 (R0 ω) σ D) D (sq_length _ _ σ D) y) with hG
    set B : (M ≃ Fin n) → M → ℝ := fun π w => if first π x y w then 1 else 0 with hB
    set F : Fin N → M → ℝ := fun u w => ∑ i ∈ Finset.range D,
      (if m w ≤ Δ * ρ ^ (i * N + (u : ℕ)) ∧ Δ * ρ ^ (i * N + (u : ℕ)) < Mx w
        then Δ * ρ ^ (i * N + (u : ℕ)) else 0) with hF
    have hRi : ∀ (u i : ℕ), Δ * ρ ^ u / σ ^ i = Δ * ρ ^ (i * N + u) := by
      intro u i
      rw [pow_add, pow_mul', hρN, one_div_pow]
      ring
    -- per-sample bound
    have hGω : ∀ ω, G ω ≤ 8 * σ * ∑ w, B ω.1 w * F ω.2 w := by
      intro ω
      refine le_trans (upper_cut ω.1 x1 hσ (hR0 ω) (hL ω) hσ0 x y) (le_of_eq ?_)
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [hB, hF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hRi (ω.2 : ℕ) i
      simp only [hR0def] at this ⊢
      rw [this]
      by_cases hf : first ω.1 x y w
      · simp [hf, hm, hMx]
      · simp [hf]
    -- B column sums
    have hBsum : ∀ w, ∑ π, B π w = K / (S w).card := by
      intro w
      have hwS : w ∈ S w := by simp [hS]
      have hc := card_mul_card_Afirst (n := n) (S w) hwS
      have hfil : (Finset.univ.filter (fun π : M ≃ Fin n => first π x y w)) = Afirst n (S w) w := by
        ext π
        simp [Afirst, first, hS, hm]
      have hpos : (0 : ℝ) < (S w).card := by exact_mod_cast Finset.card_pos.2 ⟨w, hwS⟩
      simp only [hB]
      rw [Finset.sum_boole, hfil, hK, ← hc]
      push_cast
      field_simp
    -- F row sums
    have hFsum : ∀ w, ∑ u, F u w ≤ Q := by
      intro w
      have h0 : 0 ≤ m w := le_min dist_nonneg dist_nonneg
      have hle : m w ≤ Mx w := min_le_max
      have hgap : Mx w - m w ≤ d := by
        simp only [hm, hMx, hddef]
        have t1 := dist_triangle w x y
        have t2 := dist_triangle w y x
        rw [dist_comm y x] at t2
        rcases le_total (dist w x) (dist w y) with h | h
        · rw [min_eq_left h, max_eq_right h]; linarith
        · rw [min_eq_right h, max_eq_left h]; linarith
      have hmΔ : m w ≤ N * d / Real.log σ := by
        have h1 : m w ≤ Δ := le_trans (min_le_left _ _) (hΔ w x)
        have h2 : Δ ≤ N * δ / Real.log σ := by
          rw [le_div_iff₀ hlogσ]
          rw [div_le_iff₀ hδpos] at hN1
          linarith
        have h3 : N * δ / Real.log σ ≤ N * d / Real.log σ := by
          apply div_le_div_of_nonneg_right _ hlogσ.le
          exact mul_le_mul_of_nonneg_left hd hNR.le
        linarith
      have hgeo := grid_sum (N := N) (D := D) hρ0 hρ1 hΔpos h0 hle
      have h1ρ' : 0 < 1 - ρ := by linarith
      have hdiv : (Mx w - m w) / (1 - ρ) ≤ 2 * N * d / Real.log σ := by
        rw [div_le_div_iff₀ h1ρ' hlogσ]
        rw [div_le_iff₀ (by positivity)] at h1ρ
        have hd0 : 0 ≤ d := dist_nonneg
        nlinarith [mul_le_mul_of_nonneg_left hgap hlogσ.le]
      calc ∑ u, F u w ≤ (Mx w - m w) / (1 - ρ) + m w := hgeo
        _ ≤ 2 * N * d / Real.log σ + N * d / Real.log σ := add_le_add hdiv hmΔ
        _ = Q := by rw [hQ]; ring
    -- harmonic
    have hH : ∑ w, (1 : ℝ) / (S w).card ≤ 3 * Real.log n := by
      have h1 := sum_inv_card_le m Finset.univ
      have h2 := harmonic_le_one_add_log n
      rw [Finset.card_univ] at h1
      have h3 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
      have h4 := Real.log_two_gt_d9
      have : ∑ w, (1 : ℝ) / (S w).card ≤ 1 + Real.log n := le_trans h1 h2
      linarith
    have hQ0 : 0 ≤ Q := by
      rw [hQ]; have := (dist_nonneg : 0 ≤ d); positivity
    have hK0 : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
    have hsum : ∑ ω, G ω ≤ 8 * σ * (K * Q * (3 * Real.log n)) := by
      calc ∑ ω, G ω ≤ ∑ ω, 8 * σ * ∑ w, B ω.1 w * F ω.2 w := Finset.sum_le_sum fun ω _ => hGω ω
        _ = 8 * σ * ∑ w, (∑ π, B π w) * (∑ u, F u w) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
          exact congrArg (fun z => 8 * σ * z) (sum_swap3 B F)
        _ ≤ 8 * σ * ∑ w, (K / (S w).card) * Q := by
          gcongr with w
          · rw [hBsum w]
          · exact hFsum w
        _ = 8 * σ * (K * Q * ∑ w, (1 : ℝ) / (S w).card) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
        _ ≤ 8 * σ * (K * Q * (3 * Real.log n)) := by
          gcongr
    have hrK : (r : ℝ) = K * N := by
      rw [hr, Fintype.card_prod, Fintype.card_fin, hK]; push_cast; ring
    have hLHS : ∑ i : Fin r, 1 / (r : ℝ) *
        (tree (sq (eΩ i).1 (R0 (eΩ i)) σ D) D x1 (2 * σ * R0 (eΩ i)) σ (hL _) hσ0).treeDist
          ((leafEquiv (sq (eΩ i).1 (R0 (eΩ i)) σ D) D x1 (2 * σ * R0 (eΩ i)) σ (hL _) hσ0
            (sq_length _ _ σ D) (sq_inj (eΩ i).1 hσ0 (hR0 _) hδ hDpos (hRD _)) x : _))
          ((leafEquiv (sq (eΩ i).1 (R0 (eΩ i)) σ D) D x1 (2 * σ * R0 (eΩ i)) σ (hL _) hσ0
            (sq_length _ _ σ D) (sq_inj (eΩ i).1 hσ0 (hR0 _) hδ hDpos (hRD _)) y : _)) =
        1 / (r : ℝ) * ∑ ω, G ω := by
      rw [← Finset.mul_sum]
      congr 1
      exact Equiv.sum_comp eΩ G
    rw [hLHS]
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    calc 1 / (r : ℝ) * ∑ ω, G ω ≤ 1 / (r : ℝ) * (8 * σ * (K * Q * (3 * Real.log n))) := by
          gcongr
      _ = 72 * σ * Real.log n / Real.log σ * d := by
          rw [hrK, hQ]
          field_simp
          ring

theorem k1_proof : ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 2 ≤ σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M], 2 ≤ Fintype.card M →
        ∃ (r : ℕ) (p : Fin r → ℝ) (V : Fin r → Type) (_ : ∀ i, Fintype (V i))
          (_ : ∀ i, DecidableEq (V i)) (T : (i : Fin r) → WTree (V i))
          (e : (i : Fin r) → M ≃ (T i).Leaf),
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, (T i).IsHST σ) ∧
          (∀ i (x y : M), dist x y ≤ (T i).treeDist (e i x) (e i y)) ∧
          ∀ x y : M, ∑ i, p i * (T i).treeDist (e i x) (e i y) ≤
            C * σ * Real.log (Fintype.card M) / Real.log σ * dist x y :=
  ⟨72, by norm_num, fun σ hσ M _ _ hM => k1_main σ hσ M hM⟩

end B5077a04K1


open PolylogKServer.HST in
theorem solution :
  ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 2 ≤ σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M], 2 ≤ Fintype.card M →
        ∃ (r : ℕ) (p : Fin r → ℝ) (V : Fin r → Type) (_ : ∀ i, Fintype (V i))
          (_ : ∀ i, DecidableEq (V i)) (T : (i : Fin r) → WTree (V i))
          (e : (i : Fin r) → M ≃ (T i).Leaf),
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, (T i).IsHST σ) ∧
          (∀ i (x y : M), dist x y ≤ (T i).treeDist (e i x) (e i y)) ∧
          ∀ x y : M, ∑ i, p i * (T i).treeDist (e i x) (e i y) ≤
            C * σ * Real.log (Fintype.card M) / Real.log σ * dist x y := by
  exact B5077a04K1.k1_proof
