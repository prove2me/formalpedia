-- Prove2me | solution 1 for PolylogKServer.HST.exists_shallow_weighted_hst
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T00:00:33.51043+00:00
-- url     : https://prove2.me/submissions/e0d92394-a6a9-44f7-8c06-3d1387cf0379

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

set_option autoImplicit false

namespace F43509a3

open PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

section basic
variable (T : WTree V)

theorem anc_self (u : V) : T.IsAnc u u := ⟨0, rfl⟩

theorem anc_trans {a b c : V} (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) : T.IsAnc a c := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

theorem anc_parent (v : V) : T.IsAnc (T.parent v) v := ⟨1, rfl⟩

theorem depth_iter (v : V) (i : ℕ) : T.depth (T.parent^[i] v) = T.depth v - i := by
  induction i generalizing v with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hv : v = T.root
    · subst hv; rw [T.parent_root, T.depth_root]; simp
    · have := T.depth_parent v hv; omega

theorem eq_root_of_depth {v : V} (h : T.depth v = 0) : v = T.root := by
  by_contra hv
  have := T.depth_parent v hv; omega

theorem iter_depth (v : V) : T.parent^[T.depth v] v = T.root :=
  eq_root_of_depth T (by rw [depth_iter]; simp)

theorem anc_root (v : V) : T.IsAnc T.root v := ⟨_, iter_depth T v⟩

theorem anc_root_eq {a : V} (h : T.IsAnc a T.root) : a = T.root := by
  obtain ⟨i, hi⟩ := h
  rw [Function.iterate_fixed T.parent_root] at hi
  exact hi.symm

theorem depth_le_of_anc {a b : V} (h : T.IsAnc a b) : T.depth a ≤ T.depth b := by
  obtain ⟨i, rfl⟩ := h; rw [depth_iter]; omega

theorem iter_min (v : V) (i : ℕ) : T.parent^[i] v = T.parent^[min i (T.depth v)] v := by
  rcases le_total i (T.depth v) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, Function.iterate_add_apply, iter_depth, Function.iterate_fixed T.parent_root]

theorem anc_unique {a b v : V} (ha : T.IsAnc a v) (hb : T.IsAnc b v)
    (hd : T.depth a = T.depth b) : a = b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [depth_iter, depth_iter] at hd
  rw [iter_min T v i, iter_min T v j]
  have : min i (T.depth v) = min j (T.depth v) := by omega
  rw [this]

theorem anc_of_depth_le {a b v : V} (ha : T.IsAnc a v) (hb : T.IsAnc b v)
    (hd : T.depth a ≤ T.depth b) : T.IsAnc a b := by
  have hc : T.IsAnc (T.parent^[T.depth b - T.depth a] b) v := anc_trans T ⟨_, rfl⟩ hb
  exact ⟨_, anc_unique T hc ha (by rw [depth_iter]; omega)⟩

theorem anc_eq_of_depth {a b : V} (h : T.IsAnc a b) (hd : T.depth a = T.depth b) : a = b :=
  anc_unique T h (anc_self T b) hd

theorem depth_lt_of_anc {a b : V} (h : T.IsAnc a b) (hne : a ≠ b) : T.depth a < T.depth b :=
  lt_of_le_of_ne (depth_le_of_anc T h) (fun hd => hne (anc_eq_of_depth T h hd))

theorem anc_parent_of_ne {a b : V} (h : T.IsAnc a b) (hne : a ≠ b) : T.IsAnc a (T.parent b) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | zero => exact absurd hi.symm hne
  | succ i => exact ⟨i, by rw [Function.iterate_succ_apply] at hi; exact hi⟩

theorem ne_root_of_anc {a b : V} (h : T.IsAnc a b) (hne : a ≠ b) : b ≠ T.root := by
  intro hb; rw [hb] at h hne; exact hne (anc_root_eq T h)

theorem not_leaf_of_anc {a b : V} (h : T.IsAnc a b) (hne : a ≠ b) : ¬ T.IsLeaf a := by
  intro hl
  have hlt := depth_lt_of_anc T h hne
  obtain ⟨c, hc⟩ : ∃ c, c = T.parent^[T.depth b - T.depth a - 1] b := ⟨_, rfl⟩
  have hdc : T.depth c = T.depth a + 1 := by rw [hc, depth_iter]; omega
  have hcr : c ≠ T.root := by intro h0; rw [h0, T.depth_root] at hdc; omega
  have hcb : T.IsAnc c b := ⟨_, hc.symm⟩
  have hpc : T.parent c = a := by
    apply anc_unique T (anc_trans T (anc_parent T c) hcb) h
    have := T.depth_parent c hcr; omega
  exact hl c hcr hpc

theorem leaf_anc_eq {a b : V} (hl : T.IsLeaf a) (h : T.IsAnc a b) : a = b := by
  by_contra hne; exact not_leaf_of_anc T h hne hl

theorem exists_leaf_below (x : V) : ∃ l, T.IsLeaf l ∧ T.IsAnc x l := by
  classical
  obtain ⟨l, hl, hmax⟩ := (Finset.univ.filter (fun y => T.IsAnc x y)).exists_max_image T.depth
    ⟨x, by simp [anc_self]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hmax
  refine ⟨l, fun u hu hpu => ?_, hl⟩
  have hlu : T.IsAnc l u := by rw [← hpu]; exact anc_parent T u
  have h1 := hmax u (anc_trans T hl hlu)
  have h2 := T.depth_parent u hu
  rw [hpu] at h2; omega

end basic

section counts
variable (T : WTree V)

open Classical in
noncomputable def leafSet (x : V) : Finset V :=
  Finset.univ.filter (fun l => T.IsLeaf l ∧ T.IsAnc x l)

theorem mem_leafSet {x l : V} : l ∈ leafSet T x ↔ T.IsLeaf l ∧ T.IsAnc x l := by
  unfold leafSet; simp

noncomputable def nL (x : V) : ℕ := (leafSet T x).card

theorem nL_mono {a b : V} (h : T.IsAnc a b) : nL T b ≤ nL T a := by
  unfold nL
  apply Finset.card_le_card
  intro l hl
  rw [mem_leafSet] at hl ⊢
  exact ⟨hl.1, anc_trans T h hl.2⟩

theorem nL_leaf {u : V} (hu : T.IsLeaf u) : nL T u = 1 := by
  unfold nL
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext l
  rw [mem_leafSet, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact (leaf_anc_eq T hu h).symm
  · rintro rfl; exact ⟨hu, anc_self T _⟩

theorem nL_children {a c1 c2 : V} (h1 : T.parent c1 = a) (h2 : T.parent c2 = a)
    (r1 : c1 ≠ T.root) (r2 : c2 ≠ T.root) (hne : c1 ≠ c2) : nL T c1 + nL T c2 ≤ nL T a := by
  unfold nL
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro l hl
    rw [Finset.mem_union, mem_leafSet, mem_leafSet] at hl
    rw [mem_leafSet]
    rcases hl with ⟨hl1, hl2⟩ | ⟨hl1, hl2⟩
    · exact ⟨hl1, anc_trans T (by rw [← h1]; exact anc_parent T c1) hl2⟩
    · exact ⟨hl1, anc_trans T (by rw [← h2]; exact anc_parent T c2) hl2⟩
  · rw [Finset.disjoint_left]
    intro l hl hl'
    rw [mem_leafSet] at hl hl'
    apply hne
    apply anc_unique T hl.2 hl'.2
    have e1 := T.depth_parent c1 r1
    have e2 := T.depth_parent c2 r2
    rw [h1] at e1; rw [h2] at e2; omega

theorem nL_root_eq : nL T T.root = Fintype.card T.Leaf := by
  unfold nL
  rw [show Fintype.card T.Leaf = _ from Fintype.card_subtype T.IsLeaf]
  congr 1
  ext l
  rw [mem_leafSet]
  simp [anc_root]

def IsTop (x : V) : Prop := x = T.root ∨ 2 * nL T x ≤ nL T (T.parent x)

theorem exists_top (v : V) : ∃ i, IsTop T (T.parent^[i] v) :=
  ⟨T.depth v, Or.inl (iter_depth T v)⟩

noncomputable def topOf (v : V) : V :=
  T.parent^[@Nat.find _ (Classical.decPred _) (exists_top T v)] v

theorem topOf_top (v : V) : IsTop T (topOf T v) :=
  @Nat.find_spec _ (Classical.decPred _) (exists_top T v)

theorem anc_topOf (v : V) : T.IsAnc (topOf T v) v := ⟨_, rfl⟩

theorem topOf_greatest {t v : V} (ht : IsTop T t) (h : T.IsAnc t v) : T.IsAnc t (topOf T v) := by
  obtain ⟨j, rfl⟩ := h
  have hle : @Nat.find _ (Classical.decPred _) (exists_top T v) ≤ j :=
    @Nat.find_min' _ (Classical.decPred _) (exists_top T v) j ht
  refine ⟨j - @Nat.find _ (Classical.decPred _) (exists_top T v), ?_⟩
  unfold topOf
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]

theorem topOf_root : topOf T T.root = T.root := anc_root_eq T (anc_topOf T T.root)

def S (x : V) : Prop := IsTop T x ∨ T.IsLeaf x

@[reducible] noncomputable def fintypeS : Fintype {x : V // S T x} := by
  classical exact inferInstance

attribute [local instance] fintypeS

open Classical in
noncomputable def depSet (x : V) : Finset V :=
  Finset.univ.filter (fun y => S T y ∧ y ≠ T.root ∧ T.IsAnc y x)

theorem mem_depSet {x y : V} : y ∈ depSet T x ↔ S T y ∧ y ≠ T.root ∧ T.IsAnc y x := by
  unfold depSet; simp

open Classical in
noncomputable def lightSet (x : V) : Finset V :=
  Finset.univ.filter (fun y => IsTop T y ∧ y ≠ T.root ∧ T.IsAnc y x)

theorem mem_lightSet {x y : V} : y ∈ lightSet T x ↔ IsTop T y ∧ y ≠ T.root ∧ T.IsAnc y x := by
  unfold lightSet; simp

theorem depSet_root : (depSet T T.root).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_depSet] at hy
  exact hy.2.1 (anc_root_eq T hy.2.2)

theorem dep_step {x : V} (hx : S T x) (hr : x ≠ T.root) :
    (depSet T (topOf T (T.parent x))).card + 1 = (depSet T x).card := by
  rw [← Finset.card_insert_of_notMem (a := x)]
  · congr 1
    ext y
    rw [Finset.mem_insert, mem_depSet, mem_depSet]
    constructor
    · rintro (rfl | ⟨hs, hyr, ha⟩)
      · exact ⟨hx, hr, anc_self T _⟩
      · exact ⟨hs, hyr, anc_trans T ha (anc_trans T (anc_topOf T _) (anc_parent T x))⟩
    · rintro ⟨hs, hyr, ha⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · right
        refine ⟨hs, hyr, topOf_greatest T ?_ (anc_parent_of_ne T ha hyx)⟩
        rcases hs with h | h
        · exact h
        · exact absurd h (not_leaf_of_anc T ha hyx)
  · rw [mem_depSet]
    rintro ⟨_, _, ha⟩
    have h1 := depth_le_of_anc T ha
    have h2 := depth_le_of_anc T (anc_topOf T (T.parent x))
    have := T.depth_parent x hr
    omega

/-- The contracted tree: heavy edges are contracted, only tops and leaves survive. -/
noncomputable def contr : WTree {x : V // S T x} where
  root := ⟨T.root, Or.inl (Or.inl rfl)⟩
  parent := fun x => ⟨topOf T (T.parent x.1), Or.inl (topOf_top T _)⟩
  depth := fun x => (depSet T x.1).card
  parent_root := Subtype.ext (by
    show topOf T (T.parent T.root) = T.root
    rw [T.parent_root, topOf_root])
  depth_root := depSet_root T
  depth_parent := fun v hv => dep_step T v.2 (fun h => hv (Subtype.ext h))
  W := fun x => T.W x.1
  W_pos := fun v hv => T.W_pos v.1 (fun h => hv (Subtype.ext h))

theorem anc'_imp {x y : {x : V // S T x}} (h : (contr T).IsAnc x y) : T.IsAnc x.1 y.1 := by
  obtain ⟨i, rfl⟩ := h
  induction i with
  | zero => exact anc_self T _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact anc_trans T (anc_trans T (anc_topOf T _) (anc_parent T _)) ih

theorem anc'_of (x : {x : V // S T x}) : ∀ n, ∀ y : {x : V // S T x}, T.depth y.1 ≤ n →
    T.IsAnc x.1 y.1 → (contr T).IsAnc x y := by
  intro n
  induction n with
  | zero =>
    intro y hy ha
    have hy0 : y.1 = T.root := eq_root_of_depth T (by omega)
    have hx0 : x.1 = T.root := by rw [hy0] at ha; exact anc_root_eq T ha
    exact ⟨0, Subtype.ext (by rw [Function.iterate_zero_apply, hy0, hx0])⟩
  | succ n ih =>
    intro y hy ha
    by_cases hxy : x = y
    · exact ⟨0, hxy.symm⟩
    have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hxt : IsTop T x.1 := x.2.resolve_right (not_leaf_of_anc T ha hne)
    have hyr : y.1 ≠ T.root := ne_root_of_anc T ha hne
    have h1 : T.IsAnc x.1 ((contr T).parent y).1 :=
      topOf_greatest T hxt (anc_parent_of_ne T ha hne)
    have h2 : T.depth ((contr T).parent y).1 ≤ n := by
      have a1 := depth_le_of_anc T (anc_topOf T (T.parent y.1))
      have a2 := T.depth_parent y.1 hyr
      show T.depth (topOf T (T.parent y.1)) ≤ n
      omega
    obtain ⟨i, hi⟩ := ih _ h2 h1
    exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩

theorem anc'_iff (x y : {x : V // S T x}) : (contr T).IsAnc x y ↔ T.IsAnc x.1 y.1 :=
  ⟨anc'_imp T, anc'_of T x _ y le_rfl⟩

theorem leaf'_iff (x : {x : V // S T x}) : (contr T).IsLeaf x ↔ T.IsLeaf x.1 := by
  constructor
  · intro hl
    obtain ⟨l, hl1, hl2⟩ := exists_leaf_below T x.1
    by_cases hxl : x.1 = l
    · rw [hxl]; exact hl1
    · exfalso
      have ha : (contr T).IsAnc x ⟨l, Or.inr hl1⟩ := (anc'_iff T _ _).2 hl2
      exact not_leaf_of_anc (contr T) ha (fun h => hxl (congrArg Subtype.val h)) hl
  · intro hl u hu hpu
    have hur : u.1 ≠ T.root := fun h => hu (Subtype.ext h)
    have ha : T.IsAnc x.1 u.1 := anc'_imp T ⟨1, hpu⟩
    have hxu := leaf_anc_eq T hl ha
    have a1 : T.IsAnc x.1 (T.parent u.1) := by rw [← hpu]; exact anc_topOf T _
    have a2 := depth_le_of_anc T a1
    have a3 := T.depth_parent u.1 hur
    rw [hxu] at a2; omega

noncomputable def eqv : T.Leaf ≃ (contr T).Leaf where
  toFun u := ⟨⟨u.1, Or.inr u.2⟩, (leaf'_iff T _).2 u.2⟩
  invFun y := ⟨y.1.1, (leaf'_iff T _).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end counts

section dist

open Classical in
theorem treeDist_sum {U : Type} [Fintype U] [DecidableEq U] (R : WTree U) (u v : U) :
    R.treeDist u v = ∑ x, (if x ≠ R.root ∧ ¬(R.IsAnc x u ↔ R.IsAnc x v) then R.W x else 0) := by
  unfold WTree.treeDist
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> first | rfl | (exfalso; tauto)

variable (T : WTree V)

open Classical in
noncomputable def gap (u v x : V) : ℝ :=
  if x ≠ T.root ∧ ¬(T.IsAnc x u ↔ T.IsAnc x v) then T.W x else 0

theorem gap_nonneg (u v x : V) : 0 ≤ gap T u v x := by
  unfold gap
  split_ifs with h
  · exact (T.W_pos x h.1).le
  · exact le_rfl

theorem treeDist_gap (u v : V) : T.treeDist u v = ∑ x, gap T u v x := by
  rw [treeDist_sum]; rfl

theorem mem_img (u : V) (a : ℕ) (x : V) :
    x ∈ (Finset.Ico a (T.depth u)).image (fun j => T.parent^[T.depth u - 1 - j] u) ↔
      T.IsAnc x u ∧ a < T.depth x := by
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [depth_iter]; omega
  · rintro ⟨ha, hd⟩
    have hdu := depth_le_of_anc T ha
    refine ⟨T.depth x - 1, ⟨by omega, by omega⟩, ?_⟩
    apply anc_unique T ⟨_, rfl⟩ ha
    rw [depth_iter]; omega

theorem sum_img (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (u : V) (a : ℕ) :
    ∑ x ∈ (Finset.Ico a (T.depth u)).image (fun j => T.parent^[T.depth u - 1 - j] u), T.W x
      ≤ L / σ ^ a * (σ / (σ - 1)) := by
  rw [Finset.sum_image]
  · have hterm : ∀ j ∈ Finset.Ico a (T.depth u),
        T.W (T.parent^[T.depth u - 1 - j] u) = L * (σ⁻¹) ^ j := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hd : T.depth (T.parent^[T.depth u - 1 - j] u) = j + 1 := by rw [depth_iter]; omega
      have hr : T.parent^[T.depth u - 1 - j] u ≠ T.root := by
        intro h; rw [h, T.depth_root] at hd; omega
      rw [hW _ hr, hd, Nat.add_sub_cancel, inv_pow, div_eq_mul_inv]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hσ0 : 0 < σ := by linarith
    have hi0 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ0.le
    have hi1 : σ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hσ
    have hg := geom_sum_Ico_le_of_lt_one (m := a) (n := T.depth u) hi0 hi1
    calc L * ∑ j ∈ Finset.Ico a (T.depth u), σ⁻¹ ^ j ≤ L * (σ⁻¹ ^ a / (1 - σ⁻¹)) :=
          mul_le_mul_of_nonneg_left hg hL.le
      _ = L / σ ^ a * (σ / (σ - 1)) := by
          have h1 : σ - 1 ≠ 0 := by linarith
          have h2 : σ ≠ 0 := by linarith
          field_simp
          rw [← mul_pow, one_div_mul_cancel h2, one_pow]
  · intro i hi j hj hij
    have := congrArg T.depth hij
    simp only at this
    rw [depth_iter, depth_iter] at this
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    omega

theorem dist_bound (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (u v : V)
    (hu : T.IsLeaf u) (hv : T.IsLeaf v) (huv : u ≠ v) :
    ∃ c, c ≠ T.root ∧ IsTop T c ∧ ¬(T.IsAnc c u ↔ T.IsAnc c v) ∧
      T.treeDist u v ≤ 2 * σ / (σ - 1) * T.W c := by
  classical
  obtain ⟨a, ha, hmax⟩ := (Finset.univ.filter (fun x => T.IsAnc x u ∧ T.IsAnc x v)).exists_max_image
    T.depth ⟨T.root, by simp [anc_root]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
  have hau : a ≠ u := by
    intro h; rw [h] at ha; exact huv (leaf_anc_eq T hu ha.2)
  have hav : a ≠ v := by
    intro h; rw [h] at ha; exact huv (leaf_anc_eq T hv ha.1).symm
  have hdu := depth_lt_of_anc T ha.1 hau
  have hdv := depth_lt_of_anc T ha.2 hav
  obtain ⟨cu, hcu⟩ : ∃ c, c = T.parent^[T.depth u - T.depth a - 1] u := ⟨_, rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ c, c = T.parent^[T.depth v - T.depth a - 1] v := ⟨_, rfl⟩
  have hcuA : T.IsAnc cu u := ⟨_, hcu.symm⟩
  have hcvA : T.IsAnc cv v := ⟨_, hcv.symm⟩
  have dcu : T.depth cu = T.depth a + 1 := by rw [hcu, depth_iter]; omega
  have dcv : T.depth cv = T.depth a + 1 := by rw [hcv, depth_iter]; omega
  have rcu : cu ≠ T.root := by intro h; rw [h, T.depth_root] at dcu; omega
  have rcv : cv ≠ T.root := by intro h; rw [h, T.depth_root] at dcv; omega
  have pcu : T.parent cu = a := by
    apply anc_unique T (anc_trans T (anc_parent T cu) hcuA) ha.1
    have := T.depth_parent cu rcu; omega
  have pcv : T.parent cv = a := by
    apply anc_unique T (anc_trans T (anc_parent T cv) hcvA) ha.2
    have := T.depth_parent cv rcv; omega
  have ncuv : ¬ T.IsAnc cu v := by
    intro h; have := hmax cu ⟨hcuA, h⟩; omega
  have ncvu : ¬ T.IsAnc cv u := by
    intro h; have := hmax cv ⟨h, hcvA⟩; omega
  have hne : cu ≠ cv := by intro h; rw [h] at ncuv; exact ncuv hcvA
  have hcount := nL_children T pcu pcv rcu rcv hne
  have hWc : ∀ c, c ≠ T.root → T.depth c = T.depth a + 1 → T.W c = L / σ ^ T.depth a := by
    intro c hc hd; rw [hW c hc, hd, Nat.add_sub_cancel]
  obtain ⟨Iu, hIu⟩ : ∃ s, s = (Finset.Ico (T.depth a) (T.depth u)).image
      (fun j => T.parent^[T.depth u - 1 - j] u) := ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ s, s = (Finset.Ico (T.depth a) (T.depth v)).image
      (fun j => T.parent^[T.depth v - 1 - j] v) := ⟨_, rfl⟩
  have memu : ∀ x, x ∈ Iu ↔ T.IsAnc x u ∧ T.depth a < T.depth x := by
    intro x; rw [hIu]; exact mem_img T u _ x
  have memv : ∀ x, x ∈ Iv ↔ T.IsAnc x v ∧ T.depth a < T.depth x := by
    intro x; rw [hIv]; exact mem_img T v _ x
  have hpos : ∀ x, T.depth a < T.depth x → 0 ≤ T.W x := by
    intro x hx
    have : x ≠ T.root := by intro h; rw [h, T.depth_root] at hx; omega
    exact (T.W_pos x this).le
  have hdist : T.treeDist u v ≤ 2 * σ / (σ - 1) * (L / σ ^ T.depth a) := by
    rw [treeDist_gap]
    calc ∑ x, gap T u v x
        ≤ ∑ x, ((if x ∈ Iu then T.W x else 0) + (if x ∈ Iv then T.W x else 0)) := by
          apply Finset.sum_le_sum
          intro x _
          have h1 : 0 ≤ (if x ∈ Iu then T.W x else 0) := by
            split_ifs with h
            · exact hpos x ((memu x).1 h).2
            · exact le_rfl
          have h2 : 0 ≤ (if x ∈ Iv then T.W x else 0) := by
            split_ifs with h
            · exact hpos x ((memv x).1 h).2
            · exact le_rfl
          unfold gap
          by_cases hx : x ≠ T.root ∧ ¬(T.IsAnc x u ↔ T.IsAnc x v)
          · rw [if_pos hx]
            by_cases hxu : T.IsAnc x u
            · have hxv : ¬ T.IsAnc x v := fun h => hx.2 ⟨fun _ => h, fun _ => hxu⟩
              have hd : T.depth a < T.depth x := by
                by_contra hle
                exact hxv (anc_trans T (anc_of_depth_le T hxu ha.1 (by omega)) ha.2)
              rw [if_pos ((memu x).2 ⟨hxu, hd⟩)]
              linarith
            · have hxv : T.IsAnc x v := by
                by_contra h; exact hx.2 ⟨fun h' => absurd h' hxu, fun h' => absurd h' h⟩
              have hd : T.depth a < T.depth x := by
                by_contra hle
                exact hxu (anc_trans T (anc_of_depth_le T hxv ha.2 (by omega)) ha.1)
              rw [if_pos ((memv x).2 ⟨hxv, hd⟩)]
              linarith
          · rw [if_neg hx]
            linarith
      _ = ∑ x ∈ Iu, T.W x + ∑ x ∈ Iv, T.W x := by
          rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, Fintype.sum_ite_mem]
      _ ≤ L / σ ^ T.depth a * (σ / (σ - 1)) + L / σ ^ T.depth a * (σ / (σ - 1)) := by
          rw [hIu, hIv]
          exact add_le_add (sum_img T σ L hσ hL hW u _) (sum_img T σ L hσ hL hW v _)
      _ = 2 * σ / (σ - 1) * (L / σ ^ T.depth a) := by ring
  by_cases hc : 2 * nL T cu ≤ nL T a
  · refine ⟨cu, rcu, Or.inr (by rw [pcu]; exact hc), ?_, ?_⟩
    · intro h; exact ncuv (h.1 hcuA)
    · rw [hWc cu rcu dcu]; exact hdist
  · have hc' : 2 * nL T cv ≤ nL T a := by omega
    refine ⟨cv, rcv, Or.inr (by rw [pcv]; exact hc'), ?_, ?_⟩
    · intro h; exact ncvu (h.2 hcvA)
    · rw [hWc cv rcv dcv]; exact hdist

attribute [local instance] fintypeS

theorem contr_sum (u v : V) (hu : S T u) (hv : S T v) :
    (contr T).treeDist ⟨u, hu⟩ ⟨v, hv⟩ = ∑ y : {x : V // S T x}, gap T u v y.1 := by
  rw [treeDist_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold gap
  by_cases h : y.1 ≠ T.root ∧ ¬(T.IsAnc y.1 u ↔ T.IsAnc y.1 v)
  · rw [if_pos h, if_pos]
    · rfl
    · refine ⟨fun e => h.1 (congrArg Subtype.val e), ?_⟩
      rw [anc'_iff, anc'_iff]; exact h.2
  · rw [if_neg h, if_neg]
    intro hc
    apply h
    refine ⟨fun e => hc.1 (Subtype.ext e), ?_⟩
    have := hc.2
    rwa [anc'_iff, anc'_iff] at this

theorem dist_le (u v : T.Leaf) :
    (contr T).treeDist (eqv T u) (eqv T v) ≤ T.treeDist u v := by
  rw [show (contr T).treeDist (eqv T u) (eqv T v) = _ from
    contr_sum T u.1 v.1 (Or.inr u.2) (Or.inr v.2), treeDist_gap]
  calc ∑ y : {x : V // S T x}, gap T u v y.1
      = ∑ x ∈ Finset.univ.map (Function.Embedding.subtype (S T)), gap T u v x := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ x, gap T u v x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => gap_nonneg T u v x)

theorem dist_ge (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (u v : T.Leaf) :
    T.treeDist u v ≤ 2 * σ / (σ - 1) * (contr T).treeDist (eqv T u) (eqv T v) := by
  have hk : 0 ≤ 2 * σ / (σ - 1) := by apply div_nonneg <;> linarith
  rw [show (contr T).treeDist (eqv T u) (eqv T v) = _ from
    contr_sum T u.1 v.1 (Or.inr u.2) (Or.inr v.2)]
  by_cases huv : u = v
  · subst huv
    have h0 : T.treeDist u u = 0 := by
      rw [treeDist_gap]
      apply Finset.sum_eq_zero
      intro x _
      unfold gap
      rw [if_neg]
      intro h; exact h.2 Iff.rfl
    rw [h0]
    exact mul_nonneg hk (Finset.sum_nonneg (fun y _ => gap_nonneg T u u y.1))
  · obtain ⟨c, hcr, hct, hcs, hd⟩ :=
      dist_bound T σ L hσ hL hW u.1 v.1 u.2 v.2 (fun h => huv (Subtype.ext h))
    have hgc : gap T u.1 v.1 c = T.W c := by unfold gap; exact if_pos ⟨hcr, hcs⟩
    have hsum : T.W c ≤ ∑ y : {x : V // S T x}, gap T u.1 v.1 y.1 := by
      rw [← hgc]
      exact Finset.single_le_sum (f := fun y : {x : V // S T x} => gap T u.1 v.1 y.1)
        (fun y _ => gap_nonneg T u.1 v.1 y.1) (Finset.mem_univ ⟨c, Or.inl hct⟩)
    calc T.treeDist u v ≤ 2 * σ / (σ - 1) * T.W c := hd
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hk

theorem weighted (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) : (contr T).IsWeightedHST σ := by
  intro v hv hpv
  have hvr : v.1 ≠ T.root := fun h => hv (Subtype.ext h)
  have htr : topOf T (T.parent v.1) ≠ T.root := fun h => hpv (Subtype.ext h)
  show σ * T.W v.1 ≤ T.W (topOf T (T.parent v.1))
  rw [hW _ hvr, hW _ htr]
  have a1 := depth_le_of_anc T (anc_topOf T (T.parent v.1))
  have a2 := T.depth_parent v.1 hvr
  have a3 : 1 ≤ T.depth (topOf T (T.parent v.1)) := by
    by_contra h; exact htr (eq_root_of_depth T (by omega))
  obtain ⟨k, hk⟩ : ∃ k, T.depth v.1 - 1 = (T.depth (topOf T (T.parent v.1)) - 1) + 1 + k :=
    ⟨T.depth v.1 - 1 - (T.depth (topOf T (T.parent v.1)) - 1) - 1, by omega⟩
  rw [hk]
  generalize T.depth (topOf T (T.parent v.1)) - 1 = m
  have hσ0 : 0 < σ := by linarith
  have hk1 : 1 ≤ σ ^ k := one_le_pow₀ hσ.le
  have hp : 0 < σ ^ m := pow_pos hσ0 _
  have e : σ * (L / σ ^ (m + 1 + k)) = L / (σ ^ m * σ ^ k) := by
    rw [pow_add, pow_succ]; field_simp
  rw [e]
  exact div_le_div_of_nonneg_left hL.le hp (le_mul_of_one_le_right hp.le hk1)

theorem lights_bound : ∀ n, ∀ x, T.depth x = n →
    2 ^ (lightSet T x).card * nL T x ≤ nL T T.root := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have := eq_root_of_depth T hx; subst this
    have h0 : (lightSet T T.root).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_lightSet] at hy
      exact hy.2.1 (anc_root_eq T hy.2.2)
    rw [h0]; simp
  | succ n ih =>
    intro x hx
    have hxr : x ≠ T.root := by intro h; rw [h, T.depth_root] at hx; omega
    have hp := ih (T.parent x) (by have := T.depth_parent x hxr; omega)
    have hmono := nL_mono T (anc_parent T x)
    have hsub : lightSet T x ⊆ insert x (lightSet T (T.parent x)) := by
      intro y hy
      rw [mem_lightSet] at hy
      rw [Finset.mem_insert, mem_lightSet]
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hy.1, hy.2.1, anc_parent_of_ne T hy.2.2 hyx⟩
    by_cases ht : IsTop T x
    · have hl : (lightSet T x).card ≤ (lightSet T (T.parent x)).card + 1 :=
        (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have h2 : 2 * nL T x ≤ nL T (T.parent x) := ht.resolve_left hxr
      calc 2 ^ (lightSet T x).card * nL T x
          ≤ 2 ^ ((lightSet T (T.parent x)).card + 1) * nL T x :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hl)
        _ = 2 ^ (lightSet T (T.parent x)).card * (2 * nL T x) := by ring
        _ ≤ 2 ^ (lightSet T (T.parent x)).card * nL T (T.parent x) := Nat.mul_le_mul_left _ h2
        _ ≤ nL T T.root := hp
    · have hsub' : lightSet T x ⊆ lightSet T (T.parent x) := by
        intro y hy
        have hy' := hsub hy
        rw [Finset.mem_insert] at hy'
        rcases hy' with rfl | h
        · rw [mem_lightSet] at hy; exact absurd hy.1 ht
        · exact h
      calc 2 ^ (lightSet T x).card * nL T x
          ≤ 2 ^ (lightSet T (T.parent x)).card * nL T (T.parent x) :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card hsub')) hmono
        _ ≤ nL T T.root := hp

theorem dep_le (x : V) : (depSet T x).card ≤ (lightSet T x).card + 1 := by
  have hsub : depSet T x ⊆ insert x (lightSet T x) := by
    intro y hy
    rw [mem_depSet] at hy
    rw [Finset.mem_insert, mem_lightSet]
    by_cases hyx : y = x
    · exact Or.inl hyx
    · refine Or.inr ⟨?_, hy.2.1, hy.2.2⟩
      rcases hy.1 with h | h
      · exact h
      · exact absurd h (not_leaf_of_anc T hy.2.2 hyx)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem height_le (hN : 2 ≤ Fintype.card T.Leaf) :
    ((contr T).height : ℝ) ≤ 3 * Real.log (Fintype.card T.Leaf) := by
  obtain ⟨l, hl, _⟩ := exists_leaf_below T T.root
  have hne : (Finset.univ.filter (contr T).IsLeaf).Nonempty :=
    ⟨⟨l, Or.inr hl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, (leaf'_iff T _).2 hl⟩⟩
  obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup _ hne (contr T).depth
  have hyl : T.IsLeaf y.1 := (leaf'_iff T y).1 (Finset.mem_filter.1 hy).2
  unfold WTree.height
  rw [hsup]
  show (((depSet T y.1).card : ℕ) : ℝ) ≤ _
  have h1 := dep_le T y.1
  have h2 := lights_bound T _ y.1 rfl
  rw [nL_leaf T hyl, nL_root_eq, mul_one] at h2
  obtain ⟨k, hk⟩ : ∃ k, k = (lightSet T y.1).card := ⟨_, rfl⟩
  rw [← hk] at h1 h2
  have hkR : ((2 : ℝ) ^ k) ≤ (Fintype.card T.Leaf : ℝ) := by exact_mod_cast h2
  have hlog : (k : ℝ) * Real.log 2 ≤ Real.log (Fintype.card T.Leaf) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hkR
  have hl2 : Real.log 2 ≤ Real.log (Fintype.card T.Leaf) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hd : ((depSet T y.1).card : ℝ) ≤ k + 1 := by exact_mod_cast h1
  have h3 := Real.log_two_gt_d9
  have h4 : ((k : ℝ) + 1) * 0.6931471803 ≤ ((k : ℝ) + 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h3.le (by positivity)
  nlinarith

end dist

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 1 < σ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
        2 ≤ Fintype.card T.Leaf →
        ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V')
          (e : T.Leaf ≃ T'.Leaf),
          T'.IsWeightedHST σ ∧
          (T'.height : ℝ) ≤ C * Real.log (Fintype.card T.Leaf) ∧
          ∀ u v : T.Leaf,
            T'.treeDist (e u) (e v) ≤ T.treeDist u v ∧
            T.treeDist u v ≤ 2 * σ / (σ - 1) * T'.treeDist (e u) (e v) := by
  refine ⟨3, by norm_num, fun σ hσ V _ _ T hT hN => ?_⟩
  obtain ⟨L, hL, hW⟩ := hT
  exact ⟨{x : V // S T x}, fintypeS T, inferInstance, contr T, eqv T,
    weighted T σ L hσ hL hW, height_le T hN,
    fun u v => ⟨dist_le T u v, dist_ge T σ L hσ hL hW u v⟩⟩

end F43509a3

open PolylogKServer.HST in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 1 < σ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
        2 ≤ Fintype.card T.Leaf →
        ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V')
          (e : T.Leaf ≃ T'.Leaf),
          T'.IsWeightedHST σ ∧
          (T'.height : ℝ) ≤ C * Real.log (Fintype.card T.Leaf) ∧
          ∀ u v : T.Leaf,
            T'.treeDist (e u) (e v) ≤ T.treeDist u v ∧
            T.treeDist u v ≤ 2 * σ / (σ - 1) * T'.treeDist (e u) (e v) := by
  exact F43509a3.main
