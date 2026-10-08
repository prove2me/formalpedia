-- Prove2me | solution 1 for TalagrandConc.TSP.regular_tour
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:16:44.424094+00:00
-- url     : https://prove2.me/submissions/8d50efc8-55cc-49a7-afe2-e29778642a56

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic



namespace TalagrandConc.TSP

/-! ### Basic facts about `edist` -/

lemma edist_eq (x y : Point) :
    edist x y = Real.sqrt (((x 0 : ℝ) - y 0) ^ 2 + ((x 1 : ℝ) - y 1) ^ 2) := by
  unfold edist; rw [Fin.sum_univ_two]

lemma edist_nonneg' (x y : Point) : 0 ≤ edist x y := Real.sqrt_nonneg _

lemma edist_comm' (x y : Point) : edist x y = edist y x := by
  rw [edist_eq, edist_eq]; congr 1; ring

lemma edist_self' (x : Point) : edist x x = 0 := by
  rw [edist_eq]; simp

lemma edist_le_abs_add (x y : Point) :
    edist x y ≤ |(x 0 : ℝ) - y 0| + |(x 1 : ℝ) - y 1| := by
  rw [edist_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [abs_nonneg ((x 0 : ℝ) - y 0), abs_nonneg ((x 1 : ℝ) - y 1),
      sq_abs ((x 0 : ℝ) - y 0), sq_abs ((x 1 : ℝ) - y 1),
      mul_nonneg (abs_nonneg ((x 0 : ℝ) - y 0)) (abs_nonneg ((x 1 : ℝ) - y 1))]

lemma sqrt_add_sq_le (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  have h1 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (c ^ 2 + d ^ 2) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs2 : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  have hcs : a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (a * d - b * c)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

lemma edist_triangle' (x y z : Point) : edist x z ≤ edist x y + edist y z := by
  rw [edist_eq, edist_eq, edist_eq]
  have := sqrt_add_sq_le ((x 0 : ℝ) - y 0) ((x 1 : ℝ) - y 1) ((y 0 : ℝ) - z 0) ((y 1 : ℝ) - z 1)
  have e1 : ((x 0 : ℝ) - y 0) + ((y 0 : ℝ) - z 0) = (x 0 : ℝ) - z 0 := by ring
  have e2 : ((x 1 : ℝ) - y 1) + ((y 1 : ℝ) - z 1) = (x 1 : ℝ) - z 1 := by ring
  rw [e1, e2] at this
  exact this

/-! ### Path length of a list of points -/

noncomputable def pathLen : List Point → ℝ
  | a :: b :: l => edist a b + pathLen (b :: l)
  | _ => 0

@[simp] lemma pathLen_nil : pathLen [] = 0 := rfl
@[simp] lemma pathLen_single (a : Point) : pathLen [a] = 0 := rfl
@[simp] lemma pathLen_cons_cons (a b : Point) (l : List Point) :
    pathLen (a :: b :: l) = edist a b + pathLen (b :: l) := rfl

lemma pathLen_nonneg : ∀ l : List Point, 0 ≤ pathLen l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => by
    rw [pathLen_cons_cons]
    exact add_nonneg (edist_nonneg' _ _) (pathLen_nonneg (b :: l))

/-- `pathLen (a :: l) ≤ edist a b + pathLen (b :: l)`: inserting a point costs
at most a detour. -/
lemma pathLen_cons_le (a b : Point) : ∀ l : List Point,
    pathLen (a :: l) ≤ edist a b + pathLen (b :: l)
  | [] => by simp [edist_nonneg']
  | c :: l => by
    rw [pathLen_cons_cons, pathLen_cons_cons]
    linarith [edist_triangle' a b c]

lemma pathLen_sublist (a : Point) {l' l : List Point} (h : List.Sublist l' l) :
    pathLen (a :: l') ≤ pathLen (a :: l) := by
  induction h generalizing a with
  | slnil => exact le_rfl
  | cons b _ ih =>
    exact le_trans (ih a) (pathLen_cons_le a b _)
  | cons_cons b _ ih =>
    rw [pathLen_cons_cons, pathLen_cons_cons]
    exact add_le_add le_rfl (ih b)

lemma pathLen_cons_of_ne_nil (a : Point) (l : List Point) (hl : l ≠ []) :
    pathLen (a :: l) = edist a (l.head hl) + pathLen l := by
  obtain ⟨b, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp

lemma pathLen_append (l₁ l₂ : List Point) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    pathLen (l₁ ++ l₂) = pathLen l₁ + edist (l₁.getLast h₁) (l₂.head h₂) + pathLen l₂ := by
  induction l₁ with
  | nil => exact absurd rfl h₁
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · simp [pathLen_cons_of_ne_nil a l₂ h₂]
    · rw [List.cons_append, List.cons_append, pathLen_cons_cons, ← List.cons_append,
        ih (by simp), pathLen_cons_cons]
      simp only [List.getLast_cons_cons]
      ring

/-- The head-to-last distance is at most the path length. -/
lemma edist_head_getLast_le : ∀ (l : List Point) (h : l ≠ []),
    edist (l.head h) (l.getLast h) ≤ pathLen l
  | [], h => absurd rfl h
  | [a], _ => by simp [edist_self']
  | a :: b :: l, _ => by
    simp only [List.head_cons, List.getLast_cons_cons, pathLen_cons_cons]
    have := edist_head_getLast_le (b :: l) (by simp)
    simp only [List.head_cons] at this
    linarith [edist_triangle' a b ((b :: l).getLast (by simp))]

/-- Cyclic length of a list: a closed tour starting and ending at the head. -/
noncomputable def cyc : List Point → ℝ
  | [] => 0
  | a :: l => pathLen (a :: (l ++ [a]))

@[simp] lemma cyc_nil : cyc [] = 0 := rfl
@[simp] lemma cyc_cons (a : Point) (l : List Point) : cyc (a :: l) = pathLen (a :: (l ++ [a])) := rfl

lemma cyc_nonneg (l : List Point) : 0 ≤ cyc l := by
  cases l with
  | nil => simp
  | cons a l => simp [pathLen_nonneg]

/-- Shortcutting: a sublist with the same head has smaller cyclic length. -/
lemma cyc_cons_sublist (a : Point) {l' l : List Point} (h : List.Sublist l' l) :
    cyc (a :: l') ≤ cyc (a :: l) := by
  simp only [cyc_cons]
  exact pathLen_sublist a (h.append_right [a])

/-- Insertion of a block `lG` right after the head. -/
lemma cyc_insert (a : Point) (lG l : List Point) (hG : lG ≠ []) :
    cyc (a :: (lG ++ l)) ≤ cyc (a :: l) + 2 * edist a (lG.head hG) + 2 * pathLen lG := by
  simp only [cyc_cons]
  have hne : l ++ [a] ≠ [] := by simp
  rw [List.append_assoc, pathLen_cons_of_ne_nil a (lG ++ (l ++ [a])) (by simp),
    pathLen_append lG (l ++ [a]) hG hne, pathLen_cons_of_ne_nil a (l ++ [a]) hne]
  have h1 : (lG ++ (l ++ [a])).head (by simp) = lG.head hG := List.head_append_of_ne_nil hG
  rw [h1]
  have h2 := edist_head_getLast_le lG hG
  have h3 := edist_triangle' (lG.getLast hG) (lG.head hG) ((l ++ [a]).head hne)
  have h4 := edist_triangle' (lG.head hG) a ((l ++ [a]).head hne)
  rw [edist_comm' (lG.getLast hG) (lG.head hG)] at h3
  rw [edist_comm' (lG.head hG) a] at h4
  linarith

/-! ### Bridge between `tourLength` (permutations) and `cyc` (lists) -/

lemma pathLen_ofFn_append : ∀ (m : ℕ) (v : Fin (m + 1) → Point) (x : Point),
    pathLen (List.ofFn v ++ [x]) =
      ∑ i : Fin m, edist (v i.castSucc) (v i.succ) + edist (v (Fin.last m)) x
  | 0, v, x => by simp [List.ofFn_succ]
  | m + 1, v, x => by
    rw [List.ofFn_succ, List.cons_append]
    have h := pathLen_ofFn_append m (fun i => v i.succ) x
    rw [List.ofFn_succ (f := fun i => v i.succ), List.cons_append, pathLen_cons_cons,
      ← List.cons_append, ← List.ofFn_succ (f := fun i => v i.succ), h, Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.succ_last, Fin.succ_castSucc]
    ring

lemma cyc_ofFn_succ (m : ℕ) (v : Fin (m + 1) → Point) :
    cyc (List.ofFn v) = ∑ i : Fin (m + 1), edist (v i) (v (finRotate (m + 1) i)) := by
  rw [List.ofFn_succ, cyc_cons, ← List.cons_append, ← List.ofFn_succ, pathLen_ofFn_append,
    Fin.sum_univ_castSucc]
  simp only [finRotate_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

lemma cyc_ofFn : ∀ (n : ℕ) (v : Fin n → Point),
    cyc (List.ofFn v) = ∑ i : Fin n, edist (v i) (v (finRotate n i))
  | 0, v => by simp
  | m + 1, v => cyc_ofFn_succ m v

lemma tourCost_eq_cyc {F : Finset Point} {n : ℕ} (e : Fin n ≃ F) (π : Equiv.Perm (Fin n)) :
    MetricTSP.tourCost (fun i j => edist (e i).1 (e j).1) π =
      cyc (List.ofFn (fun i => (e (π i)).1)) := by
  rw [cyc_ofFn]; rfl

lemma finRotate_pow_zero (m : ℕ) : ∀ (j : ℕ) (hj : j < m + 1),
    ((finRotate (m + 1)) ^ j) 0 = ⟨j, hj⟩
  | 0, _ => by simp
  | j + 1, hj => by
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_pow_zero m j (by omega)]
    exact finRotate_of_lt (by omega)

lemma tourCost_mul_pow {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) (j : ℕ) :
    MetricTSP.tourCost c (π * (finRotate n) ^ j) = MetricTSP.tourCost c π := by
  unfold MetricTSP.tourCost
  have hcomm : ∀ i, ((finRotate n) ^ j) (finRotate n i) = finRotate n (((finRotate n) ^ j) i) := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_succ', ← pow_succ]
  simp only [Equiv.Perm.mul_apply, hcomm]
  exact Equiv.sum_comp ((finRotate n) ^ j) (fun i => c (π i) (π (finRotate n i)))

lemma tspOpt_set_finite {n : ℕ} (c : Fin n → Fin n → ℝ) :
    {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = MetricTSP.tourCost c π}.Finite := by
  have : {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = MetricTSP.tourCost c π} =
      Set.range (MetricTSP.tourCost c) := by
    ext t; simp [eq_comm]
  rw [this]; exact Set.finite_range _

lemma tspOpt_set_nonempty {n : ℕ} (c : Fin n → Fin n → ℝ) :
    {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = MetricTSP.tourCost c π}.Nonempty :=
  ⟨_, 1, rfl⟩

lemma tspOpt_le {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    MetricTSP.tspOpt c ≤ MetricTSP.tourCost c π :=
  csInf_le (tspOpt_set_finite c).bddBelow ⟨π, rfl⟩

lemma tspOpt_attained {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), MetricTSP.tspOpt c = MetricTSP.tourCost c π :=
  (tspOpt_set_nonempty c).csInf_mem (tspOpt_set_finite c)

/-- A list of all points of `F` from a permutation. -/
lemma ofFn_perm_props {F : Finset Point} {n : ℕ} (e : Fin n ≃ F) (π : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i => (e (π i)).1)).Nodup ∧
      (List.ofFn (fun i => (e (π i)).1)).toFinset = F := by
  constructor
  · rw [List.nodup_ofFn]
    intro i j h
    exact π.injective (e.injective (Subtype.val_injective h))
  · ext x
    simp only [List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩; exact (e (π i)).2
    · intro hx
      refine ⟨π.symm (e.symm ⟨x, hx⟩), ?_⟩
      simp

lemma tspOpt_attained_list {F : Finset Point} {n : ℕ} (e : Fin n ≃ F) :
    ∃ l : List Point, l.Nodup ∧ l.toFinset = F ∧
      cyc l = MetricTSP.tspOpt (fun i j => edist (e i).1 (e j).1) := by
  obtain ⟨π, hπ⟩ := tspOpt_attained (fun i j => edist (e i).1 (e j).1)
  refine ⟨_, (ofFn_perm_props e π).1, (ofFn_perm_props e π).2, ?_⟩
  rw [hπ, tourCost_eq_cyc]

lemma tspOpt_attained_list_head {F : Finset Point} {n : ℕ} (e : Fin n ≃ F) {a : Point}
    (ha : a ∈ F) :
    ∃ l : List Point, (a :: l).Nodup ∧ (a :: l).toFinset = F ∧
      cyc (a :: l) = MetricTSP.tspOpt (fun i j => edist (e i).1 (e j).1) := by
  obtain ⟨π, hπ⟩ := tspOpt_attained (fun i j => edist (e i).1 (e j).1)
  rcases n with _ | m
  · exact (e.symm ⟨a, ha⟩).elim0
  set i0 : Fin (m + 1) := π.symm (e.symm ⟨a, ha⟩) with hi0
  set π' : Equiv.Perm (Fin (m + 1)) := π * (finRotate (m + 1)) ^ (i0.val) with hπ'
  have hπ'0 : (e (π' 0)).1 = a := by
    rw [hπ', Equiv.Perm.mul_apply, finRotate_pow_zero m i0.val i0.isLt, Fin.eta, hi0]
    simp
  have hl := ofFn_perm_props e π'
  rw [List.ofFn_succ, hπ'0] at hl
  refine ⟨_, hl.1, hl.2, ?_⟩
  rw [hπ, ← tourCost_mul_pow _ π i0.val, ← hπ', tourCost_eq_cyc, List.ofFn_succ, hπ'0]

/-- A list of all the points of `F` gives a permutation, hence an upper bound. -/
lemma tspOpt_le_cyc_aux : ∀ {F : Finset Point} {n : ℕ} (e : Fin n ≃ F) (l : List Point),
    l.Nodup → l.toFinset = F → l.length = n →
      MetricTSP.tspOpt (fun i j => edist (e i).1 (e j).1) ≤ cyc l := by
  intro F n e l hl hF hn
  subst hn
  have hmem : ∀ i : Fin l.length, l.get i ∈ F := by
    intro i; rw [← hF, List.mem_toFinset]; exact List.get_mem l i
  let f : Fin l.length → F := fun i => ⟨l.get i, hmem i⟩
  have hinj : Function.Injective f := by
    intro i j h
    exact (List.nodup_iff_injective_get.mp hl) (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin l.length) = Fintype.card F := by
    rw [Fintype.card_fin, Fintype.card_coe, ← hF, List.toFinset_card_of_nodup hl]
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  let g : Fin l.length ≃ F := Equiv.ofBijective f hbij
  let π : Equiv.Perm (Fin l.length) := g.trans e.symm
  have key : ∀ i, (e (π i)).1 = l.get i := by
    intro i
    simp [π, g, f]
  calc MetricTSP.tspOpt (fun i j => edist (e i).1 (e j).1)
      ≤ MetricTSP.tourCost (fun i j => edist (e i).1 (e j).1) π := tspOpt_le _ π
    _ = cyc (List.ofFn (fun i => (e (π i)).1)) := tourCost_eq_cyc e π
    _ = cyc l := by simp only [key, List.ofFn_get]

lemma tourLength_le_cyc {F : Finset Point} (l : List Point) (hl : l.Nodup) (hF : l.toFinset = F) :
    tourLength F ≤ cyc l := by
  unfold tourLength
  apply tspOpt_le_cyc_aux _ l hl hF
  rw [← List.toFinset_card_of_nodup hl, hF, Fintype.card_coe]

lemma tourLength_attained (F : Finset Point) :
    ∃ l : List Point, l.Nodup ∧ l.toFinset = F ∧ cyc l = tourLength F := by
  unfold tourLength
  exact tspOpt_attained_list _

lemma tourLength_attained_head {F : Finset Point} {a : Point} (ha : a ∈ F) :
    ∃ l : List Point, (a :: l).Nodup ∧ (a :: l).toFinset = F ∧ cyc (a :: l) = tourLength F := by
  unfold tourLength
  exact tspOpt_attained_list_head _ ha

lemma tourLength_nonneg (F : Finset Point) : 0 ≤ tourLength F := by
  obtain ⟨l, _, _, hl⟩ := tourLength_attained F
  rw [← hl]; exact cyc_nonneg l

lemma tourLength_empty : tourLength ∅ = 0 :=
  le_antisymm (tourLength_le_cyc [] List.nodup_nil (by simp)) (tourLength_nonneg _)

/-- Monotonicity of the optimal tour length. -/
lemma tourLength_mono (F G : Finset Point) : tourLength F ≤ tourLength (F ∪ G) := by
  classical
  by_cases hF : F = ∅
  · subst hF; rw [tourLength_empty, Finset.empty_union]; exact tourLength_nonneg G
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  obtain ⟨l, hnd, hto, hc⟩ := tourLength_attained_head (F := F ∪ G) (a := a) (Finset.mem_union_left G ha)
  rw [← hc]
  have hsub : List.Sublist (l.filter (fun x => decide (x ∈ F))) l := List.filter_sublist
  calc tourLength F ≤ cyc (a :: l.filter (fun x => decide (x ∈ F))) := by
        apply tourLength_le_cyc
        · rw [List.nodup_cons] at hnd ⊢
          exact ⟨fun h => hnd.1 (List.mem_of_mem_filter h), hnd.2.filter _⟩
        · ext x
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.mem_filter,
            decide_eq_true_eq]
          constructor
          · rintro (rfl | ⟨_, h⟩)
            · exact ha
            · exact h
          · intro hx
            by_cases hxa : x = a
            · exact Or.inl hxa
            · right
              refine ⟨?_, hx⟩
              have : x ∈ (a :: l).toFinset := by rw [hto]; exact Finset.mem_union_left G hx
              simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
              exact this.resolve_left hxa
    _ ≤ cyc (a :: l) := cyc_cons_sublist a hsub

/-! ### Short paths through points of a square -/

/-- Membership in the axis-parallel square with lower-left corner `(a0, a1)` and side `s`. -/
def InSq (a0 a1 s : ℝ) (p : Point) : Prop :=
  a0 ≤ (p 0 : ℝ) ∧ (p 0 : ℝ) ≤ a0 + s ∧ a1 ≤ (p 1 : ℝ) ∧ (p 1 : ℝ) ≤ a1 + s

lemma InSq.edist_le {a0 a1 s : ℝ} {p q : Point} (hp : InSq a0 a1 s p) (hq : InSq a0 a1 s q) :
    edist p q ≤ 2 * s := by
  obtain ⟨hp0, hp1, hp2, hp3⟩ := hp
  obtain ⟨hq0, hq1, hq2, hq3⟩ := hq
  have := edist_le_abs_add p q
  have h0 : |(p 0 : ℝ) - q 0| ≤ s := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h1 : |(p 1 : ℝ) - q 1| ≤ s := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/-- Telescoping bound along a list whose consecutive steps satisfy a one-step bound. -/
lemma pathLen_pairwise_bound (S : Point → Prop) (st : Point → ℕ) (ds s : ℝ)
    (R : Point → Point → Prop)
    (hstep : ∀ p q, S p → S q → R p q →
      edist p q ≤ ds + ((q 1 : ℝ) - p 1) + 3 * s * ((st q : ℝ) - st p)) :
    ∀ (l : List Point) (h : l ≠ []), (∀ p ∈ l, S p) → l.Pairwise R →
      pathLen l ≤ ((l.length : ℝ) - 1) * ds +
        (((l.getLast h) 1 : ℝ) - (l.head h) 1) +
        3 * s * ((st (l.getLast h) : ℝ) - st (l.head h))
  | [], h, _, _ => absurd rfl h
  | [a], _, _, _ => by simp
  | a :: b :: l, _, hS, hR => by
    rw [List.pairwise_cons] at hR
    have h1 := hstep a b (hS a (by simp)) (hS b (by simp)) (hR.1 b (by simp))
    have h2 := pathLen_pairwise_bound S st ds s R hstep (b :: l) (by simp)
      (fun p hp => hS p (List.mem_cons_of_mem a hp)) hR.2
    simp only [List.getLast_cons_cons, List.head_cons, List.length_cons] at h2 ⊢
    rw [pathLen_cons_cons]
    push_cast at h2 ⊢
    linarith

lemma exists_short_path (a0 a1 s : ℝ) (hs : 0 < s) (G : Finset Point)
    (hG : ∀ p ∈ G, InSq a0 a1 s p) (hne : G.Nonempty) :
    ∃ l : List Point, l.Nodup ∧ l.toFinset = G ∧
      pathLen l ≤ 8 * s * Real.sqrt G.card := by
  classical
  set m := G.card with hm
  have hm1 : 1 ≤ m := hne.card_pos
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsqm : 1 ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact hmR
  set r : ℕ := ⌈Real.sqrt m⌉₊ with hr
  have hr1 : 1 ≤ r := Nat.one_le_ceil_iff.mpr (by linarith)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < r := by linarith
  have hr_ge : Real.sqrt m ≤ r := Nat.le_ceil _
  have hr_le : (r : ℝ) ≤ Real.sqrt m + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  -- the strip index
  let u : Point → ℝ := fun p => ((p 0 : ℝ) - a0) * r / s
  let st : Point → ℕ := fun p => ⌊u p⌋₊
  have hu0 : ∀ p, InSq a0 a1 s p → 0 ≤ u p := by
    intro p hp
    have := hp.1
    simp only [u]
    apply div_nonneg _ hs.le
    exact mul_nonneg (by linarith) hrpos.le
  have hur : ∀ p, InSq a0 a1 s p → u p ≤ r := by
    intro p hp
    have := hp.2.1
    simp only [u]
    rw [div_le_iff₀ hs]
    nlinarith
  have hst_le : ∀ p, InSq a0 a1 s p → (st p : ℝ) ≤ r := by
    intro p hp
    exact (Nat.floor_le (hu0 p hp)).trans (hur p hp)
  have hst_nonneg : ∀ p, (0 : ℝ) ≤ st p := fun p => by positivity
  have hsame : ∀ p q, InSq a0 a1 s p → InSq a0 a1 s q → st p = st q →
      |(p 0 : ℝ) - q 0| ≤ s / r := by
    intro p q hp hq hpq
    have h1 := Nat.floor_le (hu0 p hp)
    have h2 := Nat.lt_floor_add_one (u p)
    have h3 := Nat.floor_le (hu0 q hq)
    have h4 := Nat.lt_floor_add_one (u q)
    simp only [st] at hpq
    rw [hpq] at h1 h2
    have hdiff : |u p - u q| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have hu : u p - u q = ((p 0 : ℝ) - q 0) * r / s := by simp only [u]; ring
    rw [hu, abs_div, abs_mul, abs_of_pos hs, abs_of_pos hrpos, div_le_one hs] at hdiff
    rw [le_div_iff₀ hrpos]
    exact hdiff
  let R : Point → Point → Prop := fun p q => st p < st q ∨ (st p = st q ∧ (p 1 : ℝ) ≤ q 1)
  let le : Point → Point → Bool := fun p q => decide (R p q)
  have hle : ∀ p q, le p q = true ↔ R p q := by intro p q; simp [le]
  have htrans : ∀ p q w, le p q → le q w → le p w := by
    intro p q w h1 h2
    rw [hle] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨h1.trans h2, h1'.trans h2'⟩
  have htotal : ∀ p q, le p q || le q p := by
    intro p q
    rw [Bool.or_eq_true, hle, hle]
    rcases lt_trichotomy (st p) (st q) with h | h | h
    · left; left; exact h
    · rcases le_total ((p 1 : ℝ)) (q 1) with h' | h'
      · left; right; exact ⟨h, h'⟩
      · right; right; exact ⟨h.symm, h'⟩
    · right; left; exact h
  -- the one-step bound
  have hstep : ∀ p q, InSq a0 a1 s p → InSq a0 a1 s q → R p q →
      edist p q ≤ s / r + ((q 1 : ℝ) - p 1) + 3 * s * ((st q : ℝ) - st p) := by
    intro p q hp hq hR
    rcases hR with h | ⟨h, h'⟩
    · have h1 := InSq.edist_le hp hq
      have h2 : (st p : ℝ) + 1 ≤ st q := by exact_mod_cast h
      have h3 : a1 ≤ (p 1 : ℝ) := hp.2.2.1
      have h4 : (p 1 : ℝ) ≤ a1 + s := hp.2.2.2
      have h5 : a1 ≤ (q 1 : ℝ) := hq.2.2.1
      have h6 : (q 1 : ℝ) ≤ a1 + s := hq.2.2.2
      have h7 : 0 ≤ s / r := div_nonneg hs.le hrpos.le
      nlinarith
    · have h1 := edist_le_abs_add p q
      have h2 := hsame p q hp hq h
      have h3 : |(p 1 : ℝ) - q 1| = (q 1 : ℝ) - p 1 := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [h, sub_self, mul_zero]
      linarith
  -- the sorted list
  let l : List Point := G.toList.mergeSort le
  have hperm : l.Perm G.toList := List.mergeSort_perm _ _
  have hnd : l.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList G)
  have hto : l.toFinset = G := by
    rw [List.toFinset_eq_of_perm _ _ hperm, Finset.toList_toFinset]
  have hmem : ∀ p ∈ l, InSq a0 a1 s p := by
    intro p hp
    exact hG p (Finset.mem_toList.mp (hperm.mem_iff.mp hp))
  have hpw : l.Pairwise R := by
    have := List.pairwise_mergeSort htrans htotal G.toList
    exact this.imp (fun h => (hle _ _).mp h)
  have hlne : l ≠ [] := by
    intro h
    have : G = ∅ := by rw [← hto, h]; rfl
    exact hne.ne_empty this
  have hlen : l.length = m := by
    rw [hm, ← hto, List.toFinset_card_of_nodup hnd]
  refine ⟨l, hnd, hto, ?_⟩
  have hb := pathLen_pairwise_bound (InSq a0 a1 s) st (s / r) s R hstep l hlne hmem hpw
  rw [hlen] at hb
  have hhead := hmem _ (List.head_mem hlne)
  have hlast := hmem _ (List.getLast_mem hlne)
  have hy : ((l.getLast hlne) 1 : ℝ) - (l.head hlne) 1 ≤ s := by
    have := hhead.2.2.1; have := hlast.2.2.2; linarith
  have hstd : (st (l.getLast hlne) : ℝ) - st (l.head hlne) ≤ r := by
    have := hst_le _ hlast; have := hst_nonneg (l.head hlne); linarith
  have hdiv : ((m : ℝ) - 1) * (s / r) ≤ s * Real.sqrt m := by
    rw [mul_div_assoc', div_le_iff₀ hrpos]
    have h1 : (m : ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt (by linarith)).symm
    have h2 : s * Real.sqrt m * Real.sqrt m ≤ s * Real.sqrt m * r :=
      mul_le_mul_of_nonneg_left hr_ge (by positivity)
    nlinarith
  calc pathLen l ≤ _ := hb
    _ ≤ s * Real.sqrt m + s + 3 * s * r := by nlinarith
    _ ≤ s * Real.sqrt m + s + 3 * s * (Real.sqrt m + 1) := by nlinarith
    _ ≤ 8 * s * Real.sqrt m := by nlinarith

/-! ### The regularity lemma -/

lemma mem_dyadicSquare_iff_InSq (k : ℕ) (c : Grid k) (p : Point) :
    p ∈ dyadicSquare k c ↔
      InSq ((c 0).val * (2 : ℝ) ^ (-(k : ℤ))) ((c 1).val * (2 : ℝ) ^ (-(k : ℤ)))
        ((2 : ℝ) ^ (-(k : ℤ))) p := by
  simp only [dyadicSquare, Set.mem_setOf_eq, InSq, Fin.forall_fin_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
    refine ⟨h0, ?_, h2, ?_⟩ <;> linarith
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨h0, ?_⟩, ⟨h2, ?_⟩⟩ <;> linarith

theorem regular_tour_core : ∃ K : ℝ, 0 < K ∧ Regular K tourLength := by
  classical
  refine ⟨28, by norm_num, ?_⟩
  intro k _ F G c hG hx
  obtain ⟨x, hxF, y, hyC, hxy⟩ := hx
  refine ⟨tourLength_mono F G, ?_⟩
  set s : ℝ := (2 : ℝ) ^ (-(k : ℤ)) with hs
  have hspos : 0 < s := by positivity
  have h4s : (2 : ℝ) ^ (-(k : ℤ) + 2) = 4 * s := by
    have h22 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    rw [zpow_add₀ (two_ne_zero) (-(k : ℤ)) 2, ← hs, h22]; ring
  rw [h4s] at hxy
  set G' := G \ F with hG'
  have hFG : F ∪ G = F ∪ G' := by rw [hG', Finset.union_sdiff_self_eq_union]
  rw [hFG]
  have hcard : (G'.card : ℝ) ≤ G.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  have hsqrt : Real.sqrt G'.card ≤ Real.sqrt G.card := Real.sqrt_le_sqrt hcard
  by_cases hG'e : G' = ∅
  · rw [hG'e, Finset.union_empty]
    have : 0 ≤ 28 * s * Real.sqrt G.card := by positivity
    linarith
  have hne : G'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hG'e
  have hG'sq : ∀ p ∈ G', InSq ((c 0).val * s) ((c 1).val * s) s p := by
    intro p hp
    rw [← mem_dyadicSquare_iff_InSq]
    exact hG p (Finset.mem_sdiff.mp hp).1
  obtain ⟨lG, hGnd, hGto, hGlen⟩ := exists_short_path _ _ s hspos G' hG'sq hne
  have hlGne : lG ≠ [] := by
    intro h; rw [h] at hGto; exact hne.ne_empty (by rw [← hGto]; rfl)
  obtain ⟨l1, hFnd, hFto, hFc⟩ := tourLength_attained_head hxF
  have hmemG : ∀ p ∈ lG, p ∈ G' := fun p hp => by rw [← hGto]; exact List.mem_toFinset.mpr hp
  have hmemF : ∀ p ∈ (x :: l1), p ∈ F := fun p hp => by rw [← hFto]; exact List.mem_toFinset.mpr hp
  -- the new tour
  have hnd : (x :: (lG ++ l1)).Nodup := by
    rw [List.nodup_cons] at hFnd ⊢
    rw [List.nodup_append]
    refine ⟨?_, hGnd, hFnd.2, ?_⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact (Finset.mem_sdiff.mp (hmemG x h)).2 hxF
      · exact hFnd.1 h
    · intro p hp q hq hpq
      subst hpq
      exact (Finset.mem_sdiff.mp (hmemG p hp)).2 (hmemF p (List.mem_cons_of_mem x hq))
  have hto : (x :: (lG ++ l1)).toFinset = F ∪ G' := by
    ext p
    simp only [List.toFinset_cons, List.toFinset_append, Finset.mem_insert, Finset.mem_union,
      List.mem_toFinset, Finset.mem_union]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inl hxF
      · exact Or.inr (hmemG p h)
      · exact Or.inl (hmemF p (List.mem_cons_of_mem x h))
    · rintro (h | h)
      · have : p ∈ (x :: l1).toFinset := by rw [hFto]; exact h
        simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
        rcases this with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl (by rw [← hGto] at h; exact List.mem_toFinset.mp h))
  have hg1 : lG.head hlGne ∈ G' := hmemG _ (List.head_mem hlGne)
  have hdist : edist x (lG.head hlGne) ≤ 6 * s := by
    have h1 := edist_triangle' x y (lG.head hlGne)
    have h2 : edist y (lG.head hlGne) ≤ 2 * s := by
      apply InSq.edist_le (a0 := (c 0).val * s) (a1 := (c 1).val * s)
      · rw [← mem_dyadicSquare_iff_InSq]; exact hyC
      · exact hG'sq _ hg1
    linarith
  have hm1 : 1 ≤ Real.sqrt G'.card := by
    rw [Real.one_le_sqrt]; exact_mod_cast hne.card_pos
  calc tourLength (F ∪ G') ≤ cyc (x :: (lG ++ l1)) := tourLength_le_cyc _ hnd hto
    _ ≤ cyc (x :: l1) + 2 * edist x (lG.head hlGne) + 2 * pathLen lG := cyc_insert x lG l1 hlGne
    _ ≤ tourLength F + 2 * (6 * s) + 2 * (8 * s * Real.sqrt G'.card) := by
        rw [hFc]; linarith
    _ ≤ tourLength F + 28 * s * Real.sqrt G.card := by nlinarith

end TalagrandConc.TSP

open TalagrandConc.TSP


theorem solution : ∃ K : ℝ, 0 < K ∧ Regular K tourLength := by
  exact regular_tour_core
