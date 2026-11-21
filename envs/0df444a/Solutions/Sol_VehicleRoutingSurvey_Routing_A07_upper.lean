-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.A07_upper
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:51:30.186711+00:00
-- url     : https://prove2.me/submissions/c2f66ce0-cbe9-4b5c-9c0f-8249c147e7c3

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

open Fin.NatCast

namespace Aux_A07_upper

open TSPHeuristics.Shared

section Lists
variable {α : Type} (d : α → α → ℝ)

/-- length of the path starting at `x` and then visiting `l` -/
def pl : α → List α → ℝ
  | _, [] => 0
  | x, y :: r => d x y + pl y r

/-- last vertex of the path `x :: l` -/
def lst : α → List α → α
  | x, [] => x
  | _, y :: r => lst y r

def cyc (L : List α) : ℝ := (List.zipWith d L (L.rotate 1)).sum

theorem zip_eq (x0 : α) : ∀ (x : α) (l : List α),
    (List.zipWith d (x :: l) (l ++ [x0])).sum = pl d x l + d (lst x l) x0
  | x, [] => by simp [pl, lst]
  | x, y :: r => by
    have ih := zip_eq x0 y r
    show (List.zipWith d (x :: y :: r) (y :: (r ++ [x0]))).sum = _
    rw [List.zipWith_cons_cons, List.sum_cons, ih]
    simp only [pl, lst]
    ring

theorem rot1 (x : α) (l : List α) : (x :: l).rotate 1 = l ++ [x] := by
  simp

theorem cyc_cons (x : α) (l : List α) : cyc d (x :: l) = pl d x l + d (lst x l) x := by
  unfold cyc
  rw [rot1]
  exact zip_eq d x x l

theorem pl_append (y : α) (m : List α) : ∀ (x : α) (l : List α),
    pl d x (l ++ y :: m) = pl d x l + d (lst x l) y + pl d y m
  | x, [] => by simp [pl, lst]
  | x, z :: r => by
    have ih := pl_append y m z r
    show d x z + pl d z (r ++ y :: m) = _
    rw [ih]
    simp only [pl, lst]
    ring

theorem lst_append (y : α) (m : List α) : ∀ (x : α) (l : List α),
    lst x (l ++ y :: m) = lst y m
  | x, [] => by simp [lst]
  | x, z :: r => by
    have ih := lst_append y m z r
    show lst z (r ++ y :: m) = _
    exact ih

theorem cyc_snoc (x : α) (l : List α) : cyc d (l ++ [x]) = cyc d (x :: l) := by
  cases l with
  | nil => rfl
  | cons y r =>
    show cyc d (y :: (r ++ [x])) = _
    rw [cyc_cons, cyc_cons, pl_append, lst_append]
    simp only [pl, lst]
    ring

theorem cyc_rotate : ∀ (k : ℕ) (l : List α), cyc d (l.rotate k) = cyc d l
  | 0, l => by rw [List.rotate_zero]
  | k + 1, [] => by rw [List.rotate_nil]
  | k + 1, x :: l => by
    rw [List.rotate_cons_succ, cyc_rotate k, cyc_snoc]

theorem cyc_append_rot (s L : List α) : cyc d (s ++ L) = cyc d (L ++ s) := by
  rw [← cyc_rotate d s.length (s ++ L), List.rotate_append_length_eq]

theorem insertIdx_len (x : α) (l : List α) : ∀ s : List α,
    (s ++ l).insertIdx s.length x = s ++ x :: l
  | [] => by simp
  | z :: r => by
    show (z :: (r ++ l)).insertIdx (r.length + 1) x = z :: (r ++ x :: l)
    rw [List.insertIdx_succ_cons, insertIdx_len x l r]

end Lists

section Fin
variable {n : ℕ} (d : Fin n → Fin n → ℝ)

theorem cl_eq (L : List (Fin n)) : cycleLength d L = cyc d L := rfl

theorem ins (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (v w : List (Fin n)) (x b : Fin n) (hb : b ∈ v) (hI : IsInsertion d v x w) :
    w.Perm (x :: v) ∧ cyc d w ≤ cyc d v + 2 * d x b := by
  obtain ⟨_, pos, hpos, rfl, hmin⟩ := hI
  refine ⟨List.perm_insertIdx x v hpos, ?_⟩
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have h1 := hmin s.length (by simp)
  rw [cl_eq, cl_eq, insertIdx_len] at h1
  refine le_trans h1 ?_
  rw [cyc_append_rot d s (x :: b :: t), cyc_append_rot d s (b :: t)]
  show cyc d (x :: b :: (t ++ s)) ≤ cyc d (b :: (t ++ s)) + 2 * d x b
  rw [cyc_cons, cyc_cons]
  simp only [pl, lst]
  have := htri (lst b (t ++ s)) b x
  have h2 := hsymm b x
  linarith

theorem merge (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hdiag : ∀ i, d i i = 0)
    (u v w : List (Fin n)) (a b : Fin n) (ha : a ∈ u) (hb : b ∈ v)
    (hm : VehicleRoutingSurvey.Routing.MinimumMerge d u v w) :
    w.Perm (u ++ v) ∧ cyc d w ≤ cyc d u + cyc d v + 2 * d a b := by
  rcases hm with ⟨a', rfl, hI⟩ | ⟨b', rfl, hI⟩ | ⟨_, _, hsp, hmin⟩
  · have hae : a' = a := (List.mem_singleton.mp ha).symm
    rw [hae] at hI ⊢
    obtain ⟨h1, h2⟩ := ins d hsymm htri v w a b hb hI
    refine ⟨h1, ?_⟩
    have : cyc d [a] = 0 := by
      rw [cyc_cons]; simp [pl, lst, hdiag]
    linarith
  · have hbe : b' = b := (List.mem_singleton.mp hb).symm
    rw [hbe] at hI ⊢
    obtain ⟨h1, h2⟩ := ins d hsymm htri u w b a ha hI
    refine ⟨h1.trans (List.perm_append_singleton b u).symm, ?_⟩
    have : cyc d [b] = 0 := by
      rw [cyc_cons]; simp [pl, lst, hdiag]
    have := hsymm b a
    linarith
  · unfold VehicleRoutingSurvey.Routing.SpliceCandidate at hsp
    obtain ⟨i, j, r, _, _, hw⟩ := hsp
    constructor
    · rw [hw]
      have hX : (if r then v.reverse else v).Perm v := by
        cases r <;> simp [List.reverse_perm]
      exact List.Perm.append (List.rotate_perm u i) ((List.rotate_perm _ j).trans hX)
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
      obtain ⟨s', t', rfl⟩ := List.append_of_mem hb
      have hz : VehicleRoutingSurvey.Routing.SpliceCandidate (s ++ a :: t) (s' ++ b :: t')
          ((a :: (t ++ s)) ++ (b :: (t' ++ s'))) := by
        unfold VehicleRoutingSurvey.Routing.SpliceCandidate
        refine ⟨s.length, s'.length, false, by simp, by simp, ?_⟩
        simp [List.rotate_append_length_eq]
      have h1 := hmin _ hz
      rw [cl_eq, cl_eq] at h1
      refine le_trans h1 ?_
      rw [cyc_append_rot d s, cyc_append_rot d s']
      show cyc d (a :: (t ++ s ++ b :: (t' ++ s'))) ≤
        cyc d (a :: (t ++ s)) + cyc d (b :: (t' ++ s')) + 2 * d a b
      rw [cyc_cons, cyc_cons, cyc_cons, pl_append, lst_append]
      have h3 := htri (lst a (t ++ s)) a b
      have h4 := htri (lst b (t' ++ s')) b a
      have h5 := hsymm a b
      linarith

end Fin

theorem uniq {α : Type} : ∀ (S : List (List α)), S.flatten.Nodup →
    ∀ p ∈ S, ∀ q ∈ S, ∀ x, x ∈ p → x ∈ q → p = q
  | [], _, p, hp, _, _, _, _, _ => by simp at hp
  | s :: S, h, p, hp, q, hq, x, hxp, hxq => by
    rw [List.flatten_cons, List.nodup_append] at h
    obtain ⟨_, h2, h3⟩ := h
    rcases List.mem_cons.mp hp with hp' | hp' <;> rcases List.mem_cons.mp hq with hq' | hq'
    · rw [hp', hq']
    · subst hp'
      exact absurd rfl (h3 x hxp x (List.mem_flatten.mpr ⟨q, hq', hxq⟩))
    · subst hq'
      exact absurd rfl (h3 x hxq x (List.mem_flatten.mpr ⟨p, hp', hxp⟩))
    · exact uniq S h2 p hp' q hq' x hxp hxq

theorem nodupS {α : Type} : ∀ (S : List (List α)), S.flatten.Nodup → (∀ p ∈ S, p ≠ []) → S.Nodup
  | [], _, _ => List.nodup_nil
  | s :: S, h, hne => by
    have h' := h
    rw [List.flatten_cons, List.nodup_append] at h'
    refine List.nodup_cons.mpr ⟨fun hs => ?_, nodupS S h'.2.1 (fun p hp => hne p (by simp [hp]))⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil s (hne s (by simp))
    exact h'.2.2 x hx x (List.mem_flatten.mpr ⟨s, hs, hx⟩) rfl

theorem disc {ι : Type} [DecidableEq ι] (a : ℕ → ℝ) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∀ (m : ℕ) (B : Finset ι), m ≤ B.card →
      (∀ k < m, (B.filter (fun i => b i < a k)).card ≤ k) →
      ∑ k ∈ Finset.range m, a k ≤ ∑ i ∈ B, b i := by
  intro m
  induction m with
  | zero =>
    intro B _ _
    simp only [Finset.range_zero, Finset.sum_empty]
    exact Finset.sum_nonneg (fun i _ => hb i)
  | succ m ih =>
    intro B hcard hcnt
    have hm := hcnt m (Nat.lt_succ_self m)
    obtain ⟨i, hi, hai⟩ : ∃ i ∈ B, a m ≤ b i := by
      by_contra hall
      push_neg at hall
      have : B.filter (fun i => b i < a m) = B := Finset.filter_true_of_mem hall
      rw [this] at hm
      omega
    have hc' : m ≤ (B.erase i).card := by
      rw [Finset.card_erase_of_mem hi]; omega
    have hcnt' : ∀ k < m, ((B.erase i).filter (fun i => b i < a k)).card ≤ k := by
      intro k hk
      refine le_trans (Finset.card_le_card ?_) (hcnt k (by omega))
      exact Finset.filter_subset_filter _ (Finset.erase_subset _ _)
    have h1 := ih (B.erase i) hc' hcnt'
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase B b hi]
    linarith

theorem count {m : ℕ} {β : Type} [DecidableEq β] (g : Fin (m + 1) → β) (π : ℕ → Fin (m + 1)) :
    ∀ j, ((Finset.range (j + 1)).image (fun i => g (π i))).card ≤
      1 + ((Finset.range j).filter (fun i => ¬ g (π i) = g (π (i + 1)))).card := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.range_add_one (n := j + 1), Finset.image_insert]
    by_cases hc : g (π (j + 1)) = g (π j)
    · have hmem : g (π (j + 1)) ∈ (Finset.range (j + 1)).image (fun i => g (π i)) := by
        rw [hc]; exact Finset.mem_image_of_mem _ (by simp)
      rw [Finset.insert_eq_of_mem hmem]
      refine le_trans ih ?_
      have : (Finset.range j).filter (fun i => ¬ g (π i) = g (π (i + 1))) ⊆
          (Finset.range (j + 1)).filter (fun i => ¬ g (π i) = g (π (i + 1))) :=
        Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (Nat.le_succ j))
      have := Finset.card_le_card this
      omega
    · have hf : (Finset.range (j + 1)).filter (fun i => ¬ g (π i) = g (π (i + 1))) =
          insert j ((Finset.range j).filter (fun i => ¬ g (π i) = g (π (i + 1)))) := by
        rw [Finset.range_add_one (n := j), Finset.filter_insert, if_pos (fun h => hc h.symm)]
      have hj : j ∉ (Finset.range j).filter (fun i => ¬ g (π i) = g (π (i + 1))) := by simp
      rw [hf, Finset.card_insert_of_notMem hj]
      have := Finset.card_insert_le (g (π (j + 1))) ((Finset.range (j + 1)).image (fun i => g (π i)))
      omega

end Aux_A07_upper

open Aux_A07_upper TSPHeuristics.Shared in
theorem solution :
    ∀ (n : ℕ), 1 ≤ n → ∀ (d : Fin n → Fin n → ℝ),
    TSPHeuristics.Shared.IsTSPDist d → ∀ (T : List (Fin n)), VehicleRoutingSurvey.Routing.NearestMergerRun d T →
      TSPHeuristics.Shared.cycleLength d (T) ≤ 2 * TSPHeuristics.Shared.optimal d := by
  intro n hn d hd T hrun
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsymm : ∀ i j, d i j = d j i := hd.symm
  have htri : ∀ i j k, d i k ≤ d i j + d j k := hd.triangle
  have hdiag : ∀ i, d i i = 0 := hd.diag
  have hnn : ∀ i j, 0 ≤ d i j := hd.nonneg
  unfold VehicleRoutingSurvey.Routing.NearestMergerRun at hrun
  obtain ⟨S, hS0, hstep, hfin⟩ := hrun
  unfold VehicleRoutingSurvey.Routing.NearestMergeStep at hstep
  choose u v rest w a b hP hP' ha hb hclose hmerge using hstep
  let δ : ℕ → ℝ := fun k => if h : k + 1 < m + 1 then d (a k h) (b k h) else 0
  have hδ : ∀ k (h : k + 1 < m + 1), δ k = d (a k h) (b k h) := by
    intro k h; simp only [δ, dif_pos h]
  -- invariant
  have inv : ∀ k, k ≤ m → (S k).flatten.Perm (List.finRange (m + 1)) ∧ (∀ p ∈ S k, p ≠ []) ∧
      (S k).length = m + 1 - k ∧
      ((S k).map (cycleLength d)).sum ≤ 2 * ∑ j ∈ Finset.range k, δ j := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hS0]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have : ∀ l : List (Fin (m + 1)), (l.map (fun v => [v])).flatten = l := by
          intro l
          induction l with
          | nil => rfl
          | cons x l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]
        rw [this]
      · intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨x, _, rfl⟩ := hp
        simp
      · simp
      · have : ∀ x : Fin (m + 1), cycleLength d [x] = 0 := by
          intro x; rw [cl_eq, cyc_cons]; simp [pl, lst, hdiag]
        simp [List.map_map, Function.comp_def, this]
    | succ k ih =>
      intro hk
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      have hk1 : k + 1 < m + 1 := by omega
      obtain ⟨hwp, hwc⟩ := merge d hsymm htri hdiag (u k hk1) (v k hk1) (w k hk1) (a k hk1) (b k hk1)
        (ha k hk1) (hb k hk1) (hmerge k hk1)
      have hPk := hP k hk1
      have hPk' := hP' k hk1
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine hPk'.flatten.trans ?_
        refine List.Perm.trans ?_ (hPk.flatten.symm.trans i1)
        simp only [List.flatten_cons]
        rw [← List.append_assoc]
        exact hwp.append_right _
      · intro p hp
        rcases List.mem_cons.mp (hPk'.mem_iff.mp hp) with h | h
        · rw [h]
          intro hnil
          have : a k hk1 ∈ w k hk1 := hwp.mem_iff.mpr (List.mem_append_left _ (ha k hk1))
          rw [hnil] at this
          simp at this
        · exact i2 p (hPk.mem_iff.mpr (by simp [h]))
      · rw [hPk'.length_eq]
        have := hPk.length_eq
        simp only [List.length_cons] at this ⊢
        omega
      · rw [(hPk'.map (cycleLength d)).sum_eq]
        have e2 := (hPk.map (cycleLength d)).sum_eq
        simp only [List.map_cons, List.sum_cons] at e2 ⊢
        rw [e2] at i4
        rw [Finset.sum_range_succ, hδ k hk1]
        rw [cl_eq d (w k hk1)]
        rw [cl_eq d (u k hk1), cl_eq d (v k hk1)] at i4
        linarith
  -- optimal tour
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin (m + 1))))
    (tourLength d)
  have hopt : optimal d = tourLength d τ := hτ
  let π : ℕ → Fin (m + 1) := fun i => τ (i : Fin (m + 1))
  let bb : ℕ → ℝ := fun i => d (π i) (π (i + 1))
  have htour : tourLength d τ = ∑ i ∈ Finset.range (m + 1), bb i := by
    unfold tourLength
    rw [← Fin.sum_univ_eq_sum_range bb]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [bb, π, finRotate_succ_apply, Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self]
  -- Kruskal-type bound
  have hkr : ∑ k ∈ Finset.range m, δ k ≤ ∑ i ∈ Finset.range m, bb i := by
    refine disc δ bb (fun i => hnn _ _) m (Finset.range m) (by simp) ?_
    intro k hk
    have hk1 : k + 1 < m + 1 := by omega
    obtain ⟨i1, i2, i3, _⟩ := inv k (by omega)
    have hnd : (S k).flatten.Nodup := i1.nodup_iff.mpr (List.nodup_finRange _)
    have cover : ∀ x, ∃ p ∈ S k, x ∈ p := by
      intro x
      have : x ∈ (S k).flatten := i1.mem_iff.mpr (List.mem_finRange x)
      exact List.mem_flatten.mp this
    choose g hgS hgx using cover
    have himg : Finset.univ.image g = (S k).toFinset := by
      ext p
      simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨x, rfl⟩; exact hgS x
      · intro hp
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil p (i2 p hp)
        exact ⟨x, uniq (S k) hnd _ (hgS x) p hp x (hgx x) hx⟩
    have hcardS : (Finset.univ.image g).card = m + 1 - k := by
      rw [himg, List.toFinset_card_of_nodup (nodupS (S k) hnd i2), i3]
    have hsurj : Finset.univ.image g ⊆ (Finset.range (m + 1)).image (fun i => g (π i)) := by
      intro p hp
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      refine Finset.mem_image.mpr ⟨(τ.symm x).val, Finset.mem_range.mpr (τ.symm x).isLt, ?_⟩
      simp [π, Fin.cast_val_eq_self]
    have hc := count g π m
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range m)
      (fun i => g (π i) = g (π (i + 1)))
    have hle := Finset.card_le_card hsurj
    have hsub : (Finset.range m).filter (fun i => bb i < δ k) ⊆
        (Finset.range m).filter (fun i => g (π i) = g (π (i + 1))) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      by_contra hne
      have h1 := hclose k hk1 (g (π i)) (hgS _) (g (π (i + 1))) (hgS _) hne (π i) (hgx _)
        (π (i + 1)) (hgx _)
      rw [← hδ k hk1] at h1
      exact absurd hi.2 (not_lt.mpr h1)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at hsplit
    omega
  have hpath : ∑ i ∈ Finset.range m, bb i ≤ ∑ i ∈ Finset.range (m + 1), bb i := by
    rw [Finset.sum_range_succ]
    have : 0 ≤ bb m := hnn _ _
    linarith
  obtain ⟨_, _, _, i4⟩ := inv m le_rfl
  have hfin' : S m = [T] := by simpa using hfin
  rw [hfin'] at i4
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at i4
  rw [hopt, htour]
  linarith
