-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.A06_upper
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:02:28.156493+00:00
-- url     : https://prove2.me/submissions/f3daed66-2599-491c-8deb-b969ba9367d8

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

open Fin.NatCast

namespace Aux_A06_upper

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

theorem before (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (x b : Fin n) (L : List (Fin n)) : cyc d (x :: b :: L) ≤ cyc d (b :: L) + 2 * d b x := by
  rw [cyc_cons, cyc_cons]
  simp only [pl, lst]
  have h1 := htri (lst b L) b x
  have h2 := hsymm b x
  linarith

theorem after (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hdiag : ∀ i, d i i = 0)
    (b x : Fin n) (L : List (Fin n)) : cyc d (b :: x :: L) ≤ cyc d (b :: L) + 2 * d b x := by
  cases L with
  | nil =>
    rw [cyc_cons, cyc_cons]
    simp only [pl, lst]
    have h1 := hdiag b
    have h2 := hsymm b x
    linarith
  | cons y L' =>
    rw [cyc_cons, cyc_cons]
    simp only [pl, lst]
    have h1 := htri x b y
    have h2 := hsymm x b
    linarith

theorem decomp (l : List (Fin n)) (q : ℕ) (x : Fin n) (h : l[q]? = some x) :
    ∃ s t, l = s ++ x :: t ∧ s.length = q := by
  obtain ⟨hq, hx⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨l.take q, l.drop (q + 1), ?_, by simp; omega⟩
  calc l = l.take q ++ l.drop q := (List.take_append_drop q l).symm
    _ = l.take q ++ x :: l.drop (q + 1) := by rw [← List.getElem_cons_drop hq, hx]

theorem addcost (hsymm : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hdiag : ∀ i, d i i = 0)
    (L : List (Fin n)) (x b : Fin n) (p : ℕ) (hp : p < L.length)
    (hpos : L[p]? = some b ∨ (L.rotate 1)[p]? = some b) :
    cyc d (L.insertIdx (p + 1) x) ≤ cyc d L + 2 * d b x := by
  rcases hpos with h | h
  · obtain ⟨s, t, rfl, hs⟩ := decomp L p b h
    have e : s ++ b :: t = (s ++ [b]) ++ t := by simp
    rw [e, show p + 1 = (s ++ [b]).length by simp [hs], insertIdx_len]
    rw [cyc_append_rot d (s ++ [b]) (x :: t), cyc_append_rot d (s ++ [b]) t,
      show (x :: t) ++ (s ++ [b]) = (x :: (t ++ s)) ++ [b] by simp,
      show t ++ (s ++ [b]) = (t ++ s) ++ [b] by simp, cyc_snoc, cyc_snoc]
    exact after d hsymm htri hdiag b x (t ++ s)
  · rw [List.getElem?_rotate hp] at h
    by_cases hlt : p + 1 < L.length
    · rw [Nat.mod_eq_of_lt hlt] at h
      obtain ⟨s, t, rfl, hs⟩ := decomp L (p + 1) b h
      rw [show p + 1 = s.length from hs.symm, insertIdx_len]
      rw [cyc_append_rot d s (x :: b :: t), cyc_append_rot d s (b :: t)]
      exact before d hsymm htri x b (t ++ s)
    · have hpl : p + 1 = L.length := by omega
      rw [hpl, Nat.mod_self] at h
      obtain ⟨s, t, rfl, hs⟩ := decomp L 0 b h
      have hs' : s = [] := List.length_eq_zero_iff.mp hs
      subst hs'
      rw [hpl, List.insertIdx_length_self, cyc_snoc]
      exact before d hsymm htri x b t

end Fin

theorem D2 {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (a : κ → ℝ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : ∀ (N : ℕ) (A : Finset κ) (B : Finset ι), A.card = N →
      (∀ t : ℝ, (A.filter (fun k => t < a k)).card ≤ (B.filter (fun i => t < b i)).card) →
      ∑ k ∈ A, a k ≤ ∑ i ∈ B, b i := by
  intro N
  induction N with
  | zero =>
    intro A B hA _
    rw [Finset.card_eq_zero.mp hA, Finset.sum_empty]
    exact Finset.sum_nonneg (fun i _ => hb i)
  | succ N ih =>
    intro A B hA hcnt
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k0, hk0, hk0max⟩ := Finset.exists_max_image A a hAne
    have hk0f : k0 ∈ A.filter (fun k => a k0 - 1 < a k) := by
      rw [Finset.mem_filter]; exact ⟨hk0, by linarith⟩
    have hBne : B.Nonempty := by
      have h1 := hcnt (a k0 - 1)
      have h2 : 0 < (A.filter (fun k => a k0 - 1 < a k)).card := Finset.card_pos.mpr ⟨k0, hk0f⟩
      have h3 : 0 < (B.filter (fun i => a k0 - 1 < b i)).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp h3
      exact ⟨i, (Finset.mem_filter.mp hi).1⟩
    obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image B b hBne
    have hge : a k0 ≤ b i0 := by
      by_contra hlt
      push_neg at hlt
      have h1 := hcnt (b i0)
      have h2 : 0 < (A.filter (fun k => b i0 < a k)).card :=
        Finset.card_pos.mpr ⟨k0, Finset.mem_filter.mpr ⟨hk0, hlt⟩⟩
      have h3 : B.filter (fun i => b i0 < b i) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi; exact not_lt.mpr (hi0max i hi)
      rw [h3, Finset.card_empty] at h1
      omega
    have hA' : (A.erase k0).card = N := by rw [Finset.card_erase_of_mem hk0]; omega
    have hcnt' : ∀ t : ℝ, ((A.erase k0).filter (fun k => t < a k)).card ≤
        ((B.erase i0).filter (fun i => t < b i)).card := by
      intro t
      by_cases ht : t < a k0
      · rw [Finset.filter_erase, Finset.filter_erase,
          Finset.card_erase_of_mem (show k0 ∈ A.filter (fun k => t < a k) from
            Finset.mem_filter.mpr ⟨hk0, ht⟩),
          Finset.card_erase_of_mem (show i0 ∈ B.filter (fun i => t < b i) from
            Finset.mem_filter.mpr ⟨hi0, lt_of_lt_of_le ht hge⟩)]
        have := hcnt t
        omega
      · have : (A.erase k0).filter (fun k => t < a k) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro k hk
          have := hk0max k (Finset.mem_of_mem_erase hk)
          push_neg at ht
          exact not_lt.mpr (le_trans this ht)
        rw [this, Finset.card_empty]
        exact Nat.zero_le _
    have h1 := ih (A.erase k0) (B.erase i0) hA' hcnt'
    rw [← Finset.add_sum_erase A a hk0, ← Finset.add_sum_erase B b hi0]
    linarith

end Aux_A06_upper

open Aux_A06_upper TSPHeuristics.Shared in
theorem solution :
    ∀ (n : ℕ), 1 ≤ n → ∀ (d : Fin n → Fin n → ℝ),
    TSPHeuristics.Shared.IsTSPDist d → ∀ (T : ℕ → List (Fin n)), VehicleRoutingSurvey.Routing.NearestAdditionRun d T →
      TSPHeuristics.Shared.cycleLength d (T (n - 1)) ≤ 2 * TSPHeuristics.Shared.optimal d := by
  intro n hn d hd T hrun
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsymm : ∀ i j, d i j = d j i := hd.symm
  have htri : ∀ i j k, d i k ≤ d i j + d j k := hd.triangle
  have hdiag : ∀ i, d i i = 0 := hd.diag
  have hnn : ∀ i j, 0 ≤ d i j := hd.nonneg
  unfold VehicleRoutingSurvey.Routing.NearestAdditionRun at hrun
  obtain ⟨⟨a0, hT0⟩, hstep⟩ := hrun
  choose a b p ha hb hclose hp hpos hT using hstep
  let δ : ℕ → ℝ := fun k => if h : k + 1 < m + 1 then d (b k h) (a k h) else 0
  have hδ : ∀ k (h : k + 1 < m + 1), δ k = d (b k h) (a k h) := by
    intro k h; simp only [δ, dif_pos h]
  -- cost along the run
  have hcost : ∀ k, k ≤ m → cycleLength d (T k) ≤ 2 * ∑ j ∈ Finset.range k, δ j := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hT0, cl_eq, cyc_cons]
      simp [pl, lst, hdiag]
    | succ k ih =>
      intro hk
      have hk1 : k + 1 < m + 1 := by omega
      have h1 := ih (by omega)
      rw [hT k hk1, cl_eq]
      rw [cl_eq] at h1
      have h2 := addcost d hsymm htri hdiag (T k) (a k hk1) (b k hk1) (p k hk1) (hp k hk1) (hpos k hk1)
      rw [Finset.sum_range_succ, hδ k hk1]
      linarith
  -- monotonicity of the vertex sets
  have hmono1 : ∀ k (hk : k + 1 < m + 1), ∀ x, x ∈ T k → x ∈ T (k + 1) := by
    intro k hk x hx
    rw [hT k hk]
    exact (List.mem_insertIdx (by have := hp k hk; omega)).mpr (Or.inr hx)
  have hmono : ∀ k e, k + e ≤ m → ∀ x, x ∈ T k → x ∈ T (k + e) := by
    intro k e
    induction e with
    | zero => intro _ x hx; exact hx
    | succ e ih =>
      intro hle x hx
      exact hmono1 (k + e) (by omega) x (ih (by omega) x hx)
  have hamem : ∀ k (hk : k + 1 < m + 1), a k hk ∈ T (k + 1) := by
    intro k hk
    rw [hT k hk]
    exact (List.mem_insertIdx (by have := hp k hk; omega)).mpr (Or.inl rfl)
  have ha0 : ∀ k, k ≤ m → a0 ∈ T k := by
    intro k hk
    have := hmono 0 k (by omega) a0 (by rw [hT0]; simp)
    simpa using this
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
  let idx : Fin (m + 1) → ℕ := fun x => (τ.symm x).val
  have hidx : ∀ x, π (idx x) = x := by
    intro x; simp [π, idx, Fin.cast_val_eq_self]
  have hidxle : ∀ x, idx x ≤ m := by
    intro x; have := (τ.symm x).isLt; simp only [idx]; omega
  -- Prim-type bound
  have hprim : ∀ t : ℝ, ((Finset.range m).filter (fun k => t < δ k)).card ≤
      ((Finset.range m).filter (fun i => t < bb i)).card := by
    intro t
    let comp : ℕ → ℕ := fun j => ((Finset.range j).filter (fun i => t < bb i)).card
    have comp_succ : ∀ l, comp (l + 1) = comp l + if t < bb l then 1 else 0 := by
      intro l
      simp only [comp]
      rw [Finset.range_add_one (n := l), Finset.filter_insert]
      by_cases hl : t < bb l
      · have hnm : l ∉ (Finset.range l).filter (fun i => t < bb i) := by simp
        rw [if_pos hl, if_pos hl, Finset.card_insert_of_notMem hnm]
      · simp [hl]
    have comp_mono : ∀ l l', l ≤ l' → comp l ≤ comp l' := by
      intro l l' hll
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hll))
    have prop : ∀ (P : Fin (m + 1) → Prop), (∀ i < m, bb i ≤ t → (P (π i) ↔ P (π (i + 1)))) →
        ∀ j e, j + e ≤ m → comp j = comp (j + e) → (P (π j) ↔ P (π (j + e))) := by
      intro P hP j e
      induction e with
      | zero => intro _ _; exact Iff.rfl
      | succ e ih =>
        intro hle hc
        have h1 : comp j ≤ comp (j + e) := comp_mono _ _ (by omega)
        have h2 := comp_succ (j + e)
        have hc' : comp j = comp (j + e + 1) := hc
        by_cases ht : t < bb (j + e)
        · rw [if_pos ht] at h2; omega
        · rw [if_neg ht] at h2
          have h3 := ih (by omega) (by omega)
          have h4 := hP (j + e) (by omega) (le_of_not_gt ht)
          exact h3.trans h4
    have prop' : ∀ (P : Fin (m + 1) → Prop), (∀ i < m, bb i ≤ t → (P (π i) ↔ P (π (i + 1)))) →
        ∀ j j', j ≤ m → j' ≤ m → comp j = comp j' → (P (π j) ↔ P (π j')) := by
      intro P hP j j' hj hj' hc
      rcases le_total j j' with h | h
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
        exact prop P hP j e hj' hc
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
        exact (prop P hP j' e hj hc.symm).symm
    have closed : ∀ k (hk : k + 1 < m + 1), t < δ k → ∀ i < m, bb i ≤ t →
        (π i ∈ T k ↔ π (i + 1) ∈ T k) := by
      intro k hk htk i _ hbi
      rw [hδ k hk] at htk
      constructor
      · intro hx
        by_contra hy
        have := hclose k hk (π i) hx (π (i + 1)) hy
        have : bb i = d (π i) (π (i + 1)) := rfl
        linarith
      · intro hy
        by_contra hx
        have := hclose k hk (π (i + 1)) hy (π i) hx
        have : bb i = d (π i) (π (i + 1)) := rfl
        have := hsymm (π i) (π (i + 1))
        linarith
    have comple : ∀ j ≤ m, comp j ≤ ((Finset.range m).filter (fun i => t < bb i)).card := by
      intro j hj
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega)))
    let F : ℕ → ℕ := fun k => if h : k + 1 < m + 1 then comp (idx (a k h)) else 0
    have hF : ∀ k (h : k + 1 < m + 1), F k = comp (idx (a k h)) := by
      intro k h; simp only [F, dif_pos h]
    have key : ∀ k (hk : k + 1 < m + 1), t < δ k → ∀ x y, x ∈ T k → comp (idx x) = comp (idx y) →
        y ∈ T k := by
      intro k hk htk x y hx hc
      have := prop' (fun z => z ∈ T k) (fun i hi hbi => closed k hk htk i hi hbi) (idx x) (idx y)
        (hidxle x) (hidxle y) hc
      simp only [hidx] at this
      exact this.mp hx
    have hmaps : ∀ k ∈ (Finset.range m).filter (fun k => t < δ k),
        F k ∈ (Finset.range (((Finset.range m).filter (fun i => t < bb i)).card + 1)).erase
          (comp (idx a0)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      have hk1 : k + 1 < m + 1 := by omega
      rw [hF k hk1, Finset.mem_erase, Finset.mem_range]
      refine ⟨fun heq => ?_, by have := comple _ (hidxle (a k hk1)); omega⟩
      exact ha k hk1 (key k hk1 hk.2 a0 (a k hk1) (ha0 k (by omega)) heq.symm)
    have hinj : Set.InjOn F ((Finset.range m).filter (fun k => t < δ k) : Set ℕ) := by
      intro k1 hk1 k2 hk2 heq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk1 hk2
      have hk1' : k1 + 1 < m + 1 := by omega
      have hk2' : k2 + 1 < m + 1 := by omega
      rw [hF k1 hk1', hF k2 hk2'] at heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hin : a k1 hk1' ∈ T k2 := by
          have := hmono (k1 + 1) (k2 - (k1 + 1)) (by omega) _ (hamem k1 hk1')
          rwa [show k1 + 1 + (k2 - (k1 + 1)) = k2 by omega] at this
        exact ha k2 hk2' (key k2 hk2' hk2.2 _ _ hin heq)
      · have hin : a k2 hk2' ∈ T k1 := by
          have := hmono (k2 + 1) (k1 - (k2 + 1)) (by omega) _ (hamem k2 hk2')
          rwa [show k2 + 1 + (k1 - (k2 + 1)) = k1 by omega] at this
        exact ha k1 hk1' (key k1 hk1' hk1.2 _ _ hin heq.symm)
    have hc := Finset.card_le_card_of_injOn F (fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk))) hinj
    have hmem0 : comp (idx a0) ∈
        Finset.range (((Finset.range m).filter (fun i => t < bb i)).card + 1) := by
      rw [Finset.mem_range]; have := comple _ (hidxle a0); omega
    rw [Finset.card_erase_of_mem hmem0, Finset.card_range] at hc
    omega
  have hkr : ∑ k ∈ Finset.range m, δ k ≤ ∑ i ∈ Finset.range m, bb i :=
    D2 δ bb (fun i => hnn _ _) _ (Finset.range m) (Finset.range m) rfl hprim
  have hpath : ∑ i ∈ Finset.range m, bb i ≤ ∑ i ∈ Finset.range (m + 1), bb i := by
    rw [Finset.sum_range_succ]
    have : 0 ≤ bb m := hnn _ _
    linarith
  have hfin := hcost m le_rfl
  rw [Nat.add_sub_cancel, hopt, htour]
  linarith
