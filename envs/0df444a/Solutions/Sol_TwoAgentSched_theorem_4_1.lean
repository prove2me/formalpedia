-- Prove2me | solution 1 for TwoAgentSched.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T14:55:34.275467+00:00
-- url     : https://prove2.me/submissions/ec8530dd-3038-4f46-934a-b610e4585a5c

import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_sortC
import Definitions.Def_TwoAgentSched_cpAlgo
import Definitions.Def_TwoAgentSched_fAmax
import Definitions.Def_TwoAgentSched_IsDeadline

namespace TwoAgentSched
namespace TasT41

@[simp] lemma bind_val {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).val = (f x.val).val := rfl
@[simp] lemma bind_cost {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl
@[simp] lemma pure_val {α : Type} (a : α) : (pure a : Timed α).val = a := rfl
@[simp] lemma pure_cost {α : Type} (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] lemma tick_cost : tick.cost = 1 := rfl
@[simp] lemma ticks_cost (k : ℕ) : (ticks k).cost = k := rfl
@[simp] lemma leC_val {κ : Type} [LinearOrder κ] (a b : κ) : (leC a b).val = decide (a ≤ b) := rfl
@[simp] lemma leC_cost {κ : Type} [LinearOrder κ] (a b : κ) : (leC a b).cost = 1 := rfl
@[simp] lemma addC_val {R : Type} [Add R] (a b : R) : (addC a b).val = a + b := rfl
@[simp] lemma addC_cost {R : Type} [Add R] (a b : R) : (addC a b).cost = 1 := rfl
@[simp] lemma subC_val {R : Type} [Sub R] (a b : R) : (subC a b).val = a - b := rfl
@[simp] lemma subC_cost {R : Type} [Sub R] (a b : R) : (subC a b).cost = 1 := rfl
@[simp] lemma evalC_val {R S : Type} (f : R → S) (t : R) : (evalC f t).val = f t := rfl
@[simp] lemma evalC_cost {R S : Type} (f : R → S) (t : R) : (evalC f t).cost = 1 := rfl
@[simp] lemma lookupC_val {ι S : Type} (D : ι → S) (k : ι) : (lookupC D k).val = D k := rfl
@[simp] lemma lookupC_cost {ι S : Type} (D : ι → S) (k : ι) : (lookupC D k).cost = 1 := rfl

variable {β : Type} {κ : Type} [LinearOrder κ]

lemma mergeC_val (key : β → κ) : ∀ xs ys : List β,
    (mergeC key xs ys).val = List.merge xs ys (fun a b => decide (key a ≤ key b)) := by
  intro xs
  induction xs with
  | nil => intro ys; rw [mergeC]; simp
  | cons x xs ihx =>
    intro ys
    induction ys with
    | nil => rw [mergeC]; simp
    | cons y ys ihy =>
      rw [mergeC, List.merge]
      by_cases h : key x ≤ key y
      · simp [h, ihx]
      · simp [h, ihy]

lemma mergeC_cost (key : β → κ) : ∀ xs ys : List β,
    (mergeC key xs ys).cost ≤ 2 * (xs.length + ys.length) + 1 := by
  intro xs
  induction xs with
  | nil => intro ys; rw [mergeC]; simp
  | cons x xs ihx =>
    intro ys
    induction ys with
    | nil => rw [mergeC]; simp
    | cons y ys ihy =>
      rw [mergeC]
      by_cases h : key x ≤ key y
      · simp [h]; have := ihx (y :: ys); simp at this; omega
      · simp [h]; simp at ihy; omega

lemma sortC_spec (key : β → κ) : ∀ n, ∀ l : List β, l.length = n →
    (sortC key l).val.Perm l ∧ (sortC key l).val.Pairwise (fun a b => key a ≤ key b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    match l with
    | [] => rw [sortC]; simp
    | [x] => rw [sortC]; simp
    | x :: y :: zs =>
      rw [sortC]
      simp only [bind_val, mergeC_val]
      set m := (zs.length + 2) / 2
      have hlen : (x :: y :: zs).length = zs.length + 2 := by simp
      obtain ⟨p1, s1⟩ := ih _ (by simp at hl ⊢; omega) ((x :: y :: zs).take m) rfl
      obtain ⟨p2, s2⟩ := ih _ (by simp at hl ⊢; omega) ((x :: y :: zs).drop m) rfl
      refine ⟨?_, ?_⟩
      · refine (List.merge_perm_append _).trans ?_
        refine (p1.append p2).trans ?_
        rw [List.take_append_drop]
      · have := List.pairwise_merge (le := fun a b => decide (key a ≤ key b))
          (fun a b c hab hbc => by simp at *; exact le_trans hab hbc)
          (fun a b => by simpa using le_total _ _) _ _ (by simpa using s1) (by simpa using s2)
        simpa using this

lemma sortC_length (key : β → κ) (l : List β) : (sortC key l).val.length = l.length :=
  (sortC_spec key _ l rfl).1.length_eq

lemma sortC_cost (key : β → κ) : ∀ k : ℕ, ∀ l : List β, l.length ≤ 2 ^ k →
    (sortC key l).cost ≤ 4 * l.length * k := by
  intro k
  induction k with
  | zero =>
    intro l hl
    match l with
    | [] => rw [sortC]; simp
    | [x] => rw [sortC]; simp
    | x :: y :: zs => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => rw [sortC]; simp
    | [x] => rw [sortC]; simp
    | x :: y :: zs =>
      rw [sortC]
      simp only [bind_cost, ticks_cost]
      have h1 := ih ((x :: y :: zs).take ((zs.length + 2) / 2))
        (by simp; rw [pow_succ] at hl; simp at hl; omega)
      have h2 := ih ((x :: y :: zs).drop ((zs.length + 2) / 2))
        (by simp; rw [pow_succ] at hl; simp at hl; omega)
      have h3 := mergeC_cost key (sortC key ((x :: y :: zs).take ((zs.length + 2) / 2))).val
        (sortC key ((x :: y :: zs).drop ((zs.length + 2) / 2))).val
      rw [sortC_length, sortC_length] at h3
      simp only [List.length_take, List.length_drop, List.length_cons] at h1 h2 h3 ⊢
      have e : min ((zs.length + 2) / 2) (zs.length + 1 + 1) = (zs.length + 2) / 2 := by omega
      rw [e] at h1 h3
      have e2 : (zs.length + 1 + 1 - (zs.length + 2) / 2) + (zs.length + 2) / 2 = zs.length + 2 := by omega
      nlinarith

section algo
variable {nA nB : ℕ} {R : Type} [LinearOrder R]

lemma argminC_nil (fA : Fin nA → R → R) (τ : R) : (argminC fA τ []).val = none := by
  simp [argminC]

lemma argminC_cons (fA : Fin nA → R → R) (τ : R) : ∀ (a : Fin nA) (l : List (Fin nA)),
    ∃ h v, (argminC fA τ (a :: l)).val = some (h, v) ∧ h ∈ a :: l ∧ v = fA h τ ∧
      ∀ h' ∈ a :: l, v ≤ fA h' τ := by
  intro a l
  induction l generalizing a with
  | nil => exact ⟨a, fA a τ, by simp [argminC], by simp, rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨h, v, hv, hm, hvv, hall⟩ := ih b
    by_cases hc : fA a τ ≤ v
    · refine ⟨a, fA a τ, ?_, by simp, rfl, ?_⟩
      · rw [argminC]; simp [hv, hc]
      · intro h' hh'
        rcases List.mem_cons.1 hh' with rfl | hh'
        · exact le_rfl
        · exact hc.trans (hall h' hh')
    · refine ⟨h, v, ?_, List.mem_cons_of_mem _ hm, hvv, ?_⟩
      · rw [argminC]; simp [hv, hc]
      · intro h' hh'
        rcases List.mem_cons.1 hh' with rfl | hh'
        · exact (lt_of_not_ge hc).le
        · exact hall h' hh'

lemma argminC_cost (fA : Fin nA → R → R) (τ : R) : ∀ l : List (Fin nA),
    (argminC fA τ l).cost ≤ 3 * l.length := by
  intro l
  induction l with
  | nil => simp [argminC]
  | cons a l ih =>
    rw [argminC]
    simp only [bind_cost, tick_cost, evalC_cost, List.length_cons]
    split <;> simp <;> (try split_ifs) <;> (try simp) <;> omega

lemma eraseC_val {ι : Type} [DecidableEq ι] (x : ι) : ∀ l : List ι, (eraseC x l).val = l.erase x := by
  intro l
  induction l with
  | nil => simp [eraseC]
  | cons y l ih =>
    rw [eraseC]
    by_cases h : y = x
    · subst h; simp
    · simp [h, ih]

lemma eraseC_cost {ι : Type} [DecidableEq ι] (x : ι) : ∀ l : List ι, (eraseC x l).cost ≤ l.length := by
  intro l
  induction l with
  | nil => simp [eraseC]
  | cons y l ih =>
    rw [eraseC]
    by_cases h : y = x
    · subst h; simp
    · simp [h]; omega

lemma scanA_cons (fA : Fin nA → R → R) (τ : R) (a : Fin nA) (l : List (Fin nA)) :
    ∃ h, (scanA fA τ (a :: l)).val = some (h, (a :: l).erase h) ∧ h ∈ a :: l ∧
      (∀ h' ∈ a :: l, fA h τ ≤ fA h' τ) ∧ (scanA fA τ (a :: l)).cost ≤ 4 * (l.length + 1) := by
  obtain ⟨h, v, hv, hm, rfl, hall⟩ := argminC_cons fA τ a l
  refine ⟨h, ?_, hm, hall, ?_⟩
  · simp [scanA, hv, eraseC_val]
  · have h1 := argminC_cost fA τ (a :: l)
    have h2 := eraseC_cost h (a :: l)
    simp only [scanA, bind_cost, hv, pure_cost] at h1 h2 ⊢
    simp at h1 h2 ⊢
    omega

lemma cpLoop_cost [Sub R] (p : Job nA nB → R) (fA : Fin nA → R → R)
    (D : Fin nB → WithTop (R ×ₗ Bool)) : ∀ fuel τ As Bs acc,
    (cpLoop p fA D fuel τ As Bs acc).cost ≤
      4 * Bs.length + 4 * As.length * As.length + 4 * As.length := by
  intro fuel
  induction fuel with
  | zero => intros; simp [cpLoop]
  | succ n ih =>
    intro τ As Bs acc
    rcases Bs with _ | ⟨k, Bs'⟩
    · rcases As with _ | ⟨a, As'⟩
      · simp [cpLoop]
      · obtain ⟨h, hv, hm, -, hc⟩ := scanA_cons fA τ a As'
        have := ih (τ - p (Sum.inl h)) ((a :: As').erase h) [] (Sum.inl h :: acc)
        rw [List.length_erase_of_mem hm] at this
        simp [cpLoop, hv]
        simp at this
        nlinarith
    · by_cases hk : ((toLex (τ, true) : R ×ₗ Bool) : WithTop (R ×ₗ Bool)) ≤ D k
      · have := ih (τ - p (Sum.inr k)) As Bs' (Sum.inr k :: acc)
        simp [cpLoop, hk]
        omega
      · rcases As with _ | ⟨a, As'⟩
        · simp [cpLoop, hk]; omega
        · obtain ⟨h, hv, hm, -, hc⟩ := scanA_cons fA τ a As'
          have := ih (τ - p (Sum.inl h)) ((a :: As').erase h) (k :: Bs') (Sum.inl h :: acc)
          rw [List.length_erase_of_mem hm] at this
          simp [cpLoop, hv, hk]
          simp at this
          nlinarith

end algo

lemma sumC_val {R : Type} {ι : Type} [AddCommMonoid R] (p : ι → R) : ∀ l : List ι, (sumC p l).val = (l.map p).sum := by
  intro l
  induction l with
  | nil => simp [sumC]
  | cons y l ih => simp [sumC, ih]

lemma sumC_cost {R : Type} {ι : Type} [Add R] [Zero R] (p : ι → R) : ∀ l : List ι, (sumC p l).cost = l.length := by
  intro l
  induction l with
  | nil => simp [sumC]
  | cons y l ih => simp [sumC, ih]

section seq
variable {ι : Type} [DecidableEq ι]

lemma seqC_append_of_mem (p : ι → ℝ) {L M : List ι} {j : ι} (hj : j ∈ L) :
    seqC p (L ++ M) j = seqC p L j := by
  unfold seqC
  rw [List.idxOf_append_of_mem hj, List.take_append_of_le_length]
  exact List.idxOf_lt_length_of_mem hj

lemma seqC_append_singleton (p : ι → ℝ) {L : List ι} {j : ι} (hj : j ∉ L) :
    seqC p (L ++ [j]) j = (L.map p).sum + p j := by
  unfold seqC
  rw [List.idxOf_append_of_notMem hj, List.take_of_length_le] <;> simp

lemma seqC_eq (p : ι → ℝ) {σ : List ι} {j : ι} (hj : j ∈ σ) :
    seqC p σ j = ((σ.take (σ.idxOf j)).map p).sum + p j := by
  unfold seqC
  rw [List.take_add_one, List.getElem?_idxOf hj]
  simp

omit [DecidableEq ι] in
lemma sum_take_mono (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : List ι) {m n : ℕ} (h : m ≤ n) :
    ((σ.take m).map p).sum ≤ ((σ.take n).map p).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  have : 0 ≤ (((σ.drop m).take d).map p).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hp y)
  linarith

lemma seqC_feasible (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) {σ : List ι} (hσ : IsSeq σ) :
    Feasible p (fun j => seqC p σ j - p j) := by
  have base : ∀ j, ((σ.take (σ.idxOf j)).map p).sum ≥ 0 := fun j =>
    List.sum_nonneg (by intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hp y)
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · show 0 ≤ seqC p σ j - p j
    rw [seqC_eq p (hσ.2 j)]; linarith [base j]
  · have hne : σ.idxOf i ≠ σ.idxOf j := fun h => hij ((List.idxOf_inj (hσ.2 i)).1 h)
    show seqC p σ i - p i + p i ≤ seqC p σ j - p j ∨ seqC p σ j - p j + p j ≤ seqC p σ i - p i
    simp only [sub_add_cancel]
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have := sum_take_mono p hp σ (Nat.succ_le_of_lt h)
      rw [seqC_eq p (hσ.2 j)]; unfold seqC; linarith
    · right
      have := sum_take_mono p hp σ (Nat.succ_le_of_lt h)
      rw [seqC_eq p (hσ.2 i)]; unfold seqC; linarith

lemma exists_late (p : ι → ℝ) (S : ι → ℝ) (hS : Feasible p S) :
    ∀ n, ∀ U : Finset ι, U.card = n → U.Nonempty → ∃ j ∈ U, ∑ i ∈ U, p i ≤ S j + p j := by
  intro n
  induction n with
  | zero => intro U hU hne; simp [Finset.card_eq_zero.1 hU] at hne
  | succ n ih =>
    intro U hU hne
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image U S hne
    rw [← Finset.add_sum_erase U p hx]
    rcases (U.erase x).eq_empty_or_nonempty with he | he
    · refine ⟨x, hx, ?_⟩
      rw [he]; simp; exact hS.1 x
    · obtain ⟨i, hi, hsum⟩ := ih (U.erase x) (by rw [Finset.card_erase_of_mem hx]; omega) he
      have hix : i ≠ x := Finset.ne_of_mem_erase hi
      have hSi := hmax i (Finset.mem_of_mem_erase hi)
      rcases hS.2 i x hix with h | h
      · exact ⟨x, hx, by linarith⟩
      · exact ⟨i, Finset.mem_of_mem_erase hi, by linarith⟩

lemma exists_late_list (p : ι → ℝ) (S : ι → ℝ) (hS : Feasible p S) (U : List ι) (hU : U.Nodup)
    (hne : U ≠ []) : ∃ j ∈ U, (U.map p).sum ≤ S j + p j := by
  obtain ⟨j, hj, h⟩ := exists_late p S hS _ U.toFinset rfl
    (by obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne; exact ⟨a, by simp⟩)
  rw [List.sum_toFinset p hU] at h
  exact ⟨j, List.mem_toFinset.1 hj, h⟩

end seq

section main
variable {nA nB : ℕ}

/-- the unscheduled jobs -/
def UJ (As : List (Fin nA)) (Bs : List (Fin nB)) : List (Job nA nB) :=
  As.map Sum.inl ++ Bs.map Sum.inr

def LoopSpec (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (As : List (Fin nA)) (Bs : List (Fin nB)) (acc : List (Job nA nB)) :
    Option (List (Job nA nB)) → Prop
  | some σ => ∃ L, σ = L ++ acc ∧ L.Perm (UJ As Bs) ∧
      (∀ k ∈ Bs, fB k (seqC p L (Sum.inr k)) ≤ Q) ∧
      ∀ h ∈ As, ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
        ((fA h (seqC p L (Sum.inl h)) : ℝ) : EReal) ≤ fAmax fA (fun j => S j + p j)
  | none => ¬ ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)

variable (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
  (D : Fin nB → WithTop (ℝ ×ₗ Bool))

lemma sum_nonneg_of (hp : ∀ j, 0 ≤ p j) (l : List (Job nA nB)) : 0 ≤ (l.map p).sum :=
  List.sum_nonneg (by intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hp y)

/-- if every unscheduled B-job is late at `τ`, some unscheduled A-job ends at `≥ τ` -/
lemma blocked (hp : ∀ j, 0 ≤ p j) (hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0))
    (hD : ∀ k, IsDeadline (fB k) Q (D k)) (As : List (Fin nA)) (Bs : List (Fin nB)) (τ : ℝ)
    (hnd : (UJ As Bs).Nodup) (hτ : τ = ((UJ As Bs).map p).sum) (hne : UJ As Bs ≠ [])
    (hbl : ∀ k ∈ Bs, ¬ (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k)
    (S : Job nA nB → ℝ) (hS : Feasible p S) (hB : BOk fB Q (fun j => S j + p j)) :
    ∃ h ∈ As, τ ≤ S (Sum.inl h) + p (Sum.inl h) := by
  obtain ⟨j, hj, hle⟩ := exists_late_list p S hS _ hnd hne
  rw [← hτ] at hle
  have hτ0 : 0 ≤ τ := hτ ▸ sum_nonneg_of p hp _
  rcases j with h | k
  · refine ⟨h, ?_, hle⟩
    simpa [UJ] using hj
  · exfalso
    have hk : k ∈ Bs := by simpa [UJ] using hj
    have h1 : ¬ fB k τ ≤ Q := fun h => hbl k hk ((hD k τ hτ0).1 h)
    have h2 : fB k τ ≤ fB k (S (Sum.inr k) + p (Sum.inr k)) :=
      hfB k (Set.mem_Ici.2 hτ0) (Set.mem_Ici.2 (hτ0.trans hle)) hle
    exact h1 (h2.trans (hB k))

lemma stepB (hp : ∀ j, 0 ≤ p j) (hD : ∀ k, IsDeadline (fB k) Q (D k))
    (As : List (Fin nA)) (k : Fin nB) (Bs : List (Fin nB)) (acc : List (Job nA nB)) (τ : ℝ)
    (hnd : (UJ As (k :: Bs)).Nodup) (hτ : τ = ((UJ As (k :: Bs)).map p).sum)
    (hk : (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k)
    (r : Option (List (Job nA nB))) (hr : LoopSpec p fA fB Q As Bs (Sum.inr k :: acc) r) :
    LoopSpec p fA fB Q As (k :: Bs) acc r := by
  rcases r with _ | σ
  · exact hr
  obtain ⟨L, rfl, hperm, hBk, hAh⟩ := hr
  have hpm : (UJ As (k :: Bs)).Perm (Sum.inr k :: UJ As Bs) := by
    simp only [UJ, List.map_cons]; exact List.perm_middle
  have hnd' := hpm.nodup_iff.1 hnd
  have hnot : Sum.inr k ∉ L := fun h => (List.nodup_cons.1 hnd').1 (hperm.mem_iff.1 h)
  have hsum : τ = (L.map p).sum + p (Sum.inr k) := by
    rw [hτ, (hpm.map p).sum_eq, (hperm.map p).sum_eq]; simp [add_comm]
  have hτ0 : 0 ≤ τ := hτ ▸ sum_nonneg_of p hp _
  refine ⟨L ++ [Sum.inr k], by simp, ?_, ?_, ?_⟩
  · exact (List.perm_append_singleton _ _).trans ((hperm.cons _).trans hpm.symm)
  · intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [seqC_append_singleton p hnot, ← hsum]; exact (hD k' τ hτ0).2 hk
    · have hm : Sum.inr k' ∈ L := hperm.mem_iff.2 (by simp [UJ, hk'])
      rw [seqC_append_of_mem p hm]; exact hBk k' hk'
  · intro h hh
    have hm : Sum.inl h ∈ L := hperm.mem_iff.2 (by simp [UJ, hh])
    rw [seqC_append_of_mem p hm]; exact hAh h hh

lemma stepA (hp : ∀ j, 0 ≤ p j) (hfA : ∀ h, MonotoneOn (fA h) (Set.Ici 0))
    (hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0)) (hD : ∀ k, IsDeadline (fB k) Q (D k))
    (As : List (Fin nA)) (Bs : List (Fin nB)) (acc : List (Job nA nB)) (τ : ℝ) (h : Fin nA)
    (hnd : (UJ As Bs).Nodup) (hτ : τ = ((UJ As Bs).map p).sum) (hh : h ∈ As)
    (hmin : ∀ h' ∈ As, fA h τ ≤ fA h' τ)
    (hbl : ∀ k ∈ Bs, ¬ (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k)
    (r : Option (List (Job nA nB))) (hr : LoopSpec p fA fB Q (As.erase h) Bs (Sum.inl h :: acc) r) :
    LoopSpec p fA fB Q As Bs acc r := by
  rcases r with _ | σ
  · exact hr
  obtain ⟨L, rfl, hperm, hBk, hAh⟩ := hr
  have hpm : (UJ As Bs).Perm (Sum.inl h :: UJ (As.erase h) Bs) := by
    simp only [UJ]
    have := ((List.perm_cons_erase hh).map (Sum.inl : Fin nA → Job nA nB)).append_right
      (Bs.map (Sum.inr : Fin nB → Job nA nB))
    simpa using this
  have hnd' := hpm.nodup_iff.1 hnd
  have hnot : Sum.inl h ∉ L := fun h' => (List.nodup_cons.1 hnd').1 (hperm.mem_iff.1 h')
  have hsum : τ = (L.map p).sum + p (Sum.inl h) := by
    rw [hτ, (hpm.map p).sum_eq, (hperm.map p).sum_eq]; simp [add_comm]
  have hτ0 : 0 ≤ τ := hτ ▸ sum_nonneg_of p hp _
  refine ⟨L ++ [Sum.inl h], by simp, ?_, ?_, ?_⟩
  · exact (List.perm_append_singleton _ _).trans ((hperm.cons _).trans hpm.symm)
  · intro k hk
    have hm : Sum.inr k ∈ L := hperm.mem_iff.2 (by simp [UJ, hk])
    rw [seqC_append_of_mem p hm]; exact hBk k hk
  · intro h₁ hh₁ S hS hB
    by_cases he : h₁ = h
    · subst he
      rw [seqC_append_singleton p hnot, ← hsum]
      have hne : UJ As Bs ≠ [] := by
        intro e; rw [e] at hpm; exact List.Perm.nil_eq hpm |> fun e => by simp at e
      obtain ⟨h', hh', hle⟩ := blocked p fB Q D hp hfB hD As Bs τ hnd hτ hne hbl S hS hB
      have h2 : fA h' τ ≤ fA h' (S (Sum.inl h') + p (Sum.inl h')) :=
        hfA h' (Set.mem_Ici.2 hτ0) (Set.mem_Ici.2 (hτ0.trans hle)) hle
      have h3 := (hmin h' hh').trans h2
      refine (EReal.coe_le_coe_iff.2 h3).trans ?_
      unfold fAmax
      exact Finset.le_sup (f := fun h => ((fA h (S (Sum.inl h) + p (Sum.inl h)) : ℝ) : EReal))
        (Finset.mem_univ h')
    · have hm' : h₁ ∈ As.erase h := (List.mem_erase_of_ne he).2 hh₁
      have hm : Sum.inl h₁ ∈ L := hperm.mem_iff.2 (by simp [UJ, hm'])
      rw [seqC_append_of_mem p hm]; exact hAh h₁ hm' S hS hB

lemma loop_spec (hp : ∀ j, 0 ≤ p j) (hfA : ∀ h, MonotoneOn (fA h) (Set.Ici 0))
    (hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0)) (hD : ∀ k, IsDeadline (fB k) Q (D k)) :
    ∀ fuel τ As Bs acc, (UJ As Bs).Nodup → τ = ((UJ As Bs).map p).sum →
      Bs.Pairwise (fun a b => D b ≤ D a) → As.length + Bs.length < fuel →
      LoopSpec p fA fB Q As Bs acc (cpLoop p fA D fuel τ As Bs acc).val := by
  intro fuel
  induction fuel with
  | zero => intro τ As Bs acc _ _ _ hf; omega
  | succ n ih =>
    intro τ As Bs acc hnd hτ hs hf
    -- the A-step, shared by two branches
    have stepA' : ∀ (a : Fin nA) (As' : List (Fin nA)), As = a :: As' →
        (∀ k ∈ Bs, ¬ (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k) →
        ∀ h, (scanA fA τ (a :: As')).val = some (h, (a :: As').erase h) → h ∈ a :: As' →
        (∀ h' ∈ a :: As', fA h τ ≤ fA h' τ) →
        LoopSpec p fA fB Q As Bs acc
          (cpLoop p fA D n (τ - p (Sum.inl h)) ((a :: As').erase h) Bs (Sum.inl h :: acc)).val := by
      intro a As' hAs hbl h _ hm hmin
      subst hAs
      have hpm : (UJ (a :: As') Bs).Perm (Sum.inl h :: UJ ((a :: As').erase h) Bs) := by
        simp only [UJ]
        have := ((List.perm_cons_erase hm).map (Sum.inl : Fin nA → Job nA nB)).append_right
          (Bs.map (Sum.inr : Fin nB → Job nA nB))
        simpa using this
      apply stepA p fA fB Q D hp hfA hfB hD _ Bs acc τ h hnd hτ hm hmin hbl
      apply ih
      · exact (List.nodup_cons.1 (hpm.nodup_iff.1 hnd)).2
      · rw [hτ, (hpm.map p).sum_eq]; simp
      · exact hs
      · rw [List.length_erase_of_mem hm]; simp at hf ⊢; omega
    rcases Bs with _ | ⟨k, Bs'⟩
    · rcases As with _ | ⟨a, As'⟩
      · simp only [cpLoop, bind_val, pure_val]
        exact ⟨[], by simp, by simp [UJ], by simp, by simp⟩
      · obtain ⟨h, hv, hm, hmin, -⟩ := scanA_cons fA τ a As'
        have := stepA' a As' rfl (by simp) h hv hm hmin
        simpa [cpLoop, hv] using this
    · have hpm : (UJ As (k :: Bs')).Perm (Sum.inr k :: UJ As Bs') := by
        simp only [UJ, List.map_cons]; exact List.perm_middle
      by_cases hk : (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k
      · have := stepB p fA fB Q D hp hD As k Bs' acc τ hnd hτ hk _
          (ih (τ - p (Sum.inr k)) As Bs' (Sum.inr k :: acc)
            (List.nodup_cons.1 (hpm.nodup_iff.1 hnd)).2
            (by rw [hτ, (hpm.map p).sum_eq]; simp)
            (List.Pairwise.of_cons hs) (by simp at hf; omega))
        simpa [cpLoop, hk] using this
      · have hbl : ∀ k' ∈ k :: Bs', ¬ (((toLex (τ, true) : ℝ ×ₗ Bool)) : WithTop (ℝ ×ₗ Bool)) ≤ D k' := by
          intro k' hk' hle
          rcases List.mem_cons.1 hk' with rfl | hk'
          · exact hk hle
          · exact hk (hle.trans (List.rel_of_pairwise_cons hs hk'))
        rcases As with _ | ⟨a, As'⟩
        · have : LoopSpec p fA fB Q [] (k :: Bs') acc none := by
            rintro ⟨S, hS, hB⟩
            obtain ⟨h, hh, -⟩ := blocked p fB Q D hp hfB hD [] (k :: Bs') τ hnd hτ (by simp [UJ]) hbl S hS hB
            simp at hh
          simpa [cpLoop, hk] using this
        · obtain ⟨h, hv, hm, hmin, -⟩ := scanA_cons fA τ a As'
          have := stepA' a As' rfl hbl h hv hm hmin
          simpa [cpLoop, hv, hk] using this

end main

section final
variable {nA nB : ℕ}

lemma cpAlgo_val (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool)) :
    (cpAlgo p fA D).val = (cpLoop p fA D (nA + nB + 1)
      (sumC p (UJ (List.finRange nA) (List.finRange nB))).val (List.finRange nA)
      (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val []).val := rfl

lemma cpAlgo_cost (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool)) :
    (cpAlgo p fA D).cost = 2 * (nA + nB) + ((sumC p (UJ (List.finRange nA) (List.finRange nB))).cost +
      ((sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).cost +
      (cpLoop p fA D (nA + nB + 1)
      (sumC p (UJ (List.finRange nA) (List.finRange nB))).val (List.finRange nA)
      (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val []).cost)) := rfl

lemma cpAlgo_cost_nat (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool))
    (k : ℕ) (hk : nB ≤ 2 ^ k) :
    (cpAlgo p fA D).cost ≤ 3 * (nA + nB) + 4 * nB * k + 4 * nB + 4 * nA * nA + 4 * nA := by
  rw [cpAlgo_cost, sumC_cost]
  have h1 := sortC_cost (fun k => OrderDual.toDual (D k)) k (List.finRange nB) (by simpa using hk)
  have h2 := cpLoop_cost p fA D (nA + nB + 1)
      (sumC p (UJ (List.finRange nA) (List.finRange nB))).val (List.finRange nA)
      (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val []
  rw [sortC_length] at h2
  simp only [UJ, List.length_append, List.length_map, List.length_finRange] at h1 h2 ⊢
  omega

theorem cost_part (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool))
    (hne : ¬ (nA = 0 ∧ nB = 1)) :
    ((cpAlgo p fA D).cost : ℝ) ≤ 100 * ((nA : ℝ) ^ 2 + (nB : ℝ) * Real.log (nB : ℝ)) := by
  have hA : nA ≤ nA * nA := Nat.le_mul_self nA
  rcases Nat.lt_or_ge nB 2 with hb | hb
  · have h0 := cpAlgo_cost_nat p fA D 0 (by simp; omega)
    have hlog : (nB : ℝ) * Real.log nB = 0 := by
      interval_cases nB <;> simp
    have hnat : (cpAlgo p fA D).cost ≤ 18 * (nA * nA) := by
      interval_cases nB
      · nlinarith
      · have : 1 ≤ nA := by omega
        nlinarith
    rw [hlog]
    have : ((cpAlgo p fA D).cost : ℝ) ≤ 18 * ((nA : ℝ) * nA) := by exact_mod_cast hnat
    nlinarith
  · set L := Nat.log 2 nB with hLdef
    have hL : 1 ≤ L := Nat.log_pos (by norm_num) hb
    have h0 := cpAlgo_cost_nat p fA D (L + 1) (Nat.lt_pow_succ_log_self (by norm_num) nB).le
    have hnat : (cpAlgo p fA D).cost ≤ 11 * (nA * nA) + 15 * (nB * L) := by nlinarith
    have hpow : ((2 : ℕ) : ℝ) ^ L ≤ (nB : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlogL : (L : ℝ) * Real.log 2 ≤ Real.log nB := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by simpa using hpow)
    have hl2 := Real.log_two_gt_d9
    have hc : ((cpAlgo p fA D).cost : ℝ) ≤ 11 * ((nA : ℝ) * nA) + 15 * ((nB : ℝ) * L) := by
      exact_mod_cast hnat
    have hnB : (0 : ℝ) ≤ nB := by positivity
    have hnL : (0 : ℝ) ≤ (nB : ℝ) * L := by positivity
    have h1 : (nB : ℝ) * L * Real.log 2 ≤ nB * Real.log nB := by
      have := mul_le_mul_of_nonneg_left hlogL hnB; linarith
    have h2 : (nB : ℝ) * L * 0.6931471803 ≤ (nB : ℝ) * L * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le hnL
    nlinarith

end final

end TasT41

open TasT41

theorem theorem_4_1 :
    ∃ C : ℝ, ∀ (nA nB : ℕ) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
      (Q : ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool)),
      (∀ j, 0 ≤ p j) → (∀ h, MonotoneOn (fA h) (Set.Ici 0)) →
      (∀ k, MonotoneOn (fB k) (Set.Ici 0)) → (∀ k, IsDeadline (fB k) Q (D k)) →
      (((cpAlgo p fA D).val.isSome = true) ↔
          ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) ∧
      (∀ σ, (cpAlgo p fA D).val = some σ →
        IsSeq σ ∧ BOk fB Q (seqC p σ) ∧
        ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
          fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j)) ∧
      (¬ (nA = 0 ∧ nB = 1) →
        ((cpAlgo p fA D).cost : ℝ) ≤
          C * ((nA : ℝ) ^ 2 + (nB : ℝ) * Real.log (nB : ℝ))) := by
  refine ⟨100, ?_⟩
  intro nA nB p fA fB Q D hp hfA hfB hD
  obtain ⟨hperm, hsort⟩ := sortC_spec (fun k => OrderDual.toDual (D k)) _ (List.finRange nB) rfl
  have hnd0 : (UJ (List.finRange nA) (List.finRange nB)).Nodup := by
    unfold UJ
    refine List.Nodup.append ((List.nodup_finRange nA).map Sum.inl_injective)
      ((List.nodup_finRange nB).map Sum.inr_injective) ?_
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, -, hy⟩ := List.mem_map.1 hb
    cases hy
  have hpU : (UJ (List.finRange nA) (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val).Perm
      (UJ (List.finRange nA) (List.finRange nB)) := (hperm.map _).append_left _
  have hnd := hpU.nodup_iff.2 hnd0
  have hτ : (sumC p (UJ (List.finRange nA) (List.finRange nB))).val =
      ((UJ (List.finRange nA) (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val).map p).sum := by
    rw [sumC_val, (hpU.map p).sum_eq]
  have hs : (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val.Pairwise
      (fun a b => D b ≤ D a) := by simpa using hsort
  have hspec := loop_spec p fA fB Q D hp hfA hfB hD (nA + nB + 1) _ _ _ [] hnd hτ hs
    (by rw [sortC_length]; simp)
  rw [← cpAlgo_val] at hspec
  have hmemB : ∀ k, k ∈ (sortC (fun k => OrderDual.toDual (D k)) (List.finRange nB)).val :=
    fun k => hperm.mem_iff.2 (List.mem_finRange k)
  have hsome : ∀ σ, (cpAlgo p fA D).val = some σ →
      IsSeq σ ∧ BOk fB Q (seqC p σ) ∧
        ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
          fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j) := by
    intro σ hσ
    rw [hσ] at hspec
    obtain ⟨L, rfl, hL, hB, hA⟩ := hspec
    rw [List.append_nil]
    have hLnd : L.Nodup := hL.nodup_iff.2 hnd
    refine ⟨⟨hLnd, ?_⟩, fun k => hB k (hmemB k), ?_⟩
    · intro j
      rcases j with h | k
      · exact hL.mem_iff.2 (by simp [UJ])
      · exact hL.mem_iff.2 (by simp [UJ, hmemB])
    · intro S hS hBS
      show Finset.univ.sup _ ≤ _
      apply Finset.sup_le
      intro h _
      exact hA h (List.mem_finRange h) S hS hBS
  refine ⟨⟨?_, ?_⟩, hsome, cost_part p fA D⟩
  · intro hsm
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hsm
    obtain ⟨hseq, hB, -⟩ := hsome σ hσ
    refine ⟨fun j => seqC p σ j - p j, seqC_feasible p hp hseq, ?_⟩
    intro k
    simpa using hB k
  · intro hex
    rcases hr : (cpAlgo p fA D).val with _ | σ
    · rw [hr] at hspec; exact absurd hex hspec
    · rfl
end TwoAgentSched


-- Platform entry point: restates the target verbatim.
namespace TwoAgentSched

/-- **Theorem 4.1** (Agnetis–Mirchandani–Pacciarelli–Pacifici, *Scheduling Problems with Two
Competing Agents*, Oper. Res. 52(2) (2004), p. 233: "`1‖f^A_max : f^B_max` can be solved in time
`O(n_A² + n_B log n_B)`"), for the paper's own algorithm of §4 (pp. 232–233), `cpAlgo`; this is
stronger than the existence of some algorithm.

There is one absolute constant `C`, chosen before everything else, such that for all `n_A`,
`n_B`, nonnegative processing times `p`, cost functions `f^A_h`, `f^B_k` nondecreasing on
`[0, ∞)`, every real bound `Q`, and deadlines `D k` representing `f^B_k` and `Q` (cuts, see
`IsDeadline`; the algorithm reads agent B only through them), the run `cpAlgo p fA D`
(A) reports a schedule iff some feasible schedule satisfies `f^B_max ≤ Q`;
(B) when it returns `σ`, `σ` is a sequence of all jobs (a feasible schedule without idle time,
    `seqC_feasible`) satisfying `f^B_max ≤ Q`, and its `f^A_max` is at most that of every
    feasible schedule satisfying `f^B_max ≤ Q`;
(Cost) unless `n_A = 0` and `n_B = 1` (where the printed bound is `0`), it uses at most
    `C · (n_A² + n_B log n_B)` unit-cost steps. -/
theorem _root_.solution :
    ∃ C : ℝ, ∀ (nA nB : ℕ) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
      (Q : ℝ) (D : Fin nB → WithTop (ℝ ×ₗ Bool)),
      (∀ j, 0 ≤ p j) → (∀ h, MonotoneOn (fA h) (Set.Ici 0)) →
      (∀ k, MonotoneOn (fB k) (Set.Ici 0)) → (∀ k, IsDeadline (fB k) Q (D k)) →
      (((cpAlgo p fA D).val.isSome = true) ↔
          ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) ∧
      (∀ σ, (cpAlgo p fA D).val = some σ →
        IsSeq σ ∧ BOk fB Q (seqC p σ) ∧
        ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
          fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j)) ∧
      (¬ (nA = 0 ∧ nB = 1) →
        ((cpAlgo p fA D).cost : ℝ) ≤
          C * ((nA : ℝ) ^ 2 + (nB : ℝ) * Real.log (nB : ℝ))) := by
  apply @TwoAgentSched.theorem_4_1 <;> assumption

end TwoAgentSched
