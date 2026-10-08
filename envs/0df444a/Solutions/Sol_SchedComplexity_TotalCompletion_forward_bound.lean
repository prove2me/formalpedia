-- Prove2me | solution 1 for SchedComplexity.TotalCompletion.forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:02:42.27786+00:00
-- url     : https://prove2.me/submissions/25fc4e6c-64f9-4889-8373-2537e06b88a0

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction



namespace SchedComplexity.TotalCompletion

theorem tc_lt_of_le {ι : Type*} (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    {j k : ι} (hjk : j ≠ k) (h : B j ≤ B k) : B j + p j ≤ B k := by
  by_contra hc
  push Not at hc
  exact hd j k hjk ⟨by have := hpos k; omega, hc⟩

theorem tc_chain {ι : Type*} [DecidableEq ι] (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    (s0 q : ℕ) (S : Finset ι) (hS : ∀ k ∈ S, s0 ≤ B k ∧ q ≤ p k) :
    (∀ z, z ∉ S → s0 ≤ B z → (∀ k ∈ S, B k < B z) → s0 + S.card * q ≤ B z) ∧
    2 * (S.card * s0) + q * (S.card * (S.card + 1)) ≤ 2 * ∑ k ∈ S, (B k + p k) := by
  revert hS
  refine Finset.induction_on_max_value B S ?_ ?_
  · intro _
    refine ⟨fun z _ h _ => by simpa using h, by simp⟩
  · intro a s ha hmax ih hS
    have hs : ∀ k ∈ s, s0 ≤ B k ∧ q ≤ p k := fun k hk => hS k (Finset.mem_insert_of_mem hk)
    obtain ⟨ihb, iha⟩ := ih hs
    have hlt : ∀ k ∈ s, B k < B a := by
      intro k hk
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      have := tc_lt_of_le p B hpos hd hka (hmax k hk)
      have := hpos k
      omega
    have hBa := ihb a ha (hS a (Finset.mem_insert_self _ _)).1 hlt
    have hpa := (hS a (Finset.mem_insert_self _ _)).2
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    refine ⟨?_, ?_⟩
    · intro z hz _ hzlt
      have hza : a ≠ z := fun h => hz (h ▸ Finset.mem_insert_self _ _)
      have := tc_lt_of_le p B hpos hd hza (le_of_lt (hzlt a (Finset.mem_insert_self _ _)))
      rw [hcard]
      nlinarith
    · rw [Finset.sum_insert ha, hcard]
      nlinarith

theorem tc_len {ι : Type*} [DecidableEq ι] (p B : ι → ℕ) (hpos : ∀ j, 0 < p j)
    (hd : ∀ j k : ι, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j))
    (s0 : ℕ) (S : Finset ι) :
    ∀ e, s0 ≤ e → (∀ k ∈ S, s0 ≤ B k ∧ B k + p k ≤ e) → s0 + ∑ k ∈ S, p k ≤ e := by
  refine Finset.induction_on_max_value B S ?_ ?_
  · intro e he _
    simpa using he
  · intro a s ha hmax ih e he hS
    have hs : ∀ k ∈ s, s0 ≤ B k ∧ B k + p k ≤ B a := by
      intro k hk
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      exact ⟨(hS k (Finset.mem_insert_of_mem hk)).1, tc_lt_of_le p B hpos hd hka (hmax k hk)⟩
    have h1 := ih (B a) (hS a (Finset.mem_insert_self _ _)).1 hs
    rw [Finset.sum_insert ha]
    have := (hS a (Finset.mem_insert_self _ _)).2
    omega


theorem tc_arithC (t t' τ b k r Bn : ℕ) (hτ : 0 < τ) (hkr : k + r = t + t')
    (h1 : k * τ ≤ Bn) (h2 : t * τ + b ≤ Bn)
    (h3 : (r + 1) * (Bn + 1) ≤ k * r * τ + (t + 1) * τ) : k = t := by
  rcases lt_trichotomy k t with hk | hk | hk
  · exfalso
    have hr : 1 ≤ r := by omega
    have e1 : (r + 1) * (t * τ + b + 1) ≤ (r + 1) * (Bn + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : r * (k + 1) * τ ≤ r * t * τ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
    have e3 : τ ≤ r * τ := Nat.le_mul_of_pos_left _ hr
    nlinarith
  · exact hk
  · exfalso
    have e1 : (r + 1) * (k * τ + 1) ≤ (r + 1) * (Bn + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : (t + 1) * τ ≤ k * τ := Nat.mul_le_mul_right _ hk
    nlinarith

theorem tc_arithD (t t' τ b k r Bn : ℕ) (hτ : τ = (t' + 1) * (b + 1) + t') (hk : k = t)
    (hr : r = t') (h2 : t * τ + b ≤ Bn)
    (h3 : (r + 1) * (Bn + 1) ≤ k * r * τ + (t + 1) * τ) : Bn = t * τ + b := by
  subst hk hr
  by_contra hne
  have h4 : k * τ + b + 1 ≤ Bn := by omega
  have e1 : (r + 1) * (k * τ + b + 1 + 1) ≤ (r + 1) * (Bn + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith


section ordsec
variable {ι : Type*} [DecidableEq ι] (p r : ι → ℕ)

def tcF (st : ℕ × (ι → ℕ)) (j : ι) : ℕ × (ι → ℕ) :=
  (max st.1 (r j) + p j, Function.update st.2 j (max st.1 (r j)))

def tcTf (T : ℕ) (l : List ι) : ℕ := l.foldl (fun T j => max T (r j) + p j) T

def tcSum : ℕ → List ι → ℕ
  | _, [] => 0
  | T, x :: xs => (max T (r x) + p x) + tcSum (max T (r x) + p x) xs

theorem tc_fst_foldl (l : List ι) (st : ℕ × (ι → ℕ)) :
    (l.foldl (tcF p r) st).1 = tcTf p r st.1 l := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem tc_snd_unaff (l : List ι) (j : ι) (hj : j ∉ l) (st : ℕ × (ι → ℕ)) :
    (l.foldl (tcF p r) st).2 j = st.2 j := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : j ≠ x := fun h => hj (h ▸ List.mem_cons_self)
    rw [ih (fun h => hj (List.mem_cons_of_mem _ h))]
    simp [tcF, Function.update_of_ne hx]

theorem tc_tf_append (T : ℕ) (l l' : List ι) : tcTf p r T (l ++ l') = tcTf p r (tcTf p r T l) l' := by
  simp [tcTf, List.foldl_append]

theorem tc_tf_ge (T : ℕ) (l : List ι) : T ≤ tcTf p r T l := by
  induction l generalizing T with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [tcTf, List.foldl_cons] at ih ⊢
    exact le_trans (by omega) (ih _)

theorem tc_start (l1 l2 : List ι) (j : ι) (hj : j ∉ l2) (st : ℕ × (ι → ℕ)) :
    ((l1 ++ j :: l2).foldl (tcF p r) st).2 j = max (tcTf p r st.1 l1) (r j) := by
  rw [List.foldl_append, List.foldl_cons, tc_snd_unaff p r l2 j hj]
  simp [tcF, tc_fst_foldl]

theorem tc_sum_comp (l : List ι) (hnd : l.Nodup) (st : ℕ × (ι → ℕ)) :
    (l.map fun j => (l.foldl (tcF p r) st).2 j + p j).sum = tcSum p r st.1 l := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, tcSum]
    rw [tc_snd_unaff p r xs x hnd.1]
    have := ih hnd.2 (tcF p r st x)
    simp only [tcF, Function.update_self] at this ⊢
    rw [this]

end ordsec

section ordsec2
variable {ι : Type*} (p r : ι → ℕ)

theorem tc_tf_zero (l : List ι) (hr : ∀ x ∈ l, r x = 0) (T : ℕ) :
    tcTf p r T l = T + (l.map p).sum := by
  induction l generalizing T with
  | nil => simp [tcTf]
  | cons x xs ih =>
    have h0 := hr x (List.mem_cons_self)
    have := ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (T + p x)
    simp only [tcTf, List.foldl_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [h0]
    have hm : max T 0 = T := by omega
    rw [hm]
    omega

theorem tc_sum_const (l : List ι) (hr : ∀ x ∈ l, r x = 0) (c : ℕ) (hp : ∀ x ∈ l, p x = c) (T : ℕ) :
    2 * tcSum p r T l = 2 * l.length * T + c * (l.length * (l.length + 1)) := by
  induction l generalizing T with
  | nil => simp [tcSum]
  | cons x xs ih =>
    have h0 := hr x (List.mem_cons_self)
    have h1 := hp x (List.mem_cons_self)
    have := ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (fun y hy => hp y (List.mem_cons_of_mem _ hy)) (T + p x)
    simp only [tcSum, List.length_cons]
    rw [h0]
    have hm : max T 0 = T := by omega
    rw [hm]
    rw [h1] at this ⊢
    nlinarith

theorem tc_sum_le (l : List ι) (hr : ∀ x ∈ l, r x = 0) (c : ℕ) (e : ι → ℕ)
    (hp : ∀ x ∈ l, p x = c + e x) (T : ℕ) :
    2 * tcSum p r T l ≤ 2 * l.length * T + c * (l.length * (l.length + 1))
      + 2 * l.length * (l.map e).sum := by
  induction l generalizing T with
  | nil => simp [tcSum]
  | cons x xs ih =>
    have h0 := hr x (List.mem_cons_self)
    have h1 := hp x (List.mem_cons_self)
    have := ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (fun y hy => hp y (List.mem_cons_of_mem _ hy)) (T + p x)
    simp only [tcSum, List.length_cons, List.map_cons, List.sum_cons]
    rw [h0]
    have hm : max T 0 = T := by omega
    rw [hm]
    rw [h1] at this ⊢
    nlinarith [Nat.zero_le (List.map e xs).sum]

end ordsec2

theorem tc_os_eq {n : ℕ} (p r : Fin n → ℕ) (ord : List (Fin n)) :
    orderSchedule p r ord = (ord.foldl (tcF p r) (0, fun _ => 0)).2 := rfl

section spec
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

theorem tc_tau_pos : 0 < tau a b := by unfold tau; positivity

theorem tc_u_pos : 0 < uCount a b := by
  have := tc_tau_pos a b
  unfold uCount
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.succ_pos t) this) (Nat.le_add_left _ _)

theorem tc_ups_pos : 0 < upsilon a b := Nat.mul_pos (tc_u_pos a b) (Nat.succ_pos _)

theorem tc_proc_pos (j : Fin (numJobs a b)) : 0 < procTime a b j := by
  have := tc_tau_pos a b
  have := tc_ups_pos a b
  unfold procTime
  split_ifs <;> omega

theorem tc_proc_long (j : Fin (numJobs a b)) (h : j.val < t + tPrime a) :
    tau a b ≤ procTime a b j := by
  unfold procTime
  split_ifs <;> first | exact Nat.le_add_right _ _ | exact le_rfl | omega

theorem tc_mem_U (j : Fin (numJobs a b)) :
    j ∈ groupU a b ↔ t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b := by
  simp [groupU]

theorem tc_proc_U (j : Fin (numJobs a b)) (h : j ∈ groupU a b) :
    procTime a b j = upsilon a b := by
  rw [tc_mem_U] at h
  unfold procTime
  split_ifs <;> first | rfl | omega

theorem tc_proc_last : procTime a b (lastJob a b) = 1 := by
  have hv : (lastJob a b).val = t + tPrime a + uCount a b := rfl
  unfold procTime
  rw [dif_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]

theorem tc_not_U_last : lastJob a b ∉ groupU a b := by
  rw [tc_mem_U]; unfold lastJob; simp

theorem tc_card_filter (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j : Fin n => P j.val).card = ((Finset.range n).filter P).card := by
  refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj]
  · intro x _ y _ h
    exact Fin.ext h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨⟨x, hx.1⟩, by simp [hx.2], rfl⟩

theorem tc_card_U : (groupU a b).card = uCount a b := by
  have : groupU a b = Finset.univ.filter fun j : Fin (numJobs a b) =>
      (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b) := rfl
  rw [this]
  refine (tc_card_filter (numJobs a b) (fun i => t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b)).trans ?_
  have : (Finset.range (numJobs a b)).filter (fun i => t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b)
      = Finset.Ico (t + tPrime a) (t + tPrime a + uCount a b) := by
    ext i; simp [numJobs]; omega
  rw [this]; simp

theorem tc_card_L : (Finset.univ.filter fun j : Fin (numJobs a b) => j.val < t + tPrime a).card
    = t + tPrime a := by
  refine (tc_card_filter (numJobs a b) (fun i => i < t + tPrime a)).trans ?_
  have : (Finset.range (numJobs a b)).filter (fun i => i < t + tPrime a)
      = Finset.range (t + tPrime a) := by
    ext i; simp [numJobs]; omega
  rw [this]; simp


theorem tc_sum_nonU : ∑ j ∈ (groupU a b)ᶜ, procTime a b j = sigma a b := by
  classical
  let pt : ℕ → ℕ := fun i => if h : i < t then tau a b + a ⟨i, h⟩
    else if i < t + tPrime a then tau a b
    else if i < t + tPrime a + uCount a b then upsilon a b else 1
  have hp : ∀ j : Fin (numJobs a b), procTime a b j = pt j.val := fun j => rfl
  have hc : (groupU a b)ᶜ = Finset.univ.filter fun j : Fin (numJobs a b) =>
      ¬ (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b) := by
    ext j; simp [tc_mem_U]
  rw [hc, Finset.sum_filter]
  let g : ℕ → ℕ := fun i =>
    if ¬ (t + tPrime a ≤ i ∧ i < t + tPrime a + uCount a b) then pt i else 0
  have h0 : ∑ j : Fin (numJobs a b), (if ¬ (t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b)
      then procTime a b j else 0) = ∑ j : Fin (numJobs a b), g j.val := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [g, hp]
  rw [h0, Fin.sum_univ_eq_sum_range g (numJobs a b)]
  have hn : numJobs a b = (t + tPrime a) + uCount a b + 1 := rfl
  rw [hn, Finset.sum_range_succ, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (uCount a b), g (t + tPrime a + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    simp only [g]
    rw [if_neg (by omega)]
  have h3 : g (t + tPrime a + uCount a b) = 1 := by
    simp only [g, pt]
    rw [if_pos (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have h2 : ∑ x ∈ Finset.range (t + tPrime a), g x = ∑ x ∈ Finset.range (t + tPrime a), pt x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    simp only [g]
    rw [if_pos (by omega)]
  rw [h1, h3, h2, Finset.sum_range_add]
  have h4 : ∑ x ∈ Finset.range t, pt x = ∑ i : Fin t, (tau a b + a i) := by
    rw [← Fin.sum_univ_eq_sum_range pt t]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pt]
    rw [dif_pos i.2]
  have h5 : ∑ x ∈ Finset.range (tPrime a), pt (t + x) = tPrime a * tau a b := by
    rw [Finset.sum_const_nat (m := tau a b)]
    · simp
    · intro x hx
      rw [Finset.mem_range] at hx
      simp only [pt]
      rw [dif_neg (by omega), if_pos (by omega)]
  rw [h4, h5, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold sigma sumA
  ring


theorem tc_y2 : 2 * yThreshold a b = 2 * upsilon a b + uCount a b * (uCount a b + 1) * upsilon a b := by
  have h : 2 * (uCount a b * (uCount a b + 1) / 2) = uCount a b * (uCount a b + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
  unfold yThreshold
  nlinarith [h]

theorem tc_ups_eq : upsilon a b = uCount a b * sigma a b + uCount a b := by
  unfold upsilon; ring

theorem tc_claimA_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    ∀ j' j : Fin (numJobs a b), j' ∉ groupU a b → j ∈ groupU a b → B j' < B j := by
  intro j' j hj' hj
  by_contra hcon
  push Not at hcon
  have hpos := tc_proc_pos a b
  have hd := hB.2
  have hne : j ≠ j' := fun h => hj' (h ▸ hj)
  have h1 := tc_lt_of_le _ _ hpos hd hne hcon
  rw [tc_proc_U a b j hj] at h1
  have h2 := (tc_chain (procTime a b) B hpos hd 0 (upsilon a b) (groupU a b)
    (fun k hk => ⟨Nat.zero_le _, (tc_proc_U a b k hk).ge⟩)).2
  rw [tc_card_U] at h2
  have hsplit := Finset.sum_add_sum_compl (groupU a b) (fun k => completion (procTime a b) B k)
  have hj'le : completion (procTime a b) B j' ≤ ∑ k ∈ (groupU a b)ᶜ, completion (procTime a b) B k :=
    Finset.single_le_sum (f := fun k => completion (procTime a b) B k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_compl.2 hj')
  have hpj' := hpos j'
  have hy2 := tc_y2 a b
  simp only [completion] at hy hsplit hj'le
  nlinarith

theorem tc_claimB_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (∃ j ∈ groupU a b, B j ≤ sigma a b) ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by
  have hpos := tc_proc_pos a b
  have hd := hB.2
  have hy2 := tc_y2 a b
  have hups := tc_ups_eq a b
  have hsplit := Finset.sum_add_sum_compl (groupU a b) (fun k => completion (procTime a b) B k)
  have hlast : completion (procTime a b) B (lastJob a b) ≤ ∑ k ∈ (groupU a b)ᶜ, completion (procTime a b) B k :=
    Finset.single_le_sum (f := fun k => completion (procTime a b) B k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_compl.2 (tc_not_U_last a b))
  have hlast1 : 1 ≤ completion (procTime a b) B (lastJob a b) := by
    have := tc_proc_last a b
    simp only [completion]; omega
  have hA := tc_claimA_core a b B hB hy
  simp only [completion] at hy hsplit hlast hlast1
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h2 := (tc_chain (procTime a b) B hpos hd (sigma a b + 1) (upsilon a b) (groupU a b)
      (fun k hk => ⟨by have := hcon k (by simpa using hk); omega, (tc_proc_U a b k hk).ge⟩)).2
    rw [tc_card_U] at h2
    have hh : uCount a b * (sigma a b + 1) = upsilon a b := rfl
    nlinarith
  · have hσ : ∀ j ∈ groupU a b, sigma a b ≤ B j := by
      intro j hj
      have hlen := tc_len (procTime a b) B hpos hd 0 (groupU a b)ᶜ (B j) (Nat.zero_le _)
        (fun k hk => by
          have hk' : k ∉ groupU a b := Finset.mem_compl.1 hk
          have hlt := hA k j hk' hj
          have hne : k ≠ j := fun h => hk' (h ▸ hj)
          exact ⟨Nat.zero_le _, tc_lt_of_le _ _ hpos hd hne hlt.le⟩)
      rw [tc_sum_nonU] at hlen
      omega
    have h2 := (tc_chain (procTime a b) B hpos hd (sigma a b) (upsilon a b) (groupU a b)
      (fun k hk => ⟨hσ k hk, (tc_proc_U a b k hk).ge⟩)).2
    rw [tc_card_U] at h2
    simp only [completion]
    nlinarith


theorem tc_u2 : 2 * uCount a b = (t + tPrime a) * (t + tPrime a + 1) * tau a b + 2 * ((t + 1) * tau a b) := by
  have h : 2 * ((t + tPrime a) * (t + tPrime a + 1) / 2) = (t + tPrime a) * (t + tPrime a + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
  unfold uCount
  nlinarith [h]

theorem tc_key (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    ∃ k r : ℕ, k = (Finset.univ.filter fun j => B j < B (lastJob a b)).card ∧
      k + r = t + tPrime a ∧ k * tau a b ≤ B (lastJob a b) ∧
      t * tau a b + b ≤ B (lastJob a b) ∧
      (r + 1) * (B (lastJob a b) + 1) ≤ k * r * tau a b + (t + 1) * tau a b := by
  classical
  have hpos := tc_proc_pos a b
  have hd := hB.2
  have hA := tc_claimA_core a b B hB hy
  obtain ⟨-, hBnd⟩ := tc_claimB_core a b B hB hy
  have hu2 := tc_u2 a b
  have hlastv : (lastJob a b).val = t + tPrime a + uCount a b := rfl
  have hrel : t * tau a b + b ≤ B (lastJob a b) := by
    have := hB.1 (lastJob a b)
    have hr : release a b (lastJob a b) = t * tau a b + b := by
      unfold release; rw [if_pos hlastv]
    omega
  obtain ⟨K, hK⟩ : ∃ K : Finset (Fin (numJobs a b)),
      K = Finset.univ.filter fun j => B j < B (lastJob a b) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin (numJobs a b)),
      R = Finset.univ.filter fun j => j.val < t + tPrime a ∧ B (lastJob a b) < B j := ⟨_, rfl⟩
  have hmK : ∀ j, j ∈ K ↔ B j < B (lastJob a b) := by intro j; rw [hK]; simp
  have hmR : ∀ j, j ∈ R ↔ j.val < t + tPrime a ∧ B (lastJob a b) < B j := by intro j; rw [hR]; simp
  have hKL : ∀ j ∈ K, j.val < t + tPrime a := by
    intro j hj
    rw [hmK] at hj
    by_contra hcon
    by_cases hjU : j ∈ groupU a b
    · have := hA _ _ (tc_not_U_last a b) hjU
      omega
    · rw [tc_mem_U] at hjU
      have : j = lastJob a b := Fin.ext (by have := j.2; unfold numJobs at this; omega)
      rw [this] at hj
      exact lt_irrefl _ hj
  have hKR : K ∪ R = Finset.univ.filter fun j : Fin (numJobs a b) => j.val < t + tPrime a := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hmK, hmR]
    constructor
    · rintro (h | h)
      · exact hKL j ((hmK j).2 h)
      · exact h.1
    · intro h
      have hne : j ≠ lastJob a b := fun e => by rw [e, hlastv] at h; omega
      rcases lt_trichotomy (B j) (B (lastJob a b)) with h1 | h1 | h1
      · exact Or.inl h1
      · exfalso
        have := tc_lt_of_le _ _ hpos hd hne h1.le
        have := hpos j
        omega
      · exact Or.inr ⟨h, h1⟩
  have hdisj : Disjoint K R := by
    rw [Finset.disjoint_left]
    intro j hjK hjR
    rw [hmK] at hjK
    rw [hmR] at hjR
    omega
  have hcard : K.card + R.card = t + tPrime a := by
    rw [← Finset.card_union_of_disjoint hdisj, hKR, tc_card_L]
  have hlastK : lastJob a b ∉ K := by rw [hmK]; exact lt_irrefl _
  have hlastR : lastJob a b ∉ R := by rw [hmR]; exact fun h => lt_irrefl _ h.2
  have hlastKR : lastJob a b ∉ K ∪ R := by
    rw [Finset.mem_union]; exact fun h => h.elim hlastK hlastR
  -- chain bounds
  have hK1 := tc_chain (procTime a b) B hpos hd 0 (tau a b) K
    (fun k hk => ⟨Nat.zero_le _, tc_proc_long a b k (hKL k hk)⟩)
  have hK2 := hK1.1 (lastJob a b) hlastK (Nat.zero_le _) (fun k hk => (hmK k).1 hk)
  have hR1 := tc_chain (procTime a b) B hpos hd (B (lastJob a b) + 1) (tau a b) R
    (fun k hk => ⟨by have := ((hmR k).1 hk).2; omega, tc_proc_long a b k ((hmR k).1 hk).1⟩)
  have hsub : insert (lastJob a b) (K ∪ R) ⊆ (groupU a b)ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact tc_not_U_last a b
    · rw [tc_mem_U]
      rw [hKR] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      omega
  have hle := Finset.sum_le_sum_of_subset (f := fun j => completion (procTime a b) B j) hsub
  rw [Finset.sum_insert hlastKR, Finset.sum_union hdisj] at hle
  simp only [completion] at hle hBnd
  have := tc_proc_last a b
  refine ⟨K.card, R.card, by rw [hK], hcard, ?_, hrel, ?_⟩
  · have := hK2; omega
  · rw [← hcard] at hu2
    have hK3 := hK1.2
    have hR3 := hR1.2
    rw [this] at hle
    nlinarith


theorem tc_claimC_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    (Finset.univ.filter fun j => B j < B (lastJob a b)).card = t := by
  obtain ⟨k, r, hk, hkr, h1, h2, h3⟩ := tc_key a b B hB hy
  rw [← hk]
  exact tc_arithC t (tPrime a) (tau a b) b k r _ (tc_tau_pos a b) hkr h1 h2 h3

theorem tc_claimD_core (B : Fin (numJobs a b) → ℕ)
    (hB : IsFeasible (procTime a b) (release a b) B)
    (hy : ∑ j, completion (procTime a b) B j ≤ yThreshold a b) :
    B (lastJob a b) = t * tau a b + b := by
  obtain ⟨k, r, hk, hkr, h1, h2, h3⟩ := tc_key a b B hB hy
  have hkt : k = t := by
    rw [hk]; exact tc_claimC_core a b B hB hy
  have hr : r = tPrime a := by omega
  exact tc_arithD t (tPrime a) (tau a b) b k r _ rfl hkt hr h2 h3

end spec

section ordgen
variable {ι : Type*} [DecidableEq ι] (p r : ι → ℕ)

theorem tc_before (ord s t1 t2 : List ι) (j k : ι) (hord : ord = s ++ j :: (t1 ++ k :: t2))
    (hnd : ord.Nodup) :
    ((ord.foldl (tcF p r) (0, fun _ => 0)).2 j) + p j ≤ (ord.foldl (tcF p r) (0, fun _ => 0)).2 k := by
  subst hord
  have hnd' := hnd
  rw [List.nodup_append] at hnd'
  have hj : j ∉ t1 ++ k :: t2 := by
    have := hnd'.2.1
    rw [List.nodup_cons] at this
    exact this.1
  have e1 := tc_start p r s (t1 ++ k :: t2) j hj (0, fun _ => 0)
  have hk : k ∉ t2 := by
    have := hnd'.2.1
    rw [List.nodup_cons, List.nodup_append, List.nodup_cons] at this
    exact this.2.2.1.1
  have e2 := tc_start p r (s ++ j :: t1) t2 k hk (0, fun _ => 0)
  have e3 : s ++ j :: (t1 ++ k :: t2) = (s ++ j :: t1) ++ k :: t2 := by simp
  rw [e1, e3, e2]
  have h4 := tc_tf_ge p r (max (tcTf p r 0 s) (r j) + p j) t1
  have h5 : tcTf p r 0 (s ++ j :: t1) = tcTf p r (max (tcTf p r 0 s) (r j) + p j) t1 := by
    rw [tc_tf_append]; rfl
  rw [h5]
  have := le_max_left (tcTf p r (max (tcTf p r 0 s) (r j) + p j) t1) (r k)
  exact le_trans h4 this


theorem tc_feas_gen (ord : List ι) (hnd : ord.Nodup) (hcov : ∀ j, j ∈ ord)
    (hpos : ∀ j, 0 < p j) :
    (∀ j, r j ≤ (ord.foldl (tcF p r) (0, fun _ => 0)).2 j) ∧
    ∀ j k : ι, j ≠ k → ¬ ((ord.foldl (tcF p r) (0, fun _ => 0)).2 j <
        (ord.foldl (tcF p r) (0, fun _ => 0)).2 k + p k ∧
      (ord.foldl (tcF p r) (0, fun _ => 0)).2 k <
        (ord.foldl (tcF p r) (0, fun _ => 0)).2 j + p j) := by
  refine ⟨?_, ?_⟩
  · intro j
    obtain ⟨s, u, h⟩ := List.append_of_mem (hcov j)
    have hj : j ∉ u := by
      rw [h] at hnd
      rw [List.nodup_append] at hnd
      have := hnd.2.1
      rw [List.nodup_cons] at this
      exact this.1
    have e := tc_start p r s u j hj (0, fun _ => 0)
    rw [h, e]
    exact le_max_right _ _
  · intro j k hjk
    obtain ⟨s, u, h⟩ := List.append_of_mem (hcov j)
    have hk := hcov k
    rw [h, List.mem_append, List.mem_cons] at hk
    rcases hk with hk | hk | hk
    · obtain ⟨s1, s2, hs⟩ := List.append_of_mem hk
      have := tc_before p r ord s1 s2 u k j (by rw [h, hs]; simp) hnd
      have := hpos k
      omega
    · exact absurd hk.symm hjk
    · obtain ⟨t1, t2, hu⟩ := List.append_of_mem hk
      have := tc_before p r ord s t1 t2 j k (by rw [h, hu]) hnd
      have := hpos j
      omega

theorem tc_seg (ord pre seg post : List ι) (h : ord = pre ++ seg ++ post) (hnd : ord.Nodup)
    (hsn : seg.Nodup) :
    (seg.map fun j => (ord.foldl (tcF p r) (0, fun _ => 0)).2 j + p j).sum
      = tcSum p r (tcTf p r 0 pre) seg := by
  have hnd' := hnd
  rw [h, List.nodup_append] at hnd'
  have key : ∀ j ∈ seg, (ord.foldl (tcF p r) (0, fun _ => 0)).2 j =
      (seg.foldl (tcF p r) (pre.foldl (tcF p r) (0, fun _ => 0))).2 j := by
    intro j hj
    have hjp : j ∉ post := by
      intro hp
      exact hnd'.2.2 j (List.mem_append_right _ hj) j hp rfl
    rw [h, List.foldl_append, List.foldl_append, tc_snd_unaff p r post j hjp]
  rw [List.map_congr_left (fun j hj => by rw [key j hj])]
  rw [tc_sum_comp p r seg hsn, tc_fst_foldl]

end ordgen


section fwd
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

def tcEA (j : Fin (numJobs a b)) : ℕ := if h : j.val < t then a ⟨j.val, h⟩ else 0

theorem tc_proc_eq (j : Fin (numJobs a b)) (h : j.val < t + tPrime a) :
    procTime a b j = tau a b + tcEA a b j := by
  unfold procTime tcEA
  by_cases h1 : j.val < t
  · rw [dif_pos h1, dif_pos h1]
  · rw [dif_neg h1, if_pos h, dif_neg h1]; rfl

theorem tc_tPrime_ge (ha : ∀ i, 0 < a i) (i : Fin t) : i.val < tPrime a := by
  have h1 : 1 ≤ SchedComplexity.Tardiness.aStar a := le_trans (ha i) (Finset.le_sup (f := a) (Finset.mem_univ i))
  have hi := i.2
  unfold tPrime
  have : t * (t + 1) * 1 ≤ t * (t + 1) * SchedComplexity.Tardiness.aStar a :=
    Nat.mul_le_mul_left _ h1
  nlinarith

def tcEmbT (i : Fin t) : Fin (numJobs a b) := ⟨i.val, by unfold numJobs; have := i.2; omega⟩

def tcEmbS (ha : ∀ i, 0 < a i) (i : Fin t) : Fin (numJobs a b) :=
  ⟨t + i.val, by unfold numJobs; have := tc_tPrime_ge a ha i; omega⟩

theorem tc_jobsT_eq (S : Finset (Fin t)) : jobsT a b S = S.image (tcEmbT a b) := by
  ext j
  simp only [jobsT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, tcEmbT]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, Fin.ext h.symm⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem tc_jobsShift_eq (ha : ∀ i, 0 < a i) (S : Finset (Fin t)) :
    jobsShift a b S = S.image (tcEmbS a b ha) := by
  ext j
  simp only [jobsShift, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, tcEmbS]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, Fin.ext h.symm⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem tc_card_jobsT (S : Finset (Fin t)) : (jobsT a b S).card = S.card := by
  rw [tc_jobsT_eq]
  exact Finset.card_image_of_injective _ (fun x y h => Fin.ext (by simpa [tcEmbT] using congrArg Fin.val h))

theorem tc_card_jobsShift (ha : ∀ i, 0 < a i) (S : Finset (Fin t)) :
    (jobsShift a b S).card = S.card := by
  rw [tc_jobsShift_eq a b ha]
  exact Finset.card_image_of_injective _ (fun x y h => Fin.ext (by simpa [tcEmbS] using congrArg Fin.val h))

theorem tc_sum_eA (S : Finset (Fin t)) : ∑ x ∈ jobsT a b S, tcEA a b x = ∑ i ∈ S, a i := by
  rw [tc_jobsT_eq, Finset.sum_image (fun x _ y _ h => Fin.ext (by simpa [tcEmbT] using congrArg Fin.val h))]
  apply Finset.sum_congr rfl
  intro i _
  simp [tcEA, tcEmbT]

theorem tc_mem_T' (j : Fin (numJobs a b)) :
    j ∈ groupT' a b ↔ t ≤ j.val ∧ j.val < t + tPrime a := by
  simp [groupT']

theorem tc_card_T' : (groupT' a b).card = tPrime a := by
  have : groupT' a b = Finset.univ.filter fun j : Fin (numJobs a b) =>
      (t ≤ j.val ∧ j.val < t + tPrime a) := rfl
  rw [this]
  refine (tc_card_filter (numJobs a b) (fun i => t ≤ i ∧ i < t + tPrime a)).trans ?_
  have : (Finset.range (numJobs a b)).filter (fun i => t ≤ i ∧ i < t + tPrime a)
      = Finset.Ico t (t + tPrime a) := by
    ext i; simp [numJobs]; omega
  rw [this]; simp

theorem tc_shift_sub (ha : ∀ i, 0 < a i) (S : Finset (Fin t)) :
    jobsShift a b S ⊆ groupT' a b := by
  intro j hj
  simp only [jobsShift, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨i, _, h⟩ := hj
  rw [tc_mem_T']
  have := tc_tPrime_ge a ha i
  have := i.2
  omega

end fwd


section fwd3
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

theorem tc_sum_map {ι : Type*} (l : List ι) (f e : ι → ℕ) (c : ℕ) (h : ∀ x ∈ l, f x = c + e x) :
    (l.map f).sum = l.length * c + (l.map e).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h1 := h x (List.mem_cons_self)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [this, h1]
    ring

theorem tc_rel_zero (x : Fin (numJobs a b)) (h : x.val < t + tPrime a + uCount a b) :
    release a b x = 0 := by
  unfold release
  rw [if_neg (by omega)]

theorem tc_eA_zero (x : Fin (numJobs a b)) (h : t ≤ x.val) : tcEA a b x = 0 := by
  unfold tcEA; rw [dif_neg (by omega)]

theorem tc_long_bounds (l : List (Fin (numJobs a b))) (hl : ∀ x ∈ l, x.val < t + tPrime a) (T : ℕ) :
    tcTf (procTime a b) (release a b) T l = T + l.length * tau a b + (l.map (tcEA a b)).sum ∧
    2 * tcSum (procTime a b) (release a b) T l ≤ 2 * l.length * T +
      tau a b * (l.length * (l.length + 1)) + 2 * l.length * (l.map (tcEA a b)).sum := by
  have hr : ∀ x ∈ l, release a b x = 0 := fun x hx => by
    have := hl x hx
    exact tc_rel_zero a b x (by omega)
  have hp : ∀ x ∈ l, procTime a b x = tau a b + tcEA a b x := fun x hx => tc_proc_eq a b x (hl x hx)
  refine ⟨?_, tc_sum_le _ _ l hr _ _ hp T⟩
  rw [tc_tf_zero _ _ l hr, tc_sum_map l _ _ _ hp]
  ring

theorem tc_U_bounds (l : List (Fin (numJobs a b))) (hl : ∀ x ∈ l, x ∈ groupU a b) (T : ℕ) :
    tcTf (procTime a b) (release a b) T l = T + l.length * upsilon a b ∧
    2 * tcSum (procTime a b) (release a b) T l =
      2 * l.length * T + upsilon a b * (l.length * (l.length + 1)) := by
  have hr : ∀ x ∈ l, release a b x = 0 := fun x hx => by
    have := (tc_mem_U a b x).1 (hl x hx)
    exact tc_rel_zero a b x this.2
  have hp : ∀ x ∈ l, procTime a b x = upsilon a b := fun x hx => tc_proc_U a b x (hl x hx)
  refine ⟨?_, tc_sum_const _ _ l hr _ hp T⟩
  rw [tc_tf_zero _ _ l hr, tc_sum_map l _ (fun _ => 0) (upsilon a b) (by simpa using hp)]
  simp

end fwd3


section fwd4
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

theorem tc_cover (ha : ∀ i, 0 < a i) (S : Finset (Fin t))
    (l₁ l₂ l₃ l₄ l₅ : List (Fin (numJobs a b)))
    (h₁ : l₁.toFinset = jobsShift a b Sᶜ)
    (h₂ : l₂.toFinset = jobsT a b S)
    (h₃ : l₃.toFinset = groupT' a b \ jobsShift a b Sᶜ)
    (h₄ : l₄.toFinset = jobsT a b Sᶜ)
    (h₅ : l₅.toFinset = groupU a b) (j : Fin (numJobs a b)) :
    j ∈ l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅ := by
  simp only [List.mem_append, List.mem_singleton]
  by_cases hj : j.val < t
  · by_cases hi : (⟨j.val, hj⟩ : Fin t) ∈ S
    · have : j ∈ l₂.toFinset := by
        rw [h₂]; simp only [jobsT, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, hi, rfl⟩
      rw [List.mem_toFinset] at this
      tauto
    · have : j ∈ l₄.toFinset := by
        rw [h₄]; simp only [jobsT, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, Finset.mem_compl.2 hi, rfl⟩
      rw [List.mem_toFinset] at this
      tauto
  · by_cases hj2 : j.val < t + tPrime a
    · by_cases hs : ∃ i ∈ Sᶜ, j.val = t + i.val
      · have : j ∈ l₁.toFinset := by
          rw [h₁]; simp only [jobsShift, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hs
        rw [List.mem_toFinset] at this
        tauto
      · have : j ∈ l₃.toFinset := by
          rw [h₃, Finset.mem_sdiff, tc_mem_T']
          refine ⟨⟨by omega, hj2⟩, ?_⟩
          simp only [jobsShift, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hs
        rw [List.mem_toFinset] at this
        tauto
    · by_cases hj3 : j.val < t + tPrime a + uCount a b
      · have : j ∈ l₅.toFinset := by
          rw [h₅, tc_mem_U]; omega
        rw [List.mem_toFinset] at this
        tauto
      · have : j = lastJob a b := Fin.ext (by have := j.2; unfold numJobs at this; unfold lastJob; simp only; omega)
        tauto

end fwd4


section fwd5
variable {t : ℕ} (a : Fin t → ℕ) (b : ℕ)

theorem tc_rel_last : release a b (lastJob a b) = t * tau a b + b := by
  have hv : (lastJob a b).val = t + tPrime a + uCount a b := rfl
  unfold release
  rw [if_pos hv]

theorem tc_sumA_le (ha : ∀ i, 0 < a i) : sumA a ≤ t * SchedComplexity.Tardiness.aStar a := by
  unfold sumA
  have := Finset.sum_le_card_nsmul Finset.univ a (SchedComplexity.Tardiness.aStar a)
    (fun i _ => Finset.le_sup (f := a) (Finset.mem_univ i))
  simpa using this

theorem tc_arith_nonU (n1 n2 n3 t t' τ b E4 u V1 V2 VL V3 V4 : ℕ)
    (htot : n2 + n1 = t) (hn3 : n3 + n1 = t')
    (hu2 : 2 * u = (t + t') * (t + t' + 1) * τ + 2 * ((t + 1) * τ))
    (hτ : τ = (t' + 1) * (b + 1) + t') (hX : n2 * b + n1 * E4 ≤ t')
    (hV1 : 2 * V1 ≤ τ * (n1 * (n1 + 1)))
    (hV2 : 2 * V2 ≤ 2 * n2 * (n1 * τ) + τ * (n2 * (n2 + 1)) + 2 * n2 * b)
    (hVL : VL = t * τ + b + 1)
    (hV3 : 2 * V3 ≤ 2 * n3 * (t * τ + b + 1) + τ * (n3 * (n3 + 1)))
    (hV4 : 2 * V4 ≤ 2 * n1 * (t * τ + b + 1 + n3 * τ) + τ * (n1 * (n1 + 1)) + 2 * n1 * E4) :
    V1 + V2 + VL + V3 + V4 ≤ u := by
  subst htot hn3
  have key : 2 * (V1 + V2 + VL + V3 + V4) ≤ 2 * u := by
    rw [hu2]
    rw [hVL] at *
    nlinarith [hX, hτ]
  omega

theorem tc_arith_X (n1 n2 t t' b E4 A astar : ℕ) (htot : n2 + n1 = t) (hsplit : E4 + b = A)
    (hA : A ≤ t * astar) (ht' : t' = t * (t + 1) * astar) : n2 * b + n1 * E4 ≤ t' := by
  have h1 : n2 * b ≤ n2 * A := Nat.mul_le_mul_left _ (by omega)
  have h2 : n1 * E4 ≤ n1 * A := Nat.mul_le_mul_left _ (by omega)
  have h3 : (n2 + n1) * A = t * A := by rw [htot]
  have h4 : t * A ≤ t * (t * astar) := Nat.mul_le_mul_left _ hA
  have h5 : t * (t * astar) ≤ t * (t + 1) * astar := by nlinarith [Nat.zero_le (t * astar)]
  rw [ht']
  nlinarith

theorem tc_arith_T2 (n1 n2 t τ b : ℕ) (h : n2 + n1 = t) :
    0 + n1 * τ + n2 * τ + b = t * τ + b := by
  subst h; ring

theorem tc_arith_T5 (t t' n1 n3 τ b E4 A : ℕ) (hn3 : n3 + n1 = t') (hsplit : E4 + b = A) :
    t * τ + b + 1 + n3 * τ + n1 * τ + E4 = (t + t') * τ + A + 1 := by
  rw [← hsplit, ← hn3]; ring

theorem tc_arith_U (u σ υ V5 W : ℕ) (hev : 2 * W = u * (u + 1))
    (hV5 : 2 * V5 = 2 * u * σ + υ * (u * (u + 1))) : V5 = u * σ + W * υ := by
  nlinarith

theorem tc_arith_fin (u σ υ W SU Sn y : ℕ) (hU : SU = u * σ + W * υ) (hn : Sn ≤ u)
    (hups : υ = u * σ + u) (hy : y = υ + W * υ) : SU + Sn ≤ y := by
  subst hy
  omega

theorem tc_forward_core (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (S : Finset (Fin t)) (hS : ∑ i ∈ S, a i = b)
    (l₁ l₂ l₃ l₄ l₅ : List (Fin (numJobs a b)))
    (h₁ : l₁.Nodup ∧ l₁.toFinset = jobsShift a b Sᶜ)
    (h₂ : l₂.Nodup ∧ l₂.toFinset = jobsT a b S)
    (h₃ : l₃.Nodup ∧ l₃.toFinset = groupT' a b \ jobsShift a b Sᶜ)
    (h₄ : l₄.Nodup ∧ l₄.toFinset = jobsT a b Sᶜ)
    (h₅ : l₅.Nodup ∧ l₅.toFinset = groupU a b)
    (B : Fin (numJobs a b) → ℕ)
    (hBdef : B = orderSchedule (procTime a b) (release a b)
      (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅)) :
    IsFeasible (procTime a b) (release a b) B ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b ∧
      ∑ j ∈ groupU a b, completion (procTime a b) B j =
        uCount a b * sigma a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b ∧
      ∑ j, completion (procTime a b) B j ≤ yThreshold a b := by
  classical
  obtain ⟨ord, hord⟩ : ∃ ord, ord = l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅ := ⟨_, rfl⟩
  rw [← hord] at hBdef
  have hBj : ∀ j, B j = (ord.foldl (tcF (procTime a b) (release a b)) (0, fun _ => 0)).2 j := by
    intro j; rw [hBdef]; rfl
  -- sizes
  have hn1 : l₁.length = Sᶜ.card := by
    rw [← List.toFinset_card_of_nodup h₁.1, h₁.2, tc_card_jobsShift a b ha]
  have hn2 : l₂.length = S.card := by
    rw [← List.toFinset_card_of_nodup h₂.1, h₂.2, tc_card_jobsT]
  have hn4 : l₄.length = Sᶜ.card := by
    rw [← List.toFinset_card_of_nodup h₄.1, h₄.2, tc_card_jobsT]
  have hn5 : l₅.length = uCount a b := by
    rw [← List.toFinset_card_of_nodup h₅.1, h₅.2, tc_card_U]
  have hn3 : l₃.length + Sᶜ.card = tPrime a := by
    rw [← List.toFinset_card_of_nodup h₃.1, h₃.2, ← tc_card_jobsShift a b ha Sᶜ,
      Finset.card_sdiff_add_card_eq_card (tc_shift_sub a b ha Sᶜ), tc_card_T']
  have htot : S.card + Sᶜ.card = t := by
    have := Finset.card_add_card_compl S
    simpa using this
  have hlen' : ord.length = t + tPrime a + uCount a b + 1 := by
    rw [hord]
    simp only [List.length_append, List.length_singleton]
    rw [hn1, hn2, hn4, hn5]
    linarith
  have hlen : ord.length = numJobs a b := hlen'
  have hcov : ∀ j, j ∈ ord := by
    intro j; rw [hord]; exact tc_cover a b ha S l₁ l₂ l₃ l₄ l₅ h₁.2 h₂.2 h₃.2 h₄.2 h₅.2 j
  have hts : ord.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun j => List.mem_toFinset.2 (hcov j))
  have hnd : ord.Nodup := by
    have hcard : ord.toFinset.card = ord.length := by
      rw [hts, Finset.card_univ, Fintype.card_fin, hlen]
    have := (Multiset.toFinset_card_eq_card_iff_nodup (m := (ord : Multiset (Fin (numJobs a b))))).1
      (by simpa using hcard)
    simpa using this
  have hfeas := tc_feas_gen (procTime a b) (release a b) ord hnd hcov (tc_proc_pos a b)
  have hF : IsFeasible (procTime a b) (release a b) B := by
    unfold IsFeasible
    refine ⟨fun j => ?_, fun j k hjk => ?_⟩
    · rw [hBj]; exact hfeas.1 j
    · rw [hBj j, hBj k]; exact hfeas.2 j k hjk
  obtain ⟨Cf, hCf⟩ : ∃ Cf : Fin (numJobs a b) → ℕ, ∀ j, Cf j =
      (ord.foldl (tcF (procTime a b) (release a b)) (0, fun _ => 0)).2 j + procTime a b j :=
    ⟨_, fun _ => rfl⟩
  have hcomp : ∀ j, completion (procTime a b) B j = Cf j := by
    intro j; rw [hCf]; show B j + procTime a b j = _; rw [hBj j]
  have hseg : ∀ (pre seg post : List (Fin (numJobs a b))), ord = pre ++ seg ++ post →
      seg.Nodup → (seg.map Cf).sum = tcSum (procTime a b) (release a b)
        (tcTf (procTime a b) (release a b) 0 pre) seg := by
    intro pre seg post h hsn
    rw [← tc_seg (procTime a b) (release a b) ord pre seg post h hnd hsn]
    congr 1
    exact List.map_congr_left (fun j _ => hCf j)
  have hs1 := hseg [] l₁ (l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅) (by rw [hord]; simp [List.append_assoc]) h₁.1
  have hs2 := hseg l₁ l₂ ([lastJob a b] ++ l₃ ++ l₄ ++ l₅) (by rw [hord]; simp [List.append_assoc]) h₂.1
  have hsL := hseg (l₁ ++ l₂) [lastJob a b] (l₃ ++ l₄ ++ l₅) (by rw [hord]; simp [List.append_assoc]) (List.nodup_singleton _)
  have hs3 := hseg (l₁ ++ l₂ ++ [lastJob a b]) l₃ (l₄ ++ l₅) (by rw [hord]; simp [List.append_assoc]) h₃.1
  have hs4 := hseg (l₁ ++ l₂ ++ [lastJob a b] ++ l₃) l₄ l₅ (by rw [hord]) h₄.1
  have hs5 := hseg (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄) l₅ [] (by rw [hord]; simp) h₅.1
  -- membership facts
  have hmem1 : ∀ x ∈ l₁, t ≤ x.val ∧ x.val < t + tPrime a := by
    intro x hx
    have : x ∈ groupT' a b := tc_shift_sub a b ha _ (by rw [← h₁.2]; exact List.mem_toFinset.2 hx)
    exact (tc_mem_T' a b x).1 this
  have hmem3 : ∀ x ∈ l₃, t ≤ x.val ∧ x.val < t + tPrime a := by
    intro x hx
    have : x ∈ groupT' a b \ jobsShift a b Sᶜ := by rw [← h₃.2]; exact List.mem_toFinset.2 hx
    exact (tc_mem_T' a b x).1 (Finset.mem_sdiff.1 this).1
  have hmemT : ∀ (S' : Finset (Fin t)) (l : List (Fin (numJobs a b))), l.toFinset = jobsT a b S' →
      ∀ x ∈ l, x.val < t := by
    intro S' l hl x hx
    have : x ∈ jobsT a b S' := by rw [← hl]; exact List.mem_toFinset.2 hx
    simp only [jobsT, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨i, _, h⟩ := this
    rw [h]; exact i.2
  have hmem2 := hmemT S l₂ h₂.2
  have hmem4 := hmemT Sᶜ l₄ h₄.2
  have hmem5 : ∀ x ∈ l₅, x ∈ groupU a b := fun x hx => by rw [← h₅.2]; exact List.mem_toFinset.2 hx
  have hE1 : (l₁.map (tcEA a b)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact tc_eA_zero a b x (hmem1 x hx).1
  have hE3 : (l₃.map (tcEA a b)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact tc_eA_zero a b x (hmem3 x hx).1
  have hE2 : (l₂.map (tcEA a b)).sum = b := by
    rw [← List.sum_toFinset _ h₂.1, h₂.2, tc_sum_eA, hS]
  have hsplitA : ∑ i ∈ Sᶜ, a i + b = sumA a := by
    rw [← hS]; exact Finset.sum_compl_add_sum S a
  obtain ⟨E4, hE4def⟩ : ∃ E4, E4 = ∑ i ∈ Sᶜ, a i := ⟨_, rfl⟩
  have hE4 : (l₄.map (tcEA a b)).sum = E4 := by
    rw [← List.sum_toFinset _ h₄.1, h₄.2, tc_sum_eA, hE4def]
  rw [← hE4def] at hsplitA
  -- numbers
  have hτ := tc_tau_pos a b
  have e1 : (S.card + Sᶜ.card) * tau a b = t * tau a b := by rw [htot]
  have hlb1 := tc_long_bounds a b l₁ (fun x hx => (hmem1 x hx).2) 0
  have hT1 : tcTf (procTime a b) (release a b) 0 l₁ = Sᶜ.card * tau a b := by
    rw [hlb1.1, hE1, hn1]; ring
  have hlb2 := tc_long_bounds a b l₂ (fun x hx => by have := hmem2 x hx; omega) (Sᶜ.card * tau a b)
  have hT2 : tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂) = t * tau a b + b := by
    rw [tc_tf_append, hT1, hlb2.1, hE2, hn2]
    have := tc_arith_T2 Sᶜ.card S.card t (tau a b) b htot
    omega
  have hT3 : tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b]) = t * tau a b + b + 1 := by
    rw [tc_tf_append, hT2]
    simp only [tcTf, List.foldl_cons, List.foldl_nil]
    rw [tc_rel_last, tc_proc_last, max_self]
  have hlb3 := tc_long_bounds a b l₃ (fun x hx => (hmem3 x hx).2) (t * tau a b + b + 1)
  have hT4 : tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b] ++ l₃) =
      t * tau a b + b + 1 + l₃.length * tau a b := by
    rw [tc_tf_append, hT3, hlb3.1, hE3]; ring
  have hlb4 := tc_long_bounds a b l₄ (fun x hx => by have := hmem4 x hx; omega)
    (t * tau a b + b + 1 + l₃.length * tau a b)
  have hT5 : tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄) = sigma a b := by
    rw [tc_tf_append, hT4, hlb4.1, hE4, hn4]
    unfold sigma
    exact tc_arith_T5 t (tPrime a) Sᶜ.card l₃.length (tau a b) b E4 (sumA a) hn3 hsplitA
  have hlb5 := tc_U_bounds a b l₅ hmem5 (sigma a b)
  have hV1 := hlb1.2
  have hV1' : 2 * tcSum (procTime a b) (release a b) (tcTf (procTime a b) (release a b) 0 []) l₁ ≤
      tau a b * (Sᶜ.card * (Sᶜ.card + 1)) := by
    have := (tc_long_bounds a b l₁ (fun x hx => (hmem1 x hx).2) 0).2
    rw [hE1, hn1] at this
    simpa [tcTf] using this
  have hV2 : 2 * tcSum (procTime a b) (release a b) (tcTf (procTime a b) (release a b) 0 l₁) l₂ ≤
      2 * S.card * (Sᶜ.card * tau a b) + tau a b * (S.card * (S.card + 1)) + 2 * S.card * b := by
    rw [hT1]
    have := hlb2.2
    rw [hE2, hn2] at this
    exact this
  have hVL : tcSum (procTime a b) (release a b)
      (tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂)) [lastJob a b] = t * tau a b + b + 1 := by
    rw [hT2]
    simp only [tcSum]
    rw [tc_rel_last, tc_proc_last, max_self]
  have hV3 : 2 * tcSum (procTime a b) (release a b)
      (tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b])) l₃ ≤
      2 * l₃.length * (t * tau a b + b + 1) + tau a b * (l₃.length * (l₃.length + 1)) := by
    rw [hT3]
    have := hlb3.2
    rw [hE3] at this
    simpa using this
  have hV4 : 2 * tcSum (procTime a b) (release a b)
      (tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b] ++ l₃)) l₄ ≤
      2 * Sᶜ.card * (t * tau a b + b + 1 + l₃.length * tau a b) +
        tau a b * (Sᶜ.card * (Sᶜ.card + 1)) + 2 * Sᶜ.card * E4 := by
    rw [hT4]
    have := hlb4.2
    rw [hE4, hn4] at this
    exact this
  have hV5 : 2 * tcSum (procTime a b) (release a b)
      (tcTf (procTime a b) (release a b) 0 (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄)) l₅ =
      2 * uCount a b * sigma a b + upsilon a b * (uCount a b * (uCount a b + 1)) := by
    rw [hT5]
    have := hlb5.2
    rw [hn5] at this
    exact this
  have hX := tc_arith_X Sᶜ.card S.card t (tPrime a) b E4 (sumA a)
    (SchedComplexity.Tardiness.aStar a) htot hsplitA (tc_sumA_le a ha) rfl
  have hnonU := tc_arith_nonU Sᶜ.card S.card l₃.length t (tPrime a) (tau a b) b E4 (uCount a b)
    _ _ _ _ _ htot hn3 (tc_u2 a b) rfl hX hV1' hV2 hVL hV3 hV4
  have hTot : ∑ j, completion (procTime a b) B j = (ord.map Cf).sum := by
    have := List.sum_toFinset Cf hnd
    rw [hts] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => hcomp j)
  have hall : (ord.map Cf).sum = (l₁.map Cf).sum + (l₂.map Cf).sum + ([lastJob a b].map Cf).sum +
      (l₃.map Cf).sum + (l₄.map Cf).sum + (l₅.map Cf).sum := by
    rw [hord]; simp only [List.map_append, List.sum_append]
  have hUsum : ∑ j ∈ groupU a b, completion (procTime a b) B j = (l₅.map Cf).sum := by
    have := List.sum_toFinset Cf h₅.1
    rw [h₅.2] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => hcomp j)
  have hsplit := Finset.sum_add_sum_compl (groupU a b) (fun j => completion (procTime a b) B j)
  rw [hall, hs1, hs2, hsL, hs3, hs4, hs5] at hTot
  rw [hs5] at hUsum
  have hev : 2 * (uCount a b * (uCount a b + 1) / 2) = uCount a b * (uCount a b + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
  have hUval : ∑ j ∈ groupU a b, completion (procTime a b) B j =
      uCount a b * sigma a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b := by
    rw [hUsum]
    exact tc_arith_U _ _ _ _ _ hev hV5
  have hnon : ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b := by
    linarith only [hsplit, hTot, hUsum, hnonU]
  refine ⟨hF, hnon, hUval, ?_⟩
  rw [← hsplit]
  exact tc_arith_fin _ _ _ _ _ _ _ hUval hnon (tc_ups_eq a b) rfl

end fwd5

end SchedComplexity.TotalCompletion

open SchedComplexity.TotalCompletion


theorem solution {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (S : Finset (Fin t)) (hS : ∑ i ∈ S, a i = b)
    (l₁ l₂ l₃ l₄ l₅ : List (Fin (numJobs a b)))
    (h₁ : l₁.Nodup ∧ l₁.toFinset = jobsShift a b Sᶜ)
    (h₂ : l₂.Nodup ∧ l₂.toFinset = jobsT a b S)
    (h₃ : l₃.Nodup ∧ l₃.toFinset = groupT' a b \ jobsShift a b Sᶜ)
    (h₄ : l₄.Nodup ∧ l₄.toFinset = jobsT a b Sᶜ)
    (h₅ : l₅.Nodup ∧ l₅.toFinset = groupU a b) :
    let B := orderSchedule (procTime a b) (release a b)
      (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅)
    IsFeasible (procTime a b) (release a b) B ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b ∧
      ∑ j ∈ groupU a b, completion (procTime a b) B j =
        uCount a b * sigma a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b ∧
      ∑ j, completion (procTime a b) B j ≤ yThreshold a b := by
  intro B
  exact tc_forward_core a b ha hb hbA S hS l₁ l₂ l₃ l₄ l₅ h₁ h₂ h₃ h₄ h₅ B rfl
