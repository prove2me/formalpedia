-- Prove2me | solution 1 for StrongConv.card_wordFree_eq_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:44:55.745223+00:00
-- url     : https://prove2.me/submissions/7845b998-f351-4567-9e80-5c9d17f13aba

import Mathlib
import Definitions.Def_StrongConv

open FreeGroup

noncomputable section

namespace StrongConv

lemma mk_cancel {α : Type*} (m : List (α × Bool)) (a : α) (b : Bool) :
    mk (m ++ [(a, b), (a, !b)]) = mk m := by
  have := @FreeGroup.Red.Step.not α m [] a b
  simp only [List.append_nil] at this
  exact Quot.sound this

lemma hit0 {α : Type*} [DecidableEq α] : ∀ (x : List (α × Bool)) (a b : List (α × Bool)),
    toWord (mk x) = a ++ b → ∃ x1 x2, x = x1 ++ x2 ∧ mk x1 = mk a ∧ mk x2 = mk b := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro a b h
    have h1 : a ++ b = [] := by rw [← h]; simp
    have ha : a = [] := (List.append_eq_nil_iff.1 h1).1
    have hb : b = [] := (List.append_eq_nil_iff.1 h1).2
    subst ha hb
    exact ⟨[], [], by simp, rfl, rfl⟩
  | append_singleton x' s ih =>
    intro a b h
    have hW' : FreeGroup.IsReduced (toWord (mk x')) := isReduced_toWord
    by_cases hr : FreeGroup.IsReduced (toWord (mk x') ++ [s])
    · have hmk : mk (toWord (mk x') ++ [s]) = mk (x' ++ [s]) := by
        rw [← mul_mk, ← mul_mk, mk_toWord]
      have heq : toWord (mk (x' ++ [s])) = toWord (mk x') ++ [s] := by
        rw [← hmk, toWord_mk, hr.reduce_eq]
      rw [heq] at h
      rcases List.eq_nil_or_concat b with hb | ⟨b', s', hb⟩
      · subst hb
        refine ⟨x' ++ [s], [], by simp, ?_, rfl⟩
        rw [List.append_nil] at h
        rw [← h, ← hmk]
      · simp only [List.concat_eq_append] at hb
        subst hb
        have h2 : toWord (mk x') ++ [s] = (a ++ b') ++ [s'] := by rw [h]; simp
        have h3 := List.append_inj_left' h2 (by simp)
        have hs : s = s' := by simpa using (List.append_inj' h2 (by simp)).2
        subst hs
        obtain ⟨x1, x2, hx, h1, h2'⟩ := ih a b' h3
        refine ⟨x1, x2 ++ [s], by simp [hx], h1, ?_⟩
        rw [← mul_mk, ← mul_mk, h2']
    · obtain ⟨m, t, hmt⟩ : ∃ m t, toWord (mk x') = m ++ [t] := by
        rcases List.eq_nil_or_concat (toWord (mk x')) with h0 | ⟨m, t, h0⟩
        · exfalso; apply hr; rw [h0]; exact FreeGroup.IsReduced.singleton
        · exact ⟨m, t, by simpa using h0⟩
      have hcan : t.1 = s.1 ∧ t.2 = !s.2 := by
        by_contra hc
        apply hr
        rw [hmt] at hW' ⊢
        unfold FreeGroup.IsReduced at hW' ⊢
        rw [List.isChain_append]
        refine ⟨hW', List.isChain_singleton _, ?_⟩
        intro u hu v hv h1
        simp at hu hv
        subst hu hv
        by_contra h2
        apply hc
        refine ⟨h1, ?_⟩
        cases ht : t.2 <;> cases hs : s.2 <;> simp_all
      obtain ⟨t1, t2⟩ := t
      obtain ⟨s1, s2⟩ := s
      simp only at hcan
      obtain ⟨rfl, rfl⟩ := hcan
      have hmk : mk (x' ++ [(t1, s2)]) = mk m := by
        have : mk x' = mk (m ++ [(t1, !s2)]) := by rw [← mk_toWord (x := mk x'), hmt]
        rw [← mul_mk, this, mul_mk]
        have := mk_cancel m t1 (!s2)
        simpa using this
      have hm : FreeGroup.IsReduced m := hW'.infix ⟨[], [(t1, !s2)], by simp [hmt]⟩
      have heq : toWord (mk (x' ++ [(t1, s2)])) = m := by
        rw [hmk, toWord_mk, hm.reduce_eq]
      rw [heq] at h
      obtain ⟨x1, x2, hx, h1, h2'⟩ := ih a (b ++ [(t1, !s2)]) (by rw [hmt, h]; simp)
      refine ⟨x1, x2 ++ [(t1, s2)], by simp [hx], h1, ?_⟩
      rw [← mul_mk, h2', mul_mk]
      have := mk_cancel b t1 (!s2)
      simpa using this

lemma hit1 {α : Type*} [DecidableEq α] (x a b : List (α × Bool)) (h : toWord (mk x) = a ++ b) :
    ∃ x1 x2, x = x1 ++ x2 ∧ mk x1 = mk a ∧ toWord (mk x2) = b := by
  obtain ⟨x1, x2, hx, h1, h2⟩ := hit0 x a b h
  refine ⟨x1, x2, hx, h1, ?_⟩
  have hb : FreeGroup.IsReduced b := by
    have : FreeGroup.IsReduced (a ++ b) := h ▸ isReduced_toWord
    exact this.infix ⟨a, [], by simp⟩
  rw [h2, toWord_mk, hb.reduce_eq]

lemma mk_flatten_replicate {α : Type*} (C : List (α × Bool)) (n : ℕ) :
    mk (List.replicate n C).flatten = (mk C) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← mul_mk, ih, pow_succ']

lemma E_pair {α : Type*} [DecidableEq α] (x : List (α × Bool)) (v : FreeGroup α) (n : ℕ)
    (hx : mk x = v ^ (n + 2)) :
    ∃ x1 x2 x3 x4 x5 : List (α × Bool), x = x1 ++ x2 ++ x3 ++ x4 ++ x5 ∧ mk x3 = mk x2 ∧
      mk x4 = (mk x2) ^ n ∧ mk x5 = (mk x1)⁻¹ ∧ v = mk x1 * mk x2 * (mk x1)⁻¹ := by
  set c := reduceCyclically.conjugator v.toWord with hc
  set C := reduceCyclically v.toWord with hC
  have hv := reduceCyclically.conj_conjugator_reduceCyclically v.toWord
  have hw : toWord (mk x) = c ++ (C ++ (C ++ ((List.replicate n C).flatten ++ invRev c))) := by
    rw [hx, toWord_pow, reduceCyclically.reduce_flatten_replicate isReduced_toWord]
    simp [List.replicate_succ, hc, hC]
  obtain ⟨x1, y1, rfl, h1, h1'⟩ := hit1 x _ _ hw
  obtain ⟨x2, y2, rfl, h2, h2'⟩ := hit1 y1 _ _ h1'
  obtain ⟨x3, y3, rfl, h3, h3'⟩ := hit1 y2 _ _ h2'
  obtain ⟨x4, x5, rfl, h4, h4'⟩ := hit1 y3 _ _ h3'
  refine ⟨x1, x2, x3, x4, x5, by simp, h3.trans h2.symm, ?_, ?_, ?_⟩
  · rw [h4, mk_flatten_replicate, h2]
  · rw [← mk_toWord (x := mk x5), h4', h1, inv_mk]
  · have := congrArg mk hv
    rw [← mul_mk, ← mul_mk, mk_toWord, ← inv_mk] at this
    rw [h1, h2, this]

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply]
  rw [← (Equiv.mulLeft g).tsum_eq (fun i => inner ℂ (x i) (y (g⁻¹ * i)))]
  simp

def lt {d : ℕ} : Fin d ⊕ Fin d → FreeGroup (Fin d) := Sum.elim FreeGroup.of (fun i => (FreeGroup.of i)⁻¹)

lemma leftReg_delta {d : ℕ} (g u : FreeGroup (Fin d)) : leftReg g (delta u) = delta (g * u) := by
  ext h
  simp only [leftReg_apply, delta, lp.coeFn_single]
  simp [Pi.single_apply, inv_mul_eq_iff_eq_mul]

lemma adj_delta {d : ℕ} (u : FreeGroup (Fin d)) :
    adjFree d (delta u) = ∑ ℓ : Fin d ⊕ Fin d, delta (lt ℓ * u) := by
  unfold adjFree
  rw [sum_apply, Fintype.sum_sum_type]
  simp only [lt, Sum.elim_inl, Sum.elim_inr, add_apply, sLimit, star_leftReg,
    leftReg_delta, Finset.sum_add_distrib]

/-- the product of a list of letters -/
def ev {d : ℕ} (l : List (Fin d ⊕ Fin d)) : FreeGroup (Fin d) := (l.map lt).prod

lemma ev_cons {d : ℕ} (a : Fin d ⊕ Fin d) (l : List (Fin d ⊕ Fin d)) : ev (a :: l) = lt a * ev l := by
  simp [ev]

def Vt (d t : ℕ) : L2Free d := ∑ x : Fin t → Fin d ⊕ Fin d, delta (ev (List.ofFn x))

lemma Vt_zero (d : ℕ) : Vt d 0 = delta 1 := by
  simp [Vt, ev]

lemma adj_Vt (d t : ℕ) : adjFree d (Vt d t) = Vt d (t + 1) := by
  unfold Vt
  rw [map_sum]
  simp only [adj_delta]
  rw [Finset.sum_comm]
  symm
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => Fin d ⊕ Fin d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
  simp [Fin.consEquiv, List.ofFn_succ, ev_cons]

def Nf (d t : ℕ) (u : FreeGroup (Fin d)) : ℕ :=
  (Finset.univ.filter fun x : Fin t → Fin d ⊕ Fin d => ev (List.ofFn x) = u).card

lemma Vt_apply (d t : ℕ) (u : FreeGroup (Fin d)) : Vt d t u = (Nf d t u : ℂ) := by
  classical
  unfold Vt Nf
  rw [lp.coeFn_sum]
  simp only [delta, lp.coeFn_single, Finset.sum_apply, Pi.single_apply]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : ev (List.ofFn x) = u
  · simp [h]
  · simp [h, Ne.symm h]


lemma Vt_eq_pow (d t : ℕ) : Vt d t = (adjFree d ^ t) (delta 1) := by
  induction t with
  | zero => simp [Vt_zero]
  | succ t ih => rw [pow_succ', mul_apply_eq_comp, ← ih, adj_Vt]

lemma norm_Vt_le (d t : ℕ) : ‖Vt d t‖ ≤ ‖adjFree d‖ ^ t := by
  rw [Vt_eq_pow]
  have h1 : ‖(delta (d := d) 1)‖ = 1 := by simp [delta]
  have := (adjFree d ^ t).le_opNorm (delta (d := d) 1)
  rw [h1, mul_one] at this
  refine this.trans ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' _ ht

lemma sum_sq_le (d t : ℕ) (U : Finset (FreeGroup (Fin d))) :
    ∑ u ∈ U, (Nf d t u : ℝ) ^ 2 ≤ ‖adjFree d‖ ^ (2 * t) := by
  have hV := Vt_apply d t
  have h2 : ‖Vt d t‖ ^ (2 : ℝ) = ∑' u, ‖Vt d t u‖ ^ (2 : ℝ) := by
    have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (Vt d t)
    simpa using this
  have hs : Summable fun u => ‖Vt d t u‖ ^ (2 : ℝ) := by
    have := (lp.memℓp (Vt d t))
    rw [memℓp_gen_iff (by norm_num)] at this
    simpa using this
  have h3 : ∑ u ∈ U, (Nf d t u : ℝ) ^ 2 ≤ ‖Vt d t‖ ^ (2 : ℝ) := by
    rw [h2]
    refine le_trans (le_of_eq ?_) (hs.sum_le_tsum U (fun _ _ => by positivity))
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hV]; simp
  have h4 : ‖Vt d t‖ ^ (2 : ℝ) ≤ (‖adjFree d‖ ^ t) ^ 2 := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Vt_le d t) 2
  rw [← pow_mul] at h4
  rw [mul_comm]
  exact h3.trans h4


/-! ### Counting -/

abbrev Lt (d : ℕ) := Fin d ⊕ Fin d

def W (d t : ℕ) : Finset (List (Lt d)) := Finset.univ.image (List.ofFn : (Fin t → Lt d) → List (Lt d))

lemma mem_W {d t : ℕ} {l : List (Lt d)} : l ∈ W d t ↔ l.length = t := by
  unfold W
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    simp
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

def Nl (d t : ℕ) (u : FreeGroup (Fin d)) : ℕ := ((W d t).filter fun l => ev l = u).card

lemma Nl_eq_Nf (d t : ℕ) (u : FreeGroup (Fin d)) : Nl d t u = Nf d t u := by
  unfold Nl Nf W
  rw [Finset.filter_image, Finset.card_image_of_injective _ List.ofFn_injective]

lemma sum_sq_le_Nl (d t : ℕ) (U : Finset (FreeGroup (Fin d))) :
    ∑ u ∈ U, (Nl d t u : ℝ) ^ 2 ≤ ‖adjFree d‖ ^ (2 * t) := by
  simp only [Nl_eq_Nf]; exact sum_sq_le d t U

lemma Nl_le (d t : ℕ) (u : FreeGroup (Fin d)) : (Nl d t u : ℝ) ≤ ‖adjFree d‖ ^ t := by
  have h := sum_sq_le_Nl d t {u}
  simp only [Finset.sum_singleton] at h
  rw [pow_mul'] at h
  exact le_of_sq_le_sq (by simpa [sq] using h) (by positivity)

lemma card_pairs_le (d t s : ℕ) (e : FreeGroup (Fin d) ≃ FreeGroup (Fin d)) :
    (((W d t ×ˢ W d s).filter fun z => ev z.2 = e (ev z.1)).card : ℝ) ≤ ‖adjFree d‖ ^ (t + s) := by
  classical
  set R := ‖adjFree d‖
  set U := (W d t).image ev with hU
  have h1 : ((W d t ×ˢ W d s).filter fun z => ev z.2 = e (ev z.1)).card =
      ∑ u ∈ U, Nl d t u * Nl d s (e u) := by
    rw [Finset.card_filter, Finset.sum_product]
    have : ∀ a ∈ W d t, (∑ b ∈ W d s, if ev b = e (ev a) then 1 else 0) = Nl d s (e (ev a)) := by
      intro a _
      unfold Nl
      rw [Finset.card_filter]
    rw [Finset.sum_congr rfl this]
    rw [← Finset.sum_fiberwise_of_maps_to (s := W d t) (t := U) (g := ev)
      (fun a ha => Finset.mem_image_of_mem _ ha)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => Nl d s (e u)) (fun a ha => by
      rw [(Finset.mem_filter.1 ha).2])]
    simp [Nl]
  rw [h1]
  push_cast
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun u => (Nl d t u : ℝ)) (fun u => (Nl d s (e u) : ℝ))
  have hA := sum_sq_le_Nl d t U
  have hB : ∑ u ∈ U, (Nl d s (e u) : ℝ) ^ 2 ≤ R ^ (2 * s) := by
    have := sum_sq_le_Nl d s (U.image e)
    rwa [Finset.sum_image (fun a _ b _ h => e.injective h)] at this
  have hS : 0 ≤ ∑ u ∈ U, (Nl d t u : ℝ) * (Nl d s (e u) : ℝ) := by positivity
  have h2 : (∑ u ∈ U, (Nl d t u : ℝ) * (Nl d s (e u) : ℝ)) ^ 2 ≤ (R ^ (t + s)) ^ 2 := by
    refine hcs.trans ?_
    have : (R ^ (t + s)) ^ 2 = R ^ (2 * t) * R ^ (2 * s) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [this]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  exact le_of_sq_le_sq h2 (by positivity)

/-! ### Letters and free-group words -/

def toPair {d : ℕ} : Lt d → Fin d × Bool
  | Sum.inl i => (i, true)
  | Sum.inr i => (i, false)

def ofPair {d : ℕ} (p : Fin d × Bool) : Lt d := if p.2 then Sum.inl p.1 else Sum.inr p.1

lemma ofPair_toPair {d : ℕ} (a : Lt d) : ofPair (toPair a) = a := by
  cases a <;> simp [toPair, ofPair]

lemma toPair_ofPair {d : ℕ} (p : Fin d × Bool) : toPair (ofPair p) = p := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [toPair, ofPair]

lemma ev_eq_mk {d : ℕ} (l : List (Lt d)) : ev l = mk (l.map toPair) := by
  induction l with
  | nil => simp [ev]; rfl
  | cons a l ih =>
    rw [ev_cons, ih, List.map_cons, ← List.singleton_append, ← mul_mk]
    congr 1
    cases a with
    | inl i => rfl
    | inr i =>
      simp only [lt, toPair, Sum.elim_inr]
      rw [of, inv_mk]
      simp [invRev]

lemma E_list {d : ℕ} (x : List (Lt d)) (v : FreeGroup (Fin d)) (n : ℕ) (hx : ev x = v ^ (n + 2)) :
    ∃ l1 l2 l3 l4 l5 : List (Lt d), x = l1 ++ l2 ++ l3 ++ l4 ++ l5 ∧ ev l3 = ev l2 ∧
      ev l4 = (ev l2) ^ n ∧ ev l5 = (ev l1)⁻¹ ∧ v = ev l1 * ev l2 * (ev l1)⁻¹ := by
  rw [ev_eq_mk] at hx
  obtain ⟨x1, x2, x3, x4, x5, hxe, h3, h4, h5, hv⟩ := E_pair _ v n hx
  have hx' : x = (x.map toPair).map ofPair := by
    simp [List.map_map, Function.comp_def, ofPair_toPair]
  refine ⟨x1.map ofPair, x2.map ofPair, x3.map ofPair, x4.map ofPair, x5.map ofPair, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx', hxe]; simp
  all_goals simp only [ev_eq_mk, List.map_map, Function.comp_def, toPair_ofPair, List.map_id']
  · exact h3
  · exact h4
  · exact h5
  · exact hv

lemma wordFree_map_some {d : ℕ} (l : List (Lt d)) : wordFree (l.map some) = ev l := by
  induction l with
  | nil => simp [wordFree, ev]
  | cons a l ih =>
    rw [List.map_cons, ev_cons, ← ih]
    cases a <;> simp [wordFree, lt]

/-! ### Assembly -/

lemma card_filter_prod {α β : Type*} (A : Finset α) (B : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    ((A ×ˢ B).filter fun z => P z.1 z.2).card = ∑ a ∈ A, (B.filter (P a)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

def Pset (d t1 t5 : ℕ) : Finset (List (Lt d) × List (Lt d)) :=
  (W d t1 ×ˢ W d t5).filter fun z => ev z.2 = (ev z.1)⁻¹

def Qset (d n t2 t3 t4 : ℕ) : Finset ((List (Lt d) × List (Lt d)) × List (Lt d)) :=
  (((W d t2 ×ˢ W d t3).filter fun z => ev z.2 = ev z.1) ×ˢ W d t4).filter
    fun z => ev z.2 = (ev z.1.1) ^ n

lemma card_Pset_le (d t1 t5 : ℕ) :
    ((Pset d t1 t5).card : ℝ) ≤ ‖adjFree d‖ ^ (t1 + t5) :=
  card_pairs_le d t1 t5 (Equiv.inv _)

lemma card_Qset_le (d n t2 t3 t4 : ℕ) :
    ((Qset d n t2 t3 t4).card : ℝ) ≤ ‖adjFree d‖ ^ (t2 + t3 + t4) := by
  unfold Qset
  rw [card_filter_prod (P := fun (a : List (Lt d) × List (Lt d)) (b : List (Lt d)) =>
    ev b = (ev a.1) ^ n)]
  have h1 : ∀ a ∈ ((W d t2 ×ˢ W d t3).filter fun z => ev z.2 = ev z.1),
      (((W d t4).filter fun b => ev b = (ev a.1) ^ n).card : ℝ) ≤ ‖adjFree d‖ ^ t4 :=
    fun a _ => Nl_le d t4 _
  push_cast
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_pairs_le d t2 t3 (Equiv.refl _)
  simp only [Equiv.refl_apply] at this
  calc _ ≤ ‖adjFree d‖ ^ (t2 + t3) * ‖adjFree d‖ ^ t4 :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by rw [pow_add, pow_add, pow_add]

def Bset (d n p : ℕ) (τ : ℕ × ℕ × ℕ × ℕ) :
    Finset ((List (Lt d) × List (Lt d)) × ((List (Lt d) × List (Lt d)) × List (Lt d))) :=
  Pset d τ.1 (p - (τ.1 + τ.2.1 + τ.2.2.1 + τ.2.2.2)) ×ˢ Qset d n τ.2.1 τ.2.2.1 τ.2.2.2

def Tset (p : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (p + 1) ×ˢ Finset.range (p + 1) ×ˢ Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
    fun τ => τ.1 + τ.2.1 + τ.2.2.1 + τ.2.2.2 ≤ p

lemma card_Tset_le (p : ℕ) : (Tset p).card ≤ (p + 1) ^ 4 := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product]
  nlinarith

lemma card_Bset_le (d n p : ℕ) (τ : ℕ × ℕ × ℕ × ℕ) (hτ : τ ∈ Tset p) :
    ((Bset d n p τ).card : ℝ) ≤ ‖adjFree d‖ ^ p := by
  have hle := (Finset.mem_filter.1 hτ).2
  unfold Bset
  rw [Finset.card_product]
  push_cast
  refine (mul_le_mul (card_Pset_le _ _ _) (card_Qset_le _ _ _ _ _) (by positivity)
    (by positivity)).trans (le_of_eq ?_)
  rw [← pow_add]
  congr 1
  omega

def Psi {d : ℕ} (z : (List (Lt d) × List (Lt d)) × ((List (Lt d) × List (Lt d)) × List (Lt d))) :
    List (Lt d) × FreeGroup (Fin d) :=
  (z.1.1 ++ z.2.1.1 ++ z.2.1.2 ++ z.2.2 ++ z.1.2, ev z.1.1 * ev z.2.1.1 * (ev z.1.1)⁻¹)

open Classical in
def Gset (d n p : ℕ) : Finset (List (Lt d) × FreeGroup (Fin d)) :=
  ((Tset p).biUnion (Bset d n p)).image Psi

open Classical in
lemma card_Gset_le (d n p : ℕ) :
    ((Gset d n p).card : ℝ) ≤ ((p : ℝ) + 1) ^ 4 * ‖adjFree d‖ ^ p := by
  unfold Gset
  refine (Nat.cast_le.2 (Finset.card_image_le.trans Finset.card_biUnion_le)).trans ?_
  push_cast
  calc ∑ τ ∈ Tset p, ((Bset d n p τ).card : ℝ) ≤ ∑ τ ∈ Tset p, ‖adjFree d‖ ^ p :=
        Finset.sum_le_sum (fun τ hτ => card_Bset_le d n p τ hτ)
    _ = ((Tset p).card : ℝ) * ‖adjFree d‖ ^ p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_Tset_le p

open Classical in
lemma mem_Gset (d n p : ℕ) (x : List (Lt d)) (hx : x.length = p) (v : FreeGroup (Fin d))
    (h : ev x = v ^ (n + 2)) : (x, v) ∈ Gset d n p := by
  obtain ⟨l1, l2, l3, l4, l5, hxe, h3, h4, h5, hv⟩ := E_list x v n h
  have hlen : l1.length + l2.length + l3.length + l4.length + l5.length = p := by
    rw [← hx, hxe]; simp; omega
  unfold Gset
  rw [Finset.mem_image]
  refine ⟨((l1, l5), ((l2, l3), l4)), ?_, ?_⟩
  · rw [Finset.mem_biUnion]
    refine ⟨(l1.length, l2.length, l3.length, l4.length), ?_, ?_⟩
    · unfold Tset
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · unfold Bset Pset Qset
      simp only [Finset.mem_product, Finset.mem_filter, mem_W]
      refine ⟨⟨⟨trivial, by omega⟩, h5⟩, ⟨⟨⟨⟨trivial, trivial⟩, h3⟩, trivial⟩, h4⟩⟩
  · simp only [Psi]
    rw [hxe, ← hv]

/-- the pairs `(x, v)` with `x` a word reducing to `v ^ k` -/
theorem card_wordFree_eq_pow_le_dev (d k p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p) :
    (Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} : ℝ) ≤
      ((p : ℝ) + 1) ^ 4 * ‖adjFree d‖ ^ p := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  refine le_trans ?_ (card_Gset_le d n p)
  have hinj : Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ (n + 2)} ≤
      Nat.card (Gset d n p) := by
    refine Nat.card_le_card_of_injective
      (fun z => ⟨(List.ofFn z.1.1, z.1.2), mem_Gset d n p _ (by simp) _ ?_⟩) ?_
    · have := z.2.2
      rw [← wordFree_map_some, List.map_ofFn]
      exact this
    · intro z z' h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (List.ofFn_injective h.1) h.2)
  have h2 : Nat.card (Gset d n p) = (Gset d n p).card := by simp
  rw [h2] at hinj
  exact_mod_cast hinj

end StrongConv

theorem solution : type_of% @StrongConv.card_wordFree_eq_pow_le_dev :=
  @StrongConv.card_wordFree_eq_pow_le_dev

end
