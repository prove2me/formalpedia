-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.formulation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T23:14:43.564363+00:00
-- url     : https://prove2.me/submissions/f1f46c58-4007-4e65-8cc8-33906c13dfbb

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes

set_option autoImplicit false

namespace RBCP52
open RobustBCPCVRP.Formulation LysgaardCVRP.Shrink

variable {n : ℕ}

/-- consecutive-pair edges of a vertex list -/
def pe : List (Fin (n + 1)) → List (Sym2 (Fin (n + 1)))
  | a :: b :: t => s(a, b) :: pe (b :: t)
  | _ => []

lemma pe_cons_cons (a b : Fin (n + 1)) (t : List (Fin (n + 1))) :
    pe (a :: b :: t) = s(a, b) :: pe (b :: t) := rfl

lemma pe_single (a : Fin (n + 1)) : pe [a] = [] := rfl

lemma pe_nil : pe ([] : List (Fin (n + 1))) = [] := rfl

lemma zip_eq_pe : ∀ l : List (Fin (n + 1)),
    (l.zip l.tail).map (fun p => s(p.1, p.2)) = pe l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      rw [pe_cons_cons, ← zip_eq_pe (b :: t)]
      rfl

lemma edges_eq (r : List (Fin (n + 1))) : edges r = pe (0 :: (r ++ [0])) := by
  rw [edges, walk, zip_eq_pe]

lemma mem_pe : ∀ (l : List (Fin (n + 1))) (e : Sym2 (Fin (n + 1))),
    e ∈ pe l → ∀ y ∈ e, y ∈ l
  | [], e, h => by simp [pe_nil] at h
  | [a], e, h => by simp [pe_single] at h
  | a :: b :: t, e, h => by
      intro y hy
      rw [pe_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · rw [Sym2.mem_iff] at hy
        rcases hy with rfl | rfl <;> simp
      · exact List.mem_cons_of_mem _ (mem_pe (b :: t) e h y hy)

/-! cut algebra -/

lemma cut_add (f g : Sym2 (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) :
    cut (fun e => f e + g e) S = cut f S + cut g S := by
  simp [cut, Finset.sum_add_distrib]

lemma cut_sub (f g : Sym2 (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) :
    cut (fun e => f e - g e) S = cut f S - cut g S := by
  simp [cut, Finset.sum_sub_distrib]

lemma cut_mul (c : ℝ) (f : Sym2 (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) :
    cut (fun e => c * f e) S = c * cut f S := by
  simp [cut, Finset.mul_sum]

lemma cut_sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 (Fin (n + 1)) → ℝ)
    (S : Finset (Fin (n + 1))) :
    cut (fun e => ∑ k ∈ s, f k e) S = ∑ k ∈ s, cut (f k) S := by
  unfold cut
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

lemma cut_mono {f g : Sym2 (Fin (n + 1)) → ℝ} (h : ∀ e, f e ≤ g e) (S : Finset (Fin (n + 1))) :
    cut f S ≤ cut g S :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h _

lemma cut_singleton (f : Sym2 (Fin (n + 1)) → ℝ) (a : Fin (n + 1)) :
    cut f {a} = ∑ j ∈ ({a}ᶜ : Finset (Fin (n + 1))), f s(a, j) := by
  simp [cut]

lemma term_le_cut {f : Sym2 (Fin (n + 1)) → ℝ} (hf : ∀ e, 0 ≤ f e) {a b : Fin (n + 1)}
    (hab : a ≠ b) : f s(a, b) ≤ cut f {a} := by
  rw [cut_singleton]
  exact Finset.single_le_sum (f := fun j => f s(a, j)) (fun j _ => hf _)
    (by simpa [Finset.mem_compl] using hab.symm)

/-- `e` crosses `S` -/
def crossP (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) : Prop :=
  (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)

instance (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) : Decidable (crossP S a b) := by
  unfold crossP; infer_instance

lemma cut_ind_aux (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (ha : a ∈ S) (hb : b ∉ S) :
    cut (fun e => if s(a, b) = e then (1 : ℝ) else 0) S = 1 := by
  unfold cut
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro k hk hkb
      dsimp only; rw [if_neg]
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · exact hkb h.symm
      · rw [Finset.mem_compl] at hk; exact hk (h ▸ ha)
    · intro h; exact absurd (Finset.mem_compl.mpr hb) h
  · intro i hi hia
    apply Finset.sum_eq_zero
    intro k hk
    dsimp only; rw [if_neg]
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hia h.symm
    · rw [Finset.mem_compl] at hk; exact hk (h ▸ ha)
  · intro h; exact absurd ha h

lemma cut_ind (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    cut (fun e => if s(a, b) = e then (1 : ℝ) else 0) S = if crossP S a b then 1 else 0 := by
  classical
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · rw [if_neg (by simp [crossP, ha, hb])]
    unfold cut
    apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro k hk
    rw [Finset.mem_compl] at hk
    dsimp only; rw [if_neg]; intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> contradiction
  · rw [if_pos (by simp [crossP, ha, hb])]
    exact cut_ind_aux S a b ha hb
  · rw [if_pos (by simp [crossP, ha, hb])]
    have := cut_ind_aux S b a hb ha
    simpa [Sym2.eq_swap] using this
  · rw [if_neg (by simp [crossP, ha, hb])]
    unfold cut
    apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro k hk
    dsimp only; rw [if_neg]; intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> contradiction

/-- crossing count of an edge list -/
noncomputable def ncr (S : Finset (Fin (n + 1))) (L : List (Sym2 (Fin (n + 1)))) : ℝ :=
  cut (fun e => ((L.count e : ℕ) : ℝ)) S

lemma ncr_nil (S : Finset (Fin (n + 1))) : ncr S [] = 0 := by
  simp [ncr, cut]

lemma ncr_cons (S : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Sym2 (Fin (n + 1)))) :
    ncr S (s(a, b) :: L) = ncr S L + if crossP S a b then 1 else 0 := by
  classical
  unfold ncr
  rw [← cut_ind S a b, ← cut_add]
  congr 1
  funext e
  rw [List.count_cons]
  by_cases h : s(a, b) = e
  · simp [h]
  · simp [h]

lemma ncr_append (S : Finset (Fin (n + 1))) (L M : List (Sym2 (Fin (n + 1)))) :
    ncr S (L ++ M) = ncr S L + ncr S M := by
  unfold ncr
  rw [← cut_add]
  congr 1
  funext e
  rw [List.count_append]
  push_cast; ring

lemma ncr_nonneg (S : Finset (Fin (n + 1))) (L : List (Sym2 (Fin (n + 1)))) : 0 ≤ ncr S L := by
  unfold ncr cut
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma ncr_pe_same : ∀ (S : Finset (Fin (n + 1))) (l : List (Fin (n + 1))),
    ((∀ y ∈ l, y ∉ S) ∨ (∀ y ∈ l, y ∈ S)) → ncr S (pe l) = 0
  | S, [], _ => by rw [pe_nil, ncr_nil]
  | S, [a], _ => by rw [pe_single, ncr_nil]
  | S, a :: b :: t, h => by
      rw [pe_cons_cons, ncr_cons, ncr_pe_same S (b :: t)]
      · rw [if_neg]; · simp
        unfold crossP
        rcases h with h | h
        · have := h a (by simp); have := h b (by simp); tauto
        · have := h a (by simp); have := h b (by simp); tauto
      · rcases h with h | h
        · exact Or.inl fun y hy => h y (List.mem_cons_of_mem _ hy)
        · exact Or.inr fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- degree formula for a walk without loops -/
lemma deg_formula (i : Fin (n + 1)) : ∀ (t : List (Fin (n + 1))) (a : Fin (n + 1)),
    (∀ e ∈ pe (a :: t), ¬ e.IsDiag) →
    ncr {i} (pe (a :: t)) + (if a = i then 1 else 0) +
      (if (a :: t).getLast (List.cons_ne_nil _ _) = i then 1 else 0) =
      2 * (((a :: t).count i : ℕ) : ℝ)
  | [], a, _ => by
      rw [pe_single, ncr_nil]
      by_cases h : a = i <;> simp [h] <;> norm_num
  | b :: t, a, hd => by
      have hab : a ≠ b := by
        have := hd s(a, b) (by simp [pe_cons_cons])
        simpa using this
      have ih := deg_formula i t b (fun e he => hd e (by rw [pe_cons_cons]; exact List.mem_cons_of_mem _ he))
      rw [pe_cons_cons, ncr_cons, List.getLast_cons (List.cons_ne_nil _ _), List.count_cons]
      have hcr : (if crossP {i} a b then (1 : ℝ) else 0) =
          (if a = i then 1 else 0) + (if b = i then 1 else 0) := by
        by_cases h1 : a = i <;> by_cases h2 : b = i
        · exact absurd (h1.trans h2.symm) hab
        all_goals simp [crossP, h1, h2, eq_comm]
      rw [hcr]
      by_cases h1 : a = i
      · simp only [h1, beq_self_eq_true, if_true] at ih ⊢
        push_cast; linarith
      · have : (a == i) = false := by simpa using h1
        simp only [h1, this, if_false] at ih ⊢
        push_cast; linarith

/-- two crossings for a walk from outside `S` back outside `S` that visits `S` -/
lemma two_cross (S : Finset (Fin (n + 1))) : ∀ (t : List (Fin (n + 1))) (a : Fin (n + 1)),
    ((a ∈ S → (a :: t).getLast (List.cons_ne_nil _ _) ∉ S → 1 ≤ ncr S (pe (a :: t))) ∧
     (a ∉ S → (a :: t).getLast (List.cons_ne_nil _ _) ∉ S → (∃ y ∈ a :: t, y ∈ S) →
        2 ≤ ncr S (pe (a :: t))))
  | [], a => by
      refine ⟨fun h1 h2 => absurd h1 (by simpa using h2), fun h1 _ h3 => ?_⟩
      obtain ⟨y, hy, hyS⟩ := h3
      simp at hy; subst hy; exact absurd hyS h1
  | b :: t, a => by
      have ih := two_cross S t b
      rw [List.getLast_cons (List.cons_ne_nil _ _), pe_cons_cons, ncr_cons]
      have hnn := ncr_nonneg S (pe (b :: t))
      refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
      · by_cases hb : b ∈ S
        · have := ih.1 hb h2
          split_ifs <;> linarith
        · rw [if_pos (show crossP S a b from Or.inl ⟨h1, hb⟩)]; linarith
      · by_cases hb : b ∈ S
        · have := ih.1 hb h2
          rw [if_pos (show crossP S a b from Or.inr ⟨hb, h1⟩)]; linarith
        · have h3' : ∃ y ∈ b :: t, y ∈ S := by
            obtain ⟨y, hy, hyS⟩ := h3
            rcases List.mem_cons.mp hy with rfl | hy
            · exact absurd hyS h1
            · exact ⟨y, hy, hyS⟩
          have := ih.2 hb h2 h3'
          split_ifs <;> linarith

/-- one crossing for a path inside `S` exiting at the end -/
lemma one_cross (S : Finset (Fin (n + 1))) (b : Fin (n + 1)) (hb : b ∉ S) :
    ∀ (t : List (Fin (n + 1))) (a : Fin (n + 1)), (∀ y ∈ a :: t, y ∈ S) →
      ncr S (pe (a :: (t ++ [b]))) = 1
  | [], a, h => by
      have ha := h a (by simp)
      simp only [List.nil_append]
      rw [pe_cons_cons, pe_single, ncr_cons, ncr_nil, if_pos (show crossP S a b from Or.inl ⟨ha, hb⟩)]; ring
  | c :: t, a, h => by
      have ha := h a (by simp)
      have hc := h c (by simp)
      rw [List.cons_append, pe_cons_cons, ncr_cons,
        one_cross S b hb t c (fun y hy => h y (List.mem_cons_of_mem _ hy)),
        if_neg (by simp [crossP, ha, hc])]
      ring

/-! routes and walks -/

lemma inc_eq (r : List (Fin (n + 1))) (e : Sym2 (Fin (n + 1))) :
    inc r e = (pe (0 :: (r ++ [0]))).count e := by
  rw [inc, edges_eq]

lemma getLast_walk (r : List (Fin (n + 1))) :
    (0 :: (r ++ [0])).getLast (List.cons_ne_nil _ _) = (0 : Fin (n + 1)) := by
  simp

lemma nodup_snoc0 {r : List (Fin (n + 1))} (h0 : (0 : Fin (n + 1)) ∉ r) (hnd : r.Nodup) :
    (r ++ [0]).Nodup := by
  rw [← List.nodup_reverse, List.reverse_append]
  simp [h0, hnd]

lemma pe_nodup : ∀ l : List (Fin (n + 1)), l.Nodup → (pe l).Nodup ∧ ∀ e ∈ pe l, ¬ e.IsDiag
  | [], _ => by simp [pe_nil]
  | [a], _ => by simp [pe_single]
  | a :: b :: t, h => by
      have ha : a ∉ b :: t := (List.nodup_cons.mp h).1
      have ih := pe_nodup (b :: t) (List.nodup_cons.mp h).2
      rw [pe_cons_cons]
      refine ⟨List.nodup_cons.mpr ⟨fun hm => ha (mem_pe _ _ hm a (Sym2.mem_mk_left a b)), ih.1⟩, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rw [Sym2.mk_isDiag_iff]
        intro hab
        exact ha (by simp [hab])
      · exact ih.2 e he

lemma deg_route (r : List (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ r)
    (hd : ∀ e ∈ edges r, ¬ e.IsDiag) (i : Fin (n + 1)) :
    ncr {i} (edges r) = 2 * ((r.count i : ℕ) : ℝ) + (if (0 : Fin (n + 1)) = i then 2 else 0) := by
  rw [edges_eq] at hd ⊢
  have h := deg_formula i (r ++ [0]) 0 hd
  rw [getLast_walk, List.count_cons, List.count_append] at h
  by_cases hi : (0 : Fin (n + 1)) = i
  · subst hi
    have : r.count 0 = 0 := List.count_eq_zero.mpr h0
    simp [this] at h ⊢
    linarith
  · simp [hi] at h ⊢
    linarith

lemma deg_client (r : List (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ r)
    (hd : ∀ e ∈ edges r, ¬ e.IsDiag) (i : Fin (n + 1)) (hi : i ≠ 0) :
    ncr {i} (edges r) = 2 * ((r.count i : ℕ) : ℝ) := by
  rw [deg_route r h0 hd i, if_neg (Ne.symm hi), add_zero]

lemma deg_depot (r : List (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ r)
    (hd : ∀ e ∈ edges r, ¬ e.IsDiag) : ncr {0} (edges r) = 2 := by
  rw [deg_route r h0 hd 0, if_pos rfl, List.count_eq_zero.mpr h0]
  simp

lemma count_cons_le (x : Sym2 (Fin (n + 1)) → ℝ) {L : List (Sym2 (Fin (n + 1)))} {a b : Fin (n + 1)}
    (hL : ∀ e, ((L.count e : ℕ) : ℝ) ≤ x e)
    (hab : 1 ≤ x s(a, b) - ((L.count s(a, b) : ℕ) : ℝ)) :
    ∀ e, (((s(a, b) :: L).count e : ℕ) : ℝ) ≤ x e := by
  intro e
  rw [List.count_cons]
  by_cases h : s(a, b) = e
  · subst h; simp; linarith
  · simp [h]; exact hL e

lemma int_ge_one {y : ℝ} (hy : ∃ z : ℤ, y = z) (c : ℕ) (h : 0 < y - c) : 1 ≤ y - c := by
  obtain ⟨z, rfl⟩ := hy
  have e1 : ((z : ℝ) - (c : ℝ)) = (((z - (c : ℤ)) : ℤ) : ℝ) := by push_cast; ring
  rw [e1] at h ⊢
  have h' : (0 : ℤ) < z - c := by exact_mod_cast h
  have h2 : (1 : ℤ) ≤ z - c := by omega
  exact_mod_cast h2

lemma find_step (x : Sym2 (Fin (n + 1)) → ℝ) (hint : ∀ e, ∃ z : ℤ, x e = z)
    (hdeg : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 0 ∨ cut x {i} = 2)
    (r : List (Fin (n + 1))) (hr : r ≠ []) (h0 : (0 : Fin (n + 1)) ∉ r) (hnd : r.Nodup)
    (hb : ∀ e, (((pe (r ++ [0])).count e : ℕ) : ℝ) ≤ x e) :
    (∀ e, (inc r e : ℝ) ≤ x e) ∨ ∃ j : Fin (n + 1), j ≠ 0 ∧ j ∉ r ∧
      ∀ e, (((pe ((j :: r) ++ [0])).count e : ℕ) : ℝ) ≤ x e := by
  obtain ⟨v, t, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hnd' := nodup_snoc0 h0 hnd
  have hOd := pe_nodup _ hnd'
  rw [List.cons_append] at hnd' hOd hb
  have hv0 : v ≠ 0 := fun h => h0 (by simp [h])
  -- degree of `v` in the open path
  have hdv : ncr {v} (pe (v :: (t ++ [0]))) = 1 := by
    have h := deg_formula v (t ++ [0]) v hOd.2
    have hc : (v :: (t ++ [0])).count v = 1 := List.count_eq_one_of_mem hnd' (by simp)
    have hl : (v :: (t ++ [0])).getLast (List.cons_ne_nil _ _) = 0 := by simp
    rw [hc, hl, if_pos rfl, if_neg (Ne.symm hv0)] at h
    push_cast at h; linarith
  have hxv : cut x {v} = 2 := by
    have hle : ncr {v} (pe (v :: (t ++ [0]))) ≤ cut x {v} := cut_mono hb {v}
    rcases hdeg v hv0 with h | h
    · rw [h] at hle; linarith
    · exact h
  set O := pe (v :: (t ++ [0])) with hO
  set y : Sym2 (Fin (n + 1)) → ℝ := fun e => x e - ((O.count e : ℕ) : ℝ) with hy
  have hynn : ∀ e, 0 ≤ y e := fun e => by simp only [hy]; linarith [hb e]
  have hcy : ∀ S, cut y S = cut x S - ncr S O := fun S => cut_sub x _ S
  have hyv : ∑ j ∈ ({v}ᶜ : Finset (Fin (n + 1))), y s(v, j) = 1 := by
    rw [← cut_singleton, hcy, hxv, hdv]; norm_num
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ ({v}ᶜ : Finset (Fin (n + 1))), 0 < y s(v, j) := by
    by_contra hc
    push Not at hc
    have := Finset.sum_nonpos hc
    linarith
  have hjv : j ≠ v := by simpa using hj
  have hy1 : 1 ≤ x s(v, j) - ((O.count s(v, j) : ℕ) : ℝ) := int_ge_one (hint _) _ hjpos
  by_cases hj0 : j = 0
  · subst hj0
    left
    intro e
    rw [inc_eq, List.cons_append, pe_cons_cons]
    refine count_cons_le x hb ?_ e
    rw [Sym2.eq_swap]; exact hy1
  · by_cases hjr : j ∈ v :: t
    · exfalso
      have hjt : j ∈ t := by
        rcases List.mem_cons.mp hjr with h | h
        · exact absurd h hjv
        · exact h
      have hdj : ncr {j} O = 2 := by
        have h := deg_formula j (t ++ [0]) v hOd.2
        have hc : (v :: (t ++ [0])).count j = 1 := List.count_eq_one_of_mem hnd' (by simp [hjt])
        have hl : (v :: (t ++ [0])).getLast (List.cons_ne_nil _ _) = 0 := by simp
        rw [hc, hl, if_neg (Ne.symm hjv), if_neg (Ne.symm hj0)] at h
        push_cast at h; linarith
      have h1 : y s(j, v) ≤ cut y {j} := term_le_cut hynn hjv
      rw [Sym2.eq_swap] at h1
      have h2 : y s(v, j) = x s(v, j) - ((O.count s(v, j) : ℕ) : ℝ) := rfl
      rw [hcy, hdj] at h1
      rcases hdeg j hj0 with h | h <;> rw [h] at h1 <;> linarith
    · right
      refine ⟨j, hj0, hjr, ?_⟩
      intro e
      rw [List.cons_append, List.cons_append, pe_cons_cons]
      refine count_cons_le x hb ?_ e
      rw [Sym2.eq_swap]; exact hy1

lemma find_route (x : Sym2 (Fin (n + 1)) → ℝ) (hint : ∀ e, ∃ z : ℤ, x e = z)
    (hdeg : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 0 ∨ cut x {i} = 2) :
    ∀ (m : ℕ) (r : List (Fin (n + 1))), r ≠ [] → (0 : Fin (n + 1)) ∉ r → r.Nodup →
      (∀ e, (((pe (r ++ [0])).count e : ℕ) : ℝ) ≤ x e) → n + 1 - r.length ≤ m →
      ∃ q : List (Fin (n + 1)), q ≠ [] ∧ (0 : Fin (n + 1)) ∉ q ∧ q.Nodup ∧
        ∀ e, (inc q e : ℝ) ≤ x e := by
  intro m
  induction m with
  | zero =>
    intro r hr h0 hnd hb hm
    rcases find_step x hint hdeg r hr h0 hnd hb with h | ⟨j, hj0, hjr, hb'⟩
    · exact ⟨r, hr, h0, hnd, h⟩
    · exfalso
      have := (List.nodup_cons.mpr ⟨hjr, hnd⟩).length_le_card
      simp at this
      omega
  | succ m ih =>
    intro r hr h0 hnd hb hm
    rcases find_step x hint hdeg r hr h0 hnd hb with h | ⟨j, hj0, hjr, hb'⟩
    · exact ⟨r, hr, h0, hnd, h⟩
    · have hlen := (List.nodup_cons.mpr ⟨hjr, hnd⟩).length_le_card
      simp at hlen
      refine ih (j :: r) (List.cons_ne_nil _ _) ?_ (List.nodup_cons.mpr ⟨hjr, hnd⟩) hb' ?_
      · rw [List.mem_cons]; push Not; exact ⟨Ne.symm hj0, h0⟩
      · simp only [List.length_cons]; omega

lemma decomp (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ i : Fin (n + 1), i ≠ 0 → 0 < d i) (hC : 0 < C) :
    ∀ (K : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ), (∀ e, ∃ z : ℤ, x e = z) → (∀ e, 0 ≤ x e) → OnE E x →
      (∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 0 ∨ cut x {i} = 2) → cut x {0} = 2 * (K : ℝ) →
      (∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ S → (∀ i ∈ S, cut x {i} = 2) →
        2 * (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ cut x S) →
      ∃ R : Fin K → List (Fin (n + 1)), (∀ k, IsRoute E d C (R k)) ∧
        (∀ i : Fin (n + 1), i ≠ 0 → 2 * (((∑ k, (R k).count i : ℕ)) : ℝ) = cut x {i}) ∧
        x = chi R := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  intro K
  induction K with
  | zero =>
    intro x hint hnn hon hdeg hdep hcap
    have hz : ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i0, hi00, hi0⟩ := hcon
      have hi02 : cut x {i0} = 2 := (hdeg i0 hi00).resolve_left hi0
      classical
      set S := Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ cut x {i} = 2) with hS
      have h0S : (0 : Fin (n + 1)) ∉ S := by simp [hS]
      have hi0S : i0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi00, hi02⟩
      have hcS := hcap S h0S (fun i hi => (Finset.mem_filter.mp hi).2.2)
      have hcut0 : cut x S = 0 := by
        unfold cut
        apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro k hk
        rw [Finset.mem_compl] at hk
        have hik : i ≠ k := fun h => hk (h ▸ hi)
        apply le_antisymm _ (hnn _)
        by_cases hk0 : k = 0
        · subst hk0
          have := term_le_cut hnn (Ne.symm hik)
          rw [hdep, Sym2.eq_swap] at this
          simpa using this
        · have hkc : cut x {k} = 0 := by
            rcases hdeg k hk0 with h | h
            · exact h
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, h⟩) hk
          have := term_le_cut hnn (Ne.symm hik)
          rw [hkc, Sym2.eq_swap] at this
          exact this
      have hdem : 0 < demand d S :=
        lt_of_lt_of_le (by exact_mod_cast hd i0 hi00)
          (Finset.single_le_sum (f := fun i => (d i : ℝ)) (fun i _ => Nat.cast_nonneg _) hi0S)
      have hpos : 0 < roundedCapacityBound d (C : ℝ) S := Nat.ceil_pos.mpr (div_pos hdem hCpos)
      have : (1 : ℝ) ≤ (roundedCapacityBound d (C : ℝ) S : ℝ) := by exact_mod_cast hpos
      linarith
    have hx0 : ∀ e, x e = 0 := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      by_cases hab : a = b
      · subst hab
        exact hon _ (fun he => hE _ he (Sym2.mk_isDiag_iff.mpr rfl))
      · apply le_antisymm _ (hnn _)
        have := term_le_cut hnn hab
        by_cases ha : a = 0
        · subst ha; rw [hdep] at this; simpa using this
        · rw [hz a ha] at this; exact this
    refine ⟨fun k => k.elim0, fun k => k.elim0, fun i hi => ?_, ?_⟩
    · rw [hz i hi]; simp
    · funext e; simp [chi, hx0]
  | succ K ih =>
    intro x hint hnn hon hdeg hdep hcap
    obtain ⟨v, hv, hvpos⟩ : ∃ v ∈ ({0}ᶜ : Finset (Fin (n + 1))), 0 < x s(0, v) := by
      by_contra h
      push Not at h
      have := Finset.sum_nonpos h
      rw [← cut_singleton, hdep] at this
      push_cast at this
      linarith
    have hv0 : v ≠ 0 := by simpa using hv
    have hv1 : 1 ≤ x s(0, v) - ((0 : ℕ) : ℝ) := int_ge_one (hint _) 0 (by simpa using hvpos)
    have hb0 : ∀ e, (((pe ([v] ++ [0])).count e : ℕ) : ℝ) ≤ x e := by
      intro e
      show (((s(v, 0) :: []).count e : ℕ) : ℝ) ≤ x e
      rw [List.count_cons]
      by_cases h : s(v, 0) = e
      · subst h; rw [Sym2.eq_swap]; simp at hv1 ⊢; linarith
      · simp [h]; exact hnn e
    obtain ⟨q, hq, hq0, hqnd, hqb⟩ := find_route x hint hdeg (n + 1) [v] (List.cons_ne_nil _ _)
      (by simpa [eq_comm] using hv0) (List.nodup_singleton _) hb0 (by simp)
    set x' : Sym2 (Fin (n + 1)) → ℝ := fun e => x e - (inc q e : ℝ) with hx'
    have hqE : ∀ e ∈ edges q, e ∈ E := by
      intro e he
      by_contra hne
      have h1 : (1 : ℝ) ≤ (inc q e : ℝ) := by
        have : 0 < inc q e := List.count_pos_iff.mpr he
        exact_mod_cast this
      have := hqb e
      rw [hon e hne] at this
      linarith
    have hqd : ∀ e ∈ edges q, ¬ e.IsDiag := fun e he => hE e (hqE e he)
    have hdq : ∀ i, i ≠ 0 → ncr {i} (edges q) = 2 * ((q.count i : ℕ) : ℝ) :=
      fun i hi => deg_client q hq0 hqd i hi
    have hd0 : ncr {0} (edges q) = 2 := deg_depot q hq0 hqd
    have hcx : ∀ S, cut x' S = cut x S - ncr S (edges q) := fun S => cut_sub x _ S
    have hin : ∀ i ∈ q, cut x {i} = 2 ∧ q.count i = 1 := by
      intro i hi
      have hi0 : i ≠ 0 := fun h => hq0 (h ▸ hi)
      have hc1 := List.count_eq_one_of_mem hqnd hi
      refine ⟨?_, hc1⟩
      have hle : ncr {i} (edges q) ≤ cut x {i} := cut_mono hqb {i}
      rw [hdq i hi0, hc1] at hle
      rcases hdeg i hi0 with h | h
      · rw [h] at hle; norm_num at hle
      · exact h
    have hout : ∀ i, i ≠ 0 → i ∉ q → ncr {i} (edges q) = 0 := by
      intro i hi0 hi
      rw [hdq i hi0, List.count_eq_zero.mpr hi]
      simp
    have hint' : ∀ e, ∃ z : ℤ, x' e = z := by
      intro e
      obtain ⟨z, hz⟩ := hint e
      exact ⟨z - inc q e, by simp [hx', hz]⟩
    have hnn' : ∀ e, 0 ≤ x' e := fun e => by simp only [hx']; linarith [hqb e]
    have hon' : OnE E x' := by
      intro e he
      have h1 := hqb e
      rw [hon e he] at h1
      have h2 : (inc q e : ℝ) = 0 := le_antisymm h1 (Nat.cast_nonneg _)
      simp only [hx', hon e he, h2, sub_zero]
    have hdeg'' : ∀ i, i ≠ 0 → cut x' {i} = if i ∈ q then 0 else cut x {i} := by
      intro i hi0
      rw [hcx]
      split_ifs with h
      · rw [(hin i h).1, hdq i hi0, (hin i h).2]; norm_num
      · rw [hout i hi0 h, sub_zero]
    have hdeg' : ∀ i, i ≠ 0 → cut x' {i} = 0 ∨ cut x' {i} = 2 := by
      intro i hi0
      rw [hdeg'' i hi0]
      split_ifs
      · left; rfl
      · exact hdeg i hi0
    have hdep' : cut x' {0} = 2 * (K : ℝ) := by
      rw [hcx, hdep, hd0]; push_cast; ring
    have hcap' : ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ S → (∀ i ∈ S, cut x' {i} = 2) →
        2 * (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ cut x' S := by
      intro S h0S hS
      have hSq : ∀ i ∈ S, i ∉ q := by
        intro i hi hiq
        have := hS i hi
        rw [hdeg'' i (fun h => h0S (h ▸ hi)), if_pos hiq] at this
        norm_num at this
      have hn : ncr S (edges q) = 0 := by
        rw [edges_eq]
        apply ncr_pe_same
        left
        intro y hy hyS
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | hy | rfl
        · exact h0S hyS
        · exact hSq y hyS hy
        · exact h0S hyS
      rw [hcx, hn, sub_zero]
      apply hcap S h0S
      intro i hi
      have := hS i hi
      rwa [hdeg'' i (fun h => h0S (h ▸ hi)), if_neg (hSq i hi)] at this
    obtain ⟨R', hR', hcnt', hchi'⟩ := ih x' hint' hnn' hon' hdeg' hdep' hcap'
    have hload : load d q ≤ C := by
      classical
      set S := q.toFinset with hS
      have h0S : (0 : Fin (n + 1)) ∉ S := by simpa [hS] using hq0
      have hc := hcap S h0S (fun i hi => (hin i (List.mem_toFinset.mp hi)).1)
      have hx'S : cut x' S = 0 := by
        unfold cut
        apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro k hk
        have hiq := List.mem_toFinset.mp hi
        have hi0 : i ≠ 0 := fun h => hq0 (h ▸ hiq)
        have hik : i ≠ k := fun h => (Finset.mem_compl.mp hk) (h ▸ hi)
        apply le_antisymm _ (hnn' _)
        have := term_le_cut hnn' hik
        rwa [hdeg'' i hi0, if_pos hiq] at this
      have hnS : ncr S (edges q) = 2 := by
        obtain ⟨w, t, hwt⟩ := List.exists_cons_of_ne_nil hq
        have hwS : w ∈ S := by simp [hS, hwt]
        rw [edges_eq, hwt, List.cons_append, pe_cons_cons, ncr_cons,
          one_cross S 0 h0S t w (fun y hy => by rw [hS, hwt]; simpa using hy),
          if_pos (show crossP S 0 w from Or.inr ⟨hwS, h0S⟩)]
        norm_num
      have hxS : cut x S = 2 := by
        have := hcx S
        rw [hx'S, hnS] at this
        linarith
      rw [hxS] at hc
      have hceil : roundedCapacityBound d (C : ℝ) S ≤ 1 := by
        have : (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ 1 := by linarith
        exact_mod_cast this
      unfold roundedCapacityBound at hceil
      rw [Nat.ceil_le, div_le_iff₀ hCpos] at hceil
      unfold demand at hceil
      rw [hS, List.sum_toFinset _ hqnd] at hceil
      unfold load
      have : (((q.map d).sum : ℕ) : ℝ) ≤ C := by
        rw [Nat.cast_list_sum, List.map_map]
        have e : (Nat.cast ∘ d : Fin (n + 1) → ℝ) = fun i => (d i : ℝ) := rfl
        rw [e]
        rw [Nat.cast_one, one_mul] at hceil
        linarith [hceil]
      exact_mod_cast this
    refine ⟨Fin.cons q R', ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Fin.cons_zero]
        exact ⟨⟨hq, hq0, hqE⟩, hqnd, hload⟩
      · simp only [Fin.cons_succ]
        exact hR' k
    · intro i hi0
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have h' := hcnt' i hi0
      push_cast at h' ⊢
      rw [mul_add, h', hcx, hdq i hi0]
      ring
    · funext e
      simp only [chi, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have := congrFun hchi' e
      simp only [chi, hx'] at this
      linarith

lemma sum_count_mul (d : Fin (n + 1) → ℕ) (l : List (Fin (n + 1))) :
    ∑ i, d i * l.count i = (l.map d).sum := by
  classical
  rw [Finset.sum_list_map_count, ← Finset.sum_subset (Finset.subset_univ l.toFinset)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  · intro i _ hi
    rw [List.count_eq_zero.mpr (fun h => hi (List.mem_toFinset.mpr h)), mul_zero]

lemma route_edge_count {r : List (Fin (n + 1))} (h0 : (0 : Fin (n + 1)) ∉ r) (hnd : r.Nodup)
    {e : Sym2 (Fin (n + 1))} (he0 : (0 : Fin (n + 1)) ∉ e) {a : Fin (n + 1)} (ha : a ∈ e) :
    (edges r).count e ≤ r.count a := by
  by_cases har : a ∈ r
  · rw [List.count_eq_one_of_mem hnd har]
    obtain ⟨w, t, hwt⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem har)
    have hpn := (pe_nodup _ (nodup_snoc0 h0 hnd)).1
    rw [edges_eq, hwt, List.cons_append, pe_cons_cons, List.count_cons]
    have hne : ¬ (s(0, w) == e) = true := by
      intro h
      rw [beq_iff_eq] at h
      exact he0 (h ▸ Sym2.mem_mk_left 0 w)
    rw [if_neg hne, add_zero]
    rw [hwt, List.cons_append] at hpn
    exact List.nodup_iff_count_le_one.mp hpn e
  · rw [List.count_eq_zero.mpr har]
    apply le_of_eq
    apply List.count_eq_zero.mpr
    intro hm
    have := mem_pe _ e (by rw [← edges_eq]; exact hm) a ha
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
    rcases this with h | h | h
    · exact he0 (h ▸ ha)
    · exact har h
    · exact he0 (h ▸ ha)

lemma chi_props (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hC : 0 < C) (R : Fin K → List (Fin (n + 1)))
    (hR : IsCVRPSolution E d K C R) :
    InP3 E d K C (chi R) ∧ IsIntegerVec (chi R) := by
  classical
  obtain ⟨hroute, hcnt⟩ := hR
  have hd : ∀ k, ∀ e ∈ edges (R k), ¬ e.IsDiag := fun k e he => hE e ((hroute k).1.2.2 e he)
  have h0 : ∀ k, (0 : Fin (n + 1)) ∉ R k := fun k => (hroute k).1.2.1
  have hcutchi : ∀ S, cut (chi R) S = ∑ k, ncr S (edges (R k)) := by
    intro S
    unfold chi
    rw [cut_sum]
    rfl
  have hoff : ∀ k e, e ∉ E → inc (R k) e = 0 := fun k e he =>
    List.count_eq_zero.mpr (fun hm => he ((hroute k).1.2.2 e hm))
  set lam : List (Fin (n + 1)) →₀ ℝ := ∑ k, Finsupp.single (R k) (1 : ℝ) with hlam
  have hqr : ∀ k, IsQRoute E d C (R k) := by
    intro k
    refine ⟨(hroute k).1, ?_, (hroute k).2.2⟩
    intro j hj h
    have := ((hroute k).2.1.getElem_inj_iff).mp h
    omega
  have hsupp : ∀ r ∈ lam.support, ∃ k, R k = r := by
    intro r hr
    have := Finsupp.support_finsetSum hr
    simp only [Finset.mem_biUnion] at this
    obtain ⟨k, _, hk⟩ := this
    exact ⟨k, (Finset.mem_singleton.mp (Finsupp.support_single_subset hk)).symm⟩
  have hcols : IsColumns E d C lam := by
    intro r hr
    obtain ⟨k, rfl⟩ := hsupp r hr
    refine ⟨hqr k, ?_⟩
    rw [hlam, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun j _ => by
      rw [Finsupp.single_apply]
      split_ifs <;> norm_num
  have hcolsum : ∀ e, colSum lam e = chi R e := by
    intro e
    have : colSum lam e = lam.sum (fun r a => a * (inc r e : ℝ)) := rfl
    rw [this, hlam, ← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp [chi, Finsupp.sum_single_index]
  have hcolcount : colCount lam = K := by
    have : colCount lam = lam.sum (fun _ a => a) := rfl
    rw [this, hlam, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp [Finsupp.sum_single_index]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, lam, hcols, fun e _ => hcolsum e, hcolcount⟩, ?_⟩
  · intro e he
    simp [chi, hoff _ e he]
  · intro i hi
    rw [hcutchi]
    simp_rw [deg_client _ (h0 _) (hd _) i hi]
    rw [← Finset.mul_sum, ← Nat.cast_sum, hcnt i hi]
    norm_num
  · unfold Deg2
    rw [hcutchi]
    simp_rw [deg_depot _ (h0 _) (hd _)]
    simp
    ring
  · intro S h0S
    rw [hcutchi]
    set H := Finset.univ.filter (fun k => ∃ y ∈ R k, y ∈ S) with hH
    have hge : 2 * (H.card : ℝ) ≤ ∑ k, ncr S (edges (R k)) := by
      calc 2 * (H.card : ℝ) = ∑ k ∈ H, (2 : ℝ) := by simp; ring
        _ ≤ ∑ k ∈ H, ncr S (edges (R k)) := by
          apply Finset.sum_le_sum
          intro k hk
          obtain ⟨y, hy, hyS⟩ := (Finset.mem_filter.mp hk).2
          rw [edges_eq]
          refine (two_cross S (R k ++ [0]) 0).2 h0S ?_ ⟨y, by simp [hy], hyS⟩
          rw [getLast_walk]
          exact h0S
        _ ≤ ∑ k, ncr S (edges (R k)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => ncr_nonneg _ _)
    have hdem : ∑ i ∈ S, d i ≤ H.card * C := by
      calc ∑ i ∈ S, d i = ∑ i ∈ S, d i * ∑ k, (R k).count i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [hcnt i (fun h => h0S (h ▸ hi)), mul_one]
        _ = ∑ k, ∑ i ∈ S, d i * (R k).count i := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
        _ ≤ ∑ k ∈ H, C := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => ∃ y ∈ R k, y ∈ S)]
            have hz : ∑ k ∈ Finset.univ.filter (fun k => ¬ ∃ y ∈ R k, y ∈ S),
                ∑ i ∈ S, d i * (R k).count i = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              apply Finset.sum_eq_zero
              intro i hi
              have : (R k).count i = 0 :=
                List.count_eq_zero.mpr (fun hm => (Finset.mem_filter.mp hk).2 ⟨i, hm, hi⟩)
              rw [this, mul_zero]
            rw [hz, add_zero]
            apply Finset.sum_le_sum
            intro k _
            calc ∑ i ∈ S, d i * (R k).count i ≤ ∑ i, d i * (R k).count i :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                    (fun _ _ _ => Nat.zero_le _)
              _ = load d (R k) := sum_count_mul d (R k)
              _ ≤ C := (hroute k).2.2
        _ = H.card * C := by simp
    have hceil : roundedCapacityBound d (C : ℝ) S ≤ H.card := by
      unfold roundedCapacityBound demand
      rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hC : (0 : ℝ) < C)]
      exact_mod_cast hdem
    have : (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ H.card := by exact_mod_cast hceil
    linarith
  · intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he he0
    have ha0 : a ≠ 0 := fun h => he0 (h ▸ Sym2.mem_mk_left a b)
    unfold chi
    calc ∑ k, (inc (R k) s(a, b) : ℝ) ≤ ∑ k, (((R k).count a : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          exact_mod_cast route_edge_count (h0 k) (hroute k).2.1 he0 (Sym2.mem_mk_left a b)
      _ = 1 := by rw [← Nat.cast_sum, hcnt a ha0]; norm_num
  · intro e
    unfold chi
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · intro e
    exact ⟨∑ k, (inc (R k) e : ℤ), by simp [chi]⟩

lemma inc_off (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (r : List (Fin (n + 1))) (hr : IsQRoute E d C r) (e : Sym2 (Fin (n + 1))) (he : e ∉ E) :
    inc r e = 0 :=
  List.count_eq_zero.mpr (fun hm => he (hr.1.2.2 e hm))

lemma colSum_off (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (C : ℕ)
    (lam : List (Fin (n + 1)) →₀ ℝ) (hcol : IsColumns E d C lam) (e : Sym2 (Fin (n + 1)))
    (he : e ∉ E) : colSum lam e = 0 := by
  unfold colSum
  apply Finset.sum_eq_zero
  intro r hr
  rw [inc_off E d C r (hcol r hr).1 e he]
  simp

lemma colSum_cut (lam : List (Fin (n + 1)) →₀ ℝ) (S : Finset (Fin (n + 1))) :
    ∑ r ∈ lam.support, cutCoeff r S * lam r = cut (colSum lam) S := by
  have h := cut_sum lam.support (fun r e => lam r * (inc r e : ℝ)) S
  have h2 : colSum lam = fun e => ∑ r ∈ lam.support, lam r * (inc r e : ℝ) := rfl
  rw [h2, h]
  refine Finset.sum_congr rfl fun r _ => ?_
  show cutCoeff r S * lam r = cut (fun e => lam r * (inc r e : ℝ)) S
  rw [cut_mul, cutCoeff, mul_comm]

lemma part2 (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (x : Sym2 (Fin (n + 1)) → ℝ) :
    InP3 E d K C x ↔ ∃ lam : List (Fin (n + 1)) →₀ ℝ, IsDWMFeasible E d K C lam ∧ x = colSum lam := by
  constructor
  · rintro ⟨hon, h1, h2, h3, h4, h5, lam, hcol, hsum, hcnt⟩
    have hx : x = colSum lam := by
      funext e
      by_cases he : e ∈ E
      · exact (hsum e he).symm
      · rw [hon e he, colSum_off E d C lam hcol e he]
    subst hx
    refine ⟨lam, ⟨hcol, fun i hi => ?_, ?_, fun S hS => ?_, fun e he he0 => ?_⟩, rfl⟩
    · rw [colSum_cut]; exact h1 i hi
    · rw [colSum_cut]; exact h2
    · rw [colSum_cut]; exact h3 S hS
    · have := h4 e he he0
      unfold colSum at this
      simpa [mul_comm] using this
  · rintro ⟨lam, ⟨hcol, d1, d2, d3, d4⟩, rfl⟩
    refine ⟨fun e he => colSum_off E d C lam hcol e he, fun i hi => ?_, ?_, fun S hS => ?_,
      fun e he he0 => ?_, fun e => ?_, lam, hcol, fun e _ => rfl, ?_⟩
    · rw [← colSum_cut]; exact d1 i hi
    · unfold Deg2; rw [← colSum_cut]; exact d2
    · rw [← colSum_cut]; exact d3 S hS
    · have := d4 e he he0
      unfold colSum
      simpa [mul_comm] using this
    · unfold colSum
      exact Finset.sum_nonneg fun r hr => mul_nonneg (hcol r hr).2 (Nat.cast_nonneg _)
    · have h2c : ∀ r ∈ lam.support, cutCoeff r {0} = 2 := by
        intro r hr
        have hq := (hcol r hr).1
        exact deg_depot r hq.1.2.1 (fun e he => hE e (hq.1.2.2 e he))
      have hs : ∑ r ∈ lam.support, cutCoeff r {0} * lam r = ∑ r ∈ lam.support, 2 * lam r :=
        Finset.sum_congr rfl (fun r hr => by rw [h2c r hr])
      rw [hs, ← Finset.mul_sum] at d2
      unfold colCount
      linarith

lemma dwm_obj (E : Finset (Sym2 (Fin (n + 1)))) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (lam : List (Fin (n + 1)) →₀ ℝ) :
    dwmObjective E ℓ lam = ∑ e ∈ E, ℓ e * colSum lam e := by
  unfold dwmObjective colSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

lemma cost_eq (E : Finset (Sym2 (Fin (n + 1)))) (ℓ : Sym2 (Fin (n + 1)) → ℝ) (K : ℕ)
    (R : Fin K → List (Fin (n + 1))) (hR : ∀ k, ∀ e ∈ edges (R k), e ∈ E) :
    ∑ e ∈ E, ℓ e * chi R e = cost ℓ R := by
  classical
  unfold chi cost
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_list_map_count]
  have hsub : (edges (R k)).toFinset ⊆ E := fun e he => hR k e (List.mem_toFinset.mp he)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [nsmul_eq_mul, inc]
    ring
  · intro e _ he
    rw [inc, List.count_eq_zero.mpr (fun h => he (List.mem_toFinset.mpr h))]
    simp

end RBCP52

open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation in
theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ i : Fin (n + 1), i ≠ 0 → 0 < d i) (hK : 0 < K) (hC : 0 < C) :
    -- (i) the integer points of P₃ are exactly the edge vectors of the CVRP solutions
    (∀ x : Sym2 (Fin (n + 1)) → ℝ, (InP3 E d K C x ∧ IsIntegerVec x) ↔
      ∃ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R ∧ x = chi R) ∧
    -- (ii) P₃ is the image x = Qλ of the DWM-feasible λ, and (7) is ℓᵀ(Qλ)
    (∀ x : Sym2 (Fin (n + 1)) → ℝ, InP3 E d K C x ↔
      ∃ lam : List (Fin (n + 1)) →₀ ℝ, IsDWMFeasible E d K C lam ∧ x = colSum lam) ∧
    (∀ lam : List (Fin (n + 1)) →₀ ℝ, IsColumns E d C lam →
      dwmObjective E ℓ lam = ∑ e ∈ E, ℓ e * colSum lam e) ∧
    -- (iii) L₁ ≤ L₃, L₂ ≤ L₃ and L₃ ≤ OPT, in lower-bound form
    (∀ L : ℝ, (∀ x, InP1 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) ∧
    (∀ L : ℝ, (∀ x, InP2 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) ∧
    (∀ L : ℝ, (∀ x, InP3 E d K C x → L ≤ ∑ e ∈ E, ℓ e * x e) →
      ∀ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R → L ≤ cost ℓ R) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun x => RBCP52.part2 E d K C hE x,
    fun lam _ => RBCP52.dwm_obj E ℓ lam, ?_, ?_, ?_⟩
  · rintro ⟨⟨hon, h1, h2, h3, _, h5, _⟩, hint⟩
    obtain ⟨R, hR, hc, hx⟩ := RBCP52.decomp E d C hE hd hC K x hint h5 hon
      (fun i hi => Or.inr (h1 i hi)) h2 (fun S hS _ => h3 S hS)
    refine ⟨R, ⟨hR, fun i hi => ?_⟩, hx⟩
    have h := hc i hi
    rw [h1 i hi] at h
    have h' : ((∑ k, (R k).count i : ℕ) : ℝ) = 1 := by linarith
    exact_mod_cast h'
  · rintro ⟨R, hR, rfl⟩
    exact RBCP52.chi_props E d K C hE hC R hR
  · intro L hL x hx
    obtain ⟨hon, h1, h2, h3, h4, h5, _⟩ := hx
    exact hL x ⟨hon, h1, h2, h3, h4, h5⟩
  · intro L hL x hx
    obtain ⟨hon, h1, _, _, _, h5, hlam⟩ := hx
    exact hL x ⟨hon, h5, h1, hlam⟩
  · intro L hL R hR
    have h := hL (chi R) (RBCP52.chi_props E d K C hE hC R hR).1
    rwa [RBCP52.cost_eq E ℓ K R (fun k => (hR.1 k).1.2.2)] at h
