-- Prove2me | solution 1 for ProphetMatchingEFGT.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:13:57.500505+00:00
-- url     : https://prove2.me/submissions/4b9e2eb9-d5f6-4504-950b-54fa1350586d

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

namespace Aux_ProphetMatchingEFGT_eq_15

open ProphetMatchingEFGT


/-! ### Activation patterns: expectation lemmas -/

section BernSec

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem bern_nil (f : List (Edge G × Bool) → ℝ) : bern ([] : List (Edge G × ℝ)) f = f [] := by
  rw [bern]

theorem bern_cons (e : Edge G) (a : ℝ) (ps : List (Edge G × ℝ)) (f : List (Edge G × Bool) → ℝ) :
    bern ((e, a) :: ps) f = a * bern ps (fun l => f ((e, true) :: l)) +
      (1 - a) * bern ps (fun l => f ((e, false) :: l)) := by
  rw [bern]

theorem bern_add : ∀ (ps : List (Edge G × ℝ)) (f g : List (Edge G × Bool) → ℝ),
    bern ps (fun l => f l + g l) = bern ps f + bern ps g
  | [], f, g => by rw [bern_nil, bern_nil, bern_nil]
  | (e, a) :: ps, f, g => by
    rw [bern_cons, bern_cons, bern_cons,
      bern_add ps (fun l => f ((e, true) :: l)) (fun l => g ((e, true) :: l)),
      bern_add ps (fun l => f ((e, false) :: l)) (fun l => g ((e, false) :: l))]
    ring

theorem bern_smul : ∀ (ps : List (Edge G × ℝ)) (c : ℝ) (f : List (Edge G × Bool) → ℝ),
    bern ps (fun l => c * f l) = c * bern ps f
  | [], c, f => by rw [bern_nil, bern_nil]
  | (e, a) :: ps, c, f => by
    rw [bern_cons, bern_cons, bern_smul ps c (fun l => f ((e, true) :: l)),
      bern_smul ps c (fun l => f ((e, false) :: l))]
    ring

theorem bern_const : ∀ (ps : List (Edge G × ℝ)) (c : ℝ), bern ps (fun _ => c) = c
  | [], c => by rw [bern_nil]
  | (e, a) :: ps, c => by
    rw [bern_cons, bern_const ps c]
    ring

theorem bern_sub (ps : List (Edge G × ℝ)) (f g : List (Edge G × Bool) → ℝ) :
    bern ps (fun l => f l - g l) = bern ps f - bern ps g := by
  have h1 := bern_add ps f (fun l => (-1) * g l)
  have h2 := bern_smul ps (-1) g
  have e : (fun l => f l - g l) = (fun l => f l + (-1) * g l) := by
    funext l
    ring
  rw [e, h1, h2]
  ring

theorem bern_congr : ∀ (ps : List (Edge G × ℝ)) (f g : List (Edge G × Bool) → ℝ),
    (∀ l, l.map Prod.fst = ps.map Prod.fst → f l = g l) → bern ps f = bern ps g
  | [], f, g, h => by
    rw [bern_nil, bern_nil]
    exact h [] rfl
  | (e, a) :: ps, f, g, h => by
    rw [bern_cons, bern_cons,
      bern_congr ps (fun l => f ((e, true) :: l)) (fun l => g ((e, true) :: l))
        (fun l hl => h _ (by simp [hl])),
      bern_congr ps (fun l => f ((e, false) :: l)) (fun l => g ((e, false) :: l))
        (fun l hl => h _ (by simp [hl]))]

theorem bern_mono : ∀ (ps : List (Edge G × ℝ)), (∀ q ∈ ps, 0 ≤ q.2 ∧ q.2 ≤ 1) →
    ∀ (f g : List (Edge G × Bool) → ℝ),
    (∀ l, l.map Prod.fst = ps.map Prod.fst → f l ≤ g l) → bern ps f ≤ bern ps g
  | [], _, f, g, h => by
    rw [bern_nil, bern_nil]
    exact h [] rfl
  | (e, a) :: ps, hps, f, g, h => by
    rw [bern_cons, bern_cons]
    have ha := hps (e, a) (by simp)
    have hps' : ∀ q ∈ ps, 0 ≤ q.2 ∧ q.2 ≤ 1 := fun q hq => hps q (by simp [hq])
    have h1 := bern_mono ps hps' (fun l => f ((e, true) :: l)) (fun l => g ((e, true) :: l))
      (fun l hl => h _ (by simp [hl]))
    have h2 := bern_mono ps hps' (fun l => f ((e, false) :: l)) (fun l => g ((e, false) :: l))
      (fun l hl => h _ (by simp [hl]))
    have h3 : 0 ≤ 1 - a := by linarith [ha.2]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha.1, mul_le_mul_of_nonneg_left h2 h3]

theorem bern_append : ∀ (ps1 ps2 : List (Edge G × ℝ)) (F : List (Edge G × Bool) → ℝ),
    bern (ps1 ++ ps2) F = bern ps1 (fun l1 => bern ps2 (fun l2 => F (l1 ++ l2)))
  | [], ps2, F => by
    rw [List.nil_append, bern_nil]
    rfl
  | (e, a) :: ps1, ps2, F => by
    rw [List.cons_append, bern_cons, bern_cons, bern_append ps1 ps2, bern_append ps1 ps2]
    rfl

theorem bern_sum {ι : Type*} (s : Finset ι) (ps : List (Edge G × ℝ))
    (F : ι → List (Edge G × Bool) → ℝ) :
    bern ps (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, bern ps (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact bern_const ps 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [bern_add ps (F a) (fun l => ∑ i ∈ s, F i l), ih]

end BernSec


/-! ### Greedy and the activation probabilities -/

section GreedySec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def ind (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by
  unfold ind
  rw [if_pos h]

theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind
  rw [if_neg h]

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  by_cases h : P
  · rw [ind_pos h]; norm_num
  · rw [ind_neg h]

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]
  · rw [ind_neg h]; norm_num

theorem prob_eq_ind (ps : List (Edge G × ℝ)) (P : List (Edge G × Bool) → Prop) :
    prob ps P = bern ps (fun l => ind (P l)) := rfl

theorem greedy_nil : greedy ([] : List (Edge G × Bool)) = ∅ := rfl

theorem greedy_snoc (l : List (Edge G × Bool)) (q : Edge G × Bool) :
    greedy (l ++ [q]) =
      if q.2 = true ∧ endsFree (greedy l) q.1 then insert q.1 (greedy l) else greedy l := by
  unfold greedy
  rw [List.foldl_append]
  rfl

theorem greedy_sub (l : List (Edge G × Bool)) : ∀ f ∈ greedy l, f ∈ l.map Prod.fst := by
  induction l using List.reverseRec with
  | nil =>
    intro f hf
    rw [greedy_nil] at hf
    simp at hf
  | append_singleton l q ih =>
    intro f hf
    rw [greedy_snoc] at hf
    rw [List.map_append, List.mem_append]
    split_ifs at hf
    · rcases Finset.mem_insert.mp hf with h | h
      · right
        rw [h]
        simp
      · left
        exact ih f h
    · left
      exact ih f hf

theorem greedy_notin (l1 : List (Edge G × Bool)) (f : Edge G) :
    ∀ l2 : List (Edge G × Bool), f ∉ l2.map Prod.fst → (f ∈ greedy (l1 ++ l2) ↔ f ∈ greedy l1) := by
  intro l2
  induction l2 using List.reverseRec with
  | nil =>
    intro _
    rw [List.append_nil]
  | append_singleton l2 q ih =>
    intro h
    have h' : f ∉ l2.map Prod.fst := by
      intro hh
      apply h
      rw [List.map_append, List.mem_append]
      left
      exact hh
    have hq : f ≠ q.1 := by
      intro hh
      apply h
      rw [List.map_append, List.mem_append]
      right
      rw [hh]
      simp
    rw [← List.append_assoc, greedy_snoc]
    split_ifs
    · rw [Finset.mem_insert, ih h']
      constructor
      · rintro (hh | hh)
        · exact absurd hh hq
        · exact hh
      · intro hh
        right
        exact hh
    · exact ih h'

theorem greedy_at (l1 l2 : List (Edge G × Bool)) (f : Edge G) (b : Bool)
    (h1 : f ∉ l1.map Prod.fst) (h2 : f ∉ l2.map Prod.fst) :
    f ∈ greedy (l1 ++ (f, b) :: l2) ↔ (b = true ∧ endsFree (greedy l1) f) := by
  have e : l1 ++ (f, b) :: l2 = (l1 ++ [(f, b)]) ++ l2 := by simp
  rw [e, greedy_notin _ f l2 h2, greedy_snoc]
  have hn : f ∉ greedy l1 := fun hh => h1 (greedy_sub l1 f hh)
  split_ifs with hc
  · constructor
    · intro _
      exact hc
    · intro _
      exact Finset.mem_insert_self _ _
  · constructor
    · intro hh
      exact absurd hh hn
    · intro hh
      exact absurd hh hc

theorem actProbs_snoc (c : ℝ) (x : Edge G → ℝ) (l : List (Edge G)) (e : Edge G) :
    actProbs c x (l ++ [e]) = actProbs c x l ++ [(e, c / unmatchedProb (actProbs c x l) e * x e)] := by
  unfold actProbs
  rw [List.foldl_append]
  rfl

theorem actProbs_fst (c : ℝ) (x : Edge G → ℝ) (l : List (Edge G)) :
    (actProbs c x l).map Prod.fst = l := by
  induction l using List.reverseRec with
  | nil => rfl
  | append_singleton l e ih =>
    rw [actProbs_snoc, List.map_append, ih]
    rfl

theorem actProbs_append (c : ℝ) (x : Edge G → ℝ) (l : List (Edge G)) :
    ∀ l' : List (Edge G), ∃ R : List (Edge G × ℝ), actProbs c x (l ++ l') = actProbs c x l ++ R ∧
      R.map Prod.fst = l' := by
  intro l'
  induction l' using List.reverseRec with
  | nil => exact ⟨[], by rw [List.append_nil, List.append_nil], rfl⟩
  | append_singleton l' e ih =>
    obtain ⟨R, h1, h2⟩ := ih
    refine ⟨R ++ [(e, c / unmatchedProb (actProbs c x (l ++ l')) e * x e)], ?_, ?_⟩
    · rw [← List.append_assoc l l' [e], actProbs_snoc, h1, List.append_assoc]
    · rw [List.map_append, h2]
      rfl

theorem x_le_one [DecidableRel G.Adj] (x : Edge G → ℝ) (hx : InFM G x) (f : Edge G) : x f ≤ 1 := by
  obtain ⟨z, hz⟩ := f
  induction z using Sym2.ind with
  | _ a b =>
    have h := hx.2 a
    have hmem : (⟨s(a, b), hz⟩ : Edge G) ∈ Finset.univ.filter (fun e : Edge G => a ∈ (e : Sym2 V)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Sym2.mem_mk_left a b⟩
    have := Finset.single_le_sum (f := x) (fun e _ => hx.1 e) hmem
    linarith

theorem wd_prefix (c : ℝ) (x : Edge G → ℝ) (l : List (Edge G)) (e : Edge G)
    (h : WellDefinedOn c x (l ++ [e])) : WellDefinedOn c x l ∧ c ≤ unmatchedAt c x l e := by
  constructor
  · intro k
    have hk : (k : ℕ) < (l ++ [e]).length := by
      rw [List.length_append, List.length_singleton]
      have := k.isLt
      omega
    have h0 : c ≤ unmatchedAt c x ((l ++ [e]).take (k : ℕ)) ((l ++ [e]).get ⟨k, hk⟩) := h ⟨k, hk⟩
    have e1 : (l ++ [e]).take (k : ℕ) = l.take k := List.take_append_of_le_length (by omega)
    have e2 : (l ++ [e]).get ⟨k, hk⟩ = l.get k := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact List.getElem_append_left k.isLt
    rw [e1, e2] at h0
    exact h0
  · have hk : l.length < (l ++ [e]).length := by simp
    have h0 : c ≤ unmatchedAt c x ((l ++ [e]).take l.length) ((l ++ [e]).get ⟨l.length, hk⟩) :=
      h ⟨l.length, hk⟩
    have e1 : (l ++ [e]).take l.length = l := by simp
    have e2 : (l ++ [e]).get ⟨l.length, hk⟩ = e := by simp
    rw [e1, e2] at h0
    exact h0

theorem actProbs_bounds [DecidableRel G.Adj] (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) :
    ∀ es : List (Edge G), WellDefinedOn c x es → ∀ q ∈ actProbs c x es, 0 ≤ q.2 ∧ q.2 ≤ 1 := by
  intro es
  induction es using List.reverseRec with
  | nil =>
    intro _ q hq
    simp [actProbs] at hq
  | append_singleton l e ih =>
    intro hwd q hq
    obtain ⟨hwl, hce⟩ := wd_prefix c x l e hwd
    rw [actProbs_snoc, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ih hwl q hq
    · simp only [List.mem_singleton] at hq
      rw [hq]
      have hx0 := hx.1 e
      have hx1 := x_le_one x hx e
      show 0 ≤ c / unmatchedProb (actProbs c x l) e * x e ∧
        c / unmatchedProb (actProbs c x l) e * x e ≤ 1
      unfold unmatchedAt at hce
      by_cases hc0 : c = 0
      · rw [hc0]
        simp
      · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
        have hU : 0 < unmatchedProb (actProbs c x l) e := lt_of_lt_of_le hcpos hce
        have h1 : c / unmatchedProb (actProbs c x l) e ≤ 1 := by
          rw [div_le_one hU]
          exact hce
        have h2 : 0 ≤ c / unmatchedProb (actProbs c x l) e := div_nonneg hc hU.le
        constructor
        · exact mul_nonneg h2 hx0
        · nlinarith

theorem prob_mem_greedy (c : ℝ) (x : Edge G → ℝ) (pre post : List (Edge G)) (f : Edge G)
    (hnd : (pre ++ f :: post).Nodup) :
    prob (actProbs c x (pre ++ f :: post)) (fun l => f ∈ greedy l) =
      (c / unmatchedProb (actProbs c x pre) f * x f) * unmatchedProb (actProbs c x pre) f := by
  have hnd' := List.nodup_append.mp hnd
  have hfpre : f ∉ pre := fun h => hnd'.2.2 f h f (by simp) rfl
  have hfpost : f ∉ post := (List.nodup_cons.mp hnd'.2.1).1
  have e1 : pre ++ f :: post = (pre ++ [f]) ++ post := by simp
  obtain ⟨R, hR1, hR2⟩ := actProbs_append c x (pre ++ [f]) post
  obtain ⟨a, ha⟩ : ∃ a, a = c / unmatchedProb (actProbs c x pre) f * x f := ⟨_, rfl⟩
  have hps : actProbs c x (pre ++ f :: post) = actProbs c x pre ++ (f, a) :: R := by
    rw [e1, hR1, actProbs_snoc, ← ha]
    simp
  rw [← ha]
  unfold unmatchedProb
  rw [prob_eq_ind, prob_eq_ind, hps, bern_append, ← bern_smul]
  apply bern_congr
  intro l1 hl1
  rw [actProbs_fst] at hl1
  rw [bern_cons]
  have hT : bern R (fun l => ind (f ∈ greedy (l1 ++ (f, true) :: l))) =
      ind (endsFree (greedy l1) f) := by
    rw [← bern_const R (ind (endsFree (greedy l1) f))]
    apply bern_congr
    intro l hl
    rw [hR2] at hl
    have := greedy_at l1 l f true (by rw [hl1]; exact hfpre) (by rw [hl]; exact hfpost)
    by_cases hE : endsFree (greedy l1) f
    · rw [ind_pos (this.mpr ⟨rfl, hE⟩), ind_pos hE]
    · rw [ind_neg (fun h => hE (this.mp h).2), ind_neg hE]
  have hF : bern R (fun l => ind (f ∈ greedy (l1 ++ (f, false) :: l))) = 0 := by
    rw [← bern_const R (0 : ℝ)]
    apply bern_congr
    intro l hl
    rw [hR2] at hl
    have := greedy_at l1 l f false (by rw [hl1]; exact hfpre) (by rw [hl]; exact hfpost)
    rw [ind_neg (fun h => by simpa using (this.mp h).1)]
  rw [hT, hF]
  ring

theorem prob_mem_greedy_le (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx0 : ∀ f, 0 ≤ x f)
    (es : List (Edge G)) (hnd : es.Nodup) (f : Edge G) (hf : f ∈ es) :
    prob (actProbs c x es) (fun l => f ∈ greedy l) ≤ c * x f := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hf
  rw [prob_mem_greedy c x pre post f hnd]
  by_cases hU : unmatchedProb (actProbs c x pre) f = 0
  · rw [hU]
    simp only [mul_zero]
    exact mul_nonneg hc (hx0 f)
  · have e : c / unmatchedProb (actProbs c x pre) f * x f * unmatchedProb (actProbs c x pre) f =
        c * x f * (unmatchedProb (actProbs c x pre) f / unmatchedProb (actProbs c x pre) f) := by
      ring
    rw [e, div_self hU, mul_one] <;> exact le_refl _

theorem prob_mem_greedy_eq (c : ℝ) (x : Edge G → ℝ) (pre post : List (Edge G)) (f : Edge G)
    (hnd : (pre ++ f :: post).Nodup) (hU : unmatchedProb (actProbs c x pre) f ≠ 0) :
    prob (actProbs c x (pre ++ f :: post)) (fun l => f ∈ greedy l) = c * x f := by
  rw [prob_mem_greedy c x pre post f hnd]
  have e : c / unmatchedProb (actProbs c x pre) f * x f * unmatchedProb (actProbs c x pre) f =
      c * x f * (unmatchedProb (actProbs c x pre) f / unmatchedProb (actProbs c x pre) f) := by
    ring
  rw [e, div_self hU, mul_one]

end GreedySec


/-! ### Marginal sums and matching probabilities -/

section XPairSec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem xPair_eq (x : Edge G → ℝ) (es : List (Edge G)) (a s : V) :
    xPair x es a s = ∑ f ∈ es.toFinset.filter (fun f : Edge G => (f : Sym2 V) = s(a, s)), x f := by
  unfold xPair
  by_cases h : G.Adj a s
  · rw [dif_pos h]
    by_cases hm : (⟨s(a, s), G.mem_edgeSet.2 h⟩ : Edge G) ∈ es
    · rw [if_pos hm]
      have hset : es.toFinset.filter (fun f : Edge G => (f : Sym2 V) = s(a, s)) =
          {(⟨s(a, s), G.mem_edgeSet.2 h⟩ : Edge G)} := by
        ext f
        simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hf⟩
          exact Subtype.ext hf
        · rintro rfl
          exact ⟨hm, rfl⟩
      rw [hset, Finset.sum_singleton]
    · rw [if_neg hm]
      symm
      apply Finset.sum_eq_zero
      intro f hf
      rw [Finset.mem_filter, List.mem_toFinset] at hf
      exfalso
      apply hm
      have : f = ⟨s(a, s), G.mem_edgeSet.2 h⟩ := Subtype.ext hf.2
      rw [← this]
      exact hf.1
  · rw [dif_neg h]
    symm
    apply Finset.sum_eq_zero
    intro f hf
    rw [Finset.mem_filter] at hf
    exfalso
    apply h
    have h2 := f.2
    rw [hf.2] at h2
    exact (SimpleGraph.mem_edgeSet G).mp h2

theorem xPair_symm (x : Edge G → ℝ) (es : List (Edge G)) (a s : V) :
    xPair x es s a = xPair x es a s := by
  rw [xPair_eq, xPair_eq]
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro f _
    rw [Sym2.eq_swap]
  · intro _ _
    rfl

theorem xsum_eq (x : Edge G → ℝ) (es : List (Edge G)) (e : Edge G) (he : e ∉ es) (a b : V)
    (hab : (e : Sym2 V) = s(a, b)) :
    ∑ s ∈ Finset.univ.filter (fun s => s ≠ a ∧ s ≠ b), xPair x es a s =
      ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)), x f := by
  rw [Finset.sum_congr rfl (fun s _ => xPair_eq x es a s)]
  rw [Finset.sum_congr rfl (fun s _ =>
    Finset.sum_filter (s := es.toFinset) (fun f : Edge G => (f : Sym2 V) = s(a, s)) (fun f => x f))]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  rw [List.mem_toFinset] at hf
  by_cases hu : a ∈ (f : Sym2 V)
  · rw [if_pos hu]
    have hspec := Sym2.other_spec hu
    have hiff : ∀ s, ((f : Sym2 V) = s(a, s) ↔ s = Sym2.Mem.other hu) := by
      intro s
      constructor
      · intro h
        exact (Sym2.congr_right.mp (hspec.trans h)).symm
      · intro h
        rw [h]
        exact hspec.symm
    have hmem : Sym2.Mem.other hu ∈ Finset.univ.filter (fun s => s ≠ a ∧ s ≠ b) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro h
        have hd := SimpleGraph.not_isDiag_of_mem_edgeSet G f.2
        apply hd
        rw [← hspec, h, Sym2.mk_isDiag_iff]
      · intro h
        apply he
        have : f = e := by
          apply Subtype.ext
          rw [hab, ← hspec, h]
        rw [← this]
        exact hf
    have hc : ∑ s ∈ Finset.univ.filter (fun s => s ≠ a ∧ s ≠ b),
        (if (f : Sym2 V) = s(a, s) then x f else 0) =
        ∑ s ∈ Finset.univ.filter (fun s => s ≠ a ∧ s ≠ b),
          (if s = Sym2.Mem.other hu then x f else 0) :=
      Finset.sum_congr rfl (fun s _ => by
        by_cases h : s = Sym2.Mem.other hu
        · rw [if_pos ((hiff s).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((hiff s).mp h')), if_neg h])
    rw [hc, Finset.sum_ite_eq' _ _ (fun _ => x f), if_pos hmem]
  · rw [if_neg hu]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    intro h
    apply hu
    rw [h]
    exact Sym2.mem_mk_left a s

theorem xsum_le_one [DecidableRel G.Adj] (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (a : V) :
    ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)), x f ≤ 1 := by
  have h := hx.2 a
  have hsub : es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)) ⊆
      Finset.univ.filter (fun e : Edge G => a ∈ (e : Sym2 V)) := by
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨Finset.mem_univ _, hf.2⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hx.1 f)
  linarith

theorem matched_le [DecidableRel G.Adj] (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (a : V) :
    prob (actProbs c x es) (fun l => matchedIn l a) ≤
      c * ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)), x f := by
  have hps := actProbs_bounds c hc x hx es hwd
  rw [prob_eq_ind]
  have h1 : bern (actProbs c x es) (fun l => ind (matchedIn l a)) ≤
      bern (actProbs c x es) (fun l => ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)),
        ind (f ∈ greedy l)) := by
    apply bern_mono _ hps
    intro l hl
    rw [actProbs_fst] at hl
    by_cases hm : matchedIn l a
    · rw [ind_pos hm]
      obtain ⟨f, hf1, hf2⟩ := hm
      have hfe : f ∈ es := by
        rw [← hl]
        exact greedy_sub l f hf1
      have hmem : f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)) := by
        rw [Finset.mem_filter, List.mem_toFinset]
        exact ⟨hfe, hf2⟩
      have := Finset.single_le_sum (f := fun f => ind (f ∈ greedy l)) (fun f _ => ind_nonneg _) hmem
      beta_reduce at this
      rw [ind_pos hf1] at this
      exact this
    · rw [ind_neg hm]
      exact Finset.sum_nonneg (fun f _ => ind_nonneg _)
  rw [bern_sum] at h1
  have h2 : ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)),
      bern (actProbs c x es) (fun l => ind (f ∈ greedy l)) ≤
      ∑ f ∈ es.toFinset.filter (fun f : Edge G => a ∈ (f : Sym2 V)), c * x f := by
    apply Finset.sum_le_sum
    intro f hf
    rw [Finset.mem_filter, List.mem_toFinset] at hf
    rw [← prob_eq_ind]
    exact prob_mem_greedy_le c hc x hx.1 es hnd f hf.1
  rw [← Finset.mul_sum] at h2
  linarith

theorem unmatched_eq (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G)) (e : Edge G) (u v : V)
    (huv : (e : Sym2 V) = s(u, v)) :
    unmatchedAt c x es e = 1 - prob (actProbs c x es) (fun l => matchedIn l u)
        - prob (actProbs c x es) (fun l => matchedIn l v)
        + prob (actProbs c x es) (fun l => matchedIn l u ∧ matchedIn l v) := by
  unfold unmatchedAt unmatchedProb
  rw [prob_eq_ind, prob_eq_ind, prob_eq_ind, prob_eq_ind]
  have hpt : ∀ l : List (Edge G × Bool), ind (endsFree (greedy l) e) =
      1 - ind (matchedIn l u) - ind (matchedIn l v) + ind (matchedIn l u ∧ matchedIn l v) := by
    intro l
    have hiff : endsFree (greedy l) e ↔ ¬ matchedIn l u ∧ ¬ matchedIn l v := by
      unfold endsFree matchedIn
      rw [huv]
      constructor
      · intro h
        constructor
        · rintro ⟨f, hf, hu⟩
          exact h f hf u (Sym2.mem_mk_left u v) hu
        · rintro ⟨f, hf, hv⟩
          exact h f hf v (Sym2.mem_mk_right u v) hv
      · rintro ⟨h1, h2⟩ f hf w hw hwf
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact h1 ⟨f, hf, hwf⟩
        · exact h2 ⟨f, hf, hwf⟩
    by_cases hu : matchedIn l u <;> by_cases hv : matchedIn l v
    · have h1 : ¬ endsFree (greedy l) e := fun h => (hiff.mp h).1 hu
      have h2 : matchedIn l u ∧ matchedIn l v := ⟨hu, hv⟩
      rw [ind_neg h1, ind_pos hu, ind_pos hv, ind_pos h2]
      ring
    · have h1 : ¬ endsFree (greedy l) e := fun h => (hiff.mp h).1 hu
      have h2 : ¬ (matchedIn l u ∧ matchedIn l v) := fun h => hv h.2
      rw [ind_neg h1, ind_pos hu, ind_neg hv, ind_neg h2]
      ring
    · have h1 : ¬ endsFree (greedy l) e := fun h => (hiff.mp h).2 hv
      have h2 : ¬ (matchedIn l u ∧ matchedIn l v) := fun h => hu h.1
      rw [ind_neg h1, ind_neg hu, ind_pos hv, ind_neg h2]
      ring
    · have h1 : endsFree (greedy l) e := hiff.mpr ⟨hu, hv⟩
      have h2 : ¬ (matchedIn l u ∧ matchedIn l v) := fun h => hu h.1
      rw [ind_pos h1, ind_neg hu, ind_neg hv, ind_neg h2]
      ring
  rw [bern_congr _ _ _ (fun l _ => hpt l)]
  rw [bern_add, bern_sub, bern_sub, bern_const]

end XPairSec


/-! ### The candidate sampler has the law of the activation pattern -/

section MixSec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem bern_mix (u : V) : ∀ (ps : List (Edge G × ℝ)) (F : List (Edge G × Bool) → ℝ),
    bern ps (fun l => bern ps (fun l' => F (mixAt u l l'))) = bern ps F
  | [], F => by
    rw [bern_nil, bern_nil, bern_nil]
    rfl
  | (e, a) :: ps, F => by
    by_cases hu : u ∈ (e : Sym2 V)
    · have hm : ∀ (b b' : Bool) (l l' : List (Edge G × Bool)),
          mixAt u ((e, b) :: l) ((e, b') :: l') = (e, b) :: mixAt u l l' := by
        intro b b' l l'
        simp [mixAt, hu]
      have hin : ∀ (b : Bool) (l : List (Edge G × Bool)),
          bern ((e, a) :: ps) (fun l' => F (mixAt u ((e, b) :: l) l')) =
            bern ps (fun l'' => F ((e, b) :: mixAt u l l'')) := by
        intro b l
        rw [bern_cons]
        simp only [hm]
        ring
      rw [bern_cons, bern_cons]
      simp only [hin]
      rw [bern_mix u ps (fun m => F ((e, true) :: m)), bern_mix u ps (fun m => F ((e, false) :: m))]
    · have hm : ∀ (b b' : Bool) (l l' : List (Edge G × Bool)),
          mixAt u ((e, b) :: l) ((e, b') :: l') = (e, b') :: mixAt u l l' := by
        intro b b' l l'
        simp [mixAt, hu]
      have hin : ∀ (b : Bool) (l : List (Edge G × Bool)),
          bern ((e, a) :: ps) (fun l' => F (mixAt u ((e, b) :: l) l')) =
            a * bern ps (fun l'' => F ((e, true) :: mixAt u l l'')) +
              (1 - a) * bern ps (fun l'' => F ((e, false) :: mixAt u l l'')) := by
        intro b l
        rw [bern_cons]
        simp only [hm]
      rw [bern_cons, bern_cons]
      simp only [hin]
      rw [bern_add, bern_smul, bern_smul,
        bern_mix u ps (fun m => F ((e, true) :: m)), bern_mix u ps (fun m => F ((e, false) :: m))]
      ring

theorem prob2_mix (u : V) (ps : List (Edge G × ℝ)) (P : List (Edge G × Bool) → Prop) :
    prob2 ps (fun l l' => P (mixAt u l l')) = prob ps P := by
  have h := bern_mix u ps (fun m => ind (P m))
  exact h

end MixSec


/-! ### No active edge at a vertex -/

section NoActSec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem prob_nonneg (ps : List (Edge G × ℝ)) (hps : ∀ q ∈ ps, 0 ≤ q.2 ∧ q.2 ≤ 1)
    (P : List (Edge G × Bool) → Prop) : 0 ≤ prob ps P := by
  rw [prob_eq_ind, ← bern_const ps 0]
  exact bern_mono ps hps _ _ (fun l _ => ind_nonneg _)

theorem bern_prod (g : Edge G × Bool → ℝ) : ∀ ps : List (Edge G × ℝ),
    bern ps (fun l => (l.map g).prod) =
      (ps.map (fun q => q.2 * g (q.1, true) + (1 - q.2) * g (q.1, false))).prod
  | [] => by
    rw [bern_nil]
    rfl
  | (e, a) :: ps => by
    rw [bern_cons]
    simp only [List.map_cons, List.prod_cons]
    rw [bern_smul ps (g (e, true)) (fun l => (l.map g).prod),
      bern_smul ps (g (e, false)) (fun l => (l.map g).prod), bern_prod g ps]
    ring

theorem ind_forall (Q : Edge G × Bool → Prop) : ∀ l : List (Edge G × Bool),
    ind (∀ p ∈ l, ¬ Q p) = (l.map (fun p => 1 - ind (Q p))).prod
  | [] => by
    have h0 : ∀ p ∈ ([] : List (Edge G × Bool)), ¬ Q p := by simp
    rw [ind_pos h0]
    rfl
  | a :: l => by
    rw [List.map_cons, List.prod_cons, ← ind_forall Q l]
    by_cases ha : Q a
    · have h1 : ¬ (∀ p ∈ a :: l, ¬ Q p) := fun h => h a (by simp) ha
      rw [ind_neg h1, ind_pos ha]
      ring
    · rw [ind_neg ha]
      by_cases hl : ∀ p ∈ l, ¬ Q p
      · have h1 : ∀ p ∈ a :: l, ¬ Q p := by
          intro p hp
          rcases List.mem_cons.mp hp with h | h
          · rw [h]; exact ha
          · exact hl p h
        rw [ind_pos h1, ind_pos hl]
        ring
      · have h1 : ¬ (∀ p ∈ a :: l, ¬ Q p) := fun h => hl (fun p hp => h p (by simp [hp]))
        rw [ind_neg h1, ind_neg hl]
        ring

theorem noactive_iff (r : V) (l : List (Edge G × Bool)) :
    (∀ s : V, ¬ isActive l r s) ↔ ∀ p ∈ l, ¬ (r ∈ (p.1 : Sym2 V) ∧ p.2 = true) := by
  constructor
  · rintro h p hp ⟨h1, h2⟩
    apply h (Sym2.Mem.other h1)
    exact ⟨p, hp, h2, (Sym2.other_spec h1).symm⟩
  · rintro h s ⟨p, hp, h1, h2⟩
    apply h p hp
    refine ⟨?_, h1⟩
    rw [h2]
    exact Sym2.mem_mk_left r s

theorem prob_noactive (r : V) (ps : List (Edge G × ℝ)) :
    prob ps (fun l => ∀ s : V, ¬ isActive l r s) =
      (ps.map (fun q => 1 - ind (r ∈ (q.1 : Sym2 V)) * q.2)).prod := by
  rw [prob_eq_ind]
  have h1 : bern ps (fun l => ind (∀ s : V, ¬ isActive l r s)) =
      bern ps (fun l => (l.map (fun p => 1 - ind (r ∈ (p.1 : Sym2 V) ∧ p.2 = true))).prod) := by
    apply bern_congr
    intro l _
    rw [← ind_forall (fun p => r ∈ (p.1 : Sym2 V) ∧ p.2 = true) l]
    by_cases h : ∀ s : V, ¬ isActive l r s
    · rw [ind_pos h, ind_pos ((noactive_iff r l).mp h)]
    · rw [ind_neg h, ind_neg (fun h' => h ((noactive_iff r l).mpr h'))]
  rw [h1, bern_prod]
  congr 1
  apply List.map_congr_left
  intro q _
  obtain ⟨g, b⟩ := q
  dsimp only
  by_cases hr : r ∈ (g : Sym2 V)
  · have h2 : r ∈ (g : Sym2 V) ∧ true = true := ⟨hr, rfl⟩
    have h3 : ¬ (r ∈ (g : Sym2 V) ∧ false = true) := fun h => by simp at h
    rw [ind_pos h2, ind_neg h3, ind_pos hr]
    ring
  · have h2 : ¬ (r ∈ (g : Sym2 V) ∧ true = true) := fun h => hr h.1
    have h3 : ¬ (r ∈ (g : Sym2 V) ∧ false = true) := fun h => hr h.1
    rw [ind_neg h2, ind_neg h3, ind_neg hr]
    ring

theorem sfilter_snoc (x : Edge G → ℝ) (es : List (Edge G)) (f : Edge G) (hf : f ∉ es) (r : V) :
    ∑ g ∈ (es ++ [f]).toFinset.filter (fun g : Edge G => r ∈ (g : Sym2 V)), x g =
      ∑ g ∈ es.toFinset.filter (fun g : Edge G => r ∈ (g : Sym2 V)), x g +
        ind (r ∈ (f : Sym2 V)) * x f := by
  have hT : (es ++ [f]).toFinset = insert f es.toFinset := by
    ext g
    simp [or_comm]
  rw [hT, Finset.filter_insert]
  by_cases hr : r ∈ (f : Sym2 V)
  · rw [if_pos hr, Finset.sum_insert, ind_pos hr]
    · ring
    · rw [Finset.mem_filter, List.mem_toFinset]
      exact fun h => hf h.1
  · rw [if_neg hr, ind_neg hr]
    ring

theorem noact_bound [DecidableRel G.Adj] (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ)
    (hx : InFM G x) (r : V) : ∀ es : List (Edge G), es.Nodup → WellDefinedOn c x es →
      (1 - c - c * ∑ g ∈ es.toFinset.filter (fun g : Edge G => r ∈ (g : Sym2 V)), x g) / (1 - c) ≤
        ((actProbs c x es).map (fun q => 1 - ind (r ∈ (q.1 : Sym2 V)) * q.2)).prod := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  intro es
  induction es using List.reverseRec with
  | nil =>
    intro _ _
    have e0 : actProbs c x ([] : List (Edge G)) = [] := rfl
    rw [e0]
    simp only [List.toFinset_nil, Finset.filter_empty, Finset.sum_empty, mul_zero, sub_zero,
      List.map_nil, List.prod_nil]
    exact le_of_eq (div_self (ne_of_gt h1c))
  | append_singleton es f ih =>
    intro hnd hwd
    have hnd' := List.nodup_append.mp hnd
    have hf : f ∉ es := fun h => hnd'.2.2 f h f (by simp) rfl
    obtain ⟨hwl, hce⟩ := wd_prefix c x es f hwd
    have hIH := ih hnd'.1 hwl
    rw [actProbs_snoc, List.map_append, List.prod_append, sfilter_snoc x es f hf r]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ g ∈ es.toFinset.filter (fun g : Edge G => r ∈ (g : Sym2 V)), x g :=
      ⟨_, rfl⟩
    rw [← hS] at hIH ⊢
    have hS1 : S + ind (r ∈ (f : Sym2 V)) * x f ≤ 1 := by
      have := xsum_le_one x hx (es ++ [f]) r
      rw [sfilter_snoc x es f hf r, ← hS] at this
      exact this
    have hS0 : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg (fun g _ => hx.1 g)
    have hxf0 := hx.1 f
    have hP0 : 0 ≤ (1 - c - c * S) / (1 - c) := by
      apply div_nonneg _ h1c.le
      have : S ≤ 1 := by
        have := ind_nonneg (r ∈ (f : Sym2 V))
        nlinarith
      nlinarith
    by_cases hr : r ∈ (f : Sym2 V)
    · simp only [ind_pos hr, one_mul]
      simp only [ind_pos hr, one_mul] at hS1
      -- lower bound on the unmatched probability
      have hspec := Sym2.other_spec hr
      have hU := unmatched_eq c x es f r (Sym2.Mem.other hr) hspec.symm
      have hmr := matched_le c hc0.le x hx es hnd'.1 hwl r
      have hmo := matched_le c hc0.le x hx es hnd'.1 hwl (Sym2.Mem.other hr)
      have hso := xsum_le_one x hx es (Sym2.Mem.other hr)
      have hps := actProbs_bounds c hc0.le x hx es hwl
      have hboth := prob_nonneg (actProbs c x es) hps
        (fun l => matchedIn l r ∧ matchedIn l (Sym2.Mem.other hr))
      rw [← hS] at hmr
      have hUlow : 1 - c - c * S ≤ unmatchedProb (actProbs c x es) f := by
        have e : unmatchedAt c x es f = unmatchedProb (actProbs c x es) f := rfl
        rw [← e, hU]
        nlinarith [mul_le_mul_of_nonneg_left hso hc0.le]
      have hS1' : S ≤ 1 := by linarith
      have hden : 0 < 1 - c - c * S := by nlinarith [mul_le_mul_of_nonneg_left hS1' hc0.le]
      have hden' : 1 - c - c * S ≠ 0 := ne_of_gt hden
      have h1c' : 1 - c ≠ 0 := ne_of_gt h1c
      have ha : c / unmatchedProb (actProbs c x es) f * x f ≤ c * x f / (1 - c - c * S) := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_left (mul_nonneg hc0.le hxf0) hden hUlow
      have hfac : (1 - c - c * (S + x f)) / (1 - c - c * S) ≤
          1 - c / unmatchedProb (actProbs c x es) f * x f := by
        have e : 1 - c * x f / (1 - c - c * S) = (1 - c - c * (S + x f)) / (1 - c - c * S) := by
          rw [one_sub_div hden']
          congr 1
          ring
        rw [← e]
        linarith
      have hfac0 : 0 ≤ (1 - c - c * (S + x f)) / (1 - c - c * S) := by
        apply div_nonneg _ hden.le
        nlinarith [mul_le_mul_of_nonneg_left hS1 hc0.le]
      calc (1 - c - c * (S + x f)) / (1 - c)
          = (1 - c - c * S) / (1 - c) * ((1 - c - c * (S + x f)) / (1 - c - c * S)) := by
            rw [div_mul_div_comm, mul_comm (1 - c - c * S) (1 - c - c * (S + x f)),
              mul_div_mul_right _ _ hden']
        _ ≤ ((actProbs c x es).map (fun q => 1 - ind (r ∈ (q.1 : Sym2 V)) * q.2)).prod *
              (1 - c / unmatchedProb (actProbs c x es) f * x f) :=
            mul_le_mul hIH hfac hfac0 (le_trans hP0 hIH)
    · simp only [ind_neg hr, zero_mul, add_zero, sub_zero, mul_one]
      exact hIH

end NoActSec


/-! ### Deactivating an edge at u never destroys a candidate -/

section FlipSec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem greedy_mono (l : List (Edge G × Bool)) :
    ∀ l' : List (Edge G × Bool), greedy l ⊆ greedy (l ++ l') := by
  intro l'
  induction l' using List.reverseRec with
  | nil =>
    rw [List.append_nil]
  | append_singleton l' q ih =>
    rw [← List.append_assoc, greedy_snoc]
    split_ifs
    · exact fun g hg => Finset.mem_insert_of_mem (ih hg)
    · exact ih

theorem greedy_matching : ∀ l : List (Edge G × Bool), ∀ f ∈ greedy l, ∀ g ∈ greedy l, f ≠ g →
    ∀ w, w ∈ (f : Sym2 V) → w ∉ (g : Sym2 V) := by
  intro l
  induction l using List.reverseRec with
  | nil =>
    intro f hf
    rw [greedy_nil] at hf
    simp at hf
  | append_singleton l q ih =>
    intro f hf g hg hne w hwf hwg
    rw [greedy_snoc] at hf hg
    split_ifs at hf hg with hc
    · rcases Finset.mem_insert.mp hf with h1 | h1 <;> rcases Finset.mem_insert.mp hg with h2 | h2
      · exact hne (h1.trans h2.symm)
      · rw [h1] at hwf
        exact hc.2 g h2 w hwf hwg
      · rw [h2] at hwg
        exact hc.2 f h1 w hwg hwf
      · exact ih f h1 g h2 hne w hwf hwg
    · exact ih f hf g hg hne w hwf hwg

theorem greedy_append_congr (X X' B : List (Edge G × Bool)) (h : greedy X = greedy X') :
    greedy (X ++ B) = greedy (X' ++ B) := by
  unfold greedy at h ⊢
  rw [List.foldl_append, List.foldl_append, h]

theorem greedy_flip (A B : List (Edge G × Bool)) (f g : Edge G) (u : V) (hu : u ∈ (f : Sym2 V))
    (hug : u ∈ (g : Sym2 V)) (hne : g ≠ f) (h : g ∈ greedy (A ++ (f, true) :: B)) :
    g ∈ greedy (A ++ (f, false) :: B) := by
  have eT : A ++ (f, true) :: B = (A ++ [(f, true)]) ++ B := by simp
  have eF : A ++ (f, false) :: B = (A ++ [(f, false)]) ++ B := by simp
  rw [eT] at h
  rw [eF]
  by_cases hE : endsFree (greedy A) f
  · exfalso
    have hf1 : f ∈ greedy (A ++ [(f, true)]) := by
      rw [greedy_snoc, if_pos ⟨rfl, hE⟩]
      exact Finset.mem_insert_self _ _
    have hf2 := greedy_mono (A ++ [(f, true)]) B hf1
    exact greedy_matching _ f hf2 g h (Ne.symm hne) u hu hug
  · have h1 : greedy (A ++ [(f, true)]) = greedy A := by
      rw [greedy_snoc, if_neg (fun h' => hE h'.2)]
    have h2 : greedy (A ++ [(f, false)]) = greedy A := by
      rw [greedy_snoc, if_neg (fun h' => by simp at h')]
    rw [greedy_append_congr _ _ B (h1.trans h2.symm)] at h
    exact h

theorem split_support {pre post : List (Edge G)} {f : Edge G} {l : List (Edge G × Bool)}
    (h : l.map Prod.fst = pre ++ f :: post) :
    ∃ l1 b l2, l = l1 ++ (f, b) :: l2 ∧ l1.map Prod.fst = pre ∧ l2.map Prod.fst = post := by
  obtain ⟨l1, l2', hl, h1, h2⟩ := List.map_eq_append_iff.mp h
  obtain ⟨p, l2, hl2, hp, h3⟩ := List.map_eq_cons_iff.mp h2
  refine ⟨l1, p.2, l2, ?_, h1, h3⟩
  rw [hl, hl2]
  congr 2
  rw [← hp]

theorem mix_split (u : V) (l1 l1' l2 l2' : List (Edge G × Bool)) (f : Edge G) (b b' : Bool)
    (hu : u ∈ (f : Sym2 V)) (hlen : l1.length = l1'.length) :
    mixAt u (l1 ++ (f, b) :: l2) (l1' ++ (f, b') :: l2') = mixAt u l1 l1' ++ (f, b) :: mixAt u l2 l2' := by
  unfold mixAt
  rw [List.zipWith_append hlen, List.zipWith_cons_cons]
  simp [hu]

end FlipSec


/-! ### Independence over disjoint coordinate sets -/

section IndepSec

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def mask (S : Edge G → Prop) (l : List (Edge G × Bool)) : List (Edge G × Bool) :=
  l.map (fun p => if S p.1 then p else (p.1, false))

def DepOn (S : Edge G → Prop) (F : List (Edge G × Bool) → ℝ) : Prop := ∀ l, F l = F (mask S l)

theorem mask_cons (S : Edge G → Prop) (p : Edge G × Bool) (l : List (Edge G × Bool)) :
    mask S (p :: l) = (if S p.1 then p else (p.1, false)) :: mask S l := rfl

theorem mask_mask_sub (S S' : Edge G → Prop) (hSS : ∀ e, S e → S' e) :
    ∀ l : List (Edge G × Bool), mask S (mask S' l) = mask S l
  | [] => rfl
  | p :: l => by
    rw [mask_cons, mask_cons, mask_cons, mask_mask_sub S S' hSS l]
    congr 1
    by_cases h : S p.1
    · simp [h, hSS _ h]
    · by_cases h' : S' p.1 <;> simp [h, h']

theorem mask_mask (S : Edge G → Prop) (l : List (Edge G × Bool)) : mask S (mask S l) = mask S l :=
  mask_mask_sub S S (fun _ h => h) l

theorem dep_mono {S S' : Edge G → Prop} (hSS : ∀ e, S e → S' e) {F : List (Edge G × Bool) → ℝ}
    (h : DepOn S F) : DepOn S' F := by
  intro l
  rw [h l, h (mask S' l), mask_mask_sub S S' hSS]

theorem dep_mul {S : Edge G → Prop} {F1 F2 : List (Edge G × Bool) → ℝ} (h1 : DepOn S F1)
    (h2 : DepOn S F2) : DepOn S (fun l => F1 l * F2 l) := by
  intro l
  show F1 l * F2 l = F1 (mask S l) * F2 (mask S l)
  rw [← h1, ← h2]

theorem dep_tail {S : Edge G → Prop} {F : List (Edge G × Bool) → ℝ} (h : DepOn S F) (e : Edge G)
    (b : Bool) : DepOn S (fun l => F ((e, b) :: l)) := by
  intro l
  show F ((e, b) :: l) = F ((e, b) :: mask S l)
  rw [h ((e, b) :: l), h ((e, b) :: mask S l), mask_cons, mask_cons, mask_mask]

theorem dep_bit {S : Edge G → Prop} {F : List (Edge G × Bool) → ℝ} (h : DepOn S F) (e : Edge G)
    (he : ¬ S e) (l : List (Edge G × Bool)) : F ((e, true) :: l) = F ((e, false) :: l) := by
  rw [h ((e, true) :: l), h ((e, false) :: l), mask_cons, mask_cons]
  simp only [he, if_false]

theorem bern_indep : ∀ (ps : List (Edge G × ℝ)) (S1 S2 : Edge G → Prop)
    (F1 F2 : List (Edge G × Bool) → ℝ), (∀ q ∈ ps, ¬ (S1 q.1 ∧ S2 q.1)) →
    DepOn S1 F1 → DepOn S2 F2 → bern ps (fun l => F1 l * F2 l) = bern ps F1 * bern ps F2
  | [], S1, S2, F1, F2, _, _, _ => by
    rw [bern_nil, bern_nil, bern_nil]
  | (e, a) :: ps, S1, S2, F1, F2, hd, h1, h2 => by
    have hd' : ∀ q ∈ ps, ¬ (S1 q.1 ∧ S2 q.1) := fun q hq => hd q (by simp [hq])
    rw [bern_cons, bern_cons, bern_cons]
    by_cases hS1 : S1 e
    · have hS2 : ¬ S2 e := fun h => hd (e, a) (by simp) ⟨hS1, h⟩
      have hb := dep_bit h2 e hS2
      simp only [hb]
      rw [bern_indep ps S1 S2 (fun l => F1 ((e, true) :: l)) (fun l => F2 ((e, false) :: l)) hd'
          (dep_tail h1 e true) (dep_tail h2 e false),
        bern_indep ps S1 S2 (fun l => F1 ((e, false) :: l)) (fun l => F2 ((e, false) :: l)) hd'
          (dep_tail h1 e false) (dep_tail h2 e false)]
      ring
    · have hb := dep_bit h1 e hS1
      simp only [hb]
      rw [bern_indep ps S1 S2 (fun l => F1 ((e, false) :: l)) (fun l => F2 ((e, true) :: l)) hd'
          (dep_tail h1 e false) (dep_tail h2 e true),
        bern_indep ps S1 S2 (fun l => F1 ((e, false) :: l)) (fun l => F2 ((e, false) :: l)) hd'
          (dep_tail h1 e false) (dep_tail h2 e false)]
      ring

theorem mix_mask (u : V) : ∀ (l l1 : List (Edge G × Bool)),
    mixAt u (mask (fun e : Edge G => u ∈ (e : Sym2 V)) l) l1 = mixAt u l l1
  | [], l1 => rfl
  | p :: l, [] => rfl
  | p :: l, q :: l1 => by
    have ih := mix_mask u l l1
    unfold mixAt at ih ⊢
    rw [mask_cons, List.zipWith_cons_cons, List.zipWith_cons_cons, ih]
    congr 1
    by_cases h : u ∈ (p.1 : Sym2 V)
    · simp [h]
    · simp [h]

theorem act_mask (S : Edge G → Prop) (l : List (Edge G × Bool)) (s t : V)
    (hS : ∀ e : Edge G, (e : Sym2 V) = s(s, t) → S e) :
    isActive (mask S l) s t ↔ isActive l s t := by
  constructor
  · rintro ⟨p, hp, hp2, hp1⟩
    unfold mask at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    by_cases h : S q.1
    · rw [if_pos h] at hp2 hp1
      exact ⟨q, hq, hp2, hp1⟩
    · rw [if_neg h] at hp2
      simp at hp2
  · rintro ⟨q, hq, hq2, hq1⟩
    refine ⟨q, ?_, hq2, hq1⟩
    unfold mask
    apply List.mem_map.mpr
    refine ⟨q, hq, ?_⟩
    rw [if_pos (hS q.1 hq1)]

theorem greedy_active : ∀ (m : List (Edge G × Bool)) (g : Edge G), g ∈ greedy m → (g, true) ∈ m := by
  intro m
  induction m using List.reverseRec with
  | nil =>
    intro g hg
    rw [greedy_nil] at hg
    simp at hg
  | append_singleton m q ih =>
    intro g hg
    rw [greedy_snoc] at hg
    split_ifs at hg with hc
    · rcases Finset.mem_insert.mp hg with h | h
      · rw [h]
        have : q = (q.1, true) := by
          obtain ⟨q1, q2⟩ := q
          simp only at hc ⊢
          rw [hc.1]
        rw [← this]
        simp
      · exact List.mem_append_left _ (ih g h)
    · exact List.mem_append_left _ (ih g hg)

theorem mix_mem (u : V) : ∀ (l l1 : List (Edge G × Bool)), l.map Prod.fst = l1.map Prod.fst →
    ∀ p ∈ mixAt u l l1, u ∈ (p.1 : Sym2 V) → p ∈ l
  | [], _, _, p, hp, _ => by simp [mixAt] at hp
  | _ :: _, [], h, _, _, _ => by simp at h
  | q :: l, q1 :: l1, h, p, hp, hu => by
    simp only [List.map_cons, List.cons.injEq] at h
    unfold mixAt at hp
    rw [List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with hp | hp
    · by_cases hq : u ∈ (q.1 : Sym2 V)
      · rw [if_pos hq] at hp
        rw [hp]
        simp
      · rw [if_neg hq] at hp
        exfalso
        apply hq
        rw [h.1, ← hp]
        exact hu
    · have := mix_mem u l l1 h.2 p hp hu
      exact List.mem_cons_of_mem _ this

theorem cand_act (u a : V) (l l1 : List (Edge G × Bool)) (h : l.map Prod.fst = l1.map Prod.fst)
    (hc : IsCandidate u l l1 a) : isActive l u a := by
  obtain ⟨g, hg1, hg2⟩ := hc
  have hgm := greedy_active _ g hg1
  have hu : u ∈ (g : Sym2 V) := by rw [hg2]; exact Sym2.mem_mk_left u a
  exact ⟨(g, true), mix_mem u l l1 h (g, true) hgm hu, rfl, hg2⟩

theorem entry_unique (l : List (Edge G × Bool)) (hnd : (l.map Prod.fst).Nodup) (p q : Edge G × Bool)
    (hp : p ∈ l) (hq : q ∈ l) (h : p.1 = q.1) : p = q := by
  induction l with
  | nil => simp at hp
  | cons r l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with hp' | hp' <;> rcases List.mem_cons.mp hq with hq' | hq'
    · rw [hp', hq']
    · exfalso
      apply hnd.1
      rw [← hp', h]
      exact List.mem_map_of_mem hq'
    · exfalso
      apply hnd.1
      rw [← hq', ← h]
      exact List.mem_map_of_mem hp'
    · exact ih hnd.2 hp' hq'

theorem deg_one_iff (l : List (Edge G × Bool)) (hnd : (l.map Prod.fst).Nodup) (a : V) (p : Edge G × Bool)
    (hp : p ∈ l) (hp2 : p.2 = true) (hpa : a ∈ (p.1 : Sym2 V)) :
    activeDegree l a = 1 ↔ ∀ q ∈ l, q.2 = true → a ∈ (q.1 : Sym2 V) → q = p := by
  have hndl : l.Nodup := by
    have := hnd.of_map Prod.fst
    exact this
  unfold activeDegree
  rw [List.countP_eq_length_filter]
  have hpf : p ∈ l.filter (fun q => q.2 && decide (a ∈ (q.1 : Sym2 V))) := by
    rw [List.mem_filter]
    exact ⟨hp, by simp [hp2, hpa]⟩
  constructor
  · intro h1 q hq hq2 hqa
    obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp h1
    have hqf : q ∈ l.filter (fun q => q.2 && decide (a ∈ (q.1 : Sym2 V))) := by
      rw [List.mem_filter]
      exact ⟨hq, by simp [hq2, hqa]⟩
    rw [hr] at hqf hpf
    simp only [List.mem_singleton] at hqf hpf
    rw [hqf, hpf]
  · intro h1
    have hnd2 := hndl.filter (fun q => q.2 && decide (a ∈ (q.1 : Sym2 V)))
    rw [← List.toFinset_card_of_nodup hnd2]
    have : (l.filter (fun q => q.2 && decide (a ∈ (q.1 : Sym2 V)))).toFinset = {p} := by
      ext q
      simp only [List.mem_toFinset, List.mem_filter, Finset.mem_singleton, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ⟨hq, hq2, hqa⟩
        exact h1 q hq hq2 hqa
      · rintro rfl
        exact ⟨hp, hp2, hpa⟩
    rw [this, Finset.card_singleton]

end IndepSec


section L54

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem prob2_eq_ind (ps : List (Edge G × ℝ))
    (P : List (Edge G × Bool) → List (Edge G × Bool) → Prop) :
    prob2 ps P = bern ps (fun l => bern ps (fun l' => ind (P l l'))) := rfl

theorem act_iff (pre post : List (Edge G)) (f : Edge G) (hfpre : f ∉ pre) (hfpost : f ∉ post)
    (l1 l2 : List (Edge G × Bool)) (b : Bool) (h1 : l1.map Prod.fst = pre)
    (h2 : l2.map Prod.fst = post) (u i : V) (hfs : (f : Sym2 V) = s(u, i)) :
    isActive (l1 ++ (f, b) :: l2) u i ↔ b = true := by
  constructor
  · rintro ⟨p, hp, hp2, hp1⟩
    have hpf : p.1 = f := Subtype.ext (hp1.trans hfs.symm)
    rcases List.mem_append.mp hp with h | h
    · exfalso
      apply hfpre
      rw [← h1, ← hpf]
      exact List.mem_map_of_mem h
    · rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hp2
        exact hp2
      · exfalso
        apply hfpost
        rw [← h2, ← hpf]
        exact List.mem_map_of_mem h'
  · intro hb
    exact ⟨(f, b), by simp, hb, hfs⟩

theorem lemma54 [DecidableRel G.Adj] (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (u i j : V) (hij : i ≠ j) :
    prob (actProbs c x es) (fun l => ¬ isActive l u i) *
        prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' j) ≤
      prob2 (actProbs c x es) (fun l l' => ¬ isActive l u i ∧ IsCandidate u l l' j) := by
  have hps := actProbs_bounds c hc x hx es hwd
  rw [prob_eq_ind, prob2_eq_ind, prob2_eq_ind]
  by_cases hf : ∃ f ∈ es, (f : Sym2 V) = s(u, i)
  · obtain ⟨f, hfe, hfs⟩ := hf
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hfe
    have hnd' := List.nodup_append.mp hnd
    have hfpre : f ∉ pre := fun h => hnd'.2.2 f h f (by simp) rfl
    have hfpost : f ∉ post := (List.nodup_cons.mp hnd'.2.1).1
    have e1 : pre ++ f :: post = (pre ++ [f]) ++ post := by simp
    obtain ⟨R, hR1, hR2⟩ := actProbs_append c x (pre ++ [f]) post
    obtain ⟨a, ha⟩ : ∃ a, a = c / unmatchedProb (actProbs c x pre) f * x f := ⟨_, rfl⟩
    have hpsq : actProbs c x (pre ++ f :: post) = actProbs c x pre ++ (f, a) :: R := by
      rw [e1, hR1, actProbs_snoc, ← ha]
      simp
    have hab := hps (f, a) (by rw [hpsq]; simp)
    have ha0 : 0 ≤ a := hab.1
    have ha1 : a ≤ 1 := hab.2
    have hpre : ∀ q ∈ actProbs c x pre, 0 ≤ q.2 ∧ q.2 ≤ 1 :=
      fun q hq => hps q (by rw [hpsq]; simp [hq])
    have hRb : ∀ q ∈ R, 0 ≤ q.2 ∧ q.2 ≤ 1 :=
      fun q hq => hps q (by rw [hpsq]; simp [hq])
    have hu : u ∈ (f : Sym2 V) := by rw [hfs]; exact Sym2.mem_mk_left u i
    -- probability that (ui) is inactive
    have hnot : bern (actProbs c x (pre ++ f :: post)) (fun l => ind (¬ isActive l u i)) = 1 - a := by
      rw [hpsq, bern_append, ← bern_const (actProbs c x pre) (1 - a)]
      apply bern_congr
      intro l1 hl1
      rw [actProbs_fst] at hl1
      rw [bern_cons]
      have hT : bern R (fun l2 => ind (¬ isActive (l1 ++ (f, true) :: l2) u i)) = 0 := by
        rw [← bern_const R 0]
        apply bern_congr
        intro l2 hl2
        rw [hR2] at hl2
        exact ind_neg (fun h => h ((act_iff pre post f hfpre hfpost l1 l2 true hl1 hl2 u i hfs).mpr rfl))
      have hF : bern R (fun l2 => ind (¬ isActive (l1 ++ (f, false) :: l2) u i)) = 1 := by
        rw [← bern_const R 1]
        apply bern_congr
        intro l2 hl2
        rw [hR2] at hl2
        apply ind_pos
        intro h
        have := (act_iff pre post f hfpre hfpost l1 l2 false hl1 hl2 u i hfs).mp h
        simp at this
      rw [hT, hF]
      ring
    rw [hnot, hpsq, bern_append (actProbs c x pre) ((f, a) :: R),
      bern_append (actProbs c x pre) ((f, a) :: R)]
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = actProbs c x pre ++ (f, a) :: R := ⟨_, rfl⟩
    rw [← hQ]
    have hQb : ∀ q ∈ Q, 0 ≤ q.2 ∧ q.2 ≤ 1 := by
      rw [hQ, ← hpsq]
      exact hps
    have hQf : Q.map Prod.fst = pre ++ f :: post := by
      rw [hQ, ← hpsq, actProbs_fst]
    rw [← bern_smul]
    apply bern_mono _ hpre
    intro l1 hl1
    rw [actProbs_fst] at hl1
    rw [bern_cons, bern_cons]
    -- the candidate probability with (ui) active is at most with (ui) inactive
    have hXY : bern R (fun l2 => bern Q (fun l' => ind (IsCandidate u (l1 ++ (f, true) :: l2) l' j))) ≤
        bern R (fun l2 => bern Q (fun l' => ind (IsCandidate u (l1 ++ (f, false) :: l2) l' j))) := by
      apply bern_mono _ hRb
      intro l2 hl2
      rw [hR2] at hl2
      apply bern_mono _ hQb
      intro l' hl'
      rw [hQf] at hl'
      obtain ⟨l1', b', l2', rfl, h1', h2'⟩ := split_support hl'
      have hlen : l1.length = l1'.length := by
        have := congrArg List.length (hl1.trans h1'.symm)
        simpa using this
      by_cases hC : IsCandidate u (l1 ++ (f, true) :: l2) (l1' ++ (f, b') :: l2') j
      · rw [ind_pos hC]
        apply le_of_eq
        symm
        apply ind_pos
        obtain ⟨g, hg1, hg2⟩ := hC
        refine ⟨g, ?_, hg2⟩
        rw [mix_split u l1 l1' l2 l2' f false b' hu hlen]
        rw [mix_split u l1 l1' l2 l2' f true b' hu hlen] at hg1
        have hug : u ∈ (g : Sym2 V) := by rw [hg2]; exact Sym2.mem_mk_left u j
        have hne : g ≠ f := by
          intro h
          rw [h, hfs] at hg2
          exact hij (Sym2.congr_right.mp hg2)
        exact greedy_flip _ _ f g u hu hug hne hg1
      · rw [ind_neg hC]
        exact ind_nonneg _
    have hJt : bern R (fun l2 => bern Q (fun l' =>
        ind (¬ isActive (l1 ++ (f, true) :: l2) u i ∧ IsCandidate u (l1 ++ (f, true) :: l2) l' j))) = 0 := by
      rw [← bern_const R 0]
      apply bern_congr
      intro l2 hl2
      rw [hR2] at hl2
      rw [← bern_const Q 0]
      apply bern_congr
      intro l' _
      exact ind_neg (fun h => h.1 ((act_iff pre post f hfpre hfpost l1 l2 true hl1 hl2 u i hfs).mpr rfl))
    have hJf : bern R (fun l2 => bern Q (fun l' =>
        ind (¬ isActive (l1 ++ (f, false) :: l2) u i ∧ IsCandidate u (l1 ++ (f, false) :: l2) l' j))) =
        bern R (fun l2 => bern Q (fun l' => ind (IsCandidate u (l1 ++ (f, false) :: l2) l' j))) := by
      apply bern_congr
      intro l2 hl2
      rw [hR2] at hl2
      apply bern_congr
      intro l' _
      have hna : ¬ isActive (l1 ++ (f, false) :: l2) u i := by
        intro h
        have := (act_iff pre post f hfpre hfpost l1 l2 false hl1 hl2 u i hfs).mp h
        simp at this
      by_cases hC : IsCandidate u (l1 ++ (f, false) :: l2) l' j
      · have hb : ¬ isActive (l1 ++ (f, false) :: l2) u i ∧ IsCandidate u (l1 ++ (f, false) :: l2) l' j :=
          ⟨hna, hC⟩
        rw [ind_pos hb, ind_pos hC]
      · have hb : ¬ (¬ isActive (l1 ++ (f, false) :: l2) u i ∧ IsCandidate u (l1 ++ (f, false) :: l2) l' j) :=
          fun h => hC h.2
        rw [ind_neg hb, ind_neg hC]
    rw [hJt, hJf]
    have h1a : 0 ≤ 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha0 h1a) (sub_nonneg.mpr hXY)]
  · have hnot : bern (actProbs c x es) (fun l => ind (¬ isActive l u i)) = 1 := by
      rw [← bern_const (actProbs c x es) 1]
      apply bern_congr
      intro l hl
      rw [actProbs_fst] at hl
      apply ind_pos
      rintro ⟨p, hp, _, hp1⟩
      apply hf
      refine ⟨p.1, ?_, hp1⟩
      rw [← hl]
      exact List.mem_map_of_mem hp
    have hJ : bern (actProbs c x es) (fun l => bern (actProbs c x es) (fun l' =>
        ind (¬ isActive l u i ∧ IsCandidate u l l' j))) =
        bern (actProbs c x es) (fun l => bern (actProbs c x es) (fun l' => ind (IsCandidate u l l' j))) := by
      apply bern_congr
      intro l hl
      rw [actProbs_fst] at hl
      have hna : ¬ isActive l u i := by
        rintro ⟨p, hp, _, hp1⟩
        apply hf
        refine ⟨p.1, ?_, hp1⟩
        rw [← hl]
        exact List.mem_map_of_mem hp
      apply bern_congr
      intro l' _
      by_cases hC : IsCandidate u l l' j
      · have hb : ¬ isActive l u i ∧ IsCandidate u l l' j := ⟨hna, hC⟩
        rw [ind_pos hb, ind_pos hC]
      · have hb : ¬ (¬ isActive l u i ∧ IsCandidate u l l' j) := fun h => hC h.2
        rw [ind_neg hb, ind_neg hC]
    rw [hnot, hJ, one_mul] <;> exact le_refl _

end L54


section Eq12

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem wd_at (c : ℝ) (x : Edge G → ℝ) (pre post : List (Edge G)) (f : Edge G)
    (hwd : WellDefinedOn c x (pre ++ f :: post)) :
    c ≤ unmatchedProb (actProbs c x pre) f := by
  have hk : pre.length < (pre ++ f :: post).length := by simp
  have h0 : c ≤ unmatchedAt c x ((pre ++ f :: post).take pre.length)
      ((pre ++ f :: post).get ⟨pre.length, hk⟩) := hwd ⟨pre.length, hk⟩
  have e1 : (pre ++ f :: post).take pre.length = pre := by simp
  have e2 : (pre ++ f :: post).get ⟨pre.length, hk⟩ = f := by simp
  rw [e1, e2] at h0
  exact h0

theorem cand_prob (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (es : List (Edge G)) (hnd : es.Nodup)
    (hwd : WellDefinedOn c x es) (u s : V) :
    prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' s) = c * xPair x es u s := by
  have h1 : prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' s) =
      prob (actProbs c x es) (fun m => ∃ f ∈ greedy m, (f : Sym2 V) = s(u, s)) :=
    prob2_mix u (actProbs c x es) (fun m => ∃ f ∈ greedy m, (f : Sym2 V) = s(u, s))
  rw [h1, xPair_eq]
  by_cases hf : ∃ f0 ∈ es, (f0 : Sym2 V) = s(u, s)
  · obtain ⟨f0, hf0, hf0s⟩ := hf
    have hev : (fun m => ∃ f ∈ greedy m, (f : Sym2 V) = s(u, s)) = (fun m => f0 ∈ greedy m) := by
      funext m
      apply propext
      constructor
      · rintro ⟨f, hf1, hf2⟩
        have : f = f0 := Subtype.ext (hf2.trans hf0s.symm)
        rw [← this]
        exact hf1
      · intro h
        exact ⟨f0, h, hf0s⟩
    have hset : es.toFinset.filter (fun f : Edge G => (f : Sym2 V) = s(u, s)) = {f0} := by
      ext f
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h2⟩
        exact Subtype.ext (h2.trans hf0s.symm)
      · rintro rfl
        exact ⟨hf0, hf0s⟩
    rw [hev, hset, Finset.sum_singleton]
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hf0
    by_cases hc0 : c = 0
    · rw [prob_mem_greedy c x pre post f0 hnd, hc0]
      simp
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hU : unmatchedProb (actProbs c x pre) f0 ≠ 0 := by
        have := wd_at c x pre post f0 hwd
        linarith
      exact prob_mem_greedy_eq c x pre post f0 hnd hU
  · have hset : es.toFinset.filter (fun f : Edge G => (f : Sym2 V) = s(u, s)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro f hf1 hf2
      rw [List.mem_toFinset] at hf1
      exact hf ⟨f, hf1, hf2⟩
    rw [hset, Finset.sum_empty, mul_zero, prob_eq_ind, ← bern_const (actProbs c x es) 0]
    apply bern_congr
    intro m hm
    rw [actProbs_fst] at hm
    rw [ind_neg]
    rintro ⟨f, hf1, hf2⟩
    apply hf
    refine ⟨f, ?_, hf2⟩
    rw [← hm]
    exact greedy_sub m f hf1

end Eq12


section E13

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem prob2_eq_ind' (ps : List (Edge G × ℝ))
    (P : List (Edge G × Bool) → List (Edge G × Bool) → Prop) :
    prob2 ps P = bern ps (fun l => bern ps (fun l' => ind (P l l'))) := rfl

theorem prob3_eq_ind (ps : List (Edge G × ℝ))
    (P : List (Edge G × Bool) → List (Edge G × Bool) → List (Edge G × Bool) → Prop) :
    prob3 ps P = bern ps (fun l => bern ps (fun l' => bern ps (fun l'' => ind (P l l' l'')))) := rfl

theorem bern2_prod (ps : List (Edge G × ℝ)) (f g : List (Edge G × Bool) → ℝ) (C : ℝ) :
    bern ps (fun l1 => bern ps (fun l2 => f l1 * g l2 * C)) = bern ps f * bern ps g * C := by
  have h1 : ∀ l1, bern ps (fun l2 => f l1 * g l2 * C) = (f l1 * C) * bern ps g := by
    intro l1
    rw [← bern_smul]
    congr 1
    funext l2
    ring
  simp only [h1]
  have h2 : (fun l1 => f l1 * C * bern ps g) = (fun l1 => (C * bern ps g) * f l1) := by
    funext l1
    ring
  rw [h2, bern_smul]
  ring

theorem sym2_ne {x y z : V} (hne : x ≠ y) (hz : z ≠ x) : s(x, z) ≠ s(y, z) := by
  intro h
  rcases Sym2.eq_iff.mp h with h' | h'
  · exact hne h'.1
  · exact hz h'.1.symm

theorem sum_ind_le_one {ι : Type*} (A : Finset ι) (P : ι → Prop) (h : ∀ a a', P a → P a' → a = a') :
    ∑ a ∈ A, ind (P a) ≤ 1 := by
  by_cases hex : ∃ a ∈ A, P a
  · obtain ⟨a0, ha0, hP0⟩ := hex
    rw [Finset.sum_eq_single a0]
    · exact ind_le_one _
    · intro b _ hb
      exact ind_neg (fun hPb => hb (h b a0 hPb hP0))
    · intro h'
      exact absurd ha0 h'
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun a ha => ind_neg (hex a ha))]
    norm_num

theorem cand_unique (u : V) (l l1 : List (Edge G × Bool)) (a a' : V)
    (h : IsCandidate u l l1 a) (h' : IsCandidate u l l1 a') : a = a' := by
  obtain ⟨g, hg1, hg2⟩ := h
  obtain ⟨g', hg1', hg2'⟩ := h'
  by_cases hgg : g = g'
  · rw [hgg, hg2'] at hg2
    exact (Sym2.congr_right.mp hg2).symm
  · exfalso
    have hu : u ∈ (g : Sym2 V) := by rw [hg2]; exact Sym2.mem_mk_left u a
    have hu' : u ∈ (g' : Sym2 V) := by rw [hg2']; exact Sym2.mem_mk_left u a'
    exact greedy_matching _ g hg1 g' hg1' hgg u hu hu'

theorem ev_iff (es : List (Edge G)) (hnd : es.Nodup) (u v a b : V) (huv : u ≠ v)
    (ha : a ≠ u ∧ a ≠ v) (hb : b ≠ u ∧ b ≠ v ∧ b ≠ a) (l l1 l2 : List (Edge G × Bool))
    (hl : l.map Prod.fst = es) (hl1 : l1.map Prod.fst = es) (hl2 : l2.map Prod.fst = es) :
    (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧ activeDegree l a = 1 ∧ activeDegree l b = 1) ↔
      ((IsCandidate u l l1 a ∧ ¬ isActive l u b) ∧ (IsCandidate v l l2 b ∧ ¬ isActive l v a) ∧
        ∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b) := by
  have hndl : (l.map Prod.fst).Nodup := by rw [hl]; exact hnd
  constructor
  · rintro ⟨c1, c2, da, db⟩
    obtain ⟨pa, hpa, hpa2, hpa1⟩ := cand_act u a l l1 (by rw [hl, hl1]) c1
    obtain ⟨pb, hpb, hpb2, hpb1⟩ := cand_act v b l l2 (by rw [hl, hl2]) c2
    have hpaa : a ∈ (pa.1 : Sym2 V) := by rw [hpa1]; exact Sym2.mem_mk_right u a
    have hpbb : b ∈ (pb.1 : Sym2 V) := by rw [hpb1]; exact Sym2.mem_mk_right v b
    have hda := (deg_one_iff l hndl a pa hpa hpa2 hpaa).mp da
    have hdb := (deg_one_iff l hndl b pb hpb hpb2 hpbb).mp db
    refine ⟨⟨c1, ?_⟩, ⟨c2, ?_⟩, ?_⟩
    · rintro ⟨q, hq, hq2, hq1⟩
      have hqb : b ∈ (q.1 : Sym2 V) := by rw [hq1]; exact Sym2.mem_mk_right u b
      have := hdb q hq hq2 hqb
      rw [this, hpb1] at hq1
      exact sym2_ne (Ne.symm huv) hb.2.1 hq1
    · rintro ⟨q, hq, hq2, hq1⟩
      have hqa : a ∈ (q.1 : Sym2 V) := by rw [hq1]; exact Sym2.mem_mk_right v a
      have := hda q hq hq2 hqa
      rw [this, hpa1] at hq1
      exact sym2_ne huv ha.1 hq1
    · intro s hsu hsv
      constructor
      · rintro ⟨q, hq, hq2, hq1⟩
        have hqa : a ∈ (q.1 : Sym2 V) := by rw [hq1]; exact Sym2.mem_mk_right s a
        have := hda q hq hq2 hqa
        rw [this, hpa1] at hq1
        exact sym2_ne (Ne.symm hsu) ha.1 hq1
      · rintro ⟨q, hq, hq2, hq1⟩
        have hqb : b ∈ (q.1 : Sym2 V) := by rw [hq1]; exact Sym2.mem_mk_right s b
        have := hdb q hq hq2 hqb
        rw [this, hpb1] at hq1
        exact sym2_ne (Ne.symm hsv) hb.2.1 hq1
  · rintro ⟨⟨c1, nub⟩, ⟨c2, nva⟩, rst⟩
    obtain ⟨pa, hpa, hpa2, hpa1⟩ := cand_act u a l l1 (by rw [hl, hl1]) c1
    obtain ⟨pb, hpb, hpb2, hpb1⟩ := cand_act v b l l2 (by rw [hl, hl2]) c2
    have hpaa : a ∈ (pa.1 : Sym2 V) := by rw [hpa1]; exact Sym2.mem_mk_right u a
    have hpbb : b ∈ (pb.1 : Sym2 V) := by rw [hpb1]; exact Sym2.mem_mk_right v b
    refine ⟨c1, c2, ?_, ?_⟩
    · rw [deg_one_iff l hndl a pa hpa hpa2 hpaa]
      intro q hq hq2 hqa
      have hspec := Sym2.other_spec hqa
      by_cases hw1 : Sym2.Mem.other hqa = u
      · apply entry_unique l hndl q pa hq hpa
        apply Subtype.ext
        rw [hpa1, ← hspec, hw1, Sym2.eq_swap]
      · by_cases hw2 : Sym2.Mem.other hqa = v
        · exfalso
          apply nva
          refine ⟨q, hq, hq2, ?_⟩
          rw [← hspec, hw2, Sym2.eq_swap]
        · exfalso
          apply (rst (Sym2.Mem.other hqa) hw1 hw2).1
          refine ⟨q, hq, hq2, ?_⟩
          rw [Sym2.eq_swap]
          exact hspec.symm
    · rw [deg_one_iff l hndl b pb hpb hpb2 hpbb]
      intro q hq hq2 hqb
      have hspec := Sym2.other_spec hqb
      by_cases hw1 : Sym2.Mem.other hqb = v
      · apply entry_unique l hndl q pb hq hpb
        apply Subtype.ext
        rw [hpb1, ← hspec, hw1, Sym2.eq_swap]
      · by_cases hw2 : Sym2.Mem.other hqb = u
        · exfalso
          apply nub
          refine ⟨q, hq, hq2, ?_⟩
          rw [← hspec, hw2, Sym2.eq_swap]
        · exfalso
          apply (rst (Sym2.Mem.other hqb) hw2 hw1).2
          refine ⟨q, hq, hq2, ?_⟩
          rw [Sym2.eq_swap]
          exact hspec.symm

theorem cand_mask (u a : V) (l l1 : List (Edge G × Bool)) :
    IsCandidate u (mask (fun e : Edge G => u ∈ (e : Sym2 V)) l) l1 a ↔ IsCandidate u l l1 a := by
  unfold IsCandidate
  rw [mix_mask]

theorem summand_eq [DecidableRel G.Adj] (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G))
    (hnd : es.Nodup) (e : Edge G) (he : e ∉ es) (u v : V) (huv : (e : Sym2 V) = s(u, v))
    (hne : u ≠ v) (a b : V) (ha : a ≠ u ∧ a ≠ v) (hb : b ≠ u ∧ b ≠ v ∧ b ≠ a) :
    prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
        activeDegree l a = 1 ∧ activeDegree l b = 1) =
      prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
      prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
      prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
        ¬ isActive l s a ∧ ¬ isActive l s b) := by
  rw [prob3_eq_ind, prob2_eq_ind', prob2_eq_ind', prob_eq_ind]
  obtain ⟨ps, hps⟩ : ∃ ps, ps = actProbs c x es := ⟨_, rfl⟩
  rw [← hps]
  have hsupp : ps.map Prod.fst = es := by rw [hps, actProbs_fst]
  -- the three factors
  obtain ⟨Φ1, hΦ1⟩ : ∃ Φ : List (Edge G × Bool) → ℝ, Φ = fun l =>
      bern ps (fun l1 => ind (IsCandidate u l l1 a ∧ ¬ isActive l u b)) := ⟨_, rfl⟩
  obtain ⟨Φ2, hΦ2⟩ : ∃ Φ : List (Edge G × Bool) → ℝ, Φ = fun l =>
      bern ps (fun l2 => ind (IsCandidate v l l2 b ∧ ¬ isActive l v a)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : List (Edge G × Bool) → ℝ, R = fun l =>
      ind (∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b) := ⟨_, rfl⟩
  have hstep : bern ps (fun l => bern ps (fun l1 => bern ps (fun l2 =>
      ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
        activeDegree l a = 1 ∧ activeDegree l b = 1)))) =
      bern ps (fun l => Φ1 l * Φ2 l * R l) := by
    apply bern_congr
    intro l hl
    rw [hsupp] at hl
    have h1 : bern ps (fun l1 => bern ps (fun l2 =>
        ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
          activeDegree l a = 1 ∧ activeDegree l b = 1))) =
        bern ps (fun l1 => bern ps (fun l2 =>
          ind (IsCandidate u l l1 a ∧ ¬ isActive l u b) *
            ind (IsCandidate v l l2 b ∧ ¬ isActive l v a) * R l)) := by
      apply bern_congr
      intro l1 hl1
      rw [hsupp] at hl1
      apply bern_congr
      intro l2 hl2
      rw [hsupp] at hl2
      have hiff := ev_iff es hnd u v a b hne ha hb l l1 l2 hl hl1 hl2
      simp only [hR]
      by_cases h1 : IsCandidate u l l1 a ∧ ¬ isActive l u b
      · by_cases h2 : IsCandidate v l l2 b ∧ ¬ isActive l v a
        · by_cases h3 : ∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b
          · rw [ind_pos (hiff.mpr ⟨h1, h2, h3⟩), ind_pos h1, ind_pos h2, ind_pos h3]
            ring
          · rw [ind_neg (fun h => h3 (hiff.mp h).2.2), ind_neg h3]
            ring
        · rw [ind_neg (fun h => h2 (hiff.mp h).2.1), ind_neg h2]
          ring
      · rw [ind_neg (fun h => h1 (hiff.mp h).1), ind_neg h1]
        ring
    rw [h1, bern2_prod, hΦ1, hΦ2]
  rw [hstep]
  have e1 : bern ps (fun l => bern ps (fun l1 => ind (IsCandidate u l l1 a ∧ ¬ isActive l u b))) =
      bern ps Φ1 := by rw [hΦ1]
  have e2 : bern ps (fun l => bern ps (fun l2 => ind (IsCandidate v l l2 b ∧ ¬ isActive l v a))) =
      bern ps Φ2 := by rw [hΦ2]
  have e3 : bern ps (fun l => ind (∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b)) =
      bern ps R := by rw [hR]
  rw [e1, e2, e3]
  -- dependence sets
  have d1 : DepOn (fun f : Edge G => u ∈ (f : Sym2 V)) Φ1 := by
    intro l
    rw [hΦ1]
    show bern ps (fun l1 => ind (IsCandidate u l l1 a ∧ ¬ isActive l u b)) =
      bern ps (fun l1 => ind (IsCandidate u (mask (fun f : Edge G => u ∈ (f : Sym2 V)) l) l1 a ∧ ¬ isActive (mask (fun f : Edge G => u ∈ (f : Sym2 V)) l) u b))
    congr 1
    funext l1
    congr 1
    apply propext
    rw [cand_mask, act_mask (fun f : Edge G => u ∈ (f : Sym2 V)) l u b (fun f hf => by
      show u ∈ (f : Sym2 V)
      rw [hf]
      exact Sym2.mem_mk_left u b)]
  have d2 : DepOn (fun f : Edge G => v ∈ (f : Sym2 V)) Φ2 := by
    intro l
    rw [hΦ2]
    show bern ps (fun l2 => ind (IsCandidate v l l2 b ∧ ¬ isActive l v a)) =
      bern ps (fun l2 => ind (IsCandidate v (mask (fun f : Edge G => v ∈ (f : Sym2 V)) l) l2 b ∧ ¬ isActive (mask (fun f : Edge G => v ∈ (f : Sym2 V)) l) v a))
    congr 1
    funext l2
    congr 1
    apply propext
    rw [cand_mask, act_mask (fun f : Edge G => v ∈ (f : Sym2 V)) l v a (fun f hf => by
      show v ∈ (f : Sym2 V)
      rw [hf]
      exact Sym2.mem_mk_left v a)]
  have d3 : DepOn (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) R := by
    intro l
    rw [hR]
    show ind (∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b) =
      ind (∀ s : V, s ≠ u → s ≠ v → ¬ isActive (mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l) s a ∧ ¬ isActive (mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l) s b)
    congr 1
    apply propext
    constructor
    · intro h s hsu hsv
      rw [act_mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l s a, act_mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l s b]
      · exact h s hsu hsv
      · intro f hf
        show (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)
        rw [hf]
        refine ⟨Or.inr (Sym2.mem_mk_right s b), ?_, ?_⟩
        · intro h'
          rcases Sym2.mem_iff.mp h' with h'' | h''
          · exact hsu h''.symm
          · exact hb.1 h''.symm
        · intro h'
          rcases Sym2.mem_iff.mp h' with h'' | h''
          · exact hsv h''.symm
          · exact hb.2.1 h''.symm
      · intro f hf
        show (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)
        rw [hf]
        refine ⟨Or.inl (Sym2.mem_mk_right s a), ?_, ?_⟩
        · intro h'
          rcases Sym2.mem_iff.mp h' with h'' | h''
          · exact hsu h''.symm
          · exact ha.1 h''.symm
        · intro h'
          rcases Sym2.mem_iff.mp h' with h'' | h''
          · exact hsv h''.symm
          · exact ha.2 h''.symm
    · intro h s hsu hsv
      have h' := h s hsu hsv
      rw [act_mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l s a, act_mask (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) l s b] at h'
      · exact h'
      · intro f hf
        show (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)
        rw [hf]
        refine ⟨Or.inr (Sym2.mem_mk_right s b), ?_, ?_⟩
        · intro h''
          rcases Sym2.mem_iff.mp h'' with h3 | h3
          · exact hsu h3.symm
          · exact hb.1 h3.symm
        · intro h''
          rcases Sym2.mem_iff.mp h'' with h3 | h3
          · exact hsv h3.symm
          · exact hb.2.1 h3.symm
      · intro f hf
        show (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)
        rw [hf]
        refine ⟨Or.inl (Sym2.mem_mk_right s a), ?_, ?_⟩
        · intro h''
          rcases Sym2.mem_iff.mp h'' with h3 | h3
          · exact hsu h3.symm
          · exact ha.1 h3.symm
        · intro h''
          rcases Sym2.mem_iff.mp h'' with h3 | h3
          · exact hsv h3.symm
          · exact ha.2 h3.symm
  have dj1 : ∀ q ∈ ps, ¬ ((fun f : Edge G => u ∈ (f : Sym2 V)) q.1 ∧ (fun f : Edge G => v ∈ (f : Sym2 V)) q.1) := by
    rintro q hq ⟨h1, h2⟩
    have hqe : q.1 ∈ es := by
      rw [← hsupp]
      exact List.mem_map_of_mem hq
    have : q.1 = e := by
      apply Subtype.ext
      rw [huv]
      exact (Sym2.mem_and_mem_iff hne).mp ⟨h1, h2⟩
    rw [this] at hqe
    exact he hqe
  have dj2 : ∀ q ∈ ps, ¬ ((fun f => (fun f : Edge G => u ∈ (f : Sym2 V)) f ∨ (fun f : Edge G => v ∈ (f : Sym2 V)) f) q.1 ∧ (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) q.1) := by
    rintro q _ ⟨h1, h2⟩
    rcases h1 with h1 | h1
    · exact h2.2.1 h1
    · exact h2.2.2 h1
  have d12 : DepOn (fun f => (fun f : Edge G => u ∈ (f : Sym2 V)) f ∨ (fun f : Edge G => v ∈ (f : Sym2 V)) f) (fun l => Φ1 l * Φ2 l) :=
    dep_mul (dep_mono (fun f h => Or.inl h) d1) (dep_mono (fun f h => Or.inr h) d2)
  rw [bern_indep ps (fun f => (fun f : Edge G => u ∈ (f : Sym2 V)) f ∨ (fun f : Edge G => v ∈ (f : Sym2 V)) f) (fun f : Edge G => (a ∈ (f : Sym2 V) ∨ b ∈ (f : Sym2 V)) ∧ u ∉ (f : Sym2 V) ∧ v ∉ (f : Sym2 V)) (fun l => Φ1 l * Φ2 l) R dj2 d12 d3,
    bern_indep ps (fun f : Edge G => u ∈ (f : Sym2 V)) (fun f : Edge G => v ∈ (f : Sym2 V)) Φ1 Φ2 dj1 d1 d2]

theorem sum_le_hw [DecidableRel G.Adj] (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (u v : V) :
    (∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1))
        ≤ prob (actProbs c x es) (fun l => HaveWitnesses l u v) := by
  have hps := actProbs_bounds c hc x hx es hwd
  obtain ⟨ps, hpsd⟩ : ∃ ps, ps = actProbs c x es := ⟨_, rfl⟩
  rw [← hpsd]
  rw [← hpsd] at hps
  have hsupp : ps.map Prod.fst = es := by rw [hpsd, actProbs_fst]
  simp only [prob3_eq_ind, prob_eq_ind]
  have hsum : bern ps (fun l => ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
      ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
        bern ps (fun l1 => bern ps (fun l2 => ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
          activeDegree l a = 1 ∧ activeDegree l b = 1)))) =
      ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          bern ps (fun l => bern ps (fun l1 => bern ps (fun l2 => ind (IsCandidate u l l1 a ∧
            IsCandidate v l l2 b ∧ activeDegree l a = 1 ∧ activeDegree l b = 1)))) := by
    rw [bern_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [bern_sum]
  rw [← hsum]
  apply bern_mono _ hps
  intro l hl
  rw [hsupp] at hl
  have hndl : (l.map Prod.fst).Nodup := by rw [hl]; exact hnd
  -- candidate probabilities
  have hP1 : ∀ w : V, ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
      bern ps (fun l1 => ind (IsCandidate w l l1 a)) ≤ 1 := by
    intro w
    rw [← bern_sum, ← bern_const ps 1]
    apply bern_mono _ hps
    intro l1 _
    exact sum_ind_le_one _ _ (fun a a' h h' => cand_unique w l l1 a a' h h')
  have hpt : ∀ a b : V, bern ps (fun l1 => bern ps (fun l2 =>
      ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
        activeDegree l a = 1 ∧ activeDegree l b = 1))) ≤
      bern ps (fun l1 => ind (IsCandidate u l l1 a)) * bern ps (fun l2 => ind (IsCandidate v l l2 b)) *
        (ind (IsWitness l u a) * ind (IsWitness l v b)) := by
    intro a b
    rw [← bern2_prod]
    apply bern_mono _ hps
    intro l1 hl1
    rw [hsupp] at hl1
    apply bern_mono _ hps
    intro l2 hl2
    rw [hsupp] at hl2
    by_cases hJ : IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
        activeDegree l a = 1 ∧ activeDegree l b = 1
    · rw [ind_pos hJ]
      have hwa : IsWitness l u a := ⟨cand_act u a l l1 (by rw [hl, hl1]) hJ.1, hJ.2.2.1⟩
      have hwb : IsWitness l v b := ⟨cand_act v b l l2 (by rw [hl, hl2]) hJ.2.1, hJ.2.2.2⟩
      rw [ind_pos hJ.1, ind_pos hJ.2.1, ind_pos hwa, ind_pos hwb]
      norm_num
    · rw [ind_neg hJ]
      exact mul_nonneg (mul_nonneg (ind_nonneg _) (ind_nonneg _))
        (mul_nonneg (ind_nonneg _) (ind_nonneg _))
  have hbern_nn : ∀ (F : List (Edge G × Bool) → ℝ), (∀ l, 0 ≤ F l) → 0 ≤ bern ps F := by
    intro F hF
    rw [← bern_const ps 0]
    exact bern_mono _ hps _ _ (fun l _ => hF l)
  obtain ⟨A, hA⟩ : ∃ A : Finset V, A = Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v) := ⟨_, rfl⟩
  rw [← hA] at hP1
  have hsub : ∀ a, Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a) ⊆ A := by
    intro a b hb
    rw [Finset.mem_filter] at hb
    rw [hA, Finset.mem_filter]
    exact ⟨hb.1, hb.2.1, hb.2.2.1⟩
  have h1 : ∑ a ∈ A, ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
      bern ps (fun l1 => bern ps (fun l2 =>
        ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
          activeDegree l a = 1 ∧ activeDegree l b = 1))) ≤
      ∑ a ∈ A, ∑ b ∈ A, (ind (IsWitness l u a) * bern ps (fun l1 => ind (IsCandidate u l l1 a))) *
        (ind (IsWitness l v b) * bern ps (fun l2 => ind (IsCandidate v l l2 b))) := by
    apply Finset.sum_le_sum
    intro a _
    calc ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          bern ps (fun l1 => bern ps (fun l2 =>
            ind (IsCandidate u l l1 a ∧ IsCandidate v l l2 b ∧
              activeDegree l a = 1 ∧ activeDegree l b = 1)))
        ≤ ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          (ind (IsWitness l u a) * bern ps (fun l1 => ind (IsCandidate u l l1 a))) *
            (ind (IsWitness l v b) * bern ps (fun l2 => ind (IsCandidate v l l2 b))) := by
          apply Finset.sum_le_sum
          intro b _
          have := hpt a b
          linarith
      _ ≤ ∑ b ∈ A, (ind (IsWitness l u a) * bern ps (fun l1 => ind (IsCandidate u l l1 a))) *
            (ind (IsWitness l v b) * bern ps (fun l2 => ind (IsCandidate v l l2 b))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (hsub a)
          intro b _ _
          exact mul_nonneg (mul_nonneg (ind_nonneg _) (hbern_nn _ (fun _ => ind_nonneg _)))
            (mul_nonneg (ind_nonneg _) (hbern_nn _ (fun _ => ind_nonneg _)))
  rw [← Finset.sum_mul_sum] at h1
  have hW : ∀ w : V, ∑ a ∈ A, ind (IsWitness l w a) * bern ps (fun l1 => ind (IsCandidate w l l1 a)) ≤
      ind (∃ a, IsWitness l w a) := by
    intro w
    by_cases hex : ∃ a, IsWitness l w a
    · rw [ind_pos hex]
      calc ∑ a ∈ A, ind (IsWitness l w a) * bern ps (fun l1 => ind (IsCandidate w l l1 a))
          ≤ ∑ a ∈ A, bern ps (fun l1 => ind (IsCandidate w l l1 a)) := by
            apply Finset.sum_le_sum
            intro a _
            have h0 := hbern_nn (fun l1 => ind (IsCandidate w l l1 a)) (fun _ => ind_nonneg _)
            have h1' := ind_le_one (IsWitness l w a)
            nlinarith
        _ ≤ 1 := hP1 w
    · push_neg at hex
      have h0 : ∑ a ∈ A, ind (IsWitness l w a) * bern ps (fun l1 => ind (IsCandidate w l l1 a)) = 0 :=
        Finset.sum_eq_zero (fun a _ => by rw [ind_neg (hex a), zero_mul])
      rw [h0]
      exact ind_nonneg _
  have hWu := hW u
  have hWv := hW v
  have hHW : ind (∃ a, IsWitness l u a) * ind (∃ b, IsWitness l v b) = ind (HaveWitnesses l u v) := by
    by_cases h1 : ∃ a, IsWitness l u a
    · by_cases h2 : ∃ b, IsWitness l v b
      · rw [ind_pos h1, ind_pos h2, ind_pos (show HaveWitnesses l u v from ⟨h1, h2⟩)]
        ring
      · rw [ind_neg h2, ind_neg (show ¬ HaveWitnesses l u v from fun h => h2 h.2)]
        ring
    · rw [ind_neg h1, ind_neg (show ¬ HaveWitnesses l u v from fun h => h1 h.1)]
      ring
  have hn1 : 0 ≤ ∑ a ∈ A, ind (IsWitness l u a) * bern ps (fun l1 => ind (IsCandidate u l l1 a)) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (ind_nonneg _) (hbern_nn _ (fun _ => ind_nonneg _)))
  rw [hA] at h1
  rw [hA] at hWu hWv hn1
  have := mul_le_mul hWu hWv (Finset.sum_nonneg (fun a _ => mul_nonneg (ind_nonneg _)
    (hbern_nn _ (fun _ => ind_nonneg _)))) (ind_nonneg _)
  rw [hHW] at this
  linarith

end E13


/-! ### Witness bounds (eq. 15) -/

section E15

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem wit_matched (es : List (Edge G)) (hnd : es.Nodup) (l : List (Edge G × Bool))
    (hl : l.map Prod.fst = es) (w r : V) (h : IsWitness l w r) : matchedIn l w := by
  obtain ⟨⟨p, hp, hp2, hp1⟩, hdeg⟩ := h
  have hndl : (l.map Prod.fst).Nodup := by rw [hl]; exact hnd
  have hpr : r ∈ (p.1 : Sym2 V) := by rw [hp1]; exact Sym2.mem_mk_right w r
  have hpw : w ∈ (p.1 : Sym2 V) := by rw [hp1]; exact Sym2.mem_mk_left w r
  have hdu := (deg_one_iff l hndl r p hp hp2 hpr).mp hdeg
  obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hp
  have e1 : l = (l1 ++ [p]) ++ l2 := by rw [hsplit]; simp
  by_cases hE : endsFree (greedy l1) p.1
  · have hin : p.1 ∈ greedy (l1 ++ [p]) := by
      rw [greedy_snoc, if_pos ⟨hp2, hE⟩]
      exact Finset.mem_insert_self _ _
    have hin2 : p.1 ∈ greedy l := by
      rw [e1]
      exact greedy_mono _ l2 hin
    exact ⟨p.1, hin2, hpw⟩
  · unfold endsFree at hE
    push_neg at hE
    obtain ⟨g, hg, z, hz1, hz2⟩ := hE
    have hgl : g ∈ greedy l := by
      rw [hsplit]
      exact greedy_mono l1 (p :: l2) hg
    rw [hp1] at hz1
    rcases Sym2.mem_iff.mp hz1 with hzw | hzr
    · rw [hzw] at hz2
      exact ⟨g, hgl, hz2⟩
    · exfalso
      rw [hzr] at hz2
      have hgt := greedy_active l1 g hg
      have hgl' : (g, true) ∈ l := by rw [hsplit]; exact List.mem_append_left _ hgt
      have heq := hdu (g, true) hgl' rfl hz2
      have hp1' : p ∈ l1 := by rw [← heq]; exact hgt
      rw [hsplit, List.map_append, List.nodup_append] at hndl
      exact hndl.2.2 p.1 (List.mem_map_of_mem hp1') p.1 (by simp) rfl

theorem prob_inactive (T : Edge G → Prop) (ps : List (Edge G × ℝ)) :
    prob ps (fun l => ∀ p ∈ l, T p.1 → p.2 = false) =
      (ps.map (fun q => 1 - ind (T q.1) * q.2)).prod := by
  rw [prob_eq_ind]
  have h1 : bern ps (fun l => ind (∀ p ∈ l, T p.1 → p.2 = false)) =
      bern ps (fun l => (l.map (fun p => 1 - ind (T p.1 ∧ p.2 = true))).prod) := by
    apply bern_congr
    intro l _
    rw [← ind_forall (fun p => T p.1 ∧ p.2 = true) l]
    have hiff : (∀ p ∈ l, T p.1 → p.2 = false) ↔ ∀ p ∈ l, ¬ (T p.1 ∧ p.2 = true) := by
      constructor
      · rintro h p hp ⟨h1, h2⟩
        have := h p hp h1
        rw [h2] at this
        exact absurd this (by decide)
      · intro h p hp h1
        cases hb : p.2
        · rfl
        · exact absurd ⟨h1, hb⟩ (h p hp)
    by_cases h : ∀ p ∈ l, T p.1 → p.2 = false
    · rw [ind_pos h, ind_pos (hiff.mp h)]
    · rw [ind_neg h, ind_neg (fun h' => h (hiff.mpr h'))]
  rw [h1, bern_prod]
  congr 1
  apply List.map_congr_left
  intro q _
  obtain ⟨g, b⟩ := q
  dsimp only
  by_cases hr : T g
  · have h2 : T g ∧ true = true := ⟨hr, rfl⟩
    have h3 : ¬ (T g ∧ false = true) := fun h => by simp at h
    rw [ind_pos h2, ind_neg h3, ind_pos hr]
    ring
  · have h2 : ¬ (T g ∧ true = true) := fun h => hr h.1
    have h3 : ¬ (T g ∧ false = true) := fun h => hr h.1
    rw [ind_neg h2, ind_neg h3, ind_neg hr]
    ring

theorem prod_le_prod_nn : ∀ (ps : List (Edge G × ℝ)) (f g : Edge G × ℝ → ℝ),
    (∀ q ∈ ps, 0 ≤ g q ∧ g q ≤ f q) → 0 ≤ (ps.map g).prod ∧ (ps.map g).prod ≤ (ps.map f).prod
  | [], f, g, _ => by simp
  | q :: ps, f, g, h => by
    have hq := h q (by simp)
    have ih := prod_le_prod_nn ps f g (fun q' hq' => h q' (by simp [hq']))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨mul_nonneg hq.1 ih.1, ?_⟩
    exact mul_le_mul hq.2 ih.2 ih.1 (le_trans hq.1 hq.2)

theorem kappa_bound [DecidableRel G.Adj] (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ)
    (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (r : V) :
    (1 - 2 * c) / (1 - c) ≤ ((actProbs c x es).map (fun q => 1 - ind (r ∈ (q.1 : Sym2 V)) * q.2)).prod := by
  have h := noact_bound c hc0 hc x hx r es hnd hwd
  have hS := xsum_le_one x hx es r
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have h2 : (1 - 2 * c) / (1 - c) ≤
      (1 - c - c * ∑ g ∈ es.toFinset.filter (fun g : Edge G => r ∈ (g : Sym2 V)), x g) / (1 - c) := by
    apply div_le_div_of_nonneg_right _ h1c.le
    nlinarith [mul_le_mul_of_nonneg_left hS hc0.le]
  linarith

theorem three_ge (u v a b : V) (huv : u ≠ v) (ha : a ≠ u ∧ a ≠ v) (hb : b ≠ u ∧ b ≠ v ∧ b ≠ a)
    (q : Edge G × ℝ) (hq : 0 ≤ q.2 ∧ q.2 ≤ 1) :
    0 ≤ (1 - ind (a ∈ (q.1 : Sym2 V)) * q.2) * (1 - ind (b ∈ (q.1 : Sym2 V)) * q.2) ∧
    (1 - ind (a ∈ (q.1 : Sym2 V)) * q.2) * (1 - ind (b ∈ (q.1 : Sym2 V)) * q.2) ≤
      (1 - ind ((q.1 : Sym2 V) = s(u, b)) * q.2) * (1 - ind ((q.1 : Sym2 V) = s(v, a)) * q.2) *
        (1 - ind (∃ s : V, s ≠ u ∧ s ≠ v ∧ ((q.1 : Sym2 V) = s(s, a) ∨ (q.1 : Sym2 V) = s(s, b))) * q.2) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hia := ind_nonneg (a ∈ (q.1 : Sym2 V))
  have hia1 := ind_le_one (a ∈ (q.1 : Sym2 V))
  have hib := ind_nonneg (b ∈ (q.1 : Sym2 V))
  have hib1 := ind_le_one (b ∈ (q.1 : Sym2 V))
  have hA0 : 0 ≤ 1 - ind (a ∈ (q.1 : Sym2 V)) * q.2 := by nlinarith
  have hB0 : 0 ≤ 1 - ind (b ∈ (q.1 : Sym2 V)) * q.2 := by nlinarith
  have hA1 : 1 - ind (a ∈ (q.1 : Sym2 V)) * q.2 ≤ 1 := by nlinarith
  have hB1 : 1 - ind (b ∈ (q.1 : Sym2 V)) * q.2 ≤ 1 := by nlinarith
  refine ⟨mul_nonneg hA0 hB0, ?_⟩
  by_cases h1 : (q.1 : Sym2 V) = s(u, b)
  · have hbq : b ∈ (q.1 : Sym2 V) := by rw [h1]; exact Sym2.mem_mk_right u b
    have h2 : ¬ (q.1 : Sym2 V) = s(v, a) := by
      rw [h1]
      intro h
      rcases Sym2.eq_iff.mp h with h' | h'
      · exact huv h'.1
      · exact ha.1 h'.1.symm
    have h3 : ¬ ∃ s : V, s ≠ u ∧ s ≠ v ∧ ((q.1 : Sym2 V) = s(s, a) ∨ (q.1 : Sym2 V) = s(s, b)) := by
      rintro ⟨s, hsu, hsv, hs | hs⟩
      · rw [h1] at hs
        rcases Sym2.eq_iff.mp hs with h' | h'
        · exact hsu h'.1.symm
        · exact ha.1 h'.1.symm
      · rw [h1] at hs
        rcases Sym2.eq_iff.mp hs with h' | h'
        · exact hsu h'.1.symm
        · exact hb.1 h'.1.symm
    rw [ind_pos h1, ind_neg h2, ind_neg h3, ind_pos hbq]
    nlinarith
  · by_cases h2 : (q.1 : Sym2 V) = s(v, a)
    · have haq : a ∈ (q.1 : Sym2 V) := by rw [h2]; exact Sym2.mem_mk_right v a
      have h3 : ¬ ∃ s : V, s ≠ u ∧ s ≠ v ∧ ((q.1 : Sym2 V) = s(s, a) ∨ (q.1 : Sym2 V) = s(s, b)) := by
        rintro ⟨s, hsu, hsv, hs | hs⟩
        · rw [h2] at hs
          rcases Sym2.eq_iff.mp hs with h' | h'
          · exact hsv h'.1.symm
          · exact ha.2 h'.1.symm
        · rw [h2] at hs
          rcases Sym2.eq_iff.mp hs with h' | h'
          · exact hb.2.2 h'.2.symm
          · exact hb.2.1 h'.1.symm
      rw [ind_neg h1, ind_pos h2, ind_neg h3, ind_pos haq]
      nlinarith
    · by_cases h3 : ∃ s : V, s ≠ u ∧ s ≠ v ∧ ((q.1 : Sym2 V) = s(s, a) ∨ (q.1 : Sym2 V) = s(s, b))
      · have hab : a ∈ (q.1 : Sym2 V) ∨ b ∈ (q.1 : Sym2 V) := by
          obtain ⟨s, _, _, hs | hs⟩ := h3
          · left
            rw [hs]
            exact Sym2.mem_mk_right s a
          · right
            rw [hs]
            exact Sym2.mem_mk_right s b
        rw [ind_neg h1, ind_neg h2, ind_pos h3]
        rcases hab with haq | hbq
        · rw [ind_pos haq]
          nlinarith
        · rw [ind_pos hbq]
          nlinarith
      · rw [ind_neg h1, ind_neg h2, ind_neg h3]
        nlinarith

end E15


section E15m

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem prob2_comm (ps : List (Edge G × ℝ)) (A B : List (Edge G × Bool) → List (Edge G × Bool) → Prop) :
    prob2 ps (fun l l' => A l l' ∧ B l l') = prob2 ps (fun l l' => B l l' ∧ A l l') := by
  rw [prob2_eq_ind', prob2_eq_ind']
  congr 1
  funext l
  congr 1
  funext l'
  congr 1
  exact propext and_comm

theorem xPair_nonneg [DecidableRel G.Adj] (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G))
    (a s : V) : 0 ≤ xPair x es a s := by
  rw [xPair_eq]
  exact Finset.sum_nonneg (fun f _ => hx.1 f)

theorem sum_B (u v a : V) (ha : a ≠ u ∧ a ≠ v) (f : V → ℝ) :
    ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a), f b =
      ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v), f b - f a := by
  have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v))
    (fun b => b ≠ a) f
  have h2 : (Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v)).filter (fun b => b ≠ a) =
      Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have h3 : (Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v)).filter (fun b => ¬ b ≠ a) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, not_not]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · rintro rfl
      exact ⟨ha, rfl⟩
  rw [h2, h3, Finset.sum_singleton] at h1
  linarith

theorem term_bound [DecidableRel G.Adj] (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ)
    (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (u v : V)
    (hne : u ≠ v) (a b : V) (ha : a ≠ u ∧ a ≠ v) (hb : b ≠ u ∧ b ≠ v ∧ b ≠ a) :
    c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * (xPair x es u a * xPair x es v b) ≤
      prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
      prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
      prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
        ¬ isActive l s a ∧ ¬ isActive l s b) := by
  have hps := actProbs_bounds c hc0.le x hx es hwd
  have hA := lemma54 c hc0.le x hx es hnd hwd u b a hb.2.2
  rw [cand_prob c hc0.le x es hnd hwd u a, prob2_comm] at hA
  have hB := lemma54 c hc0.le x hx es hnd hwd v a b (Ne.symm hb.2.2)
  rw [cand_prob c hc0.le x es hnd hwd v b, prob2_comm] at hB
  obtain ⟨ps, hpsd⟩ : ∃ ps, ps = actProbs c x es := ⟨_, rfl⟩
  rw [← hpsd] at hA hB hps ⊢
  have e1 : prob ps (fun l => ¬ isActive l u b) =
      prob ps (fun l => ∀ p ∈ l, (fun f : Edge G => (f : Sym2 V) = s(u, b)) p.1 → p.2 = false) := by
    rw [prob_eq_ind, prob_eq_ind]
    congr 1
    funext l
    congr 1
    apply propext
    constructor
    · intro h p hp hp1
      cases hb2 : p.2
      · rfl
      · exact absurd ⟨p, hp, hb2, hp1⟩ h
    · rintro h ⟨p, hp, hp2, hp1⟩
      have := h p hp hp1
      rw [hp2] at this
      exact absurd this (by decide)
  have e2 : prob ps (fun l => ¬ isActive l v a) =
      prob ps (fun l => ∀ p ∈ l, (fun f : Edge G => (f : Sym2 V) = s(v, a)) p.1 → p.2 = false) := by
    rw [prob_eq_ind, prob_eq_ind]
    congr 1
    funext l
    congr 1
    apply propext
    constructor
    · intro h p hp hp1
      cases hb2 : p.2
      · rfl
      · exact absurd ⟨p, hp, hb2, hp1⟩ h
    · rintro h ⟨p, hp, hp2, hp1⟩
      have := h p hp hp1
      rw [hp2] at this
      exact absurd this (by decide)
  have e3 : prob ps (fun l => ∀ s : V, s ≠ u → s ≠ v → ¬ isActive l s a ∧ ¬ isActive l s b) =
      prob ps (fun l => ∀ p ∈ l, (fun f : Edge G => ∃ s : V, s ≠ u ∧ s ≠ v ∧
        ((f : Sym2 V) = s(s, a) ∨ (f : Sym2 V) = s(s, b))) p.1 → p.2 = false) := by
    rw [prob_eq_ind, prob_eq_ind]
    congr 1
    funext l
    congr 1
    apply propext
    constructor
    · rintro h p hp ⟨s, hsu, hsv, hs⟩
      cases hb2 : p.2
      · rfl
      · exfalso
        rcases hs with hs | hs
        · exact (h s hsu hsv).1 ⟨p, hp, hb2, hs⟩
        · exact (h s hsu hsv).2 ⟨p, hp, hb2, hs⟩
    · intro h s hsu hsv
      constructor
      · rintro ⟨p, hp, hp2, hp1⟩
        have := h p hp ⟨s, hsu, hsv, Or.inl hp1⟩
        rw [hp2] at this
        exact absurd this (by decide)
      · rintro ⟨p, hp, hp2, hp1⟩
        have := h p hp ⟨s, hsu, hsv, Or.inr hp1⟩
        rw [hp2] at this
        exact absurd this (by decide)
  obtain ⟨L1, hL1⟩ : ∃ L, L = prob ps (fun l => ¬ isActive l u b) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L, L = prob ps (fun l => ¬ isActive l v a) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ L, L = prob ps (fun l => ∀ s : V, s ≠ u → s ≠ v →
      ¬ isActive l s a ∧ ¬ isActive l s b) := ⟨_, rfl⟩
  have hL1n : 0 ≤ L1 := by rw [hL1]; exact prob_nonneg ps hps _
  have hL2n : 0 ≤ L2 := by rw [hL2]; exact prob_nonneg ps hps _
  have hRn : 0 ≤ R := by rw [hR]; exact prob_nonneg ps hps _
  have hprod : L1 * L2 * R =
      (ps.map (fun q => (1 - ind ((fun f : Edge G => (f : Sym2 V) = s(u, b)) q.1) * q.2) *
        (1 - ind ((fun f : Edge G => (f : Sym2 V) = s(v, a)) q.1) * q.2) *
        (1 - ind ((fun f : Edge G => ∃ s : V, s ≠ u ∧ s ≠ v ∧
          ((f : Sym2 V) = s(s, a) ∨ (f : Sym2 V) = s(s, b))) q.1) * q.2))).prod := by
    rw [hL1, hL2, hR, e1, e2, e3,
      prob_inactive (fun f : Edge G => (f : Sym2 V) = s(u, b)) ps,
      prob_inactive (fun f : Edge G => (f : Sym2 V) = s(v, a)) ps,
      prob_inactive (fun f : Edge G => ∃ s : V, s ≠ u ∧ s ≠ v ∧
        ((f : Sym2 V) = s(s, a) ∨ (f : Sym2 V) = s(s, b))) ps,
      ← List.prod_map_mul, ← List.prod_map_mul]
  have hge := prod_le_prod_nn ps
    (fun q => (1 - ind ((fun f : Edge G => (f : Sym2 V) = s(u, b)) q.1) * q.2) *
        (1 - ind ((fun f : Edge G => (f : Sym2 V) = s(v, a)) q.1) * q.2) *
        (1 - ind ((fun f : Edge G => ∃ s : V, s ≠ u ∧ s ≠ v ∧
          ((f : Sym2 V) = s(s, a) ∨ (f : Sym2 V) = s(s, b))) q.1) * q.2))
    (fun q => (1 - ind (a ∈ (q.1 : Sym2 V)) * q.2) * (1 - ind (b ∈ (q.1 : Sym2 V)) * q.2))
    (fun q hq => three_ge u v a b hne ha hb q (hps q hq))
  have hgs : (ps.map (fun q => (1 - ind (a ∈ (q.1 : Sym2 V)) * q.2) *
      (1 - ind (b ∈ (q.1 : Sym2 V)) * q.2))).prod =
      (ps.map (fun q => 1 - ind (a ∈ (q.1 : Sym2 V)) * q.2)).prod *
        (ps.map (fun q => 1 - ind (b ∈ (q.1 : Sym2 V)) * q.2)).prod := List.prod_map_mul
  have ka := kappa_bound c hc0 hc x hx es hnd hwd a
  have kb := kappa_bound c hc0 hc x hx es hnd hwd b
  rw [← hpsd] at ka kb
  have hκ0 : 0 ≤ (1 - 2 * c) / (1 - c) := by
    apply div_nonneg <;> linarith
  have hkk : ((1 - 2 * c) / (1 - c)) ^ 2 ≤ L1 * L2 * R := by
    rw [hprod, sq]
    have := mul_le_mul ka kb hκ0 (le_trans hκ0 ka)
    rw [← hgs] at this
    linarith [hge.2]
  rw [← hL1] at hA
  rw [← hL2] at hB
  rw [← hR]
  have hxa := xPair_nonneg x hx es u a
  have hxb := xPair_nonneg x hx es v b
  have hP1 : 0 ≤ L1 * (c * xPair x es u a) := mul_nonneg hL1n (mul_nonneg hc0.le hxa)
  have hP2 : 0 ≤ L2 * (c * xPair x es v b) := mul_nonneg hL2n (mul_nonneg hc0.le hxb)
  have h1 := mul_le_mul hA hB hP2 (le_trans hP1 hA)
  have h2 := mul_le_mul_of_nonneg_right h1 hRn
  have h3 : c ^ 2 * (xPair x es u a * xPair x es v b) * ((1 - 2 * c) / (1 - c)) ^ 2 ≤
      c ^ 2 * (xPair x es u a * xPair x es v b) * (L1 * L2 * R) :=
    mul_le_mul_of_nonneg_left hkk (mul_nonneg (sq_nonneg c) (mul_nonneg hxa hxb))
  nlinarith [h2, h3]

end E15m


section E15main

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem eq15_main [DecidableRel G.Adj]
    (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (e : Edge G) (he : e ∉ es) (u v : V)
    (huv : (e : Sym2 V) = s(u, v)) (hwd : WellDefinedOn c x es) :
    1 - c * (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
        + ∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + prob (actProbs c x es) (fun l => HaveWitnesses l u v) ≤ unmatchedAt c x es e ∧
      1 - c * (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 *
          ((∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s) *
              (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
            - ∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s * xPair x es v s)
        ≤ 1 - c * (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
          + prob (actProbs c x es) (fun l => HaveWitnesses l u v) := by
  have hne : u ≠ v := by
    intro h
    have hd := SimpleGraph.not_isDiag_of_mem_edgeSet G e.2
    apply hd
    rw [huv, h, Sym2.mk_isDiag_iff]
  have hps := actProbs_bounds c hc0.le x hx es hwd
  constructor
  · have hu1 := xsum_eq x es e he u v huv
    have hvu : (e : Sym2 V) = s(v, u) := by rw [huv, Sym2.eq_swap]
    have hv1 := xsum_eq x es e he v u hvu
    have hfc : Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v) = Finset.univ.filter (fun s => s ≠ v ∧ s ≠ u) := by
      apply Finset.filter_congr
      intro s _
      exact And.comm
    have hmu := matched_le c hc0.le x hx es hnd hwd u
    have hmv := matched_le c hc0.le x hx es hnd hwd v
    have heq := unmatched_eq c x es e u v huv
    have hHW : prob (actProbs c x es) (fun l => HaveWitnesses l u v) ≤
        prob (actProbs c x es) (fun l => matchedIn l u ∧ matchedIn l v) := by
      rw [prob_eq_ind, prob_eq_ind]
      apply bern_mono _ hps
      intro l hl
      rw [actProbs_fst] at hl
      by_cases h : HaveWitnesses l u v
      · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
        have hm : matchedIn l u ∧ matchedIn l v :=
          ⟨wit_matched es hnd l hl u a ha, wit_matched es hnd l hl v b hb⟩
        rw [ind_pos hm]
        exact ind_le_one _
      · rw [ind_neg h]
        exact ind_nonneg _
    rw [← hfc] at hv1
    rw [hu1, hv1, heq]
    linarith
  · have hle := sum_le_hw c hc0.le x hx es hnd hwd u v
    have hrw : (∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1)) =
        ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
          ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
            prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
            prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
            prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
              ¬ isActive l s a ∧ ¬ isActive l s b) :=
      Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb =>
        summand_eq c x es hnd e he u v huv hne a b (Finset.mem_filter.mp ha).2
          (Finset.mem_filter.mp hb).2))
    rw [hrw] at hle
    have hterm : ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * (xPair x es u a * xPair x es v b) ≤
        ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
          ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
            prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
            prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
            prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
              ¬ isActive l s a ∧ ¬ isActive l s b) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact term_bound c hc0 hc x hx es hnd hwd u v hne a b (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2
    have hid : ∑ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * (xPair x es u a * xPair x es v b) =
        c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 *
          ((∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s) *
              (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
            - ∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s * xPair x es v s) := by
      have h1 : ∀ a ∈ Finset.univ.filter (fun a => a ≠ u ∧ a ≠ v),
          ∑ b ∈ Finset.univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
            c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * (xPair x es u a * xPair x es v b) =
          c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * (xPair x es u a *
            (∑ s ∈ Finset.univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s) -
              xPair x es u a * xPair x es v a) := by
        intro a ha
        rw [sum_B u v a (Finset.mem_filter.mp ha).2, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    linarith

end E15main

end Aux_ProphetMatchingEFGT_eq_15

open Finset ProphetMatchingEFGT Aux_ProphetMatchingEFGT_eq_15 in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (e : Edge G) (he : e ∉ es) (u v : V)
    (huv : (e : Sym2 V) = s(u, v)) (hwd : WellDefinedOn c x es) :
    1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
        + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + prob (actProbs c x es) (fun l => HaveWitnesses l u v) ≤ unmatchedAt c x es e ∧
      1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
        + c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 *
          ((∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s) *
              (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
            - ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s * xPair x es v s)
        ≤ 1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es v s)
          + prob (actProbs c x es) (fun l => HaveWitnesses l u v) :=
  eq15_main c hc0 hc x hx es hnd e he u v huv hwd

