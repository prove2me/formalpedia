-- Prove2me | solution 1 for ProphetMatchingEFGT.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:07:11.998401+00:00
-- url     : https://prove2.me/submissions/e570e531-efe1-4d7c-9077-b8412ec84036

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

namespace Aux_ProphetMatchingEFGT_eq_13

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

end Aux_ProphetMatchingEFGT_eq_13

open Finset ProphetMatchingEFGT Aux_ProphetMatchingEFGT_eq_13 in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (u v : V) (huv : (e : Sym2 V) = s(u, v))
    (hwd : WellDefinedOn c x es) :
    (∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1))
        ≤ prob (actProbs c x es) (fun l => HaveWitnesses l u v) ∧
      (∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
        ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
          prob3 (actProbs c x es) (fun l l₁ l₂ => IsCandidate u l l₁ a ∧ IsCandidate v l l₂ b ∧
            activeDegree l a = 1 ∧ activeDegree l b = 1))
        = ∑ a ∈ univ.filter (fun a => a ≠ u ∧ a ≠ v),
            ∑ b ∈ univ.filter (fun b => b ≠ u ∧ b ≠ v ∧ b ≠ a),
              prob2 (actProbs c x es) (fun l l₁ => IsCandidate u l l₁ a ∧ ¬ isActive l u b) *
              prob2 (actProbs c x es) (fun l l₂ => IsCandidate v l l₂ b ∧ ¬ isActive l v a) *
              prob (actProbs c x es) (fun l => ∀ s : V, s ≠ u → s ≠ v →
                ¬ isActive l s a ∧ ¬ isActive l s b) := by
  have hne : u ≠ v := by
    intro h
    have hd := SimpleGraph.not_isDiag_of_mem_edgeSet G e.2
    apply hd
    rw [huv, h, Sym2.mk_isDiag_iff]
  refine ⟨sum_le_hw c hc x hx es hnd hwd u v, ?_⟩
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_filter] at ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_filter] at hb
  exact summand_eq c x es hnd e he u v huv hne a b ha.2 hb.2

