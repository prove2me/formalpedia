-- Prove2me | solution 1 for ProphetMatchingEFGT.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:52:57.252977+00:00
-- url     : https://prove2.me/submissions/d069ddc9-f4bc-4beb-9184-355123da15b3

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

namespace Aux_ProphetMatchingEFGT_lemma_5_4

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

end Aux_ProphetMatchingEFGT_lemma_5_4

open Finset ProphetMatchingEFGT Aux_ProphetMatchingEFGT_lemma_5_4 in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (hwd : WellDefinedOn c x es) (u i j : V) (hij : i ≠ j) :
    prob (actProbs c x es) (fun l => ¬ isActive l u i) *
        prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' j) ≤
      prob2 (actProbs c x es) (fun l l' => ¬ isActive l u i ∧ IsCandidate u l l' j) :=
  lemma54 c hc x hx es hnd hwd u i j hij

