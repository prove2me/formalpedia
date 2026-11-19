-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.sampling_monomial_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:33:02.659205+00:00
-- url     : https://prove2.me/submissions/3b1e0f48-1c63-4edb-9f8b-f94224f62fe1

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_topology_pattern_comparison
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_5
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness.MonomialProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def Other {n colors : ℕ} (e : ColoredEdge n colors) (u : Fin n) : Fin n :=
  if e.1 = u then e.2.1 else e.1

private lemma reconstruct {n colors : ℕ} (e : ColoredEdge n colors) (u : Fin n)
    (he : e.1 < e.2.1) (hu : Incident e u) :
    e = (min u (Other e u),max u (Other e u),e.2.2) := by
  rcases hu with h | h
  · subst u
    simp [Other,min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)]
  · subst u
    simp [Other,ne_of_lt he,min_eq_right (le_of_lt he),max_eq_left (le_of_lt he)]

private lemma response_some {n colors : ℕ} (F : Finset (ColoredEdge n colors)) (hF : Consistent F)
    (b : ColoredEdge n colors → Bool) (u v : Fin n) (j : Fin colors) (s : Bool) :
    SignedResponse F b (u,j) = some (v,s) ↔
      ∃ e ∈ F, e.2.2 = j ∧ Incident e u ∧ Other e u = v ∧ b e = s := by
  unfold SignedResponse
  split_ifs with h
  · have hc := h.choose_spec
    constructor
    · intro hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      exact ⟨h.choose,hc.1,hc.2.1,hc.2.2,hs.1,hs.2⟩
    · rintro ⟨e,he,hj,hu,hv,hb⟩
      have hh : h.choose = e := hF.2 h.choose hc.1 e he (hc.2.1.trans hj.symm)
        ⟨u,hc.2.2,hu⟩
      simp only [hh, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hv,hb⟩
  · constructor
    · simp
    · rintro ⟨e,he,hj,hu,_,_⟩
      exact (h ⟨e,he,hj,hu⟩).elim


private def Fits {N colors : ℕ} (T : GraphTable N colors) (F : Finset (ColoredEdge N colors))
    (b : ColoredEdge N colors → Bool) : Prop :=
  ∀ az ∈ T.val, LiftOracle (SignedResponse F b) az.1 = some az.2

private def Observed {N colors : ℕ} (az : Address N colors × (Fin N × Bool)) (u : Fin N) : ColoredEdge N colors :=
  (min u az.2.1,max u az.2.1,az.1.2)

private lemma pattern_member {N colors : ℕ} (T : GraphTable N colors) (e : ColoredEdge N colors) :
    e ∈ PatternOf T ↔ ∃ az ∈ T.val, ∃ u, az.1.1 = some u ∧ Observed az u = e := by
  unfold PatternOf
  constructor
  · intro he
    obtain ⟨az,haz,he⟩ := mem_biUnion.mp he
    cases hu : az.1.1 with
    | none => simp only [hu,notMem_empty] at he
    | some u =>
      refine ⟨az,haz,u,hu,?_⟩
      have hh : e = Observed az u := by simpa only [hu,mem_singleton,Observed] using he
      exact hh.symm
  · rintro ⟨az,haz,u,hu,rfl⟩
    exact mem_biUnion.mpr ⟨az,haz,by simp only [hu,Observed,mem_singleton]⟩

private lemma fits_observation {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (b : ColoredEdge N colors → Bool)
    (hfit : Fits T F b) (az : Address N colors × (Fin N × Bool)) (haz : az ∈ T.val)
    (u : Fin N) (hu : az.1.1 = some u) : Observed az u ∈ F ∧ b (Observed az u) = az.2.2 := by
  have hr := hfit az haz
  have hresp : SignedResponse F b (u,az.1.2) = some az.2 := by
    simpa only [LiftOracle,hu] using hr
  obtain ⟨e,he,hj,hei,heo,heb⟩ := (response_some F hF b u az.2.1 az.1.2 az.2.2).mp hresp
  have heq : e = Observed az u := by
    rw [reconstruct e u (hF.1 e he) hei]
    simp only [Observed,heo,hj]
  simpa only [heq] using (show e ∈ F ∧ b e = az.2.2 from ⟨he,heb⟩)

private lemma fits_subset {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (b : ColoredEdge N colors → Bool)
    (hfit : Fits T F b) : PatternOf T ⊆ F := by
  intro e he
  obtain ⟨az,haz,u,hu,rfl⟩ := (pattern_member T e).mp he
  exact (fits_observation T F hF b hfit az haz u hu).1

private lemma observed_from_endpoints {N colors : ℕ} (az : Address N colors × (Fin N × Bool))
    (e : ColoredEdge N colors) (he : e.1 < e.2.1) (hc : az.1.2 = e.2.2)
    (hp : (az.1.1 = some e.1 ∧ az.2.1 = e.2.1) ∨ (az.1.1 = some e.2.1 ∧ az.2.1 = e.1)) :
    ∃ u, az.1.1 = some u ∧ Observed az u = e := by
  rcases hp with hp | hp
  · refine ⟨e.1,hp.1,?_⟩
    simp only [Observed,hp.2,hc,min_eq_left he.le,max_eq_right he.le]
  · refine ⟨e.2.1,hp.1,?_⟩
    simp only [Observed,hp.2,hc,min_eq_right he.le,max_eq_left he.le]

private lemma observed_endpoints {N colors : ℕ} (az : Address N colors × (Fin N × Bool))
    (u : Fin N) (hu : az.1.1 = some u) :
    (az.1.1 = some (Observed az u).1 ∧ az.2.1 = (Observed az u).2.1) ∨
      (az.1.1 = some (Observed az u).2.1 ∧ az.2.1 = (Observed az u).1) := by
  by_cases h : u ≤ az.2.1
  · simp only [Observed,min_eq_left h,max_eq_right h,hu,true_and,true_or]
  · have h' := le_of_not_ge h
    simp only [Observed,min_eq_right h',max_eq_left h',hu,true_and,or_true]

private lemma pattern_sign_of_fits {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (b : ColoredEdge N colors → Bool)
    (hfit : Fits T F b) (e : ColoredEdge N colors) (he : e ∈ PatternOf T) : PatternSign T e = b e := by
  have heF := fits_subset T F hF b hfit he
  cases hbe : b e with
  | false =>
    simp only [hbe,PatternSign,decide_eq_false_iff_not]
    rintro ⟨az,haz,htrue,hc,hp⟩
    obtain ⟨u,hu,heq⟩ := observed_from_endpoints az e (hF.1 e heF) hc hp
    have hh := (fits_observation T F hF b hfit az haz u hu).2
    rw [heq,hbe,htrue] at hh
    contradiction
  | true =>
    simp only [hbe,PatternSign,decide_eq_true_eq]
    obtain ⟨az,haz,u,hu,heq⟩ := (pattern_member T e).mp he
    have hh := (fits_observation T F hF b hfit az haz u hu).2
    have htrue : az.2.2 = true := by rw [heq,hbe] at hh; exact hh.symm
    refine ⟨az,haz,htrue,?_,?_⟩
    · rw [← heq]; rfl
    · rw [← heq]; exact observed_endpoints az u hu

private lemma consistent_subset {N colors : ℕ} (F G : Finset (ColoredEdge N colors))
    (hG : Consistent G) (hFG : F ⊆ G) : Consistent F :=
  ⟨fun e he => hG.1 e (hFG he),fun e he f hf hc hu => hG.2 e (hFG he) f (hFG hf) hc hu⟩

private lemma fits_dummy {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) (hfit : Fits T F b)
    (az : Address N colors × (Fin N × Bool)) (haz : az ∈ T.val) : az.1.1 ≠ none := by
  intro h
  have hh := hfit az haz
  simp only [LiftOracle,h] at hh
  contradiction

private lemma fits_transport {N colors : ℕ} (T : GraphTable N colors)
    (F G : Finset (ColoredEdge N colors)) (hF : Consistent F) (hG : Consistent G)
    (b b' : ColoredEdge N colors → Bool) (hsub : F ⊆ G) (heq : ∀ e ∈ F, b e = b' e)
    (hfit : Fits T F b) : Fits T G b' := by
  intro az haz
  cases hu : az.1.1 with
  | none => exact ((fits_dummy T F b hfit az haz) hu).elim
  | some u =>
    have hr : SignedResponse F b (u,az.1.2) = some az.2 := by
      simpa only [LiftOracle,hu] using hfit az haz
    obtain ⟨e,he,hj,hei,heo,heb⟩ := (response_some F hF b u az.2.1 az.1.2 az.2.2).mp hr
    have ht := (response_some G hG b' u az.2.1 az.1.2 az.2.2).mpr
      ⟨e,hsub he,hj,hei,heo,(heq e he).symm.trans heb⟩
    simpa only [LiftOracle,hu] using ht

private lemma fits_consistent {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (b : ColoredEdge N colors → Bool)
    (hfit : Fits T F b) : ConsistentTable T := by
  have hsub := fits_subset T F hF b hfit
  have hP := consistent_subset (PatternOf T) F hF hsub
  refine ⟨hP,?_⟩
  intro az haz
  cases hu : az.1.1 with
  | none => exact ((fits_dummy T F b hfit az haz) hu).elim
  | some u =>
    have hr : SignedResponse F b (u,az.1.2) = some az.2 := by
      simpa only [LiftOracle,hu] using hfit az haz
    obtain ⟨e,he,hj,hei,heo,heb⟩ := (response_some F hF b u az.2.1 az.1.2 az.2.2).mp hr
    have heq : e = Observed az u := by
      rw [reconstruct e u (hF.1 e he) hei]
      simp only [Observed,heo,hj]
    have heP : e ∈ PatternOf T := (pattern_member T e).mpr ⟨az,haz,u,hu,heq.symm⟩
    have hbP : PatternSign T e = az.2.2 := (pattern_sign_of_fits T F hF b hfit e heP).trans heb
    have ht := (response_some (PatternOf T) hP (PatternSign T) u az.2.1 az.1.2 az.2.2).mpr
      ⟨e,heP,hj,hei,heo,hbP⟩
    simpa only [LiftOracle,hu] using ht

private lemma fits_iff {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (b : ColoredEdge N colors → Bool) :
    Fits T F b ↔ ConsistentTable T ∧ PatternOf T ⊆ F ∧ ∀ e ∈ PatternOf T, b e = PatternSign T e := by
  constructor
  · intro hfit
    exact ⟨fits_consistent T F hF b hfit,fits_subset T F hF b hfit,
      fun e he => (pattern_sign_of_fits T F hF b hfit e he).symm⟩
  · rintro ⟨hT,hsub,hb⟩
    exact fits_transport T (PatternOf T) F hT.1 hF (PatternSign T) b hsub
      (fun e he => (hb e he).symm) hT.2

private lemma indicator_product {N colors : ℕ} (T : GraphTable N colors)
    (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) :
    (∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az) =
      if Fits T F b then (1:ℝ) else 0 := by
  by_cases hfit : Fits T F b
  · rw [if_pos hfit]
    exact prod_eq_one (fun az haz => if_pos (hfit az haz))
  · rw [if_neg hfit]
    unfold Fits at hfit
    push Not at hfit
    obtain ⟨az,haz,hazbad⟩ := hfit
    exact Finset.prod_eq_zero haz (if_neg hazbad)

private lemma average_product {I α : Type*} [Fintype I] [Fintype α] [DecidableEq I]
    (f : I → α → ℝ) :
    Average univ (fun x : I → α => ∏ i, f i (x i)) = ∏ i, Average univ (f i) := by
  unfold Average
  simp only [card_univ,Fintype.card_fun]
  rw [← Fintype.prod_sum f,Finset.prod_div_distrib]
  simp


private lemma assignment_cylinder {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (target : α → Bool) :
    Average univ (fun b : α → Bool => if ∀ a ∈ S, b a = target a then (1:ℝ) else 0) =
      (2:ℝ)^(-(S.card:ℤ)) := by
  let f := fun a z => if a ∈ S then (if z = target a then (1:ℝ) else 0) else 1
  have hfun (b : α → Bool) : (if ∀ a ∈ S, b a = target a then (1:ℝ) else 0) =
      ∏ a : α, f a (b a) := by
    by_cases hb : ∀ a ∈ S, b a = target a
    · rw [if_pos hb]
      symm
      apply prod_eq_one
      intro a ha
      by_cases hS : a ∈ S
      · simp only [f,if_pos hS,if_pos (hb a hS)]
      · simp only [f,if_neg hS]
    · rw [if_neg hb]
      symm
      push Not at hb
      obtain ⟨a,ha,hab⟩ := hb
      apply Finset.prod_eq_zero (mem_univ a)
      simp only [f,if_pos ha,if_neg hab]
  simp_rw [hfun]
  rw [average_product f]
  have havg (a : α) : Average univ (f a) = if a ∈ S then (1/2:ℝ) else 1 := by
    by_cases ha : a ∈ S
    · cases ht : target a <;> simp [f,ha,ht,Average,Fintype.sum_bool]
    · simp [f,ha,Average]
  simp_rw [havg]
  rw [Fintype.prod_ite_mem,Finset.prod_const,one_div,inv_pow,zpow_neg,zpow_natCast]

private lemma yes_event_probability {N colors : ℕ} (G P : Finset (ColoredEdge N colors))
    (p : ColoredEdge N colors → Bool) :
    SigningAverage .yes G (fun b => if ∀ e ∈ P, b e = p e then (1:ℝ) else 0) = SignProbYes P p := by
  unfold SigningAverage SignProbYes Average
  simp only [card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  congr 1
  rw [← Finset.sum_filter]
  simp

private lemma no_event_probability {N colors : ℕ} (G P : Finset (ColoredEdge N colors))
    (hsub : P ⊆ G) (hP : Consistent P) (p : ColoredEdge N colors → Bool) :
    SigningAverage .no G (fun b => if ∀ e ∈ P, b e = p e then (1:ℝ) else 0) = SignProbNo P p := by
  let S : Finset {e // e ∈ G} := univ.filter (fun e => e.val ∈ P)
  let hequiv : {a : {e // e ∈ G} // a.val ∈ P} ≃ {e // e ∈ P} := {
    toFun a := ⟨a.val.val,a.property⟩
    invFun a := ⟨⟨a.val,hsub a.property⟩,a.property⟩
    left_inv a := rfl
    right_inv a := rfl }
  have hcard : S.card = P.card := by
    have hh := Fintype.card_congr hequiv
    simpa only [S,Fintype.card_subtype,Fintype.card_coe,filter_mem_eq_inter,univ_inter] using hh
  have hh := assignment_cylinder S (fun e => p e.val)
  have hprop (b : {e // e ∈ G} → Bool) :
      (∀ e ∈ P, (if h : e ∈ G then b ⟨e,h⟩ else false) = p e) ↔
      (∀ a ∈ S, b a = p a.val) := by
    constructor
    · intro hb a ha
      have haP := (mem_filter.mp ha).2
      simpa only [dif_pos a.property] using hb a.val haP
    · intro hb e he
      have ha : (⟨e,hsub he⟩ : {e // e ∈ G}) ∈ S := mem_filter.mpr ⟨mem_univ _,he⟩
      simpa only [dif_pos (hsub he)] using hb ⟨e,hsub he⟩ ha
  unfold SigningAverage
  simp_rw [hprop]
  rw [hh,hcard,(lemma_3_5 P hP p).1]

private def SignProbability {N colors : ℕ} (s : Signing) (P : Finset (ColoredEdge N colors))
    (p : ColoredEdge N colors → Bool) : ℝ :=
  match s with | .yes => SignProbYes P p | .no => SignProbNo P p

private lemma average_congr {α : Type*} (S : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ S, f x = g x) : Average S f = Average S g := by
  unfold Average
  congr 1
  exact sum_congr rfl h

private lemma signing_zero {N colors : ℕ} (s : Signing) (G : Finset (ColoredEdge N colors)) :
    SigningAverage s G (fun _ => (0:ℝ)) = 0 := by
  cases s <;> simp only [SigningAverage,Average,sum_const_zero,zero_div]

private lemma signing_monomial {N colors : ℕ} (T : GraphTable N colors) (s : Signing)
    (G : Finset (ColoredEdge N colors)) (hG : Consistent G) :
    SigningAverage s G (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse G b)) az) =
      if ConsistentTable T then
        (if PatternOf T ⊆ G then SignProbability s (PatternOf T) (PatternSign T) else 0) else 0 := by
  by_cases hT : ConsistentTable T
  swap
  · rw [if_neg hT]
    have hzero : (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse G b)) az) = fun _ => (0:ℝ) := by
      funext b
      rw [indicator_product,if_neg (fun hb => hT (fits_consistent T G hG b hb))]
    rw [hzero,signing_zero]
  rw [if_pos hT]
  by_cases hsub : PatternOf T ⊆ G
  swap
  · rw [if_neg hsub]
    have hzero : (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse G b)) az) = fun _ => (0:ℝ) := by
      funext b
      rw [indicator_product,if_neg (fun hb => hsub (fits_subset T G hG b hb))]
    rw [hzero,signing_zero]
  rw [if_pos hsub]
  have hfun : (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse G b)) az) =
      fun b => if ∀ e ∈ PatternOf T, b e = PatternSign T e then (1:ℝ) else 0 := by
    funext b
    rw [indicator_product]
    have hi : Fits T G b ↔ ∀ e ∈ PatternOf T, b e = PatternSign T e := by
      simp only [fits_iff T G hG b,hT,hsub,true_and]
    by_cases hb : ∀ e ∈ PatternOf T, b e = PatternSign T e
    · rw [if_pos hb,if_pos (hi.mpr hb)]
    · rw [if_neg hb,if_neg (fun hp => hb (hi.mp hp))]
  rw [hfun]
  cases s
  · exact yes_event_probability G (PatternOf T) (PatternSign T)
  · exact no_event_probability G (PatternOf T) hsub hT.1 (PatternSign T)

private lemma visible_other {N M colors : ℕ} (l : ℕ) (t : Fin N → Fin M)
    (h : Fin colors → (Fin M → Fin M)) (hm : ∀ j, h j ∈ Matchings M l)
    (e : ColoredEdge N colors) (he : e ∈ VisibleEdges t h) (u : Fin N) (hu : Incident e u) :
    h e.2.2 (t u) = t (Other e u) := by
  have helt := (mem_filter.mp he).2.1
  have heq := (mem_filter.mp he).2.2
  rcases hu with hu | hu
  · subst u
    simpa [Other] using heq
  · subst u
    have hinv := ((mem_filter.mp (hm e.2.2)).2.1 (t e.1)).1
    rw [heq] at hinv
    simpa [Other,ne_of_lt helt] using hinv

private lemma visible_consistent {N M colors : ℕ} (l : ℕ) (t : Fin N → Fin M)
    (ht : Function.Injective t) (h : Fin colors → (Fin M → Fin M))
    (hm : ∀ j, h j ∈ Matchings M l) : Consistent (VisibleEdges t h) := by
  refine ⟨fun e he => (mem_filter.mp he).2.1,?_⟩
  intro e he f hf hc hu
  obtain ⟨u,heu,hfu⟩ := hu
  have heq := visible_other l t h hm e he u heu
  have hfq := visible_other l t h hm f hf u hfu
  have ho : Other e u = Other f u := by
    apply ht
    rw [← heq,← hfq,hc]
  calc
    e = (min u (Other e u),max u (Other e u),e.2.2) := reconstruct e u (mem_filter.mp he).2.1 heu
    _ = (min u (Other f u),max u (Other f u),f.2.2) := by rw [ho,hc]
    _ = f := (reconstruct f u (mem_filter.mp hf).2.1 hfu).symm

private lemma feasible_consistent_congr {N colors M l : ℕ}
    (f g : Finset (ColoredEdge N colors) → ℝ) (hfg : ∀ G, Consistent G → f G = g G) :
    FeasibleBase N M l f = FeasibleBase N M l g := by
  unfold FeasibleBase MatchingAverage
  apply average_congr
  intro b hb
  apply average_congr
  intro t ht
  apply average_congr
  intro h hh
  exact hfg (VisibleEdges t h) (visible_consistent l t (mem_filter.mp ht).2.1 h (mem_filter.mp hh).2)

private lemma average_smul {α : Type*} (S : Finset α) (c : ℝ) (f : α → ℝ) :
    Average S (fun x => c*f x) = c*Average S f := by
  unfold Average
  rw [← Finset.mul_sum,mul_div_assoc]

private lemma feasible_smul {N colors M l : ℕ} (c : ℝ) (f : Finset (ColoredEdge N colors) → ℝ) :
    FeasibleBase N M l (fun F => c*f F) = c*FeasibleBase N M l f := by
  unfold FeasibleBase MatchingAverage
  simp_rw [average_smul]

private lemma feasible_zero {N colors M l : ℕ} :
    FeasibleBase N M l (fun _ : Finset (ColoredEdge N colors) => (0:ℝ)) = 0 := by
  unfold FeasibleBase MatchingAverage
  simp only [Average,sum_const_zero,zero_div]

private lemma average_bounds {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ Average s f ∧ Average s f ≤ 1 := by
  unfold Average
  constructor
  · exact div_nonneg (sum_nonneg (fun x hx => (hf x hx).1)) (Nat.cast_nonneg _)
  · by_cases hs : s.card = 0
    · simp [hs]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs)).mpr
      calc
        _ ≤ ∑ x ∈ s, (1:ℝ) := sum_le_sum (fun x hx => (hf x hx).2)
        _ = _ := by simp


private lemma sign_probability_bounds {N colors : ℕ} (s : Signing) (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (p : ColoredEdge N colors → Bool) :
    0 ≤ SignProbability s F p ∧ SignProbability s F p ≤ 1 := by
  cases s
  · simp only [SignProbability]
    rw [← yes_event_probability F F p]
    unfold SigningAverage
    apply average_bounds
    intro x hx
    dsimp only
    split_ifs <;> norm_num
  · simp only [SignProbability]
    rw [← no_event_probability F F (subset_refl _) hF p]
    unfold SigningAverage
    apply average_bounds
    intro b hb
    dsimp only
    split_ifs <;> norm_num

private lemma pattern_card {N colors : ℕ} (T : GraphTable N colors) : (PatternOf T).card ≤ T.val.card := by
  unfold PatternOf
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ az ∈ T.val, 1 := by
      apply sum_le_sum
      intro az haz
      cases az.1.1 <;> simp
    _ = _ := by simp

private lemma overflow_nonneg (N M l : ℕ) : 0 ≤ OverflowProbability N M l := by
  unfold OverflowProbability Average
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro b hb
  split_ifs <;> norm_num

end
end QuantumBipartiteTesting.Bipartiteness.MonomialProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.MonomialProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {N colors : ℕ} (M l : ℕ) (hValid : ValidParameters N M l)
    (T : GraphTable N colors) (hsmall : 4*T.val.card ≤ M/l) (s : Signing) :
    |FeasibleBase N M l (fun F : Finset (ColoredEdge N colors) =>
        SigningAverage s F (fun b =>
          ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az)) -
      FormalMonomial s T M l| ≤ OverflowProbability N M l := by
  by_cases hT : ConsistentTable T
  swap
  · have hz : FeasibleBase N M l (fun F : Finset (ColoredEdge N colors) =>
        SigningAverage s F (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az)) = 0 := by
      calc
        _ = FeasibleBase N M l (fun _ : Finset (ColoredEdge N colors) => (0:ℝ)) := by
          apply feasible_consistent_congr
          intro G hG
          rw [signing_monomial T s G hG,if_neg hT]
        _ = _ := feasible_zero
    rw [hz]
    simp only [FormalMonomial,if_neg hT,sub_zero,abs_zero]
    exact overflow_nonneg N M l
  let P := PatternOf T
  let prob := SignProbability s P (PatternSign T)
  have hactual : FeasibleBase N M l (fun F : Finset (ColoredEdge N colors) =>
        SigningAverage s F (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az)) =
      prob * FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if P ⊆ G then (1:ℝ) else 0) := by
    calc
      _ = FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => prob*(if P ⊆ G then (1:ℝ) else 0)) := by
        apply feasible_consistent_congr
        intro G hG
        rw [signing_monomial T s G hG,if_pos hT]
        by_cases hsub : P ⊆ G <;> simp only [P] at hsub ⊢ <;> simp [hsub,prob,P]
      _ = _ := feasible_smul _ _
  rw [hactual]
  simp only [FormalMonomial,if_pos hT]
  change |prob*FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if P ⊆ G then (1:ℝ) else 0)-
    TopologyMoment P M l*prob| ≤ _
  have hprob := sign_probability_bounds s P hT.1 (PatternSign T)
  have hab : |prob| ≤ 1 := by rw [abs_of_nonneg hprob.1]; exact hprob.2
  have hcap : 2*P.card ≤ M/l := by have hh := pattern_card T; dsimp only [P]; omega
  have hcore := topology_pattern_comparison M l hValid P hT.1 hcap
  have heq : prob*FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if P ⊆ G then (1:ℝ) else 0)-
      TopologyMoment P M l*prob =
      prob*(FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if P ⊆ G then (1:ℝ) else 0)-TopologyMoment P M l) := by ring
  rw [heq,abs_mul]
  exact (mul_le_mul hab hcore (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
end
