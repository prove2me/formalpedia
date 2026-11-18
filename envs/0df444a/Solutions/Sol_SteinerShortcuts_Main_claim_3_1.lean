-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:23:25.77658+00:00
-- url     : https://prove2.me/submissions/52117e81-0938-4ba8-866b-2808a33a02b0

import Definitions.Def_SteinerShortcuts_Main_TestFunctions
import Theorems.Thm_SteinerShortcuts_Main_equation_11

open SteinerShortcuts.Main
open scoped Classical
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

private noncomputable def pot (coeff : Fin 21 → ℝ) (g : ℤ → ℝ) (v : Point) : ℝ :=
  (∑ i, (v i : ℝ) * coeff i) + ∑ j ∈ Finset.Ico (0:ℤ) (v 0), g j

private theorem layer_nonneg (L q : ℕ) (v : Point) (hv : v ∈ vertices L q) :
    0 ≤ v 0 := by
  have layer_mem (ell : ℕ) (scale : ℤ) (hm : v ∈ layerBox L q ell scale) :
      v 0 = (ell:ℤ) := by
    have := Fintype.mem_piFinset.mp hm 0
    simpa using this
  rcases Finset.mem_union.mp hv with hs | hv
  · rw [layer_mem 1 1 hs]; omega
  · obtain ⟨ell, hell, hv⟩ := Finset.mem_biUnion.mp hv
    rw [layer_mem ell 2 hv]; omega

private theorem potential_step (L q : ℕ) (coeff : Fin 21 → ℝ) (g : ℤ → ℝ)
    (v : Point) (hv : v ∈ vertices L q) (t : Fin q) :
    pot coeff g (step q v t) - pot coeff g v =
      (∑ i, (update q (position v) t i : ℝ) * coeff i) + g (v 0) := by
  have h0 : step q v t 0 = v 0 + 1 := by simp [step, update]
  have hs := (Finset.sum_Ico_add_eq_sum_Ico_add_one (show (0:ℤ) ≤ v 0 from layer_nonneg L q v hv) g).symm
  unfold pot
  rw [h0, hs]
  simp only [step, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

private theorem chain_zip {V : Type} (r : V → V → Prop) (a : V) (l : List V) :
    (a::l).IsChain r ↔ ∀ e ∈ (a::l).zip l, r e.1 e.2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [List.isChain_cons_cons, ih]

private theorem chain_le {V : Type} (p : V → ℝ) (a : V) (l : List V)
    (hc : (a::l).IsChain (fun u v => p u ≤ p v)) : p a ≤ p (l.getLastD a) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hc' := List.isChain_cons_cons.mp hc
    have hi := ih b hc'.2
    simpa only [List.getLastD_cons] using hc'.1.trans hi

private theorem chain_eq {V : Type} (p : V → ℝ) (a : V) (l : List V)
    (hc : (a::l).IsChain (fun u v => p u = p v)) : p a = p (l.getLastD a) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hc' := List.isChain_cons_cons.mp hc
    have hi := ih b hc'.2
    simpa only [List.getLastD_cons] using hc'.1.trans hi

private theorem chain_eq_of_le {V : Type} (p : V → ℝ) (a : V) (l : List V)
    (hc : (a::l).IsChain (fun u v => p u ≤ p v)) (he : p a = p (l.getLastD a)) :
    (a::l).IsChain (fun u v => p u = p v) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hc' := List.isChain_cons_cons.mp hc
    have hi := chain_le p b l hc'.2
    have hab : p a = p b := by simp only [List.getLastD_cons] at he; linarith
    apply List.isChain_cons_cons.mpr
    refine ⟨hab, ih b hc'.2 ?_⟩
    simpa only [List.getLastD_cons, ← hab] using he

private theorem arc_adj {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P)
    (e : V × V) (he : e ∈ P.arcs) : G.Adj e.1 e.2 :=
  (chain_zip G.Adj P.start P.tail).mp hp e he

private theorem edge_rep (L q : ℕ) (F : TestFunction q) (coeff : Fin 21 → ℝ)
    (g : ℤ → ℝ)
    (hl : ∀ v ∈ vertices L q, ∀ t : Fin q,
      F (position v) t = (∑ i, (update q (position v) t i : ℝ)*coeff i)+g (v 0))
    (v w : Point) (hv : v ∈ vertices L q) (t : Fin q) (hw : w = step q v t) :
    F (position v) t = pot coeff g w - pot coeff g v := by
  rw [hw, potential_step L q coeff g v hv t, hl v hv t]

private theorem route_nondecreasing (L q : ℕ) (F : TestFunction q) (coeff : Fin 21 → ℝ)
    (g : ℤ → ℝ)
    (hl : ∀ v ∈ vertices L q, ∀ t : Fin q,
      F (position v) t = (∑ i, (update q (position v) t i : ℝ)*coeff i)+g (v 0))
    (P : Route Point) (hp : IsPath (construction L q) P) (hn : NonnegativeOn F P) :
    P.vertices.IsChain (fun u v => pot coeff g u ≤ pot coeff g v) := by
  apply (chain_zip _ P.start P.tail).mpr
  intro e he
  rcases arc_adj _ P hp e he with ⟨hu, hw, hL, t, ht⟩
  have hf := hn e he t ht
  rw [edge_rep L q F coeff g hl e.1 e.2 hu t ht] at hf
  linarith

private theorem route_constant (L q : ℕ) (F : TestFunction q) (coeff : Fin 21 → ℝ)
    (g : ℤ → ℝ)
    (hl : ∀ v ∈ vertices L q, ∀ t : Fin q,
      F (position v) t = (∑ i, (update q (position v) t i : ℝ)*coeff i)+g (v 0))
    (P : Route Point) (hp : IsPath (construction L q) P) (hz : Vanishes F P) :
    P.vertices.IsChain (fun u v => pot coeff g u = pot coeff g v) := by
  apply (chain_zip _ P.start P.tail).mpr
  intro e he
  rcases arc_adj _ P hp e he with ⟨hu, hw, hL, t, ht⟩
  have hf := hz e he t ht
  rw [edge_rep L q F coeff g hl e.1 e.2 hu t ht] at hf
  linarith

private theorem vanish_of_constant (L q : ℕ) (F : TestFunction q) (coeff : Fin 21 → ℝ)
    (g : ℤ → ℝ)
    (hl : ∀ v ∈ vertices L q, ∀ t : Fin q,
      F (position v) t = (∑ i, (update q (position v) t i : ℝ)*coeff i)+g (v 0))
    (P : Route Point) (hp : IsPath (construction L q) P)
    (hc : P.vertices.IsChain (fun u v => pot coeff g u = pot coeff g v)) :
    Vanishes F P := by
  intro e he t ht
  have ha := arc_adj _ P hp e he
  have hh := (chain_zip _ P.start P.tail).mp hc e he
  rw [edge_rep L q F coeff g hl e.1 e.2 ha.1 t ht, hh, sub_self]

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T)
    (F : TestFunction q) (hn : T1prime F R T)
    (hv : Vanishes F (P.route L) ∧ Vanishes F (Q.route L))
    (hl : T3prime L q F) : Vanishes F R ∧ Vanishes F T := by
  rcases hl with ⟨coeff, g, hl⟩
  rcases hs with ⟨hp, hq, hcomp, hR, hT⟩
  obtain ⟨c,C,hc,hcC,hall⟩ := equation_11
  obtain ⟨_,_,_,_,_,_,hpaths,_⟩ := hall L q h
  have mem (S : CriticalData q) (hS : S.Valid L) : S.route L ∈ criticalPaths L q := by
    apply Finset.mem_image.mpr
    refine ⟨(S.source,(S.a,S.b)), ?_, rfl⟩
    simpa [CriticalData.Valid] using hS
  have hP := (hpaths _ (mem P hp)).1
  have hQ := (hpaths _ (mem Q hq)).1
  have eP := chain_eq (pot coeff g) (P.route L).start (P.route L).tail
    (route_constant L q F coeff g hl _ hP hv.1)
  have eQ := chain_eq (pot coeff g) (Q.route L).start (Q.route L).tail
    (route_constant L q F coeff g hl _ hQ hv.2)
  have nR := route_nondecreasing L q F coeff g hl R hR.1 hn.1
  have nT := route_nondecreasing L q F coeff g hl T hT.1 hn.2
  have leR := chain_le (pot coeff g) R.start R.tail nR
  have leT := chain_le (pot coeff g) T.start T.tail nT
  change pot coeff g (P.route L).start = pot coeff g (P.route L).finish at eP
  change pot coeff g (Q.route L).start = pot coeff g (Q.route L).finish at eQ
  change pot coeff g R.start ≤ pot coeff g R.finish at leR
  change pot coeff g T.start ≤ pot coeff g T.finish at leT
  have eR : pot coeff g R.start = pot coeff g R.finish := by
    rw [hR.2.1,hR.2.2] at *
    rw [hT.2.1,hT.2.2] at leT
    linarith
  have eT : pot coeff g T.start = pot coeff g T.finish := by
    rw [hT.2.1,hT.2.2] at *
    rw [hR.2.1,hR.2.2] at leR
    linarith
  exact ⟨vanish_of_constant L q F coeff g hl R hR.1
      (chain_eq_of_le (pot coeff g) R.start R.tail nR eR),
    vanish_of_constant L q F coeff g hl T hT.1
      (chain_eq_of_le (pot coeff g) T.start T.tail nT eT)⟩
