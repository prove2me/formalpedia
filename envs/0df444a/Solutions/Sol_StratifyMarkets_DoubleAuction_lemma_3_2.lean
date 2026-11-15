-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:36:30.622833+00:00
-- url     : https://prove2.me/submissions/7501da70-02fa-4082-b2f7-aceb5993114b

import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib

set_option autoImplicit false

-- Solutions.StratifyMarketsRefinements
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction.Stratification

/-- The shared boundary belongs to both adjacent pieces. The membership rule
uses the left piece's copy at exactly the join. -/
def edge (σ ρ : Stratification) (i : Fin (σ.N + ρ.N + 1)) : ℝ :=
  if h : i.val ≤ σ.N then σ.m ⟨i.val, by omega⟩ else ρ.m ⟨i.val - σ.N, by omega⟩

def tagPrice (σ ρ : Stratification) : Fin (σ.N + ρ.N) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) σ.p ρ.p

theorem left_edges (σ ρ : Stratification) (k : Fin σ.N) :
    edge σ ρ (k.castAdd ρ.N).castSucc = σ.m k.castSucc ∧
    edge σ ρ (k.castAdd ρ.N).succ = σ.m k.succ := by
  have h₁ : k.val ≤ σ.N := k.isLt.le
  have h₂ : k.val + 1 ≤ σ.N := k.isLt
  simp [edge, h₁, h₂]
  exact ⟨rfl,rfl⟩

theorem right_edges (σ ρ : Stratification) (join : σ.m (Fin.last σ.N) = ρ.m 0)
    (k : Fin ρ.N) :
    edge σ ρ (k.natAdd σ.N).castSucc = ρ.m k.castSucc ∧
    edge σ ρ (k.natAdd σ.N).succ = ρ.m k.succ := by
  have positive : ¬ σ.N + k.val + 1 ≤ σ.N := by omega
  constructor
  · by_cases h : k.val = 0
    · have hzero : k.castSucc = 0 := Fin.ext h
      rw [hzero, ← join]
      simp [edge, h]
      rfl
    · have hh : ¬σ.N + k.val ≤ σ.N := by omega
      simp [edge, hh]
      rfl
  · simp [edge, Nat.add_assoc]
    rfl

noncomputable def concatenate (σ ρ : Stratification) (join : σ.m (Fin.last σ.N) = ρ.m 0) :
    Stratification where
  N := σ.N + ρ.N
  one_le_N := by have := σ.one_le_N; omega
  m := edge σ ρ
  p := tagPrice σ ρ
  zero_le_m := by simpa [edge] using σ.zero_le_m
  m_le_one := by
    have h : ¬σ.N + ρ.N ≤ σ.N := by have := ρ.one_le_N; omega
    simp [edge, h]
    exact ρ.m_le_one
  m_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.addCases (motive := fun k => edge σ ρ k.castSucc < edge σ ρ k.succ) ?_ ?_ i
    · intro k
      rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
      exact σ.m_strictMono k.castSucc_lt_succ
    · intro k
      rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
      exact ρ.m_strictMono k.castSucc_lt_succ
  p_mem := by
    intro i
    refine Fin.addCases (motive := fun k => edge σ ρ k.castSucc ≤ tagPrice σ ρ k ∧
      tagPrice σ ρ k ≤ edge σ ρ k.succ) ?_ ?_ i
    · intro k
      rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
      simpa [tagPrice] using σ.p_mem k
    · intro k
      rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
      simpa [tagPrice] using ρ.p_mem k

theorem concatenate_start (σ ρ : Stratification) (join) :
    (concatenate σ ρ join).m 0 = σ.m 0 := by simp [concatenate, edge]

theorem concatenate_end (σ ρ : Stratification) (join) :
    (concatenate σ ρ join).m (Fin.last (concatenate σ ρ join).N) = ρ.m (Fin.last ρ.N) := by
  have h : ¬σ.N + ρ.N ≤ σ.N := by have := ρ.one_le_N; omega
  simp [concatenate, edge, h]
  rfl

theorem concatenate_gains {n m : ℕ} (I : DAInstance n m) (σ ρ : Stratification) (join) :
    I.strat (concatenate σ ρ join) = I.strat σ + I.strat ρ := by
  change (∑ k : Fin (σ.N + ρ.N), I.worstRationedIn (edge σ ρ k.castSucc)
    (tagPrice σ ρ k) (edge σ ρ k.succ)) = _
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
    simp [tagPrice]
  · apply Finset.sum_congr rfl
    intro k _
    rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
    simp [tagPrice]

/-- Glue all pieces of a nonempty partition, preserving the interval ends
and adding their gains exactly. The number of pieces is arbitrary. -/
theorem assemble_chain {n m : ℕ} (I : DAInstance n m) (d : ℕ)
    (pieces : Fin (d+1) → Stratification)
    (join : ∀ i : Fin d, (pieces i.castSucc).m (Fin.last (pieces i.castSucc).N) =
      (pieces i.succ).m 0) :
    ∃ σ : Stratification, σ.m 0 = (pieces 0).m 0 ∧
      σ.m (Fin.last σ.N) = (pieces (Fin.last d)).m (Fin.last (pieces (Fin.last d)).N) ∧
      I.strat σ = ∑ i, I.strat (pieces i) := by
  induction d with
  | zero => exact ⟨pieces 0,rfl,rfl,by rw [Fin.sum_univ_one]⟩
  | succ d ih =>
    let pref : Fin (d+1) → Stratification := fun i => pieces i.castSucc
    have chain (i : Fin d) : (pref i.castSucc).m (Fin.last (pref i.castSucc).N) =
        (pref i.succ).m 0 := join i.castSucc
    obtain ⟨σ,hl,hr,hg⟩ := ih pref chain
    let last := pieces (Fin.last (d+1))
    have j : σ.m (Fin.last σ.N) = last.m 0 := hr.trans (join (Fin.last d))
    refine ⟨concatenate σ last j, (concatenate_start _ _ _).trans hl, concatenate_end _ _ _, ?_⟩
    rw [concatenate_gains, hg, Fin.sum_univ_castSucc (fun i : Fin (d+2) => I.strat (pieces i))]

theorem assemble_refinements {n m : ℕ} (I : DAInstance n m) (base : Stratification)
    (pieces : Fin base.N → Stratification)
    (left : ∀ i, (pieces i).m 0 = base.m i.castSucc)
    (right : ∀ i, (pieces i).m (Fin.last (pieces i).N) = base.m i.succ) :
    ∃ σ : Stratification, I.strat σ = ∑ i, I.strat (pieces i) := by
  obtain ⟨N,hN,edges,prices,first,last,strict,valid⟩ := base
  cases N with
  | zero => omega
  | succ d =>
    have join (i : Fin d) : (pieces i.castSucc).m (Fin.last (pieces i.castSucc).N) =
        (pieces i.succ).m 0 := (right i.castSucc).trans (left i.succ).symm
    obtain ⟨σ,_,_,h⟩ := assemble_chain I d pieces join
    exact ⟨σ,h⟩

end StratifyMarkets.DoubleAuction.Stratification
end

-- Solutions.StratifyMarketsBilateralMatching
section
open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace StratifyMarkets.DoubleAuction.OrderedProof

structure Pair where
  sl : ℝ
  sh : ℝ
  bl : ℝ
  bh : ℝ
  sl0 : 0 ≤ sl
  ss : sl ≤ sh
  mid : sh ≤ bl
  bb : bl ≤ bh
  bh1 : bh ≤ 1

def follows (A B : Pair) : Prop := A.sh ≤ B.sl ∧ A.bh ≤ B.bl
def joins (A B : Pair) : Prop := B.sh ≤ A.bl
def rect (q : Pair) (x : ℝ × ℝ) : ℝ :=
  if q.sl ≤ x.1 ∧ x.1 ≤ q.sh ∧ q.bl ≤ x.2 ∧ x.2 ≤ q.bh then x.2-x.1 else 0
def gain (I : BTInstance) (q : Pair) := ∫ x, rect q x ∂I.law

private theorem rectMeasurable (q : Pair) : Measurable (rect q) := by
  unfold rect
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
       ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const)))
  · exact measurable_snd.sub measurable_fst
  · exact measurable_const

private theorem rectNonneg (q : Pair) (x : ℝ × ℝ) : 0 ≤ rect q x := by
  unfold rect
  split <;> grind [q.mid]

private theorem rectInt (I : BTInstance) (q : Pair) : Integrable (rect q) I.law := by
  letI := I.isProb_B
  letI := I.isProb_S
  haveI : IsProbabilityMeasure I.law := inferInstanceAs (IsProbabilityMeasure (I.μS.prod I.μB))
  apply (integrable_const (μ := I.law) (1:ℝ)).mono' (rectMeasurable q).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rectNonneg q x)]
    unfold rect
    split <;> grind [q.sl0,q.bh1])

theorem gain_nonneg (I : BTInstance) (q : Pair) : 0 ≤ gain I q := integral_nonneg (rectNonneg q)

def merge (A B : Pair) (f : follows A B) (j : joins A B) : Pair :=
  ⟨A.sl,B.sh,A.bl,B.bh,A.sl0,A.ss.trans (f.1.trans B.ss),j,A.bb.trans (f.2.trans B.bb),B.bh1⟩

theorem merge_gain (I : BTInstance) (A B : Pair) (f : follows A B) (j : joins A B) :
    gain I A + gain I B ≤ gain I (merge A B f j) := by
  letI := I.isProb_B
  letI := I.isProb_S
  letI := I.noAtoms_S
  have hs : ∀ᵐ x : ℝ × ℝ ∂I.law, x.1 ≠ A.sh :=
    (measurePreserving_fst (μ := I.μS) (ν := I.μB)).quasiMeasurePreserving.ae (I.μS.ae_ne A.sh)
  unfold gain
  rw [← integral_add (rectInt I A) (rectInt I B)]
  apply integral_mono_ae ((rectInt I A).add (rectInt I B)) (rectInt I _)
  filter_upwards [hs] with x hx
  have mid := A.mid
  have mid' := B.mid
  obtain ⟨fs,fb⟩ := f
  simp only [Pi.add_apply,rect,merge]
  have jmid : B.sh ≤ A.bl := j
  split_ifs <;> grind [A.ss,A.bb,B.ss,B.bb]

def weight (I : BTInstance) (qs : List Pair) := (qs.map (gain I)).sum

/-- A pass that merges adjacent pairs until further merging would violate
full tradability. It preserves the first lower endpoints. -/
private theorem normalize (I : BTInstance) (a : Pair) (xs : List Pair)
    (order : (a::xs).IsChain follows) :
    ∃ b ys, (b::ys).IsChain follows ∧ (b::ys).IsChain (fun x y => ¬joins x y) ∧
      b.sl = a.sl ∧ b.bl = a.bl ∧
      weight I (a::xs) ≤ weight I (b::ys) := by
  induction xs generalizing a with
  | nil => exact ⟨a,[],by simp,by simp,rfl,rfl,le_rfl⟩
  | cons x xs ih =>
    obtain ⟨b,ys,hord,hjoin,hs,hb,hg⟩ := ih x (List.IsChain.tail order)
    have f : follows a b := by
      have old : follows a x := (List.isChain_cons_cons.mp order).1
      simpa only [follows,hs,hb] using old
    by_cases h : joins a b
    · let m := merge a b f h
      have om : (m::ys).IsChain follows := by
        cases ys with
        | nil => simp
        | cons v vs => exact List.isChain_cons_cons.mpr ⟨(List.isChain_cons_cons.mp hord).1,(List.isChain_cons_cons.mp hord).2⟩
      have jm : (m::ys).IsChain (fun x y => ¬ joins x y) := by
        cases ys with
        | nil => simp
        | cons v vs =>
          refine List.isChain_cons_cons.mpr ⟨?_,(List.isChain_cons_cons.mp hjoin).2⟩
          intro h'
          apply (List.isChain_cons_cons.mp hjoin).1
          exact (show v.sh ≤ a.bl from h').trans (a.bb.trans f.2)
      refine ⟨m,ys,om,jm,rfl,rfl,?_⟩
      have g := merge_gain I a b f h
      simp only [weight,List.map_cons,List.sum_cons] at *
      dsimp [m]
      linarith
    · refine ⟨a,b::ys,List.isChain_cons_cons.mpr ⟨f,hord⟩,List.isChain_cons_cons.mpr ⟨h,hjoin⟩,rfl,rfl,?_⟩
      exact add_le_add_right hg _


private def firstColor : List Pair → List Pair
  | a::b::c::xs => a::firstColor xs
  | [] => []
  | [a] => [a]
  | [a,b] => [a]

private theorem firstColor_head (a : Pair) (xs : List Pair) :
    firstColor (a::xs) = a::firstColor (xs.drop 2) := by
  cases xs with
  | nil => rfl
  | cons b xs => cases xs <;> rfl

private theorem colors_weight (I : BTInstance) (xs : List Pair) :
    weight I xs = weight I (firstColor xs) + weight I (firstColor xs.tail) +
      weight I (firstColor xs.tail.tail) := by
  induction xs with
  | nil => simp [weight,firstColor]
  | cons a xs ih =>
    rw [firstColor_head]
    simp only [List.tail_cons]
    have eq : xs.drop 2 = xs.tail.tail := by cases xs with | nil => rfl | cons b bs => cases bs <;> rfl
    rw [eq]
    simp only [weight,List.map_cons,List.sum_cons] at *
    linarith

private theorem color_chain (xs : List Pair) (ho : xs.IsChain follows)
    (hj : xs.IsChain (fun x y => ¬ joins x y)) :
    (firstColor xs).IsChain (fun x y => x.bh ≤ y.sl) := by
  match xs with
  | [] => simp [firstColor]
  | [a] => simp [firstColor]
  | [a,b] => simp [firstColor]
  | [a,b,c] => simp [firstColor]
  | a::b::c::d::ds =>
    have one := (List.isChain_cons_cons.mp ho).1
    have two := (List.isChain_cons_cons.mp (List.IsChain.tail hj)).1
    have three := (List.isChain_cons_cons.mp (List.IsChain.tail (List.IsChain.tail ho))).1
    have space : a.bh ≤ d.sl := one.2.trans ((lt_of_not_ge two).le.trans three.1)
    change (a :: firstColor (d::ds)).IsChain _
    rw [firstColor_head]
    apply List.isChain_cons_cons.mpr
    refine ⟨space,?_⟩
    rw [← firstColor_head]
    exact color_chain (d::ds) ho.tail.tail.tail hj.tail.tail.tail
termination_by xs.length

private def oneInterval (l p u : ℝ) (hl : 0 ≤ l) (hu : u ≤ 1) (sep : l < u)
    (lp : l ≤ p) (pu : p ≤ u) : Stratification where
  N := 1
  one_le_N := by decide
  m := ![l,u]
  p := fun _ => p
  zero_le_m := hl
  m_le_one := hu
  m_strictMono := Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i;exact sep)
  p_mem := by intro i;fin_cases i;exact ⟨lp,pu⟩

private theorem priceGainAdd (I : BTInstance) (σ ρ : Stratification)
    (join : σ.m (Fin.last σ.N) = ρ.m 0) :
    I.strat (σ.concatenate ρ join) = I.strat σ + I.strat ρ := by
  unfold BTInstance.strat
  change (∑ k : Fin (σ.N+ρ.N), _) = _
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    obtain ⟨h1,h2⟩ := Stratification.left_edges σ ρ k
    simp only [Stratification.concatenate,Stratification.tagPrice,Fin.addCases_left,h1,h2]
  · apply Finset.sum_congr rfl
    intro k _
    obtain ⟨h1,h2⟩ := Stratification.right_edges σ ρ join k
    simp only [Stratification.concatenate,Stratification.tagPrice,Fin.addCases_right,h1,h2]

private theorem stratNonneg (I : BTInstance) (σ : Stratification) : 0 ≤ I.strat σ :=
  Finset.sum_nonneg (fun k _ => integral_nonneg (fun x => by
    change (0 : ℝ) ≤ ite _ _ _
    split <;> grind))

private theorem intervalGain (I : BTInstance) (a : Pair) (lt : a.sl < a.bh) :
    gain I a ≤ I.strat (oneInterval a.sl a.sh a.bh a.sl0 a.bh1 lt a.ss (a.mid.trans a.bb)) := by
  let b : Pair := ⟨a.sl,a.sh,a.sh,a.bh,a.sl0,a.ss,le_rfl,a.mid.trans a.bb,a.bh1⟩
  unfold BTInstance.strat
  change _ ≤ ∑ k : Fin 1, _
  rw [Fin.sum_univ_one]
  change gain I a ≤ gain I b
  apply integral_mono (rectInt I _) (rectInt I _) (fun x => ?_)
  simp only [rect,b]
  split <;> split <;> grind [a.mid,a.ss,a.bb]

private def paste (I : BTInstance) (σ ρ : Stratification)
    (sep : σ.m (Fin.last σ.N) ≤ ρ.m 0) :
    ∃ τ : Stratification, τ.m 0 = σ.m 0 ∧ τ.m (Fin.last τ.N) = ρ.m (Fin.last ρ.N) ∧
      I.strat σ + I.strat ρ ≤ I.strat τ := by
  rcases sep.eq_or_lt with join|gap
  · exact ⟨σ.concatenate ρ join,σ.concatenate_start ρ join,σ.concatenate_end ρ join,(priceGainAdd I σ ρ join).ge⟩
  · let l := σ.m (Fin.last σ.N)
    let u := ρ.m 0
    let filler := oneInterval l l u
      (σ.zero_le_m.trans (σ.m_strictMono.monotone (Fin.zero_le _))) (ρ.m_le_one.trans' (ρ.m_strictMono.monotone (Fin.le_last _))) gap le_rfl gap.le
    let j1 : σ.m (Fin.last σ.N) = filler.m 0 := rfl
    let left := σ.concatenate filler j1
    have j2 : left.m (Fin.last left.N) = ρ.m 0 := σ.concatenate_end filler j1
    let τ := left.concatenate ρ j2
    refine ⟨τ,(left.concatenate_start ρ j2).trans (σ.concatenate_start filler j1),left.concatenate_end ρ j2,?_⟩
    change _ ≤ I.strat (left.concatenate ρ j2)
    rw [priceGainAdd]
    change _ ≤ I.strat (σ.concatenate filler j1) + I.strat ρ
    rw [priceGainAdd]
    linarith [stratNonneg I filler]
    

private theorem gather (I : BTInstance) (a : Pair) (xs : List Pair)
    (h : (a::xs).IsChain (fun x y => x.bh ≤ y.sl)) :
    weight I (a::xs) = 0 ∨ ∃ σ : Stratification, a.sl ≤ σ.m 0 ∧ weight I (a::xs) ≤ I.strat σ := by
  by_cases lt : a.sl < a.bh
  · let one := oneInterval a.sl a.sh a.bh a.sl0 a.bh1 lt a.ss (a.mid.trans a.bb)
    have capture : gain I a ≤ I.strat one := intervalGain I a lt
    cases xs with
    | nil => exact Or.inr ⟨one,le_rfl,by simpa [weight] using capture⟩
    | cons b bs =>
      obtain ⟨sep,ho⟩ := List.isChain_cons_cons.mp h
      rcases gather I b bs ho with zero|⟨ρ,hr,hw⟩
      · right
        exact ⟨one,le_rfl,by change gain I a + weight I (b::bs) ≤ _; rw [zero,add_zero]; exact capture⟩
      · obtain ⟨τ,hl,_,hg⟩ := paste I one ρ (sep.trans hr)
        exact Or.inr ⟨τ,hl.ge,(add_le_add capture hw).trans hg⟩
  · have heq : a.bh ≤ a.sl := le_of_not_gt lt
    have zero : gain I a = 0 := by
      have point (x : ℝ × ℝ) : rect a x = 0 := by
        unfold rect
        split <;> grind [a.mid,a.ss,a.bb]
      simp only [gain,point,integral_zero]
    cases xs with
    | nil => exact Or.inl (by simp [weight,zero])
    | cons b bs =>
      obtain ⟨sep,ho⟩ := List.isChain_cons_cons.mp h
      rcases gather I b bs ho with hz|⟨ρ,hr,hw⟩
      · exact Or.inl (by change gain I a + weight I (b::bs) = 0;rw [zero,hz,add_zero])
      · exact Or.inr ⟨ρ,(a.ss.trans (a.mid.trans a.bb)).trans (sep.trans hr),by
          change gain I a + weight I (b::bs) ≤ _;rw [zero,zero_add]; exact hw⟩
termination_by xs.length

private theorem captureColor (I : BTInstance) (xs : List Pair) (h : xs.IsChain (fun a b => a.bh ≤ b.sl)) :
    ∃ σ : Stratification, weight I xs ≤ I.strat σ := by
  let dummy := oneInterval 0 0 1 le_rfl le_rfl zero_lt_one le_rfl zero_le_one
  cases xs with
  | nil => exact ⟨dummy,stratNonneg I dummy⟩
  | cons a xs =>
    rcases gather I a xs h with zero|⟨σ,_,hw⟩
    · exact ⟨dummy,zero.trans_le (stratNonneg I dummy)⟩
    · exact ⟨σ,hw⟩

private def fromMatching (M : OrderedMatching) (k : Fin M.N) : Pair :=
  ⟨M.mS k.castSucc,M.mS k.succ,M.mB k.castSucc,M.mB k.succ,
    M.zero_le_mS.trans (M.mS_mono (Fin.zero_le _)), M.mS_mono (Fin.castSucc_le_succ _),
    M.tradable k,M.mB_mono (Fin.castSucc_le_succ _),(M.mB_mono (Fin.le_last _)).trans M.mB_le_one⟩

private theorem orderedList (M : OrderedMatching) : (List.ofFn (fromMatching M)).IsChain follows := by
  apply List.Pairwise.isChain
  apply List.pairwise_ofFn.mpr
  intro i j h
  constructor
  · apply M.mS_mono
    exact h
  · apply M.mB_mono
    exact h

theorem matchingToStratification (I : BTInstance) (M : OrderedMatching) :
    ∃ σ : Stratification, I.orderedMatching M / 3 ≤ I.strat σ := by
  let qs := List.ofFn (fromMatching M)
  have w : I.orderedMatching M = weight I qs := by
    simp only [weight,qs,List.map_ofFn,List.sum_ofFn]
    rfl
  rw [w]
  have ho : qs.IsChain follows := orderedList M
  cases e : qs with
  | nil =>
    let dummy := oneInterval 0 0 1 le_rfl le_rfl zero_lt_one le_rfl zero_le_one
    exact ⟨dummy,by simpa [weight] using stratNonneg I dummy⟩
  | cons a xs =>
    rw [e] at ho
    obtain ⟨b,ys,ord,j,_,_,sum⟩ := normalize I a xs ho
    let v := b::ys
    obtain ⟨σ,hs⟩ := captureColor I (firstColor v) (color_chain v ord j)
    obtain ⟨ρ,hr⟩ := captureColor I (firstColor v.tail) (color_chain v.tail ord.tail j.tail)
    obtain ⟨η,he⟩ := captureColor I (firstColor v.tail.tail) (color_chain v.tail.tail ord.tail.tail j.tail.tail)
    have all := colors_weight I v
    change weight I (a::xs) ≤ weight I v at sum
    by_cases h : weight I (a::xs) / 3 ≤ I.strat σ
    · exact ⟨σ,h⟩
    by_cases h' : weight I (a::xs) / 3 ≤ I.strat ρ
    · exact ⟨ρ,h'⟩
    · exact ⟨η,by linarith⟩

end StratifyMarkets.DoubleAuction.OrderedProof
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_3_2
section
open StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) (M : OrderedMatching) :
    ∃ σ : Stratification, I.orderedMatching M / 3 ≤ I.strat σ :=
  OrderedProof.matchingToStratification I M
end
