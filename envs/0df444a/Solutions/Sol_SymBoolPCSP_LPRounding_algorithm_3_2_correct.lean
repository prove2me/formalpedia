-- Prove2me | solution 1 for SymBoolPCSP.LPRounding.algorithm_3_2_correct
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T11:16:10.639996+00:00
-- url     : https://prove2.me/submissions/f2b3c6dc-85a8-49ef-8fd4-a90d6031a5d3

import Mathlib
import Definitions.Def_SymBoolPCSP_LPRounding_Basic


open Finset PCSPBLPAff.Symmetric SymBoolPCSP.LPRounding
namespace PCLPProof
variable {τ : Type} {ar : τ → ℕ}

theorem hull_mix (A : RelStruct τ ar Bool) (X : Instance τ ar)
    {v w : Fin X.n → ℚ} (hv : IsHullLPSol A X v) (hw : IsHullLPSol A X w)
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsHullLPSol A X (fun i => (1-t)*v i+t*w i) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hv.1 i).1) (mul_nonneg ht0 (hw.1 i).1)
    · nlinarith [(hv.1 i).1, (hv.1 i).2, (hw.1 i).1, (hw.1 i).2]
  · intro j
    obtain ⟨α, hα0, hαs, hα1, hαv⟩ := hv.2 j
    obtain ⟨β, hβ0, hβs, hβ1, hβv⟩ := hw.2 j
    refine ⟨fun y => (1-t)*α y+t*β y, ?_, ?_, ?_, ?_⟩
    · intro y
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hα0 y)) (mul_nonneg ht0 (hβ0 y))
    · intro y hy
      dsimp only
      rw [hαs y hy, hβs y hy]; ring
    · simp only [sum_add_distrib, ← mul_sum, hα1, hβ1]; ring
    · intro c
      dsimp only
      rw [hαv c, hβv c]
      simp only [add_mul, mul_assoc, sum_add_distrib, ← mul_sum]

theorem accepts_of_sat (A : RelStruct τ ar Bool) (X : Instance τ ar)
    (h : SatIn X A) : LPAlgAccepts A X := by
  classical
  obtain ⟨σ, hσ⟩ := h
  let v : Fin X.n → ℚ := fun i => if σ i then 1 else 0
  have hv : IsHullLPSol A X v := by
    refine ⟨?_, ?_⟩
    · intro i; dsimp [v]; split <;> norm_num
    · intro j
      refine ⟨fun y => if y = σ ∘ X.scope j then 1 else 0, ?_, ?_, ?_, ?_⟩
      · intro y; dsimp only; split <;> norm_num
      · intro y hy
        dsimp only
        split_ifs with he
        · exact (hy (he ▸ hσ j)).elim
        · rfl
      · simp
      · intro c
        dsimp only
        simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
        rfl
  refine ⟨⟨v,hv⟩, ?_⟩
  intro i
  cases hs : σ i
  · exact Or.inl ⟨v,hv,by simp [v,hs]⟩
  · exact Or.inr ⟨v,hv,by simp [v,hs]⟩
end PCLPProof


open Finset PCSPBLPAff.Symmetric SymBoolPCSP.LPRounding
namespace PCLPProof

theorem convex_avoid {n : ℕ} (C : Set (Fin n → ℚ)) (hne : C.Nonempty)
    (hmix : ∀ v ∈ C, ∀ w ∈ C, ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      (fun i => (1-t)*v i+t*w i) ∈ C)
    (c : Fin n → ℚ) (S : Finset (Fin n))
    (hw : ∀ i ∈ S, ∃ w ∈ C, w i ≠ c i) :
    ∃ v ∈ C, ∀ i ∈ S, v i ≠ c i := by
  classical
  induction S using Finset.induction_on with
  | empty => obtain ⟨v,hv⟩ := hne; exact ⟨v,hv,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨v,hv,hvc⟩ := ih (fun j hj => hw j (mem_insert_of_mem hj))
    by_cases hvi : v i = c i
    · obtain ⟨w,hwm,hwi⟩ := hw i (mem_insert_self _ _)
      let bad : Finset ℚ := S.image (fun j => (c j-v j)/(w j-v j))
      obtain ⟨t,ht,htbad⟩ := (Set.Ioo_infinite (show (0:ℚ)<1 by norm_num)).exists_notMem_finset bad
      refine ⟨fun j => (1-t)*v j+t*w j, hmix v hv w hwm t ht.1.le ht.2.le, ?_⟩
      intro j hj he
      dsimp only at he
      rcases mem_insert.mp hj with rfl | hj
      · have he' : t*(w j-v j)=0 := by nlinarith [he]
        rcases mul_eq_zero.mp he' with hz | hz
        · exact (ne_of_gt ht.1) hz
        · exact hwi (by linarith)
      · by_cases hz : w j-v j=0
        · rw [sub_eq_zero.mp hz] at he
          exact hvc j hj (by nlinarith [he])
        · apply htbad
          apply mem_image.mpr
          refine ⟨j,hj,?_⟩
          apply (div_eq_iff hz).mpr
          nlinarith [he]
    · exact ⟨v,hv,by intro j hj; rcases mem_insert.mp hj with rfl | hj; exact hvi; exact hvc j hj⟩

variable {τ : Type} {ar : τ → ℕ}

theorem accepts_avoids_half (A : RelStruct τ ar Bool) (X : Instance τ ar)
    (hacc : LPAlgAccepts A X) :
    ∃ v, IsHullLPSol A X v ∧ ∀ i, v i ≠ 1/2 := by
  classical
  obtain ⟨v,hv,h⟩ := convex_avoid {v | IsHullLPSol A X v} hacc.1
    (fun v hv w hw t ht0 ht1 => hull_mix A X hv hw t ht0 ht1)
    (fun _ => 1/2) univ (by
      intro i _
      rcases hacc.2 i with ⟨w,hw,hwi⟩ | ⟨w,hw,hwi⟩
      · exact ⟨w,hw,by rw [hwi]; norm_num⟩
      · exact ⟨w,hw,by rw [hwi]; norm_num⟩)
  exact ⟨v,hv,fun i => h i (mem_univ i)⟩

theorem accepts_avoids_interior (A : RelStruct τ ar Bool) (X : Instance τ ar)
    (hacc : LPAlgAccepts A X) (hat : Fin X.n → ℚ) (hhat : IsHullLPSol A X hat) :
    ∃ w, IsHullLPSol A X w ∧ ∀ i, w i=hat i → hat i=0 ∨ hat i=1 := by
  classical
  obtain ⟨w,hw,h⟩ := convex_avoid {v | IsHullLPSol A X v} ⟨hat,hhat⟩
    (fun v hv w hw t ht0 ht1 => hull_mix A X hv hw t ht0 ht1)
    hat (univ.filter fun i => hat i ≠ 0 ∧ hat i ≠ 1) (by
      intro i hi
      have hi' := (mem_filter.mp hi).2
      rcases hacc.2 i with ⟨v,hv,hvi⟩ | ⟨v,hv,hvi⟩
      · exact ⟨v,hv,by rw [hvi]; exact Ne.symm hi'.1⟩
      · exact ⟨v,hv,by rw [hvi]; exact Ne.symm hi'.2⟩)
  refine ⟨w,hw,?_⟩
  intro i he
  by_contra hn
  exact h i (by simp only [mem_filter, mem_univ, true_and]; tauto) he
end PCLPProof

set_option autoImplicit false
noncomputable section
namespace PCLPProof
attribute [local instance] Classical.propDecidable
open scoped BigOperators

 theorem replicate_counts {A : Type} [Fintype A] (c : A → ℕ) (D : ℕ)
    (hc : ∑ a, c a = D) :
    ∃ rows : Fin D → A, (∀ t, 0 < c (rows t)) ∧
      ∀ f : A → ℚ, ∑ t, f (rows t) = ∑ a, (c a : ℚ) * f a := by
  classical
  let e : (Σ a, Fin (c a)) ≃ Fin D := Fintype.equivFinOfCardEq (by simpa using hc)
  refine ⟨fun t => (e.symm t).1, ?_, ?_⟩
  · intro t
    exact Nat.zero_lt_of_lt (e.symm t).2.isLt
  · intro f
    calc
      _ = ∑ x : (Σ a, Fin (c a)), f x.1 :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = ∑ a, (c a : ℚ) * f a := by simp [Fintype.sum_sigma]

 theorem replicate_family {K A : Type} [Fintype K] [Fintype A]
    (w : K → A → ℚ) (hw : ∀ k a, 0 ≤ w k a) (hs : ∀ k, ∑ a, w k a = 1) :
    ∃ D : ℕ, 0 < D ∧ ∃ rows : K → Fin D → A,
      (∀ k t, 0 < w k (rows k t)) ∧
      ∀ k a, ((Finset.univ.filter (fun t => rows k t = a)).card : ℚ) = (D:ℚ) * w k a := by
  classical
  let D := Matrix.den w
  have hD : 0 < D := Nat.pos_of_ne_zero (Matrix.den_ne_zero w)
  have hDq : (0:ℚ) < D := by exact_mod_cast hD
  let z := Matrix.num w
  have hz (k : K) (a : A) : (z k a : ℚ) = (D:ℚ) * w k a := by
    have h := Matrix.num_div_den w k a
    exact (div_eq_iff (ne_of_gt hDq)).mp h |>.trans (mul_comm _ _)
  have hzn (k : K) (a : A) : 0 ≤ z k a := by
    exact_mod_cast (show (0:ℚ) ≤ (z k a : ℚ) by rw [hz]; exact mul_nonneg hDq.le (hw k a))
  let c := fun k a => (z k a).toNat
  have hcq (k : K) (a : A) : (c k a : ℚ) = (D:ℚ) * w k a := by
    rw [← hz]
    exact_mod_cast Int.toNat_of_nonneg (hzn k a)
  have hc (k : K) : ∑ a, c k a = D := by
    have h : (∑ a, (c k a : ℚ)) = (D:ℚ) := by simp_rw [hcq]; rw [← Finset.mul_sum, hs, mul_one]
    exact_mod_cast h
  choose rows hp hsum using fun k => replicate_counts (c k) D (hc k)
  refine ⟨D, hD, rows, ?_, ?_⟩
  · intro k t
    have h : (0:ℚ) < (c k (rows k t) : ℚ) := by exact_mod_cast hp k t
    rw [hcq] at h
    exact (mul_pos_iff_of_pos_left hDq).mp h
  · intro k a
    have hh : ((Finset.univ.filter (fun t => rows k t = a)).card : ℚ) = (c k a : ℚ) := by
      simpa using hsum k (fun x => if x = a then (1:ℚ) else 0)
    exact hh.trans (hcq k a)

 theorem replicated_sum {A : Type} [Fintype A] {D : ℕ} (rows : Fin D → A)
    (w : A → ℚ)
    (hc : ∀ a, ((Finset.univ.filter (fun t => rows t = a)).card : ℚ) = (D:ℚ)*w a)
    (f : A → ℚ) : ∑ t, f (rows t) = (D:ℚ) * ∑ a, w a*f a := by
  classical
  calc
    _ = ∑ a, ∑ t ∈ Finset.univ.filter (fun t => rows t = a), f a :=
      (Finset.sum_fiberwise' Finset.univ rows f).symm
    _ = ∑ a, ((Finset.univ.filter (fun t => rows t = a)).card : ℚ) * f a := by simp
    _ = _ := by simp_rw [hc]; rw [Finset.mul_sum]; congr 1; ext a; ring


def pairIndex (D : ℕ) : Fin D × Fin 2 ≃ Fin (2*D) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm D 2))

def interleave {A : Type} {D : ℕ} (a b : Fin D → A) (pad : A) : Fin (2*D+1) → A :=
  Fin.snoc (fun i => if ((pairIndex D).symm i).2 = 0 then a ((pairIndex D).symm i).1
    else b ((pairIndex D).symm i).1) pad

 theorem interleave_mem {A : Type} {D : ℕ} (a b : Fin D → A) (pad : A) (P : A → Prop)
    (ha : ∀ i, P (a i)) (hb : ∀ i, P (b i)) (hp : P pad) :
    ∀ i, P (interleave a b pad i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [interleave] using hp
  · simp only [interleave, Fin.snoc_castSucc]
    split <;> simp_all

 theorem interleave_sum {A : Type} {D : ℕ} (a b : Fin D → A) (pad : A) (f : A → ℚ) :
    ∑ i, f (interleave a b pad i) = (∑ i, f (a i)) + (∑ i, f (b i)) + f pad := by
  rw [Fin.sum_univ_castSucc]
  simp only [interleave, Fin.snoc_castSucc, Fin.snoc_last]
  have h := Fintype.sum_equiv (pairIndex D).symm
    (fun i => f (if ((pairIndex D).symm i).2 = 0 then a ((pairIndex D).symm i).1 else b ((pairIndex D).symm i).1))
    (fun p : Fin D × Fin 2 => f (if p.2 = 0 then a p.1 else b p.1)) (fun _ => rfl)
  rw [h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

 theorem interleave_bit_sum {D : ℕ} (a b : Fin D → Bool) (pad : Bool) :
    (∑ i, if interleave a b pad i then (1:ℚ) else 0) =
    (∑ i, if a i then (1:ℚ) else 0) + (∑ i, if b i then (1:ℚ) else 0) + (if pad then 1 else 0) :=
  interleave_sum a b pad (fun x => if x then 1 else 0)

 theorem interleave_signed_sum {D : ℕ} (a b : Fin D → Bool) (pad : Bool) :
    (∑ i : Fin (2*D+1), (-1:ℤ)^i.val * (if interleave a b pad i then 1 else 0)) =
    (∑ i, if a i then (1:ℤ) else 0) - (∑ i, if b i then (1:ℤ) else 0) + (if pad then 1 else 0) := by
  rw [Fin.sum_univ_castSucc]
  simp only [interleave, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hp : (-1:ℤ)^(2*D) = 1 := by simp [pow_mul]
  rw [hp, one_mul]
  have h := Fintype.sum_equiv (pairIndex D).symm
    (fun i : Fin (2*D) => (-1:ℤ)^i.val * (if (if ((pairIndex D).symm i).2 = 0 then a ((pairIndex D).symm i).1 else b ((pairIndex D).symm i).1) then 1 else 0))
    (fun p : Fin D × Fin 2 => (-1:ℤ)^((pairIndex D p).val) * (if (if p.2=0 then a p.1 else b p.1) then 1 else 0))
    (by intro i; simp)
  rw [h]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, pairIndex, finProdFinEquiv, pow_add, pow_mul, sub_eq_add_neg, Finset.sum_add_distrib]
  have hn (x : Fin D) : (if b x then (-1:ℤ) else 0) = -(if b x then (1:ℤ) else 0) := by split <;> rfl
  simp_rw [hn, Finset.sum_neg_distrib]
  simp
end PCLPProof


open Finset PCSPBLPAff.Symmetric SymBoolPCSP.LPRounding SymBoolPCSP.CFixing
namespace PCLPProof

theorem hw_cast {D : ℕ} (x : Fin D → Bool) :
    (hw x : ℚ) = ∑ i, if x i then 1 else 0 := by
  classical
  exact Finset.natCast_card_filter _ _

theorem majority_interleave {D : ℕ} (x : Fin D → Bool) (b : Bool)
    (v : ℚ) (hcount : (hw x : ℚ) = (D:ℚ)*v) (hD : 0<D) (hv : v ≠ 1/2) :
    Maj (2*D+1) (interleave x x b) = decide ((1/2:ℚ)<v) := by
  classical
  have hsum := interleave_bit_sum x x b
  rw [← hw_cast, ← hw_cast] at hsum
  have hc : hw (interleave x x b) = 2*hw x + (if b then 1 else 0) := by
    have hq : (hw (interleave x x b) : ℚ) = 2*(hw x:ℚ)+(if b then 1 else 0) := by
      rw [hsum]; ring
    exact_mod_cast hq
  have hDq : (0:ℚ)<D := by exact_mod_cast hD
  have hneq : 2*hw x ≠ D := by
    intro he
    have heq : 2*(hw x:ℚ)=(D:ℚ) := by exact_mod_cast he
    apply hv; nlinarith
  have hviff : (1/2:ℚ)<v ↔ D<2*hw x := by
    constructor
    · intro h
      have : (D:ℚ)<2*(hw x:ℚ) := by nlinarith
      exact_mod_cast this
    · intro h
      have : (D:ℚ)<2*(hw x:ℚ) := by exact_mod_cast h
      nlinarith
  simp only [Maj,hc]
  apply decide_eq_decide.mpr
  rw [hviff]
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega

theorem interleave_column {D k : ℕ} (a b : Fin D → Fin k → Bool)
    (pad : Fin k → Bool) (c : Fin k) :
    (fun i => interleave a b pad i c) =
      interleave (fun i => a i c) (fun i => b i c) (pad c) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [interleave]
  · simp only [interleave,Fin.snoc_castSucc]
    split <;> rfl

theorem majority_round {τ : Type} {ar : τ → ℕ}
    (A B : RelStruct τ ar Bool) (X : Instance τ ar)
    (hpol : ∀ L : ℕ, Odd L → IsPolymorphism A B (Maj L))
    (v : Fin X.n → ℚ) (hv : IsHullLPSol A X v) (hhalf : ∀ i, v i ≠ 1/2) :
    SatIn X B := by
  classical
  refine ⟨fun i => decide ((1/2:ℚ)<v i),?_⟩
  intro j
  obtain ⟨α,hα0,hαs,hα1,hαv⟩ := hv.2 j
  obtain ⟨D,hD,rows,hpos,hcard⟩ := replicate_family (fun (_ : Unit) => α)
    (fun _ => hα0) (fun _ => hα1)
  let r := rows ()
  let pad := r ⟨0,hD⟩
  have hr (i : Fin D) : r i ∈ A.rel (X.sym j) := by
    by_contra hn
    have hh := hpos () i
    rw [hαs (r i) hn] at hh
    exact (lt_irrefl 0) hh
  have hp := hpol (2*D+1) ⟨D,by omega⟩ (X.sym j) (interleave r r pad)
    (interleave_mem r r pad (fun y => y ∈ A.rel (X.sym j)) hr hr (hr _))
  have he : (fun c => Maj (2*D+1) (fun i => interleave r r pad i c)) =
      (fun c => decide ((1/2:ℚ)<v (X.scope j c))) := by
    funext c
    rw [interleave_column]
    apply majority_interleave _ _ _ ?_ hD (hhalf _)
    rw [hw_cast]
    have hs := replicated_sum r α (hcard ()) (fun y => if y c then 1 else 0)
    exact hs.trans (congrArg (fun z => (D:ℚ)*z) (hαv c).symm)
  rw [he] at hp
  exact hp
end PCLPProof

set_option autoImplicit false
noncomputable section
namespace PCLPProof
open scoped BigOperators
open PCSPBLPAff.Symmetric SymBoolPCSP.LPRounding SymBoolPCSP.CFixing
attribute [local instance] Classical.propDecidable

 theorem interleave_map {A B : Type} {D : ℕ} (a b : Fin D → A) (pad : A) (f : A → B) (i) :
    f (interleave a b pad i) = interleave (f ∘ a) (f ∘ b) (f pad) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [interleave]
  · simp only [interleave, Fin.snoc_castSucc, Function.comp_apply]
    split <;> rfl

 theorem bit_endpoint {D : ℕ} (b : Fin D → Bool) (t : Fin D) (x : ℚ)
    (hs : (∑ i, if b i then (1:ℚ) else 0) = (D:ℚ)*x)
    (hx : x=0 ∨ x=1) : (if b t then (1:ℚ) else 0) = x := by
  have hb : ∀ i : Fin D, (0:ℚ) ≤ (if b i then 1 else 0) := by intro i; split <;> norm_num
  have hle := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => if b i then (1:ℚ) else 0)
    (fun i _ => hb i) (Finset.mem_univ t)
  rcases hx with rfl | rfl
  · rw [mul_zero] at hs
    linarith [hb t]
  · have hc : (∑ i, if b i then (0:ℚ) else 1) = 0 := by
      have hsum : (∑ i, if b i then (1:ℚ) else 0) + (∑ i, if b i then (0:ℚ) else 1) = D := by
        rw [← Finset.sum_add_distrib]
        calc
          _ = ∑ _i : Fin D, (1:ℚ) := by
            apply Finset.sum_congr rfl
            intro i _
            split <;> norm_num
          _ = D := by simp
      linarith
    have hle' := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => if b i then (0:ℚ) else 1)
      (by intro i _; split <;> norm_num) (Finset.mem_univ t)
    cases h : b t <;> simp_all
    norm_num at *

 theorem alternating_bits {D : ℕ} (hD : 0<D) (a b : Fin D → Bool) (w hat : ℚ)
    (ha : (∑ i, if a i then (1:ℚ) else 0) = (D:ℚ)*w)
    (hb : (∑ i, if b i then (1:ℚ) else 0) = (D:ℚ)*hat)
    (heq : w=hat → hat=0 ∨ hat=1) :
    AT (2*D+1) (interleave a b (b ⟨0,hD⟩)) = decide (hat<w ∨ (w=hat ∧ hat=1)) := by
  let u : ℤ := ∑ i, if a i then 1 else 0
  let v : ℤ := ∑ i, if b i then 1 else 0
  let p : ℤ := if b ⟨0,hD⟩ then 1 else 0
  have hu : (u:ℚ) = (D:ℚ)*w := by simpa [u] using ha
  have hv : (v:ℚ) = (D:ℚ)*hat := by simpa [v] using hb
  have hp : 0≤p ∧ p≤1 := by dsimp [p]; split <;> norm_num
  have hDq : (0:ℚ)<D := by exact_mod_cast hD
  unfold AT
  rw [interleave_signed_sum]
  change decide (0<u-v+p) = decide (hat<w ∨ (w=hat ∧ hat=1))
  apply decide_eq_decide.mpr
  rcases lt_trichotomy w hat with hlt | he | hgt
  · have huv : u<v := by exact_mod_cast (show (u:ℚ)<v by rw [hu,hv]; exact mul_lt_mul_of_pos_left hlt hDq)
    have hn : ¬hat<w := not_lt_of_ge hlt.le
    have hne : w≠hat := ne_of_lt hlt
    have hnon : ¬(0<u-v+p) := by omega
    simp [hnon,hn,hne]
  · have huv : u=v := by exact_mod_cast (show (u:ℚ)=v by rw [hu,hv,he])
    have hep := bit_endpoint b ⟨0,hD⟩ hat hb (heq he)
    have hpc : (p:ℚ)=hat := by simpa [p] using hep
    subst w
    simp only [lt_self_iff_false,true_and,false_or,huv,sub_self,zero_add]
    rcases heq rfl with hz | ho
    · have : p=0 := by exact_mod_cast hpc.trans hz
      simp [this,hz]
    · have : p=1 := by exact_mod_cast hpc.trans ho
      simp [this,ho]
  · have huv : v<u := by exact_mod_cast (show (v:ℚ)<u by rw [hu,hv]; exact mul_lt_mul_of_pos_left hgt hDq)
    simp only [hgt,true_or,iff_true]
    omega

 theorem alternating_round {τ : Type} {ar : τ → ℕ} (A B : RelStruct τ ar Bool)
    (X : Instance τ ar) (hpol : ∀ L, Odd L → IsPolymorphism A B (AT L))
    (w hat : Fin X.n → ℚ) (hw : IsHullLPSol A X w) (hhat : IsHullLPSol A X hat)
    (heq : ∀ i, w i=hat i → hat i=0 ∨ hat i=1) : SatIn X B := by
  classical
  refine ⟨fun i => decide (hat i<w i ∨ (w i=hat i ∧ hat i=1)), ?_⟩
  intro j
  obtain ⟨α,hαn,hαs,hα1,hαm⟩ := hw.2 j
  obtain ⟨β,hβn,hβs,hβ1,hβm⟩ := hhat.2 j
  let weights : Bool → (Fin (ar (X.sym j)) → Bool) → ℚ := fun b => if b then β else α
  have hn : ∀ b a, 0≤weights b a := by intro b a; cases b <;> simp [weights,hαn,hβn]
  have hs : ∀ b, ∑ a, weights b a = 1 := by intro b; cases b <;> simpa [weights] using (by assumption)
  obtain ⟨D,hD,rows,hpos,hcount⟩ := replicate_family weights hn hs
  let a := rows false
  let b := rows true
  let pad := b ⟨0,hD⟩
  have haP : ∀ i, a i ∈ A.rel (X.sym j) := by
    intro i
    by_contra h
    have := hpos false i
    simp only [weights,Bool.false_eq_true,ite_false] at this
    rw [hαs _ h] at this
    exact (lt_irrefl _ this)
  have hbP : ∀ i, b i ∈ A.rel (X.sym j) := by
    intro i
    by_contra h
    have := hpos true i
    simp only [weights,ite_true] at this
    rw [hβs _ h] at this
    exact (lt_irrefl _ this)
  have hm := hpol (2*D+1) ⟨D,by omega⟩ (X.sym j) (interleave a b pad)
    (interleave_mem a b pad (fun y => y ∈ A.rel (X.sym j)) haP hbP (hbP _))
  convert hm using 1
  ext c
  have ha : (∑ i, if a i c then (1:ℚ) else 0) = (D:ℚ)*w (X.scope j c) := by
    rw [hαm c]
    simpa only [a,weights,Bool.false_eq_true,ite_false] using replicated_sum (rows false) (weights false) (hcount false) (fun y => if y c then 1 else 0)
  have hb : (∑ i, if b i c then (1:ℚ) else 0) = (D:ℚ)*hat (X.scope j c) := by
    rw [hβm c]
    simpa only [b,weights,ite_true] using replicated_sum (rows true) (weights true) (hcount true) (fun y => if y c then 1 else 0)
  have hh := alternating_bits hD (fun i => a i c) (fun i => b i c) _ _ ha hb (heq (X.scope j c))
  change decide (hat (X.scope j c)<w (X.scope j c) ∨ (w (X.scope j c)=hat (X.scope j c) ∧ hat (X.scope j c)=1)) = _
  rw [←hh]
  congr 1
  funext l
  exact (interleave_map a b pad (fun y => y c) l).symm
end PCLPProof

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.LPRounding

/-- §3.2, pp. 13–15 (algebraic core of the Majority and Alternating-Threshold cases of
Theorem 3.2, p. 15): let `Γ` be a finite family of Boolean promise relations such that `Maj_L` is a
polymorphism of `Γ` for every odd `L`, or `AT_L` is a polymorphism of `Γ` for every odd `L`. Then
the LP algorithm of §3.2 decides `PCSP(Γ)`: it reports "satisfiable" on every instance with
`Ψ_P` satisfiable, and whenever it reports "satisfiable", `Ψ_Q` is satisfiable. -/
theorem algorithm_3_2_correct {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPQ : ∀ R, 𝔸.rel R ⊆ 𝔹.rel R)
    (hpol : (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.Maj L)) ∨
      (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.AT L))) :
    ∀ X : Instance τ ar,
      (SatIn X 𝔸 → LPAlgAccepts 𝔸 X) ∧ (LPAlgAccepts 𝔸 X → SatIn X 𝔹) := by
  have _promise := hPQ
  intro X
  constructor
  · exact PCLPProof.accepts_of_sat 𝔸 X
  · intro hacc
    rcases hpol with hmaj | hat
    · obtain ⟨v,hv,hhalf⟩ := PCLPProof.accepts_avoids_half 𝔸 X hacc
      exact PCLPProof.majority_round 𝔸 𝔹 X hmaj v hv hhalf
    · obtain ⟨v,hv⟩ := hacc.1
      obtain ⟨w,hw,heq⟩ := PCLPProof.accepts_avoids_interior 𝔸 X hacc v hv
      exact PCLPProof.alternating_round 𝔸 𝔹 X hat w v hw hv heq

end SymBoolPCSP.LPRounding

open PCSPBLPAff.Symmetric SymBoolPCSP.LPRounding
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPQ : ∀ R, 𝔸.rel R ⊆ 𝔹.rel R)
    (hpol : (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.Maj L)) ∨
      (∀ L : ℕ, Odd L → IsPolymorphism 𝔸 𝔹 (SymBoolPCSP.CFixing.AT L))) :
    ∀ X : Instance τ ar,
      (SatIn X 𝔸 → LPAlgAccepts 𝔸 X) ∧ (LPAlgAccepts 𝔸 X → SatIn X 𝔹) := SymBoolPCSP.LPRounding.algorithm_3_2_correct 𝔸 𝔹 hPQ hpol
