-- Prove2me | solution 1 for SingleExpBisect.Main.charged_child_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:39:44.251738+00:00
-- url     : https://prove2.me/submissions/f1793197-1153-4b71-9619-006f8f5a3cbc

import Definitions.Def_SingleExpBisect_Main_ChargedChildConvolution
import Mathlib
import Definitions.Def_SingleExpBisect_Main_Encodings
import Definitions.Def_SingleExpBisect_Main_Graphs
import Theorems.Thm_SingleExpBisect_Main_lemma_3_1
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

set_option autoImplicit false

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT

abbrev LaurentEntry (n : ℕ) := (Var n →₀ ℤ) × ℚ

def isInternal {n : ℕ} : Var n → Bool
  | .y _ => false
  | _ => true

private theorem internal_iff {n : ℕ} (v : Var n) : isInternal v = true ↔ ¬IsYVar v := by
  cases v <;> simp [isInternal,IsYVar]

/-- Test the complete boundary signature, strip the boundary variables and
convert exponents to integers so that negative correction offsets are retained. -/
noncomputable def select {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) : List (LaurentEntry n) :=
  L.filterMap (fun p =>
    if ∀ v : Fin n, p.1 (.y v) = if v ∈ P then 1 else 0 then
      some ((p.1.filter fun v => isInternal v).mapRange (fun a : ℕ => (a:ℤ)) Nat.cast_zero, p.2)
    else none)

/-- Concatenate all monomial products, multiplying the rational coefficients.
Repeated exponents are added by the final coefficient extraction. -/
noncomputable def multiply {n : ℕ} (A B : List (LaurentEntry n)) : List (LaurentEntry n) :=
  A.flatMap fun a => B.map fun b => (a.1+b.1,a.2*b.2)

noncomputable def degreeShift {n : ℕ} (z : ℤ) : List (LaurentEntry n) := [(Finsupp.single .w z,1)]

/-- Process the child factors by sparse convolution; do not truncate before
the negative child corrections and the parent correction have all been added. -/
noncomputable def combine {n : ℕ} (base : ℤ) (factors : List (List (LaurentEntry n))) (k : ℕ) :
    List (LaurentEntry n) :=
  (factors.foldl multiply (degreeShift base)).filter (fun e => e.1 (.w) ≤ (k:ℤ))

def coefficient {n : ℕ} (q : Var n →₀ ℤ) (L : List (LaurentEntry n)) : ℚ :=
  ((L.filter (fun p => decide (p.1 = q))).map Prod.snd).sum

private noncomputable def decode {n : ℕ} (L : List (Entry n)) : MvPolynomial (Var n) ℚ :=
  (L.map (fun p => MvPolynomial.monomial p.1 p.2)).sum

private noncomputable def decodeL {n : ℕ} (L : List (LaurentEntry n)) : LPoly n :=
  (L.map (fun p => AddMonoidAlgebra.single p.1 p.2)).sum

private theorem decode_coeff {n : ℕ} (e : Var n →₀ ℕ) (L : List (Entry n)) :
    MvPolynomial.coeff e (decode L) = ((L.filter (fun p => decide (p.1 = e))).map Prod.snd).sum := by
  induction L with
  | nil => simp [decode]
  | cons p L ih =>
    by_cases he : p.1 = e <;> simp [decode,he,MvPolynomial.coeff_monomial] at ih ⊢ <;> exact ih

private theorem decode_rep {n : ℕ} (F : MvPolynomial (Var n) ℚ) (L : List (Entry n))
    (h : IsSparseRep L (fun e => MvPolynomial.coeff e F)) : decode L = F := by
  ext e
  exact (decode_coeff e L).trans (h.2.2 e).symm

private theorem project_add {n : ℕ} (P : Finset (Fin n)) (F H : MvPolynomial (Var n) ℚ) :
    yCoeff P (F+H) = yCoeff P F + yCoeff P H := by
  classical
  let f := fun (e : Var n →₀ ℕ) (q : ℚ) =>
    if (∀ v : Fin n, e (Var.y v) = if v ∈ P then 1 else 0) then
      MvPolynomial.monomial (e.filter fun z => ¬ IsYVar z) q else 0
  change ((AddMonoidAlgebra.coeff F + AddMonoidAlgebra.coeff H).sum f) =
      (AddMonoidAlgebra.coeff F).sum f + (AddMonoidAlgebra.coeff H).sum f
  apply Finsupp.sum_add_index'
  · intro e; dsimp only [f]; split <;> simp
  · intro e x y; dsimp only [f]; split <;> simp

private theorem toL_add {n : ℕ} (P Q : MvPolynomial (Var n) ℚ) : toL (P+Q) = toL P+toL Q := by
  classical
  exact AddMonoidAlgebra.mapDomain_add ..

private theorem selected {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) :
    decodeL (select P L) = toL (yCoeff P (decode L)) := by
  classical
  induction L with
  | nil => simp [select,decodeL,decode,yCoeff,toL]
  | cons p L ih =>
    change decodeL (select P (p::L)) = toL (yCoeff P (MvPolynomial.monomial p.1 p.2 + decode L))
    rw [project_add,toL_add,←ih]
    have same : p.1.filter (fun v => isInternal v) = p.1.filter (fun v => ¬ IsYVar v) := by
      ext v; simp only [Finsupp.filter_apply,internal_iff]
    by_cases matchAll : ∀ v : Fin n, p.1 (.y v) = if v ∈ P then 1 else 0
    · simp only [select,List.filterMap_cons,if_pos matchAll]
      change AddMonoidAlgebra.single _ _ + decodeL (select P L) = _ + _
      congr 1
      by_cases hq : p.2 = 0
      · simp [hq,toL,yCoeff]
      · have mono : yCoeff P (MvPolynomial.monomial p.1 p.2) =
            MvPolynomial.monomial (p.1.filter fun z => ¬IsYVar z) p.2 := by
          simp [yCoeff,MvPolynomial.support_monomial,hq,MvPolynomial.coeff_monomial,matchAll]
        rw [mono,toL,← MvPolynomial.single_eq_monomial,AddMonoidAlgebra.mapDomain_single,same]
    · have none : select P (p::L) = select P L := by simp [select,matchAll]
      rw [none]
      by_cases hq : p.2 = 0
      · simp [hq,toL,yCoeff]
      · simp [yCoeff,MvPolynomial.support_monomial,hq,MvPolynomial.coeff_monomial,matchAll,toL]

private theorem single_mul_list {n : ℕ} (a : LaurentEntry n) (B : List (LaurentEntry n)) :
    decodeL (B.map fun b => (a.1+b.1,a.2*b.2)) = AddMonoidAlgebra.single a.1 a.2 * decodeL B := by
  induction B with
  | nil => simp [decodeL]
  | cons b B ih =>
    change AddMonoidAlgebra.single _ _ + decodeL _ = _ * (AddMonoidAlgebra.single _ _ + decodeL B)
    rw [mul_add, AddMonoidAlgebra.single_mul_single, ih]

private theorem product_exact {n : ℕ} (A B : List (LaurentEntry n)) :
    decodeL (multiply A B) = decodeL A * decodeL B := by
  induction A with
  | nil => simp [decodeL,multiply]
  | cons a A ih =>
    have app (u v : List (LaurentEntry n)) : decodeL (u++v) = decodeL u+decodeL v := by simp [decodeL]
    change decodeL (_ ++ multiply A B) = (AddMonoidAlgebra.single _ _ + decodeL A) * decodeL B
    rw [app,single_mul_list,ih,add_mul]

private theorem trunc_add {n : ℕ} (k : ℕ) (a b : LPoly n) :
    truncWL k (a+b) = truncWL k a + truncWL k b := by
  classical
  unfold truncWL; simp [Finsupp.filter_add]

private theorem cutoff {n : ℕ} (k : ℕ) (L : List (LaurentEntry n)) :
    decodeL (L.filter (fun p => p.1 (.w) ≤ (k:ℤ))) = truncWL k (decodeL L) := by
  classical
  induction L with
  | nil =>
    change 0 = truncWL k 0
    have t : truncWL k (0 : LPoly n) + 0 = truncWL k 0 + truncWL k 0 := by
      simpa only [add_zero] using trunc_add (n:=n) k 0 0
    exact add_left_cancel t
  | cons a L ih =>
    change _ = truncWL k (AddMonoidAlgebra.single a.1 a.2 + decodeL L)
    rw [trunc_add,←ih]
    by_cases h : a.1 (.w) ≤ (k:ℤ)
    · rw [List.filter_cons_of_pos (by simpa using h)]
      change AddMonoidAlgebra.single _ _ + _ = _ + _
      congr 1
      unfold truncWL
      rw [AddMonoidAlgebra.coeff_single,Finsupp.filter_single_of_pos (fun e : Var n →₀ ℤ => e Var.w ≤ (k:ℤ)) h]; rfl
    · rw [List.filter_cons_of_neg (by simpa using h)]
      have hz : truncWL k (AddMonoidAlgebra.single a.1 a.2) = 0 := by
        unfold truncWL
        rw [AddMonoidAlgebra.coeff_single,Finsupp.filter_single_of_neg (fun e : Var n →₀ ℤ => e Var.w ≤ (k:ℤ)) h]; rfl
      rw [hz,zero_add]

private theorem folded {n : ℕ} (F : List (List (LaurentEntry n))) (A : List (LaurentEntry n)) :
    decodeL (F.foldl multiply A) = decodeL A * (F.map decodeL).prod := by
  induction F generalizing A with
  | nil => simp
  | cons f F ih => simp only [List.foldl_cons,List.map_cons,List.prod_cons,ih,product_exact,mul_assoc]

private theorem coefficients {n : ℕ} (q : Var n →₀ ℤ) (L : List (LaurentEntry n)) :
    (decodeL L).coeff q = coefficient q L := by
  induction L with
  | nil => simp [decodeL,coefficient]
  | cons a L ih =>
    change (AddMonoidAlgebra.single a.1 a.2 + decodeL L).coeff q = _
    rw [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,AddMonoidAlgebra.coeff_single,ih]
    by_cases he : a.1=q <;> simp [coefficient,he] 

private theorem degreeShiftExact {n : ℕ} (z : ℤ) : decodeL (degreeShift (n:=n) z) = wPow z := by
  simp [decodeL,degreeShift,wPow]

/-- All child corrections and base terms are parameters to the computation and
can be precomputed separately. No query is made to any child's semantic Z polynomial. -/
noncomputable def fromChildren {n : ℕ} (k : ℕ) (base : ℤ) (P : List (Finset (Fin n) × ℤ × List (Entry n))) :
    List (LaurentEntry n) :=
  combine base (P.map fun (sig,c,L) => multiply (degreeShift (-c)) (select sig L)) k

theorem childConvolution {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (hT : IsRootedTreeDecomp G T) (k : ℕ) (t : Fin T.N) (R : Finset (Fin n))
    (hR : R ⊆ T.bag t) (Lc : Fin T.N → List (Entry n))
    (children : ∀ s, T.parent s = some t →
        IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R ∩ T.adhesion t) : ℕ) : ℤ)
    let factors := (T.children t).toList.map (fun s =>
      (R ∩ T.adhesion s,((etaNode G T s (R ∩ T.adhesion s) : ℕ) : ℤ),Lc s))
    ∀ q : Var n →₀ ℤ, coefficient q (fromChildren k base factors) =
      (toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff q := by
  classical
  dsimp only
  intro q
  rw [←coefficients,lemma_3_1 G T hT k t R hR]
  apply congrArg (fun P : LPoly n => P.coeff q)
  rw [fromChildren,combine,cutoff,folded,degreeShiftExact]
  congr 2
  rw [List.map_map,List.map_map,Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro s hs
  have child : T.parent s = some t := (Finset.mem_filter.mp hs).2
  dsimp only [Function.comp_apply]
  rw [product_exact,degreeShiftExact,selected,decode_rep _ _ (children s child)]

end SingleExpBisect.Convolution


set_option autoImplicit false
namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT



private noncomputable def expand {n : ℕ} (d : Degrees) : Var n →₀ ℤ :=
  Finsupp.single .x d.x + Finsupp.single .x' d.aux + Finsupp.single .w d.w

private theorem expand_injective (n : ℕ) : Function.Injective (expand (n:=n)) := by
  intro a b h
  have hx := congrArg (fun (e : Var n →₀ ℤ) => e .x) h
  have ha := congrArg (fun (e : Var n →₀ ℤ) => e .x') h
  have hw := congrArg (fun (e : Var n →₀ ℤ) => e .w) h
  simp [expand] at hx ha hw
  cases a; cases b; congr

private theorem expand_add {n : ℕ} (a b : Degrees) :
    expand (n:=n) (degreesAdd a b) = expand a + expand b := by
  ext v; cases v <;> simp [expand,degreesAdd]

private theorem expand_w {n : ℕ} (d : Degrees) : expand (n:=n) d .w = d.w := by
  simp [expand]




/-- Native executable evaluator. Inputs are the local correction and the actual
lists of child terms, annotated with their boundary set and correction. -/
def evaluate {n : ℕ} (k : ℕ) (base : ℤ) (children : List (SparseChild n)) (q : Degrees) : ℚ :=
  let factors := children.map fun (P,c,L) =>
    multiplyDegrees [(wDegree (-c),1)] (selectDegrees P L)
  let terms := factors.foldl multiplyDegrees [(wDegree base,1)]
  (((terms.filter fun p => p.1.w ≤ (k:ℤ)).filter fun p => p.1 = q).map Prod.snd).sum

private noncomputable def embed {n : ℕ} (a : CoeffEntry) : LaurentEntry n :=
  (expand a.1,a.2)

private theorem selected_degrees {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) :
    (selectDegrees P L).map (embed (n:=n)) = select P L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases p with ⟨e,c⟩
    by_cases matchAll : ∀ v : Fin n, e (.y v) = if v ∈ P then 1 else 0
    · simp only [select,selectDegrees,List.filterMap_cons,if_pos matchAll,List.map_cons]
      congr 2
      unfold embed
      congr 1
      ext z
      rw [Finsupp.mapRange_apply,Finsupp.filter_apply]
      cases z <;> simp [expand,isInternal]
    · simpa [select,selectDegrees,matchAll] using ih

private theorem multiplication {n : ℕ} (A B : List CoeffEntry) :
    (multiplyDegrees A B).map (embed (n:=n)) = multiply (A.map embed) (B.map embed) := by
  simp [multiplyDegrees,multiply,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,embed,expand_add]

private theorem singleton {n : ℕ} (c : ℤ) : [(wDegree c, (1:ℚ))].map (embed (n:=n)) = degreeShift c := by
  simp [embed,degreeShift,wDegree,expand]

private theorem fold_map {n : ℕ} (F : List (List CoeffEntry)) (A : List CoeffEntry) :
    (F.foldl multiplyDegrees A).map (embed (n:=n)) =
      (F.map (fun L => L.map embed)).foldl multiply (A.map embed) := by
  induction F generalizing A with
  | nil => rfl
  | cons f F ih => simp only [List.foldl_cons,List.map_cons,ih,multiplication]

private theorem result {n : ℕ} (k : ℕ) (q : Degrees) (L : List CoeffEntry) :
    coefficient (expand (n:=n) q)
      ((L.map embed).filter (fun p => p.1 (.w) ≤ (k:ℤ))) =
      (((L.filter fun p => p.1.w ≤ (k:ℤ)).filter fun p => p.1=q).map Prod.snd).sum := by
  have inj (a : CoeffEntry) : expand (n:=n) a.1 = expand q ↔ a.1=q := (expand_injective n).eq_iff
  simp only [coefficient,List.filter_map,List.map_map,Function.comp_def,embed,expand_w,inj]

private theorem executable_eq {n : ℕ} (k : ℕ) (base : ℤ) (P : List (SparseChild n)) (q : Degrees) :
    evaluate k base P q = coefficient (expand q) (fromChildren k base P) := by
  let F := P.map (fun (sig,c,L) => multiplyDegrees [(wDegree (-c),1)] (selectDegrees sig L))
  let L := F.foldl multiplyDegrees [(wDegree base,1)]
  have fs : F.map (fun L => L.map (embed (n:=n))) =
      P.map (fun (sig,c,L) => multiply (degreeShift (-c)) (select sig L)) := by
    simp only [F,List.map_map]
    apply List.map_congr_left
    rintro ⟨sig,c,L⟩ _
    change (multiplyDegrees [(wDegree (-c),1)] (selectDegrees sig L)).map embed = _
    rw [multiplication,singleton,selected_degrees]
  have eq : L.map (embed (n:=n)) =
      (P.map (fun (sig,c,L) => multiply (degreeShift (-c)) (select sig L))).foldl multiply (degreeShift base) := by
    rw [show L.map (embed (n:=n)) = _ from fold_map ..,fs,singleton]
  unfold fromChildren combine
  rw [←eq,result]
  rfl

/-- Recover any Q coefficient from the child term lists in equation (8) of the
paper. The supplied offsets are exactly those of the published recurrence. -/
theorem evaluate_Q {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (hT : IsRootedTreeDecomp G T) (k : ℕ) (t : Fin T.N) (R : Finset (Fin n))
    (hR : R ⊆ T.bag t) (Lc : Fin T.N → List (Entry n))
    (children : ∀ s, T.parent s = some t →
        IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) (q : Degrees) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R ∩ T.adhesion t) : ℕ) : ℤ)
    let factors := (T.children t).toList.map (fun s =>
      (R ∩ T.adhesion s,((etaNode G T s (R ∩ T.adhesion s) : ℕ) : ℤ),Lc s))
    evaluate k base factors q = (toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff
      (Finsupp.single .x q.x + Finsupp.single .x' q.aux + Finsupp.single .w q.w) := by
  dsimp only
  rw [executable_eq]
  exact childConvolution G T hT k t R hR Lc children (expand q)

end SingleExpBisect.Convolution



namespace SingleExpBisect.Sparse
variable {K : Type} [DecidableEq K]
abbrev weight (s : Table K) (f : K → ℚ) := (s.map fun p => p.2 * f p.1).sum


theorem insert_weight (q : K × ℚ) (s : Table K) (f : K → ℚ) :
    weight (insertEntry q s).1 f = q.2*f q.1 + weight s f := by
  induction s with
  | nil => simp [insertEntry,weight]
  | cons p s ih =>
    by_cases h : q.1=p.1
    · simp [insertEntry,h,weight,add_mul]; ring
    · simp only [insertEntry,h,if_false,List.map_cons,List.sum_cons] at ih ⊢
      dsimp only [weight] at ih ⊢
      simp only [List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]; ring

theorem insert_keys (q : K × ℚ) (s : Table K) (k : K) :
    k ∈ ((insertEntry q s).1.map Prod.fst) ↔ k=q.1 ∨ k ∈ s.map Prod.fst := by
  induction s with
  | nil => simp [insertEntry]
  | cons p s ih =>
    by_cases h : q.1=p.1
    · simp [insertEntry,h]
    · simp [insertEntry,h,ih,or_comm,or_left_comm,or_assoc]

theorem insert_nodup (q : K × ℚ) (s : Table K) (nd : (s.map Prod.fst).Nodup) :
    ((insertEntry q s).1.map Prod.fst).Nodup := by
  induction s with
  | nil => simp [insertEntry]
  | cons p s ih =>
    by_cases h : q.1=p.1
    · simpa [insertEntry,h] using nd
    · have hh := List.nodup_cons.mp nd
      simpa [insertEntry,h,insert_keys,Ne.symm h,hh.1] using ih hh.2

theorem insert_cost (q : K × ℚ) (s : Table K) : (insertEntry q s).2 ≤ s.length+1 := by
  induction s with
  | nil => simp [insertEntry]
  | cons p s ih => by_cases h : q.1=p.1 <;> simp [insertEntry,h] <;> omega


theorem absorb_weight (input : Table K) (acc : Table K × ℕ) (f : K → ℚ) :
    weight (absorb input acc).1 f = weight input f + weight acc.1 f := by
  induction input generalizing acc with
  | nil => simp [absorb,weight]
  | cons q l ih =>
    rw [show absorb (q::l) acc=absorb l ((insertEntry q acc.1).1,acc.2+3+(insertEntry q acc.1).2) from rfl,ih]
    simp only [insert_weight,weight,List.map_cons,List.sum_cons]; ring

theorem absorb_nodup (input : Table K) (acc : Table K × ℕ) (nd : (acc.1.map Prod.fst).Nodup) :
    ((absorb input acc).1.map Prod.fst).Nodup := by
  induction input generalizing acc with
  | nil => exact nd
  | cons q l ih => exact ih _ (insert_nodup q _ nd)

theorem absorb_keys (l : Table K) (acc : Table K × ℕ) (k : K) :
    k ∈ (absorb l acc).1.map Prod.fst ↔ k ∈ l.map Prod.fst ∨ k ∈ acc.1.map Prod.fst := by
  induction l generalizing acc with
  | nil => simp [absorb]
  | cons q l ih =>
    rw [show absorb (q::l) acc=absorb l ((insertEntry q acc.1).1,acc.2+3+(insertEntry q acc.1).2) from rfl,ih]
    simp [insert_keys,or_comm,or_left_comm,or_assoc]

theorem length_le {l : Table K} {keys : Finset K} (nd : (l.map Prod.fst).Nodup)
    (inside : ∀ k ∈ l.map Prod.fst,k∈keys) : l.length ≤ keys.card := by
  rw [← List.length_map (f:=Prod.fst) (as:=l),← List.toFinset_card_of_nodup nd]
  exact Finset.card_le_card (fun _ h => inside _ (List.mem_toFinset.mp h))

theorem absorb_cost (l : Table K) (acc : Table K × ℕ) (keys : Finset K)
    (nd : (acc.1.map Prod.fst).Nodup) (valid : ∀ k ∈ acc.1.map Prod.fst,k∈keys)
    (input : ∀ k ∈ l.map Prod.fst,k∈keys) :
    (absorb l acc).2 ≤ acc.2 + l.length*(keys.card+4) := by
  induction l generalizing acc with
  | nil => simp [absorb]
  | cons q l ih =>
    let next := ((insertEntry q acc.1).1,acc.2+3+(insertEntry q acc.1).2)
    have newkeys (k) (h : k∈next.1.map Prod.fst) : k∈keys := by
      rcases (insert_keys q acc.1 k).mp h with rfl|old
      · exact input _ (by simp)
      · exact valid _ old
    have rem := ih next (insert_nodup _ _ nd) newkeys (fun k h => input k (by simp [h]))
    have cost := insert_cost q acc.1
    have short := length_le nd valid
    change (absorb l next).2 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [next] at rem ⊢
    omega

variable (add : K → K → K)
theorem product_size (x y : Table K) : (products add x y).length=x.length*y.length := by
  induction x with
  | nil => simp [products]
  | cons a x ih => simp only [products,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,Nat.add_mul,Nat.one_mul] at ih ⊢; omega

theorem product_weight (x y : Table K) (f : K → ℚ) :
    weight (products add x y) f = weight x (fun k => weight y (fun b => f (add k b))) := by
  induction x with
  | nil => simp [products,weight]
  | cons a x ih =>
    have block : weight (y.map (fun b => (add a.1 b.1,a.2*b.2))) f =
        a.2*weight y (fun b => f (add a.1 b)) := by
      clear ih
      induction y with
      | nil => simp [weight]
      | cons b y ih =>
        simp only [weight,List.map_cons,List.sum_cons,mul_add] at ih ⊢
        rw [ih]; ring
    simp only [products,List.flatMap_cons,weight,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at ih block ⊢
    rw [ih,block]

theorem multiply_weight (x y : Table K) (f : K → ℚ) :
    weight (multiply add x y).1 f = weight x (fun k => weight y (fun b => f (add k b))) := by
  rw [multiply,absorb_weight,product_weight]; simp [weight]

theorem multiply_cost (x y : Table K) (domain : Finset K) (ok : ∀ a∈x,∀ b∈y,add a.1 b.1 ∈ domain) :
    (multiply add x y).2 ≤ x.length+1+x.length*y.length*(domain.card+4) := by
  rw [← product_size add x y]
  apply absorb_cost _ _ domain (by simp) (by simp)
  intro k hk
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
  obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hq
  obtain ⟨b,hb,eq⟩ := List.mem_map.mp hb
  exact (congrArg Prod.fst eq) ▸ ok a ha b hb
end SingleExpBisect.Sparse

namespace SingleExpBisect.Sparse
variable {K : Type} [DecidableEq K] (add : K → K → K)

def inside (l : Table K) (keys : Finset K) := ∀ k ∈ l.map Prod.fst,k∈keys
def closed (x y : Table K) (keys : Finset K) := ∀ a∈x,∀ b∈y,add a.1 b.1∈keys

theorem multiply_valid (x y : Table K) (keys : Finset K) (h : closed add x y keys) :
    ((multiply add x y).1.map Prod.fst).Nodup ∧ inside (multiply add x y).1 keys := by
  constructor
  · apply absorb_nodup; simp
  · intro k hk
    rw [multiply,absorb_keys] at hk
    simp only [List.map_nil,List.not_mem_nil,or_false] at hk
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hq
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp hb
    exact (congrArg Prod.fst eq) ▸ h a ha b hb


theorem layers_equiv (ys : List (Table K)) (x1 x2 : Table K)
    (same : ∀ f, weight x1 f=weight x2 f) (f : K → ℚ) :
    weight (layers add x1 ys).1 f = weight (ys.foldl (products add) x2) f := by
  induction ys generalizing x1 x2 with
  | nil => exact same f
  | cons y l ih =>
    change weight (layers add (multiply add x1 y).1 l).1 f =
      weight (l.foldl (products add) (products add x2 y)) f
    apply ih
    intro g
    rw [multiply_weight,product_weight,same]

/-- The finite sets may vary at each layer, e.g. as signed offsets move. -/
def Admissible (U : ℕ → Finset K) (N M : ℕ) (i : ℕ) : List (Table K) → Prop
  | [] => True
  | y::ys => (U i).card ≤ N ∧ (U (i+1)).card ≤ N ∧ y.length ≤ M ∧
      (∀ a ∈ U i,∀ b∈y,add a b.1 ∈ U (i+1)) ∧ Admissible U N M (i+1) ys

theorem layers_bound (U : ℕ → Finset K) (N M i : ℕ) (ys : List (Table K)) (x : Table K)
    (nd : (x.map Prod.fst).Nodup) (ok : inside x (U i)) (h : Admissible add U N M i ys) :
    (layers add x ys).2 ≤ ys.length * (N+1+N*M*(N+4)) ∧
    ((layers add x ys).1.map Prod.fst).Nodup ∧ inside (layers add x ys).1 (U (i+ys.length)) := by
  induction ys generalizing i x with
  | nil => simpa [layers] using And.intro (Nat.zero_le 0) (And.intro nd ok)
  | cons y ys ih =>
    obtain ⟨hi,hj,hm,cl,tail⟩ := h
    have cp : closed add x y (U (i+1)) := fun a ha b hb =>
      cl a.1 (ok _ (List.mem_map_of_mem ha)) b hb
    obtain ⟨dup,supp⟩ := multiply_valid add x y _ cp
    obtain ⟨rec1,rec2,rec3⟩ := ih (i+1) _ dup supp tail
    have hx := (length_le nd ok).trans hi
    have step := multiply_cost add x y _ cp
    have lim : (multiply add x y).2 ≤ N+1+N*M*(N+4) :=
      step.trans (Nat.add_le_add (by omega) (Nat.mul_le_mul (Nat.mul_le_mul hx hm) (by omega)))
    constructor
    · change (multiply add x y).2+(layers add (multiply add x y).1 ys).2 ≤ _
      rw [List.length_cons,Nat.succ_mul]
      omega
    · exact ⟨rec2,by simpa only [layers,List.length_cons,Nat.add_right_comm,Nat.add_assoc,
           Nat.add_comm 1 ys.length] using rec3⟩
end SingleExpBisect.Sparse


namespace SingleExpBisect.Sparse
variable {K : Type} [DecidableEq K] (add : K → K → K)

def natTable (A : Table K) : Prop := ∀ p∈A,∃ n : ℕ,p.2=(n:ℚ)
theorem insert_nat (q : K × ℚ) (A : Table K) (nq : ∃ n : ℕ,q.2=(n:ℚ)) (ha : natTable A) :
    natTable (insertEntry q A).1 := by
  induction A with
  | nil => simpa [insertEntry,natTable] using nq
  | cons p l ih =>
    have hp := ha p (by simp)
    have tail : natTable l := fun b hb => ha b (by simp [hb])
    intro t ht
    by_cases eqn : q.1=p.1
    · simp only [insertEntry,eqn,if_true,List.mem_cons] at ht
      rcases ht with rfl|hr
      · obtain ⟨i,hi⟩ := hp
        obtain ⟨j,hj⟩ := nq
        exact ⟨i+j,by simp [hi,hj]⟩
      · exact tail _ hr
    · simp only [insertEntry,eqn,if_false,List.mem_cons] at ht
      rcases ht with rfl|hr
      · exact hp
      · exact ih tail t hr

theorem absorb_nat (ys : Table K) (acc : Table K × ℕ) (h1 : natTable ys) (h2 : natTable acc.1) :
    natTable (absorb ys acc).1 := by
  induction ys generalizing acc with
  | nil => exact h2
  | cons y ys ih =>
    exact ih _ (fun q h => h1 q (by simp [h])) (insert_nat _ _ (h1 _ (by simp)) h2)

theorem multiply_nat (A B : Table K) (ha : natTable A) (hb : natTable B) :
    natTable (multiply add A B).1 := by
  apply absorb_nat _ _ _ (by simp [natTable])
  intro q hq
  obtain ⟨a,ham,h⟩ := List.mem_flatMap.mp hq
  obtain ⟨b,hbm,rfl⟩ := List.mem_map.mp h
  obtain ⟨i,hi⟩ := ha a ham
  obtain ⟨j,hj⟩ := hb b hbm
  exact ⟨i*j,by simp [hi,hj]⟩

def mass (A : Table K) := (A.map Prod.snd).sum

theorem scalar (A : Table K) (c : ℚ) : weight A (fun _ => c) = mass A*c := by
  induction A with
  | nil => simp [weight,mass]
  | cons a A ih =>
    change a.2*c+weight A (fun _ => c)=(a.2+mass A)*c
    rw [ih,add_mul]

theorem mass_product (A B : Table K) : mass (multiply add A B).1 = mass A * mass B := by
  have h := multiply_weight add A B (fun _ => 1)
  simp only [scalar,mul_one] at h
  exact h

theorem mass_nonneg (A : Table K) (h : natTable A) : 0 ≤ mass A := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    obtain ⟨n,ha⟩ := h a (by simp)
    exact add_nonneg (show 0 ≤ a.2 by rw [ha]; positivity) (ih (fun p hp => h p (by simp [hp])))

theorem entry_le_mass (A : Table K) (h : natTable A) (a : K×ℚ) (hin : a∈A) : a.2 ≤ mass A := by
  induction A with
  | nil => simp at hin
  | cons b A ih =>
    have hh : natTable A := fun p hp => h p (by simp [hp])
    obtain ⟨i,hi⟩ := h b (by simp)
    change _ ≤ b.2+mass A
    rcases List.mem_cons.mp hin with rfl|ht
    · have hh₁ := mass_nonneg A hh; linarith
    · have hh₂ := ih hh ht
      have pp : 0 ≤ b.2 := hi ▸ Nat.cast_nonneg _
      linarith

theorem bounded_mass (A : Table K) (M : ℕ) (h : ∀ p∈A,p.2 ≤ (M:ℚ)) : mass A ≤ A.length*M := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun p hp => h p (by simp [hp]))
    change a.2+mass A ≤ _
    push_cast
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    linarith

theorem layers_mass (A : Table K) (ys : List (Table K)) (B : ℕ)
    (hn : natTable A) (hi : ∀ y∈ys,natTable y ∧ mass y ≤ (B:ℚ)) :
    natTable (layers add A ys).1 ∧ mass (layers add A ys).1 ≤ mass A*(B:ℚ)^ys.length := by
  induction ys generalizing A with
  | nil => simpa [layers] using hn
  | cons y ys ih =>
    obtain ⟨hyn,hyb⟩ := hi y (by simp)
    obtain ⟨nd,h⟩ := ih (multiply add A y).1 (multiply_nat add A y hn hyn)
      (fun v hv => hi v (by simp [hv]))
    refine ⟨nd,?_⟩
    change mass (layers add (multiply add A y).1 ys).1 ≤ _
    rw [mass_product] at h
    rw [List.length_cons,pow_succ]
    calc _ ≤ mass A*mass y*(B:ℚ)^ys.length := h
         _ ≤ mass A*(B:ℚ)*(B:ℚ)^ys.length :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyb (mass_nonneg _ hn)) (by positivity)
         _ = _ := by ring
end SingleExpBisect.Sparse

namespace SingleExpBisect.Convolution
open SingleExpBisect.Sparse

def box (x w : ℕ) (offset : ℤ) : Finset Degrees :=
  ((Finset.range (x+1)).product (Finset.range (w+1))).image
    (fun p => ⟨p.1,0,offset+p.2⟩)

theorem box_card (x w : ℕ) (off : ℤ) : (box x w off).card ≤ (x+1)*(w+1) := by
  unfold box
  exact Finset.card_image_le.trans (by simp)

theorem box_cases {x w : ℕ} {off : ℤ} {d : Degrees} : d ∈ box x w off ↔
    ∃ a b : ℕ, a ≤ x ∧ b ≤ w ∧ d=⟨a,0,off+b⟩ := by
  unfold box
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp h
    have hc := Finset.mem_product.mp hp
    exact ⟨a,b,Nat.lt_succ_iff.mp (Finset.mem_range.mp hc.1),Nat.lt_succ_iff.mp (Finset.mem_range.mp hc.2),rfl⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩,rfl⟩

theorem box_add {x w m k : ℕ} {c e : ℤ} {a b : Degrees}
    (ha : a ∈ box x w c) (hb : b ∈ box m k e) :
    degreesAdd a b ∈ box (x+m) (w+k) (c+e) := by
  obtain ⟨a₁,a₂,h₁,h₂,rfl⟩ := box_cases.mp ha
  obtain ⟨b₁,b₂,h₃,h₄,rfl⟩ := box_cases.mp hb
  apply box_cases.mpr
  refine ⟨a₁+b₁,a₂+b₂,by omega,by omega,?_⟩
  simp [degreesAdd,add_assoc,add_comm,add_left_comm]

def legal (n k M : ℕ) (s : ShiftFactor) := s.2.length ≤ M ∧ inside s.2 (box n k s.1)

theorem bounded_layers (n k M X W : ℕ) (cs : List ShiftFactor) (x w : ℕ) (c : ℤ)
    (A : Table Degrees) (ha : (A.map Prod.fst).Nodup) (sa : inside A (box x w c))
    (hs : ∀ p∈cs,legal n k M p) (cx : x+cs.length*n ≤ X) (cw : w+cs.length*k ≤ W) :
    let D := (X+1)*(W+1)
    (layers degreesAdd A (cs.map Prod.snd)).2 ≤ cs.length*(D+1+D*M*(D+4)) ∧
    ((layers degreesAdd A (cs.map Prod.snd)).1.map Prod.fst).Nodup ∧
    inside (layers degreesAdd A (cs.map Prod.snd)).1 (box (x+cs.length*n) (w+cs.length*k) (c+(cs.map Prod.fst).sum)) := by
  induction cs generalizing x w c A with
  | nil => simpa [layers] using And.intro (Nat.zero_le 0) (And.intro ha sa)
  | cons p cs ih =>
    let D := (X+1)*(W+1)
    have hp := hs p (by simp)
    have tail : ∀ s∈cs,legal n k M s := fun s h => hs s (by simp [h])
    simp only [List.length_cons,Nat.succ_mul] at cx cw
    have cx' : (x+n)+cs.length*n ≤ X := by omega
    have cw' : (w+k)+cs.length*k ≤ W := by omega
    have cp : closed degreesAdd A p.2 (box (x+n) (w+k) (c+p.1)) := fun a h b hb =>
      box_add (sa _ (List.mem_map_of_mem h)) (hp.2 _ (List.mem_map_of_mem hb))
    obtain ⟨nd,su⟩ := multiply_valid degreesAdd A p.2 _ cp
    obtain ⟨hr,dr,sr⟩ := ih (x+n) (w+k) (c+p.1) _ nd su tail cx' cw'
    have cap (a b : ℕ) (u : ℤ) (ax : a ≤ X) (bw : b ≤ W) : (box a b u).card ≤ D :=
      (box_card a b u).trans (Nat.mul_le_mul (by omega) (by omega))
    have ca := cap x w c (by omega) (by omega)
    have cb := cap (x+n) (w+k) (c+p.1) (by omega) (by omega)
    have l := (length_le ha sa).trans ca
    have m := hp.1
    have step : (SingleExpBisect.Sparse.multiply degreesAdd A p.2).2 ≤ D+1+D*M*(D+4) :=
      (multiply_cost degreesAdd A p.2 _ cp).trans (Nat.add_le_add (by omega)
        (Nat.mul_le_mul (Nat.mul_le_mul l m) (by omega)))
    constructor
    · change (SingleExpBisect.Sparse.multiply degreesAdd A p.2).2 + (layers degreesAdd (SingleExpBisect.Sparse.multiply degreesAdd A p.2).1 (cs.map Prod.snd)).2 ≤ _
      change _ ≤ (cs.length+1)*(D+1+D*M*(D+4))
      rw [Nat.succ_mul]
      exact (Nat.add_le_add step hr).trans_eq (Nat.add_comm ..)
    · constructor
      · exact dr
      · change inside (layers degreesAdd (SingleExpBisect.Sparse.multiply degreesAdd A p.2).1 (cs.map Prod.snd)).1 _
        simpa only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul,add_assoc,add_comm,add_left_comm] using sr

theorem start_layers (n k M : ℕ) (base : ℤ) (cs : List ShiftFactor) (hs : ∀ p∈cs,legal n k M p) :
    let D := (cs.length*n+1)*(cs.length*k+1)
    (layers degreesAdd [(wDegree base,1)] (cs.map Prod.snd)).2 ≤ cs.length*(D+1+D*M*(D+4)) := by
  have start : inside [(wDegree base,1)] (box 0 0 base) := by
    intro d hd
    simp only [List.map_cons,List.map_nil,List.mem_singleton] at hd
    subst d
    exact box_cases.mpr ⟨0,0,by decide,by decide,by simp [wDegree]⟩
  exact (bounded_layers n k M _ _ cs 0 0 base _ (by simp) start hs (by simp) (by simp)).1
end SingleExpBisect.Convolution


namespace SingleExpBisect.Convolution
open SingleExpBisect.Main SingleExpBisect.Sparse

def signature {n : ℕ} (P : Finset (Fin n)) (e : Var n →₀ ℕ) : Prop :=
  ∀ v : Fin n, e (.y v) = if v ∈ P then 1 else 0
def grade {n : ℕ} (e : Var n →₀ ℕ) : Degrees := ⟨e .x,e .x',e .w⟩

theorem selected_item {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) (q : CoeffEntry) :
    q ∈ selectDegrees P L ↔ ∃ p∈L, signature P p.1 ∧ q=(grade p.1,p.2) := by
  constructor
  · intro h
    obtain ⟨⟨a,c⟩,hp,hq⟩ := List.mem_filterMap.mp h
    dsimp only at hq
    split at hq
    · rename_i h
      exact ⟨(a,c),hp,h,(Option.some.inj hq).symm⟩
    · contradiction
  · rintro ⟨⟨a,c⟩,hp,h,rfl⟩
    apply List.mem_filterMap.mpr
    exact ⟨(a,c),hp,by simpa [selectDegrees,grade,signature] using h⟩

theorem grade_eq {n : ℕ} {P : Finset (Fin n)} {a b : Var n →₀ ℕ}
    (ma : signature P a) (mb : signature P b) (h : grade a = grade b) : a=b := by
  ext v
  cases v with
  | x => simpa [grade] using congrArg Degrees.x h
  | x' => simpa [grade] using congrArg Degrees.aux h
  | w => simpa [grade] using congrArg Degrees.w h
  | y i => exact (ma i).trans (mb i).symm

theorem select_nodup {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) (hk : (L.map Prod.fst).Nodup) :
    ((selectDegrees P L).map Prod.fst).Nodup := by
  induction L with
  | nil => simp [selectDegrees]
  | cons p L ih =>
    obtain ⟨hkey,ht⟩ := List.nodup_cons.mp hk
    rcases p with ⟨e,c⟩
    by_cases matchSig : signature P e
    · have eqn : selectDegrees P ((e,c)::L) = (grade e,c)::selectDegrees P L := by
        unfold signature at matchSig
        simp [selectDegrees,List.filterMap_cons,grade,matchSig]
      rw [eqn,List.map_cons,List.nodup_cons]; refine ⟨?_,ih ht⟩
      intro hm
      obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
      obtain ⟨b,hb,mb,rfl⟩ := (selected_item P L q).mp hq
      have eq := grade_eq mb matchSig he
      exact hkey (List.mem_map.mpr ⟨b,hb,eq⟩)
    · have e2 : selectDegrees P ((e,c)::L) = selectDegrees P L := by
        unfold signature at matchSig
        simp [selectDegrees,List.filterMap_cons,matchSig]
      rw [e2]; exact ih ht


theorem shifted_shape {n k : ℕ} (p : SparseChild n) (nd : (p.2.2.map Prod.fst).Nodup)
    (shape : ∀ e∈p.2.2,e.1 Var.x ≤ n ∧ e.1 Var.x' = 0 ∧ e.1 Var.w ≤ k) :
    legal n k ((n+1)*(k+1)) (shifted p) := by
  have inside₀ : inside (selectDegrees p.1 p.2.2) (box n k 0) := by
    intro d hd
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
    obtain ⟨b,hb,_,rfl⟩ := (selected_item ..).mp hq
    obtain ⟨bx,ba,bw⟩ := shape b hb
    exact box_cases.mpr ⟨b.1 .x,b.1 .w,bx,bw,by simp [grade,ba]⟩
  have len := (length_le (select_nodup p.1 p.2.2 nd) inside₀).trans (box_card n k 0)
  constructor
  · simpa [shifted,multiplyDegrees] using len
  · intro d hd
    simp only [shifted,multiplyDegrees,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map] at hd
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
    obtain ⟨b,hb,_,rfl⟩ := (selected_item ..).mp hq
    obtain ⟨bx,ba,bw⟩ := shape b hb
    exact box_cases.mpr ⟨b.1 .x,b.1 .w,bx,bw,by simp [grade,degreesAdd,wDegree,ba,shifted]⟩
end SingleExpBisect.Convolution

open scoped Classical
namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT
lemma rename_exponent {n : ℕ} (D A : Finset (Fin n)) (c : ℕ) :
    Finsupp.mapDomain (omegaVar D) (Finsupp.single Var.w c + yMono A) =
      Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c + yMono (A ∩ D) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [yMono,omegaVar,Finsupp.mapDomain_single]
  | insert i A hi ih =>
    have hs : yMono (insert i A) = Finsupp.single (Var.y i) 1 + yMono A := by simp [yMono,hi]
    rw [hs,add_left_comm,Finsupp.mapDomain_add,Finsupp.mapDomain_single,ih]
    by_cases hd : i ∈ D
    · have e : insert i A \ D = A \ D := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = insert i (A ∩ D) := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f]; simp [omegaVar,hd,yMono,hi,add_comm,add_left_comm,add_assoc]
    · have e : insert i A \ D = insert i (A \ D) := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = A ∩ D := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f,Finset.card_insert_of_notMem (by simp [hi]),Finsupp.single_add]
      simp only [omegaVar,if_neg hd]; abel

private lemma renamed_cut_support {n : ℕ} (G : SimpleGraph (Fin n)) (W D : Finset (Fin n)) (k : ℕ)
    (A : Finset (Finset (Fin n))) (hk : ∀ S ∈ A, mu G W S ≤ k) :
    let P := omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1)
    P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      (∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ)) ∧
      ∀ e ∈ P.support, e Var.x ≤ n ∧ e Var.x' = 0 ∧ e Var.w ≤ k ∧ ∀ v, e (Var.y v) ≤ 1 := by
  classical
  dsimp only
  let exp := fun S : Finset (Fin n) => Finsupp.single Var.x (S \ D).card +
    Finsupp.single Var.w (mu G W S) + yMono (S ∩ D)
  let P := ∑ S ∈ A, MvPolynomial.monomial (exp S) (1:ℚ)
  have eq : omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1) = P := by
    rw [map_sum]; apply Finset.sum_congr rfl;intro S hS
    change MvPolynomial.rename (omegaVar D) _ = _
    rw [MvPolynomial.rename_monomial,rename_exponent]
  rw [eq]
  let pack := D.powerset ×ˢ (Finset.range (n+1) ×ˢ Finset.range (k+1))
  let mono := fun p : Finset (Fin n) × (ℕ × ℕ) =>
    Finsupp.single Var.x p.2.1 + Finsupp.single Var.w p.2.2 + yMono p.1
  have hc (e : Var n →₀ ℕ) : MvPolynomial.coeff e P = ((A.filter (fun S => exp S = e)).card : ℚ) := by
    simp only [P,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    simp [Finset.sum_boole,eq_comm]
  have hs : P.support ⊆ pack.image mono := by
    intro e he
    have hn := MvPolynomial.mem_support_iff.mp he
    rw [hc] at hn
    obtain ⟨S,hS⟩ := Finset.card_pos.mp (by exact_mod_cast (show 0 < (((A.filter (fun S => exp S=e)).card):ℚ) by positivity))
    obtain ⟨hA,heq⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_image.mpr ⟨(S ∩ D,(S \ D).card,mu G W S),?_,heq⟩
    apply Finset.mem_product.mpr;refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · apply Finset.mem_range.mpr
      have h : (S \ D).card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      exact Nat.lt_succ_of_le h
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hk S hA))
  constructor
  · have h := (Finset.card_le_card hs).trans Finset.card_image_le
    simpa [pack,mul_assoc] using h
  constructor
  · intro e
    refine ⟨_,?_,hc e⟩
    have hb := (Finset.card_le_card (Finset.filter_subset (fun S => exp S=e) A)).trans (Finset.card_le_univ _)
    simpa using hb


  · intro e he
    obtain ⟨⟨F,i,j⟩,h,hh⟩ := Finset.mem_image.mp (hs he)
    have ij := (Finset.mem_product.mp (Finset.mem_product.mp h).2)
    have hi := Finset.mem_range.mp ij.1
    have hj := Finset.mem_range.mp ij.2
    change i < n+1 at hi
    change j < k+1 at hj
    subst e
    have val (v : Fin n) : yMono F (Var.y v) = if v ∈ F then 1 else 0 := by
      simp [yMono,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]
    simp [mono,yMono,Finsupp.single_apply,eq_comm]
    exact ⟨by omega, by omega, fun v => by split <;> omega⟩

private theorem filterValue {α : Type} [DecidableEq α] (l : List (α × ℚ)) (x : α × ℚ)
    (distinct : (l.map Prod.fst).Nodup) (member : x ∈ l) :
    ((l.filter (fun p => decide (p.1 = x.1))).map Prod.snd).sum = x.2 := by
  induction l with
  | nil => simp at member
  | cons a l ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with rfl | tail
    · have none : l.filter (fun p => decide (p.1 = x.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        have ne : p.1 ≠ x.1 := fun e => fresh (List.mem_map.mpr ⟨p,hp,e⟩)
        simp [ne]
      simp [none]
    · have ne : a.1 ≠ x.1 := fun e => fresh (List.mem_map.mpr ⟨x,tail,e.symm⟩)
      simpa [ne] using ih nd tail


theorem table_properties {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (k : ℕ) (s : Fin T.N) (L : List (Entry n))
    (valid : IsSparseRep L (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (∀ p ∈ L,p.1 Var.x ≤ n ∧ p.1 Var.x' = 0 ∧ p.1 Var.w ≤ k) ∧
    ∀ p ∈ L,∃ j : ℕ,j ≤ 2^n ∧ p.2=(j:ℚ) := by
  have props := renamed_cut_support G (T.cone s) (T.adhesion s) k
    (((T.cone s).powerset).filter (fun A => mu G (T.cone s) A ≤ k))
    (fun A h => (Finset.mem_filter.mp h).2)
  change _ ∧ (∀ e,∃ j : ℕ,j ≤ 2^n ∧ MvPolynomial.coeff e (Zomega G T k s)=(j:ℚ)) ∧
    (∀ e ∈ (Zomega G T k s).support,e Var.x ≤ n ∧ e Var.x' = 0 ∧ e Var.w ≤ k ∧ ∀ v,e (Var.y v) ≤ 1) at props
  have eval (p) (h : p∈L) : MvPolynomial.coeff p.1 (Zomega G T k s)=p.2 :=
    (valid.2.2 p.1).trans (filterValue L p valid.1 h)
  constructor
  · intro p h
    obtain ⟨hx,ha,hw,_⟩ := props.2.2 p.1 (MvPolynomial.mem_support_iff.mpr ((eval p h) ▸ valid.2.1 p h))
    exact ⟨hx,ha,hw⟩
  · intro p h
    obtain ⟨j,hj,hq⟩ := props.2.1 p.1
    exact ⟨j,hj,(eval p h).symm.trans hq⟩

end SingleExpBisect.Convolution

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT SingleExpBisect.Sparse
theorem digits_spec {n : ℕ} (P : Finset (Fin n)) (e : Var n →₀ ℕ) (vs : List (Fin n)) :
    ((testDigits P e vs).1 = true ↔ ∀ v∈vs,e (.y v) = (if v∈P then 1 else 0)) ∧
    (testDigits P e vs).2 ≤ vs.length+1 := by
  induction vs with
  | nil => simp [testDigits]
  | cons v vs ih =>
    by_cases h : e (.y v) = (if v∈P then 1 else 0)
    · simpa [testDigits,h,ih.1] using ih.2
    · simp [testDigits,h]

theorem project_spec {n : ℕ} (P : Finset (Fin n)) (off : ℤ) (L : List (Entry n)) :
    (project P off L).1 = (shifted (P,-off,L)).2 ∧ (project P off L).2 ≤ 1+L.length*(n+3) := by
  induction L with
  | nil => simp [project,shifted,multiplyDegrees,selectDegrees]
  | cons p L ih =>
    obtain ⟨e,c⟩ := p
    have tst := digits_spec P e (List.finRange n)
    have test : (testDigits P e (List.finRange n)).1=true ↔ signature P e := by
      simpa [signature] using tst.1
    constructor
    · have eq' := ih.1
      simp only [shifted,multiplyDegrees,List.flatMap_cons,List.flatMap_nil,List.append_nil,neg_neg] at eq' ⊢
      by_cases h : signature P e
      · have pass := test.mpr h
        unfold signature at h
        simp [project,selectDegrees,List.filterMap_cons,h,pass,eq',degreesAdd,wDegree]
      · have fail : (testDigits P e (List.finRange n)).1=false := Bool.eq_false_iff.mpr (fun ht => h (test.mp ht))
        unfold signature at h
        simp [project,selectDegrees,List.filterMap_cons,h,fail,eq']
    · have bd := tst.2
      simp only [List.length_finRange] at bd
      simp only [project,List.length_cons,Nat.succ_mul]
      omega

theorem prep_spec {n : ℕ} (cs : List (SparseChild n)) :
    (prepare cs).1 = cs.map shifted ∧
      (prepare cs).2 ≤ 1+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3) := by
  induction cs with
  | nil => simp [prepare]
  | cons p cs ih =>
    rcases p with ⟨P,c,L⟩
    obtain ⟨eqn,bd⟩ := project_spec P (-c) L
    simp only [neg_neg] at eqn
    constructor
    · simp [prepare,eqn,ih.1,shifted]
    · simp only [prepare,List.length_cons,List.map_cons,List.sum_cons,Nat.add_mul,Nat.one_mul]
      omega


theorem query_spec (q : Degrees) (A : Table Degrees) (h : (A.map Prod.fst).Nodup) :
    (query q A).1=weight A (fun a => if a=q then 1 else 0) ∧ (query q A).2 ≤ A.length+1 := by
  induction A with
  | nil => simp [query,weight]
  | cons p A ih =>
    rcases p with ⟨a,c⟩
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp h
    obtain ⟨eqn,b⟩ := ih tail
    by_cases e : a=q
    · subst a
      have zero : weight A (fun a => if a=q then 1 else 0)=0 := by
        apply List.sum_eq_zero
        intro y hm
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
        have dif : p.1 ≠ q := fun e => fresh (List.mem_map.mpr ⟨p,hp,e⟩)
        simp [dif]
      simp [query,weight] at zero ⊢
      exact zero
    · simp [query,weight,e,eqn] at b ⊢
      omega


theorem weight_indicator (A : Table Degrees) (q : Degrees) (k : ℕ) :
    (if q.w ≤ (k:ℤ) then weight A (fun a => if a=q then 1 else 0) else 0) =
      (((A.filter fun p => p.1.w ≤ (k:ℤ)).filter fun p => p.1=q).map Prod.snd).sum := by
  induction A with
  | nil => simp [weight]
  | cons p A ih =>
    by_cases h : p.1=q
    · by_cases w : q.w ≤ (k:ℤ) <;> simp [weight,h,w,List.filter_cons] at ih ⊢ <;> exact ih
    · by_cases w : p.1.w ≤ (k:ℤ) <;> simp [weight,h,w,List.filter_cons] at ih ⊢ <;> exact ih
end SingleExpBisect.Convolution

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main SingleExpBisect.Sparse
theorem fast_spec {n : ℕ} (k M : ℕ) (base : ℤ) (cs : List (SparseChild n))
    (h : ∀ p∈cs,legal n k M (shifted p)) (q : Degrees) :
    let D := (cs.length*n+1)*(cs.length*k+1)
    (fast k base cs q).1=evaluate k base cs q ∧
    (fast k base cs q).2 ≤ 3+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3)
        +cs.length*(D+1+D*M*(D+4))+D := by
  let zs := cs.map shifted
  let ys := zs.map Prod.snd
  let D := (cs.length*n+1)*(cs.length*k+1)
  let acc : Table Degrees := [(wDegree base,1)]
  have ih : ∀ p∈zs,legal n k M p := by
    intro p hp; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp; exact h b hb
  have start : inside acc (box 0 0 base) := by
    intro d hd
    simp only [acc,List.map_cons,List.map_nil,List.mem_singleton] at hd
    subst d; exact box_cases.mpr ⟨0,0,by decide,by decide,by simp [wDegree]⟩
  obtain ⟨work,nd,ok⟩ := bounded_layers n k M (cs.length*n) (cs.length*k) zs 0 0 base acc (by simp [acc])
    start ih (by simp [zs]) (by simp [zs])
  have w : (layers degreesAdd acc ys).2 ≤ cs.length*(D+1+D*M*(D+4)) := by simpa [D,zs,ys] using work
  have sz : (layers degreesAdd acc ys).1.length ≤ D := by
    simpa [D,zs,ys] using (length_le nd ok).trans (box_card ..)
  have queryH := query_spec q (layers degreesAdd acc ys).1 nd
  obtain ⟨prep,prepCost⟩ := prep_spec cs
  have equal := layers_equiv degreesAdd ys acc acc (fun _ => rfl) (fun a => if a=q then 1 else 0)
  have out : (fast k base cs q).1=evaluate k base cs q := by
    simp only [fast,prep]
    change (if q.w ≤ (k:ℤ) then query q (layers degreesAdd acc ys).1 else (0,1)).1=_
    have extract := weight_indicator (ys.foldl (products degreesAdd) acc) q k
    have fs : ys=cs.map (fun (P,c,L) => multiplyDegrees [(wDegree (-c),1)] (selectDegrees P L)) := by
      simp only [ys,zs,List.map_map]
      apply List.map_congr_left
      rintro ⟨P,c,L⟩ _
      rfl
    unfold evaluate
    rw [←fs]
    change _ = (((((ys.foldl (products degreesAdd) acc).filter fun p => p.1.w ≤ (k:ℤ))).filter fun p => p.1=q).map Prod.snd).sum
    rw [←extract]
    split <;> simp_all only [queryH.1,equal]
  refine ⟨out,?_⟩
  simp only [fast,prep]
  change (prepare cs).2 + (layers degreesAdd acc ys).2 +
    (if q.w ≤ (k:ℤ) then query q (layers degreesAdd acc ys).1 else (0,1)).2+1 ≤ _
  change _ ≤ 3+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3)+cs.length*(D+1+D*M*(D+4))+D
  by_cases test : q.w ≤ (k:ℤ)
  · simp only [if_pos test]; omega
  · simp only [if_neg test]; omega
end SingleExpBisect.Convolution

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT SingleExpBisect.Sparse

theorem shifted_mass {n : ℕ} (p : SparseChild n) (N M : ℕ)
    (coeff : ∀ z∈p.2.2, ∃ j : ℕ,j ≤ N ∧ z.2=(j:ℚ)) (ln : (shifted p).2.length ≤ M) :
    natTable (shifted p).2 ∧ mass (shifted p).2 ≤ ((M*N:ℕ):ℚ) := by
  have got (q) (hq : q ∈ (shifted p).2) : ∃ j : ℕ,j ≤ N ∧ q.2=(j:ℚ) := by
    simp only [shifted,multiplyDegrees,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    obtain ⟨b,inL,_,rfl⟩ := (selected_item ..).mp hz
    simpa using coeff b inL
  constructor
  · intro q h; obtain ⟨j,_,hj⟩ := got q h; exact ⟨j,hj⟩
  · have h (q) (hq : q ∈ (shifted p).2) : q.2 ≤ (N:ℚ) := by
      obtain ⟨j,b,eqn⟩ := got q hq
      rw [eqn]; exact_mod_cast b
    exact (bounded_mass _ N h).trans (by exact_mod_cast Nat.mul_le_mul_right N ln)


theorem compressed_Q {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (ht : IsRootedTreeDecomp G T) (k : ℕ) (t : Fin T.N) (R : Finset (Fin n))
    (hr : R⊆T.bag t) (Lc : Fin T.N → List (Entry n)) (rep : ∀ s,T.parent s=some t →
     IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) (q : Degrees) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R∩T.adhesion t):ℕ):ℤ)
    let cs := records G T t R Lc
    let M := (n+1)*(k+1)
    let D := (cs.length*n+1)*(cs.length*k+1)
    (fast k base cs q).1=(toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff
      (Finsupp.single .x q.x + Finsupp.single .x' q.aux + Finsupp.single .w q.w) ∧
    (fast k base cs q).2 ≤ 3+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3)
        +cs.length*(D+1+D*M*(D+4))+D ∧
    ∀ pre post,cs=pre++post →
      ∀ z∈(layers degreesAdd [(wDegree base,1)] (pre.map (fun p=> (shifted p).2))).1,
        ∃ j : ℕ,z.2=(j:ℚ) ∧ j ≤ (M*2^n)^pre.length := by
  intro base cs M D
  have props (p) (hp : p∈cs) :
      legal n k M (shifted p) ∧ natTable (shifted p).2 ∧ mass (shifted p).2 ≤ ((M*2^n:ℕ):ℚ) := by
    obtain ⟨s,mem,rfl⟩ := List.mem_map.mp hp
    have par : T.parent s=some t := Finset.mem_filter.mp (Finset.mem_toList.mp mem) |>.2
    have valid := rep s par
    obtain ⟨shape,coeff⟩ := table_properties G T k s (Lc s) valid
    have sh := shifted_shape (n:=n) (k:=k) (R ∩ T.adhesion s, (etaNode G T s (R ∩ T.adhesion s) : ℤ), Lc s) valid.1 shape
    exact ⟨sh,shifted_mass _ (2^n) M coeff sh.1⟩
  obtain ⟨work,bd⟩ := fast_spec k M base cs (fun p h => (props p h).1) q
  refine ⟨work.trans (evaluate_Q G T ht k t R hr Lc rep q),bd,?_⟩
  intro pre post eqn z hz
  let fs := pre.map fun p => (shifted p).2
  have all (b) (hb : b∈fs) : natTable b ∧ mass b ≤ ((M*2^n:ℕ):ℚ) := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    exact (props p (eqn ▸ List.mem_append_left _ hp)).2
  have start : natTable [(wDegree base,1)] := by
    intro p hp; simp only [List.mem_singleton] at hp; subst p; exact ⟨1,by simp⟩
  obtain ⟨ns,upper⟩ := layers_mass degreesAdd [(wDegree base,1)] fs (M*2^n) start all
  obtain ⟨j,hj⟩ := ns z hz
  have magnitude := (entry_le_mass _ ns z hz).trans upper
  refine ⟨j,hj,?_⟩
  rw [hj] at magnitude
  simp only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,one_mul,
    fs,List.length_map] at magnitude
  exact_mod_cast magnitude
end SingleExpBisect.Convolution

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT

private theorem split_size {n : ℕ} (A B D : Finset (Fin n)) (hd : D⊆B) :
    (A\D).card=(A\B).card + ((A∩B)\D).card := by
  have eqn : A\D = (A\B)∪((A∩B)\D) := by
    ext x
    have h : x∈D → x∈B := fun h => hd h
    simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_union]; tauto
  rw [eqn,Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun x h g => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp g).1).2)

/-- Reconstruct all coefficients, including the boundary variables, from the fixed-bag
queries in equation (8). This also applies to a large bag when iterating over its subsets. -/
theorem reconstruct {n : ℕ} (G : SimpleGraph (Fin n)) (W B D : Finset (Fin n)) (k : ℕ)
    (hd : D⊆B) :
    omega D (Zfull G W k) =
      ∑ R ∈ B.powerset,
        (MvPolynomial.monomial (Finsupp.single Var.x (R\D).card+yMono (R∩D)) (1:ℚ)) *
          Qpoly G W B k R := by
  classical
  let S := W.powerset.filter (fun a => mu G W a ≤ k)
  let g := fun A : Finset (Fin n) =>
    Finsupp.single Var.x (A\D).card + Finsupp.single Var.w (mu G W A) + yMono (A∩D)
  have left : omega D (Zfull G W k) = ∑ A ∈ S,MvPolynomial.monomial (g A) (1:ℚ) := by
    rw [Zfull,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    change MvPolynomial.rename (omegaVar D) _ = _
    rw [MvPolynomial.rename_monomial]
    rw [rename_exponent]
  rw [left]
  have grouped := Finset.sum_fiberwise_of_maps_to
      (s := S) (t := B.powerset) (g := fun A => A∩B)
      (fun a _ => Finset.mem_powerset.mpr Finset.inter_subset_right)
      (fun A => MvPolynomial.monomial (g A) (1:ℚ))
  rw [←grouped]
  apply Finset.sum_congr rfl
  intro R _
  have eqn : S.filter (fun A => A∩B=R) = W.powerset.filter (fun A => mu G W A ≤ k ∧ A∩B=R) := by
    ext a; simp [S,and_assoc]
  rw [eqn,Qpoly,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a hab
  have inter := (Finset.mem_filter.mp hab).2.2
  rw [←inter,MvPolynomial.monomial_mul,one_mul]
  have hi : (a∩B)∩D=a∩D := by ext v; simp only [Finset.mem_inter]; have h : v∈D → v∈B := fun h => hd h; tauto
  rw [hi]
  congr 1
  unfold g
  rw [split_size _ _ _ hd,Finsupp.single_add]
  abel
end SingleExpBisect.Convolution


namespace SingleExpBisect.Convolution
open scoped Classical
open SingleExpBisect.Main MinBisectFPT

private theorem listSize {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ) (s : Fin T.N)
    (L : List (Entry n)) (valid : IsSparseRep L (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    L.length ≤ 2^(T.adhesion s).card*(n+1)*(k+1) := by
  let P := Zomega G T k s
  have h := renamed_cut_support G (T.cone s) (T.adhesion s) k
    (((T.cone s).powerset).filter (fun A => mu G (T.cone s) A ≤ k))
    (fun A h => (Finset.mem_filter.mp h).2)
  have covered : (L.map Prod.fst).toFinset ⊆ P.support := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    have eqn : MvPolynomial.coeff p.1 P = p.2 :=
      (valid.2.2 p.1).trans (filterValue L p valid.1 hp)
    exact MvPolynomial.mem_support_iff.mpr (eqn ▸ valid.2.1 _ hp)
  have cnt := (Finset.card_le_card covered).trans h.1
  simpa only [List.toFinset_card_of_nodup valid.1,List.length_map] using cnt

private theorem sum_bounded {α : Type} (l : List α) (f : α → ℕ) (b : ℕ) (h : ∀ x∈l,f x ≤ b) :
    (l.map f).sum ≤ l.length*b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    exact (Nat.add_le_add (h _ (by simp)) (ih (fun y hy => h _ (by simp [hy])))).trans_eq (Nat.add_comm ..)

theorem fpt_cost (n k h L : ℕ) (hh : h ≤ n+1)
    (hl : L ≤ h*(2^(2*k)*(n+1)*(k+1))) :
    let m := (n+1)*(k+1)
    let d := (h*n+1)*(h*k+1)
    3+h*2+L*(n+3)+h*(d+1+d*m*(d+4))+d ≤ stepBound 128 k n := by
  let z := (n+1)*(k+1)
  let e := 2^(2*k)
  intro m d
  have z1 : 1 ≤ z := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hn : n+1 ≤ z := by dsimp [z]; nlinarith
  have hk : k+1 ≤ z := by dsimp [z]; nlinarith
  have hz : h ≤ z := hh.trans hn
  have zz : 1 ≤ z*z := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have left : h*n+1 ≤ 2*(z*z) := by have := Nat.mul_le_mul hz (show n ≤ z by omega); omega
  have right : h*k+1 ≤ 2*(z*z) := by have := Nat.mul_le_mul hz (show k ≤ z by omega); omega
  have hd : d ≤ 4*z^4 := (Nat.mul_le_mul left right).trans_eq (by ring)
  have hm : m=z := rfl
  have largeL : L ≤ z*(e*z) := hl.trans (by change h*(e*(n+1)*(k+1)) ≤ z*(e*((n+1)*(k+1))); rw [Nat.mul_assoc e]; exact Nat.mul_le_mul_right _ hz)
  have n3 : n+3 ≤ 3*z := by omega
  have E : 0<e := by dsimp [e]; positivity
  calc
    _ ≤ 3+z*2+(z*(e*z))*(3*z)+z*((4*z^4)+1+(4*z^4)*z*((4*z^4)+4))+(4*z^4) := by
      rw [hm]; gcongr
    _ ≤ 128*e*z^10 := by
      have maxE : z^10 ≤ e*z^10 := Nat.le_mul_of_pos_left _ E
      have dom (j : ℕ) (jj : j ≤ 10) : z^j ≤ e*z^10 := (Nat.pow_le_pow_right z1 jj).trans maxE
      have g0 := dom 0 (by decide)
      have g1 := dom 1 (by decide)
      have g4 := dom 4 (by decide)
      have g5 := dom 5 (by decide)
      have g6 := dom 6 (by decide)
      have g3 : e*z^3 ≤ e*z^10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right z1 (by decide))
      simp only [pow_zero] at g0
      simp only [pow_one] at g1
      calc _ = 3+3*z+3*(e*z^3)+4*z^5+16*z^10+16*z^6+4*z^4 := by ring
           _ ≤ 128*(e*z^10) := by omega
           _ = _ := by ring
    _ = 128*(2^(2*k)*(k+1)^10)*(n+1)^10 := by dsimp [z,e]; ring
    _ ≤ 128*2^(128*k)*(n+1)^128 := by
      have hk2 : k+1 ≤ 2^k := Nat.succ_le_of_lt Nat.lt_two_pow_self
      have hpow : 2^(2*k)*(k+1)^10 ≤ 2^(128*k) := by
        have hi : 2^(2*k)*(2^k)^10 = 2^(2*k+k*10) := by rw [←pow_mul,←pow_add]
        exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk2 10)).trans (hi ▸ Nat.pow_le_pow_right (by decide) (by omega))
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 128 hpow) (Nat.pow_le_pow_right (by omega) (by decide))

theorem compressed_time {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ)
    (ht : IsSec3Decomp G T k) (t : Fin T.N) (R : Finset (Fin n)) (hr : R⊆T.bag t)
    (Lc : Fin T.N → List (Entry n)) (rep : ∀ s,T.parent s=some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) (q : Degrees) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R∩T.adhesion t):ℕ):ℤ)
    let cs := records G T t R Lc
    (fast k base cs q).1=(toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff
      (Finsupp.single .x q.x + Finsupp.single .x' q.aux + Finsupp.single .w q.w) ∧
    (fast k base cs q).2 ≤ stepBound 128 k n := by
  intro base cs
  obtain ⟨out,work,_⟩ := compressed_Q G T ht.1 k t R hr Lc rep q
  refine ⟨out,work.trans (fpt_cost n k cs.length _ ?_ ?_)⟩
  · have c0 : (T.children t).card ≤ T.N := by simpa using Finset.card_le_univ (T.children t)
    have c1 := ht.2.2.2.1
    change ((T.children t).toList.map _).length ≤ n+1
    simp only [List.length_map,Finset.length_toList]; omega
  · apply sum_bounded
    intro p hp
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
    have par : T.parent s=some t := (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
    have ss := listSize G T k s (Lc s) (rep s par)
    exact ss.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (ht.2.1 s))))
end SingleExpBisect.Convolution


open SingleExpBisect.Convolution SingleExpBisect.Main MinBisectFPT SingleExpBisect.Sparse
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (k : ℕ) (ht : IsSec3Decomp G T k) (t : Fin T.N) (R : Finset (Fin n))
    (hr : R⊆T.bag t) (Lc : Fin T.N → List (Entry n)) (rep : ∀ s,T.parent s=some t →
     IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) (q : Degrees) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R∩T.adhesion t):ℕ):ℤ)
    let cs := records G T t R Lc
    let M := (n+1)*(k+1)
    let D := (cs.length*n+1)*(cs.length*k+1)
    (fast k base cs q).1=(toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff
      (Finsupp.single .x q.x + Finsupp.single .x' q.aux + Finsupp.single .w q.w) ∧
    (fast k base cs q).2 ≤ stepBound 128 k n ∧
    (fast k base cs q).2 ≤ 3+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3)
        +cs.length*(D+1+D*M*(D+4))+D ∧
    ∀ pre post,cs=pre++post →
      ∀ z∈(layers degreesAdd [(wDegree base,1)] (pre.map (fun p=> (shifted p).2))).1,
        ∃ j : ℕ,z.2=(j:ℚ) ∧ j ≤ (M*2^n)^pre.length := by
  intro base cs M D
  have F := compressed_time G T k ht t R hr Lc rep q
  have E := compressed_Q G T ht.1 k t R hr Lc rep q
  exact ⟨F.1, F.2, E.2⟩
