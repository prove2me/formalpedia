-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.OrderStream.hash_order_stream_is_bounded
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:11:47.16557+00:00
-- url     : https://prove2.me/submissions/154c844c-92f3-487b-8d6c-d4855756983f

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_natural_arithmetic
import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open scoped Classical
private lemma addF {f g : Env→ℕ} (h : Form f) (k : Form g) : Form (fun ρ=>f ρ+g ρ) := .bin .add h k
private lemma cutF {f g : Env→ℕ} (h : Form f) (k : Form g) : Form (fun ρ=>f ρ-g ρ) := .bin .cut h k
private lemma mulF {f g : Env→ℕ} (h : Form f) (k : Form g) : Form (fun ρ=>f ρ*g ρ) :=
  bounded_natural_arithmetic.1 _ _ h k
private lemma divF {f g : Env→ℕ} (h : Form f) (k : Form g) : Form (fun ρ=>f ρ/g ρ) :=
  bounded_natural_arithmetic.2.1 _ _ h k
private lemma modF {f g : Env→ℕ} (h : Form f) (k : Form g) : Form (fun ρ=>f ρ%g ρ) :=
  bounded_natural_arithmetic.2.2 _ _ h k
private lemma powF {f : Env→ℕ} (h : Form f) (k : ℕ) : Form (fun ρ=>f ρ^k) := by
  induction k with
  | zero => simpa using (Form.lit 1)
  | succ k ih => simpa only [pow_succ] using mulF ih h
private lemma liftF {f : Env→ℕ} (h : Form f) : Form (fun ρ=>f (fun i=>ρ (i+1))) := h.rename Nat.succ
private lemma sumF {f : Env→ℕ} {g : Env→ℕ→ℕ} (hf : Form f)
    (hg : Form (fun ρ=>g (fun j=>ρ (j+1)) (ρ 0))) :
    Form (fun ρ=>∑i ∈ Finset.range (f ρ),g ρ i) := .sum hf hg
private lemma sumConstF (n : ℕ) (f : ℕ→Env→ℕ) (h : ∀i,Form (f i)) :
    Form (fun ρ=>∑i ∈ Finset.range n,f i ρ) := by
  induction n with
  | zero => simpa using (Form.lit 0)
  | succ n ih => simpa only [Finset.sum_range_succ] using addF ih (h n)
private noncomputable def Test (p : Env→Prop) : Prop := Form (fun ρ=>if p ρ then 1 else 0)
private lemma leT {f g : Env→ℕ} (h : Form f) (k : Form g) : Test (fun ρ=>f ρ ≤ g ρ) := by
  unfold Test
  convert Form.bin .leFlag h k using 1
  funext ρ
  by_cases e : f ρ ≤ g ρ <;> simp [Gate.val,e]
private lemma notT {p : Env→Prop} (h : Test p) : Test (fun ρ=>¬p ρ) := by
  unfold Test at *
  convert cutF (Form.lit 1) h using 1
  ext ρ;by_cases e : p ρ <;> simp [e]
private lemma andT {p q : Env→Prop} (h : Test p) (k : Test q) : Test (fun ρ=>p ρ ∧ q ρ) := by
  unfold Test at *
  convert mulF h k using 1
  ext ρ;by_cases e : p ρ <;> simp [e]
private lemma eqT {f g : Env→ℕ} (h : Form f) (k : Form g) : Test (fun ρ=>f ρ=g ρ) := by
  simpa only [le_antisymm_iff] using andT (leT h k) (leT k h)
private lemma ltT {f g : Env→ℕ} (h : Form f) (k : Form g) : Test (fun ρ=>f ρ < g ρ) := by
  simpa only [not_le] using notT (leT k h)
private lemma ifF {p : Env→Prop} {f g : Env→ℕ} [DecidablePred p] (hp : Test p) (hf : Form f) (hg : Form g) :
    Form (fun ρ=>if p ρ then f ρ else g ρ) := by
  have h := addF (mulF hp hf) (mulF (notT hp) hg)
  convert h using 1
  ext ρ;by_cases e : p ρ <;> simp [e]
private lemma noT {n : Env→ℕ} {p : Env→ℕ→Prop} (hn : Form n)
    (hp : Test (fun ρ=>p (fun j=>ρ (j+1)) (ρ 0))) :
    Test (fun ρ=>∀j < n ρ,¬p ρ j) := by
  have sum := sumF (g:=fun ρ i=>if p ρ i then 1 else 0) hn hp
  have eq := eqT sum (Form.lit 0)
  unfold Test at *
  convert eq using 1
  funext ρ
  have e : (∑i ∈ Finset.range (n ρ), if p ρ i then 1 else 0 : ℕ)=0 ↔ ∀j < n ρ,¬p ρ j := by
    simp [Finset.sum_eq_zero_iff_of_nonneg]
  by_cases hp : ∀j < n ρ,¬p ρ j <;> simp [e,hp]
private lemma primeT {f : Env→ℕ} (hf : Form f) : Test (fun ρ=>(f ρ).Prime) := by
  have ok := andT (leT (Form.lit 2) hf)
    (noT (p:=fun ρ j=>2 ≤ j ∧ f ρ%j=0) hf
      (andT (leT (Form.lit 2) (.var 0)) (eqT (modF (liftF hf) (.var 0)) (.lit 0))))
  unfold Test at *
  convert ok using 1
  funext ρ
  have e : (f ρ).Prime ↔ 2 ≤ f ρ ∧ ∀j < f ρ,¬(2 ≤ j ∧ f ρ%j=0) := by
    rw [Nat.prime_def_lt']
    simp only [Nat.dvd_iff_mod_eq_zero]
    tauto
  by_cases hh : 2 ≤ f ρ ∧ ∀ j < f ρ,¬(2 ≤ j ∧ f ρ%j=0) <;> simp [e,hh]
private lemma lowF {f : Env→ℕ} (h : Form f) : Form (fun ρ=>lower (f ρ)) :=
  addF (.lit 8193) (mulF (.lit 4) (powF h 2))
private lemma fieldF {f : Env→ℕ} (h : Form f) : Form (fun ρ=>fieldSize (f ρ)) := by
  apply sumF (g:=fun ρ j=>if Nat.Prime j ∧ lower (f ρ) ≤ j ∧
      (∀k < j,lower (f ρ) ≤ k → ¬Nat.Prime k) then j else 0)
  · exact addF (mulF (.lit 2) (lowF h)) (.lit 1)
  · let l := fun (ρ : Env) => lower (f (fun i=>ρ (i+1)))
    have hl : Form l := liftF (lowF h)
    have allT := noT (n:=fun ρ=>ρ 0) (p:=fun ρ k=>l ρ ≤ k ∧ Nat.Prime k) (.var 0)
      (andT (leT (liftF hl) (.var 0)) (primeT (.var 0)))
    have guard := andT (primeT (Form.var 0)) (andT (leT hl (.var 0)) allT)
    have yes : Test (fun ρ=>Nat.Prime (ρ 0) ∧ l ρ ≤ ρ 0 ∧ (∀k < ρ 0,l ρ ≤ k → ¬Nat.Prime k)) := by
      simpa only [not_and] using guard
    exact ifF yes (.var 0) (.lit 0)
private lemma countF {f : Env→ℕ} (h : Form f) : Form (fun ρ=>count (f ρ)) := powF (fieldF h) degreeCount
private lemma hashF {q c x : Env→ℕ} (l : ℕ) (hq : Form q) (hc : Form c) (hx : Form x) :
    Form (fun ρ=>hash (q ρ) l (c ρ) (x ρ)) :=
  modF (sumConstF l (fun i ρ=>(c ρ/q ρ^i%q ρ)*x ρ^i) (fun i=>
    mulF (modF (divF hc (powF hq i)) hq) (powF hx i))) hq
private lemma scoreF {m c x : Env→ℕ} (hm : Form m) (hc : Form c) (hx : Form x) :
    Form (fun ρ=>score (m ρ) (c ρ) (x ρ)) :=
  addF (mulF (hashF degreeCount (fieldF hm) hc hx) hm) hx
private lemma rankF {m c x : Env→ℕ} (hm : Form m) (hc : Form c) (hx : Form x) :
    Form (fun ρ=>rank (m ρ) (c ρ) (x ρ)) := by
  have check := ltT (scoreF (liftF hm) (liftF hc) (.var 0)) (scoreF (liftF hm) (liftF hc) (liftF hx))
  have asF {p : Env→Prop} [DecidablePred p] (hh : Test p) : Form (fun ρ=>if p ρ then 1 else 0) := by
    unfold Test at hh
    convert hh using 1
    funext ρ
    by_cases h : p ρ <;> simp [h]
  have hh := sumF (g:=fun ρ y=>if score (m ρ) (c ρ) y < score (m ρ) (c ρ) (x ρ) then 1 else 0) hm (asF check)
  simpa [rank,Finset.sum_boole] using hh
private lemma readF {m c j : Env→ℕ} (hm : Form m) (hc : Form c) (hj : Form j) :
    Form (fun ρ=>atRank (m ρ) (c ρ) (j ρ)) :=
  sumF (g:=fun ρ x=>if rank (m ρ) (c ρ) x=j ρ then x else 0) hm
    (ifF (eqT (rankF (liftF hm) (liftF hc) (.var 0)) (liftF hj)) (.var 0) (.lit 0))

theorem solution : Form (fun ρ=>span (ρ 0)) ∧ Form (fun ρ=>word (ρ 0) (ρ 1)) := by
  have m := Form.var 0
  have i := Form.var 1
  have width := addF m (.lit 1)
  have prev := cutF i (.lit 1)
  have rem := modF prev width
  exact ⟨addF (.lit 1) (mulF (countF m) width),ifF (eqT i (.lit 0)) (countF m)
    (ifF (eqT rem (.lit 0)) m (readF m (divF prev width) (cutF rem (.lit 1))))⟩

