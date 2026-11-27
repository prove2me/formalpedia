-- Prove2me | solution 1 for ParityDegreeDepth.Core.anf_degree_differences
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:58.887217+00:00
-- url     : https://prove2.me/submissions/3b4a6768-075d-4bfd-811e-e2ca2154f38d

import Mathlib
import Definitions.Def_ParityDegreeDepth_Core_tensorEval
import Definitions.Def_ParityCubes_anfCoeff

-- ===== Diffs =====

open scoped BigOperators
noncomputable section

namespace P2MDiff

variable {n : ℕ}

/-- iterated finite differences, as a left fold (first `h 0`, then `h 1`, …) -/
def diffs {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v x => q (x + v) + q x) p

def dl (u : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun x => q (x + u) + q x

lemma diffs_zero (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin 0 → Fin n → ZMod 2) :
    diffs p h = p := by
  simp [diffs]

lemma diffs_succ {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin (k+1) → Fin n → ZMod 2) :
    diffs p h = diffs (dl (h 0) p) (Fin.tail h) := by
  simp only [diffs, List.ofFn_succ, List.foldl_cons]; rfl

lemma diffs_closed {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (x : Fin n → ZMod 2) :
    diffs p h x = ∑ ε : Fin k → ZMod 2, p (x + ∑ i, ε i • h i) := by
  induction k generalizing p with
  | zero => simp [diffs_zero]
  | succ k ih =>
    rw [diffs_succ, ih]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ZMod 2)
      (fun z => p (x + ∑ i, (Fin.cons z.1 z.2 : Fin (k+1) → ZMod 2) i • h i)) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have h01 : ∀ F : ZMod 2 → ZMod 2, ∑ b : ZMod 2, F b = F 0 + F 1 := by
      intro F
      have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      rw [this, Finset.sum_pair (by decide)]
    rw [h01, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    simp only [dl, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, zero_smul, one_smul,
      zero_add]
    rw [add_comm (p _)]
    congr 2
    abel

lemma dl_comm (u v : Fin n → ZMod 2) (q : (Fin n → ZMod 2) → ZMod 2) :
    dl u (dl v q) = dl v (dl u q) := by
  funext x; simp only [dl]
  rw [show x + u + v = x + v + u by abel]
  abel

lemma diffs_perm {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (σ : Equiv.Perm (Fin k)) : diffs p (h ∘ σ) = diffs p h := by
  funext x
  rw [diffs_closed, diffs_closed]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ fun ε => ?_
  congr 2
  have he : (Equiv.arrowCongr σ (Equiv.refl (ZMod 2))) ε = ε ∘ σ.symm := rfl
  rw [he]
  rw [← Equiv.sum_comp σ (fun i => (ε ∘ σ.symm) i • h i)]
  simp

lemma diffs_snoc {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2)
    (u : Fin n → ZMod 2) : diffs p (Fin.snoc h u) = dl u (diffs p h) := by
  rw [diffs, List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.foldl_cons, List.foldl_nil]
  rfl

/-- `p` has degree at most `j`: all `(j+1)`-fold differences vanish -/
def DegLe (j : ℕ) (p : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ (h : Fin (j+1) → Fin n → ZMod 2) (x : Fin n → ZMod 2), diffs p h x = 0

lemma diffs_const {j : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe j p)
    (h : Fin j → Fin n → ZMod 2) (x : Fin n → ZMod 2) : diffs p h x = diffs p h 0 := by
  have := hp (Fin.snoc h x) 0
  rw [diffs_snoc] at this
  simp only [dl, zero_add] at this
  have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h2 _ _ this

lemma top_add_last {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p)
    (h : Fin k → Fin n → ZMod 2) (u v : Fin n → ZMod 2) :
    diffs p (Fin.snoc h (u + v)) 0 = diffs p (Fin.snoc h u) 0 + diffs p (Fin.snoc h v) 0 := by
  rw [diffs_snoc, diffs_snoc, diffs_snoc]
  have h2 := hp (Fin.snoc (Fin.snoc h u) v) 0
  rw [diffs_snoc, diffs_snoc] at h2
  simp only [dl, zero_add] at h2 ⊢
  have e : ∀ a b c d : ZMod 2, a + b + c + d = 0 → a + d = (c + d) + (b + d) := by decide
  apply e
  rw [show u + v = v + u by abel]
  linear_combination h2

end P2MDiff

-- ===== Diffs2 =====

open scoped BigOperators
open ParityDegreeDepth.Core
noncomputable section

namespace P2MDiff

variable {n : ℕ}

lemma diffs_cons {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (h : Fin k → Fin n → ZMod 2) : diffs p (Fin.cons u h) = diffs (dl u p) h := by
  rw [diffs_succ]; rfl

lemma degLe_dl {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe (k+1) p) (u : Fin n → ZMod 2) :
    DegLe k (dl u p) := by
  intro h x
  rw [← diffs_cons]; exact hp _ x

lemma degLe_succ {k : ℕ} {p : (Fin n → ZMod 2) → ZMod 2} (hp : DegLe k p) : DegLe (k+1) p := by
  intro h x
  rw [← Fin.snoc_init_self h, diffs_snoc]
  simp only [dl]
  rw [hp (Fin.init h), hp (Fin.init h), add_zero]

lemma diffs_dl {k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2)
    (g : Fin k → Fin n → ZMod 2) : diffs (dl u p) g = dl u (diffs p g) := by
  funext x
  simp only [diffs_closed, dl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [show x + ∑ i, ε i • g i + u = x + u + ∑ i, ε i • g i by abel]

/-- additive maps on `𝔽₂ⁿ` are linear -/
lemma additive_expand (L : (Fin n → ZMod 2) → ZMod 2) (hL : ∀ u v, L (u + v) = L u + L v)
    (w : Fin n → ZMod 2) : L w = ∑ v, w v * L (Pi.single v 1) := by
  have h0 : L 0 = 0 := by
    have := hL 0 0
    simp only [add_zero] at this
    have h2 : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
    exact h2 _ this
  let Lh : (Fin n → ZMod 2) →+ ZMod 2 := ⟨⟨L, h0⟩, hL⟩
  have hw : w = ∑ v, w v • (Pi.single v 1 : Fin n → ZMod 2) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  change Lh _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (w v) with h | h
  · rw [h, zero_smul, map_zero, zero_mul]
  · rw [h, one_smul, one_mul]; rfl

/-- coefficient tensor of the top form -/
def cT (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) : (Fin j → Fin n) → ZMod 2 :=
  fun a => diffs p (fun l => Pi.single (a l) 1) 0

lemma top_eq_tensorEval : ∀ (k : ℕ) (p : (Fin n → ZMod 2) → ZMod 2), DegLe k p →
    ∀ h : Fin k → Fin n → ZMod 2, diffs p h 0 = tensorEval (cT p k) h := by
  intro k
  induction k with
  | zero =>
    intro p _ h
    simp only [tensorEval, cT, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1 <;> funext l <;> exact Fin.elim0 l
  | succ k ih =>
    intro p hp h
    rw [← Fin.snoc_init_self h]
    generalize Fin.init h = g
    generalize h (Fin.last k) = w
    have hlin : ∀ u v, diffs p (Fin.snoc g (u + v)) 0 =
        diffs p (Fin.snoc g u) 0 + diffs p (Fin.snoc g v) 0 := top_add_last hp g
    rw [additive_expand (fun u => diffs p (Fin.snoc g u) 0) hlin w]
    have hstep : ∀ v, diffs p (Fin.snoc g (Pi.single v 1)) 0 =
        ∑ a : Fin k → Fin n, (∏ l, g l (a l)) * cT p (k+1) (Fin.snoc a v) := by
      intro v
      rw [diffs_snoc, ← diffs_dl, ih _ (degLe_dl hp _) g]
      simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 1
      simp only [cT]
      rw [diffs_dl, ← diffs_snoc]
      congr 2
      funext l
      refine Fin.lastCases ?_ (fun l' => ?_) l <;> simp
    simp only [hstep]
    simp only [tensorEval, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin n)
      (fun z => cT p (k+1) (Fin.snoc z.2 z.1) * ∏ l, (Fin.snoc g w : Fin (k+1) → Fin n → ZMod 2) l
        ((Fin.snoc z.2 z.1 : Fin (k+1) → Fin n) l)) _ (fun z => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

lemma cT_symm (p : (Fin n → ZMod 2) → ZMod 2) (j : ℕ) (σ : Equiv.Perm (Fin j))
    (a : Fin j → Fin n) : cT p j (a ∘ σ) = cT p j a := by
  unfold cT
  have := diffs_perm p (fun l => (Pi.single (a l) 1 : Fin n → ZMod 2)) σ
  rw [← this]
  rfl

/-- differences commute with affine reparametrisation -/
lemma diffs_comp {m k : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (B : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (h : Fin k → Fin m → ZMod 2) (y : Fin m → ZMod 2) :
    diffs (fun y => p (a + B y)) h y = diffs p (fun i => B (h i)) (a + B y) := by
  rw [diffs_closed, diffs_closed]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [map_add, map_sum, map_smul, add_assoc]

end P2MDiff

-- ===== ANF =====

open scoped BigOperators
noncomputable section

namespace P2MANF

open P2MDiff

variable {n : ℕ}

/-- the ANF coefficient as in the source statement -/
def coeffZ (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

def ind (B : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ B then 1 else 0

lemma natCast_zmod2 (k : ℕ) : (k : ZMod 2) = if Odd k then 1 else 0 := by
  split_ifs with h
  · exact ZMod.natCast_eq_one_iff_odd.mpr h
  · rw [ZMod.natCast_eq_zero_iff_even]; exact Nat.not_odd_iff_even.mp h

lemma coeffZ_eq (p : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) :
    coeffZ p S = ∑ B ∈ S.powerset, p (ind B) := by
  classical
  have h01 : ∀ z : ZMod 2, (if z ≠ 0 then (1 : ZMod 2) else 0) = z := by decide
  rw [← Finset.sum_congr rfl (fun B _ => h01 (p (ind B))), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one, natCast_zmod2]
  unfold coeffZ ParityCubes.anfCoeff
  have : ∀ B : Finset (Fin n), (fun i => if decide (i ∈ B) = true then (1 : ZMod 2) else 0) = ind B := by
    intro B; funext i; simp [ind]
  simp only [this, decide_eq_true_eq]
  congr

/-- affine phases have no ANF coefficients of size `≥ 2` -/
lemma coeffZ_affine (p : (Fin n → ZMod 2) → ZMod 2)
    (hp : ∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) : coeffZ p S = 0 := by
  classical
  rw [coeffZ_eq]
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set T := S.erase a
  have hS' : S = insert a T := (Finset.insert_erase ha).symm
  have haT : a ∉ T := Finset.notMem_erase a S
  have hT : T.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  rw [hS', Finset.sum_powerset_insert haT]
  rw [← Finset.sum_add_distrib]
  have hc : ∀ B ∈ T.powerset, p (ind B) + p (ind (insert a B)) = p (Pi.single a 1) + p 0 := by
    intro B hB
    have haB : a ∉ B := fun h => haT (Finset.mem_powerset.mp hB h)
    have hind : ind (insert a B) = ind B + Pi.single a 1 := by
      funext i; by_cases hi : i = a
      · subst hi; simp [ind, haB]
      · simp [ind, hi, Pi.single_apply]
    rw [hind]
    have := hp 0 (ind B) (Pi.single a 1)
    simp only [zero_add] at this
    have e : ∀ w x y z : ZMod 2, w + x + y + z = 0 → x + w = y + z := by decide
    exact e _ _ _ _ this
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  have : ((2 ^ T.card : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_pow (Finset.card_pos.mpr hT).ne']
  rw [this, zero_mul]

end P2MANF

namespace P2MANF

open P2MDiff

variable {n : ℕ}

lemma degLe_iff_succ (k : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe (k+1) f ↔ ∀ u, DegLe k (dl u f) := by
  constructor
  · intro hf u; exact degLe_dl hf u
  · intro H h x
    rw [diffs_succ]; exact H (h 0) (Fin.tail h) x

lemma degLe_zero_iff (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLe 0 f ↔ ∀ u x, f (x + u) = f x := by
  have e : ∀ h : Fin 1 → Fin n → ZMod 2, diffs f h = dl (h 0) f := by
    intro h; rw [diffs_succ, diffs_zero]
  constructor
  · intro hf u x
    have := hf (fun _ => u) x
    rw [e] at this
    simp only [dl] at this
    have e2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact e2 _ _ this
  · intro H h x
    rw [e]; simp only [dl, H]
    exact CharTwo.add_self_eq_zero _

lemma diffs_add {k : ℕ} (f g : (Fin n → ZMod 2) → ZMod 2) (h : Fin k → Fin n → ZMod 2) (x : Fin n → ZMod 2) :
    diffs (fun y => f y + g y) h x = diffs f h x + diffs g h x := by
  simp only [diffs_closed, Finset.sum_add_distrib]

lemma degLe_add {k : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (hg : DegLe k g) :
    DegLe k (fun y => f y + g y) := by
  intro h x; rw [diffs_add, hf, hg, add_zero]

lemma degLe_zerofun (k : ℕ) : DegLe k (fun _ : Fin n → ZMod 2 => (0 : ZMod 2)) := by
  intro h x; simp [diffs_closed]

lemma degLe_smul {k : ℕ} (c : ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k (fun y => c * f y) := by
  intro h x
  simp only [diffs_closed, ← Finset.mul_sum]
  rw [← diffs_closed, hf, mul_zero]

lemma degLe_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ i ∈ s, DegLe k (f i)) : DegLe k (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLe_zerofun k
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact degLe_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma degLe_translate {k : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) (u : Fin n → ZMod 2) :
    DegLe k (fun x => f (x + u)) := by
  intro h x
  have := hf h (x + u)
  rw [diffs_closed] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1; abel

lemma degLe_mono {k k' : ℕ} (hkk : k ≤ k') {f : (Fin n → ZMod 2) → ZMod 2} (hf : DegLe k f) :
    DegLe k' f := by
  induction hkk with
  | refl => exact hf
  | step _ ih => exact degLe_succ ih

lemma dl_mul (u : Fin n → ZMod 2) (g h : (Fin n → ZMod 2) → ZMod 2) :
    dl u (fun x => g x * h x) = fun x => dl u g x * h (x + u) + g x * dl u h x := by
  funext x
  simp only [dl]
  have h2 := CharTwo.add_self_eq_zero (g x * h (x + u))
  linear_combination (-1 : ZMod 2) * h2

lemma degLe_mul : ∀ (N a b : ℕ) (g h : (Fin n → ZMod 2) → ZMod 2), a + b = N → DegLe a g →
    DegLe b h → DegLe N (fun x => g x * h x) := by
  intro N
  induction N with
  | zero =>
    intro a b g h hab hg hh
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    rw [degLe_zero_iff] at *
    intro u x
    rw [hg, hh]
  | succ N ih =>
    intro a b g h hab hg hh
    rw [degLe_iff_succ]
    intro u
    rw [dl_mul]
    apply degLe_add
    · cases a with
      | zero =>
        have : ∀ x, dl u g x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff g).mp hg u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, zero_mul]
        exact degLe_zerofun N
      | succ a =>
        exact ih a b (dl u g) (fun x => h (x + u)) (by omega) (degLe_dl hg u) (degLe_translate hh u)
    · cases b with
      | zero =>
        have : ∀ x, dl u h x = 0 := by
          intro x; simp only [dl]; rw [(degLe_zero_iff h).mp hh u x]
          exact CharTwo.add_self_eq_zero _
        simp only [this, mul_zero]
        exact degLe_zerofun N
      | succ b =>
        exact ih a b g (dl u h) (by omega) hg (degLe_dl hh u)

def mon (S : Finset (Fin n)) : (Fin n → ZMod 2) → ZMod 2 := fun x => ∏ i ∈ S, x i

lemma degLe_mon (S : Finset (Fin n)) : DegLe S.card (mon S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [mon, Finset.prod_empty, Finset.card_empty]
    rw [degLe_zero_iff]; intro u x; rfl
  | insert a S ha ih =>
    have hcoord : DegLe 1 (fun x : Fin n → ZMod 2 => x a) := by
      rw [degLe_iff_succ]; intro u
      rw [degLe_zero_iff]; intro v x
      simp only [dl, Pi.add_apply]
      linear_combination CharTwo.add_self_eq_zero (v a)
    have := degLe_mul (1 + S.card) 1 S.card _ _ rfl hcoord ih
    rw [Finset.card_insert_of_notMem ha, add_comm]
    convert this using 1
    funext x
    simp [mon, Finset.prod_insert ha]

lemma mobius (T : Finset (Fin n)) : ∀ g : Finset (Fin n) → ZMod 2,
    ∑ S ∈ T.powerset, ∑ B ∈ S.powerset, g B = g T := by
  classical
  induction T using Finset.induction_on with
  | empty => intro g; simp
  | insert a T ha ih =>
    intro g
    rw [Finset.sum_powerset_insert ha]
    have h1 : ∀ S ∈ T.powerset, ∑ B ∈ (insert a S).powerset, g B =
        ∑ B ∈ S.powerset, g B + ∑ B ∈ S.powerset, g (insert a B) := by
      intro S hS
      have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
      rw [Finset.sum_powerset_insert haS]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih (fun B => g (insert a B))]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

lemma inversion (p : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    p x = ∑ S, coeffZ p S * mon S x := by
  classical
  set T := Finset.univ.filter fun i => x i ≠ 0
  have hx : x = ind T := by
    funext i
    simp only [ind, T, Finset.mem_filter, Finset.mem_univ, true_and]
    have h01 : ∀ z : ZMod 2, z = if z ≠ 0 then 1 else 0 := by decide
    exact h01 (x i)
  have hmon : ∀ S, mon S x = if S ⊆ T then 1 else 0 := by
    intro S
    rw [hx]
    simp only [mon, ind]
    split_ifs with h
    · exact Finset.prod_eq_one fun i hi => by simp [h hi]
    · rw [Finset.not_subset] at h
      obtain ⟨i, hiS, hiT⟩ := h
      exact Finset.prod_eq_zero hiS (by simp [hiT])
  simp only [hmon, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ T) = T.powerset := by
    ext S; simp
  rw [this]
  simp only [coeffZ_eq]
  rw [mobius T (fun B => p (ind B)), ← hx]

/-- ANF degree at most `d` implies vanishing `(d+1)`-fold differences -/
theorem degLe_of_coeffZ {d : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (h : ∀ S : Finset (Fin n), d < S.card → coeffZ p S = 0) : DegLe d p := by
  have hp : p = fun x => ∑ S, coeffZ p S * mon S x := funext (inversion p)
  rw [hp]
  apply degLe_sum
  intro S _
  by_cases hS : d < S.card
  · simp only [h S hS, zero_mul]; exact degLe_zerofun d
  · exact degLe_smul _ (degLe_mono (by omega) (degLe_mon S))

end P2MANF

-- ===== adapter =====
open ParityDegreeDepth.Core in
theorem solution {n d : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) :
    ((∀ S : Finset (Fin n), d < S.card →
        (if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
          then (1 : ZMod 2) else 0) = 0) →
      ∀ (h : Fin (d + 1) → Fin n → ZMod 2) (x : Fin n → ZMod 2),
        (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0) ∧
    ((∀ x u v, p (x + u + v) + p (x + u) + p (x + v) + p x = 0) →
      ∀ S : Finset (Fin n), 2 ≤ S.card →
        (if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
          then (1 : ZMod 2) else 0) = 0) := by
  refine ⟨fun h => P2MANF.degLe_of_coeffZ p h, fun h S hS => P2MANF.coeffZ_affine p h S hS⟩

