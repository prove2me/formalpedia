-- Prove2me | solution 1 for ValiantBorder.affineDetCircuit
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:22:56.884662+00:00
-- url     : https://prove2.me/submissions/4bfcf8d6-7558-4c21-81c8-c3200d477bba

/- Lean circuit construction for Bird's division-free determinant algorithm.
Source: R. S. Bird, A simple division-free algorithm for computing determinants (2011),
https://doi.org/10.1016/j.ipl.2011.08.006. The specification and its correctness are from
Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness. -/
import Definitions.Def_VP_VNP_all_fields
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness


open MvPolynomial
namespace BorderDet
variable {R V : Type} [CommRing R]
local notation "P" => MvPolynomial V R

def Good (l : ℕ → P) (s : ℕ) : Prop :=
  ∀ k < s, (∃ v : V, l k = X v) ∨ (∃ a : R, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

def Has (l : ℕ → P) (s : ℕ) (f : P) : Prop := ∃ k < s, l k = f

/-- A set of available values can be obtained in one circuit, allowing shared gates. -/
def Holds (T : Set P) (s : ℕ) : Prop :=
  ∃ l : ℕ → P, Good l s ∧ ∀ f ∈ T, Has l s f

theorem Holds.weaken {T U : Set P} {s t : ℕ} (h : Holds T s) (hU : U ⊆ T) (ht : s ≤ t) :
    Holds U t := by
  obtain ⟨l, hl, hT⟩ := h
  let L (i : ℕ) : P := if i < s then l i else C 0
  have he (i : ℕ) (hi : i < s) : L i = l i := if_pos hi
  refine ⟨L, ?_, fun f hf => ?_⟩
  · intro i _
    by_cases hi : i < s
    · rcases hl i hi with ⟨v,hv⟩ | ⟨a,ha⟩ | ⟨j,hj,k,hk,e⟩ | ⟨j,hj,k,hk,e⟩
      · exact Or.inl ⟨v, (he i hi).trans hv⟩
      · exact Or.inr (Or.inl ⟨a, (he i hi).trans ha⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,by rw [he _ hi,he _ (hj.trans hi),he _ (hk.trans hi),e]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j,hj,k,hk,by rw [he _ hi,he _ (hj.trans hi),he _ (hk.trans hi),e]⟩))
    · exact Or.inr (Or.inl ⟨0, if_neg hi⟩)
  · obtain ⟨i,hi,e⟩ := hT f (hU hf)
    exact ⟨i, hi.trans_le ht, (he _ hi).trans e⟩

theorem empty_holds : Holds (∅ : Set P) 0 :=
  ⟨fun _ => 0, fun _ hi => (Nat.not_lt_zero _ hi).elim, fun _ hf => hf.elim⟩

inductive Gate (T : Set P) : P → Prop
| var (v : V) : Gate T (X v)
| const (a : R) : Gate T (C a)
| add {f g : P} (hf : f ∈ T) (hg : g ∈ T) : Gate T (f + g)
| mul {f g : P} (hf : f ∈ T) (hg : g ∈ T) : Gate T (f * g)

theorem Holds.gate {T : Set P} {s : ℕ} {f : P} (h : Holds T s) (hg : Gate T f) :
    Holds (insert f T) (s+1) := by
  obtain ⟨l,hl,hT⟩ := h
  let L := Function.update l s f
  have he (i : ℕ) (hi : i < s) : L i = l i := Function.update_of_ne hi.ne _ _
  have hs : L s = f := Function.update_self ..
  refine ⟨L, ?_, fun g hg => ?_⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rcases hl i hi with ⟨v,hv⟩ | ⟨a,ha⟩ | ⟨j,hj,k,hk,e⟩ | ⟨j,hj,k,hk,e⟩
      · exact Or.inl ⟨v, (he i hi).trans hv⟩
      · exact Or.inr (Or.inl ⟨a, (he i hi).trans ha⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,by rw [he _ hi,he _ (hj.trans hi),he _ (hk.trans hi),e]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j,hj,k,hk,by rw [he _ hi,he _ (hj.trans hi),he _ (hk.trans hi),e]⟩))
    · cases hg with
      | var v => exact Or.inl ⟨v, hs⟩
      | const a => exact Or.inr (Or.inl ⟨a,hs⟩)
      | add hf hg =>
        obtain ⟨j,hj,ej⟩ := hT _ hf
        obtain ⟨k,hk,ek⟩ := hT _ hg
        exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,by rw [hs,he _ hj,he _ hk,ej,ek]⟩))
      | mul hf hg =>
        obtain ⟨j,hj,ej⟩ := hT _ hf
        obtain ⟨k,hk,ek⟩ := hT _ hg
        exact Or.inr (Or.inr (Or.inr ⟨j,hj,k,hk,by rw [hs,he _ hj,he _ hk,ej,ek]⟩))
  · rcases Set.mem_insert_iff.1 hg with rfl | hg
    · exact ⟨s, Nat.lt_succ_self _,hs⟩
    · obtain ⟨i,hi,e⟩ := hT _ hg
      exact ⟨i,by omega,(he _ hi).trans e⟩

/-- A formula that extends an existing tape and preserves every available entry. -/
def Ext (T : Set P) (f : P) (c : ℕ) : Prop :=
  ∀ (U : Set P) (s : ℕ), T ⊆ U → Holds U s → Holds (insert f U) (s+c)

theorem Ext.gate {T : Set P} {f : P} (hg : Gate T f) : Ext T f 1 := by
  intro U s hU h
  apply h.gate
  cases hg with
  | var v => exact .var v
  | const a => exact .const a
  | add h1 h2 => exact .add (hU h1) (hU h2)
  | mul h1 h2 => exact .mul (hU h1) (hU h2)

theorem Ext.base {T : Set P} {f : P} (hf : f ∈ T) : Ext T f 0 := by
  intro U s hu h
  simpa [Set.insert_eq_of_mem (hu hf)] using h

theorem Ext.widen {T : Set P} {f : P} {c d : ℕ} (he : Ext T f c) (hd : c ≤ d) : Ext T f d :=
  fun U s hU h => (he U s hU h).weaken (fun _ h => h) (by omega)

theorem Ext.bin {T : Set P} {f g v : P} {c d : ℕ} (hf : Ext T f c) (hg : Ext T g d)
    (hv : ∀ S : Set P, f ∈ S → g ∈ S → Gate S v) : Ext T v (c+d+1) := by
  intro U s hU h
  have h1 := hf U s hU h
  have h2 := hg (insert f U) (s+c) (hU.trans (Set.subset_insert _ _)) h1
  have h3 := h2.gate (hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert _ _))
  exact h3.weaken (Set.insert_subset_insert ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) (by omega)

theorem Ext.add {T : Set P} {f g : P} {c d : ℕ} (hf : Ext T f c) (hg : Ext T g d) :
    Ext T (f+g) (c+d+1) := hf.bin hg fun _ => Gate.add

theorem Ext.mul {T : Set P} {f g : P} {c d : ℕ} (hf : Ext T f c) (hg : Ext T g d) :
    Ext T (f*g) (c+d+1) := hf.bin hg fun _ => Gate.mul

theorem Ext.sum {T : Set P} {ι : Type} (I : Finset ι) (f : ι → P) (c : ℕ)
    (hf : ∀ i ∈ I, Ext T (f i) c) : Ext T (∑ i ∈ I, f i) (1 + I.card*(c+1)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (Ext.gate (T:=T) (Gate.const (0:R)))
  | insert i I hi ih =>
    have h1 := hf i (Finset.mem_insert_self i I)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    exact (h1.add h2).widen (by nlinarith)

theorem Ext.collect {T : Set P} {ι : Type} (I : Finset ι) (f : ι → P) (c : ℕ)
    (hf : ∀ i ∈ I, Ext T (f i) c) {s : ℕ} (h : Holds T s) :
    Holds ((f '' (I : Set ι)) ∪ T) (s + I.card*c) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using h
  | insert i I hi ih =>
    have h1 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have h2 := hf i (Finset.mem_insert_self i I) _ _ Set.subset_union_right h1
    simpa [Set.image_insert_eq, Set.insert_union, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.add_assoc] using h2

end BorderDet


open MvPolynomial
namespace BorderDet
/- The matrix/array compatibility lemmas below are from Mathlib,
Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean.
Copyright (c) 2026 Paul Cadman, Apache-2.0. They connect the
public array-correctness API to the finite-index matrix recurrence. -/
namespace BirdCompat
open Function BirdDet
variable {R : Type*} [CommRing R] {n : ℕ}
/-- `sumFrom n lo f` is the sum of `f` over the half-open interval `[lo, n)`. -/
theorem sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

theorem sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- The scalar recurrence initialized by array lookup agrees pointwise
  with the matrix recurrence. -/
theorem iterate_stepEntry_get_eq_spec (A : Array R) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    ((stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply', stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, ih,
      Matrix.of_apply, get_eq]

/-- The flat-array algorithm `BirdDet.birdDet` computes the same determinant as
  `BirdDet.Spec.birdDet`. -/
theorem birdDet_eq_birdDetSpec (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k => simp [birdDet_succ, Spec.birdDetSpec_succ, ← iterate_stepEntry_get_eq_spec A hA k]


theorem det_spec {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    A.det = Spec.birdDet A := by
  let t := Array.ofFn fun k : Fin (n*n) => A k.divNat k.modNat
  have hsize : t.size = n*n := Array.size_ofFn
  have hmat : Matrix.ofArray t hsize = A := Matrix.ofArray_ofFn A
  have hh := (BirdDet.det_eq_birdDet t hsize).trans (birdDet_eq_birdDetSpec t hsize)
  rwa [hmat] at hh
end BirdCompat

variable {R V : Type} [CommRing R]
local notation "P" => MvPolynomial V R

def entries {n : ℕ} (A : Matrix (Fin n) (Fin n) P) : Set P :=
  Set.range fun ij : Fin n × Fin n => A ij.1 ij.2

theorem mem_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    A i j ∈ entries A := ⟨(i,j),rfl⟩

theorem bird_entry {n : ℕ} (A B : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    Ext (entries A ∪ entries B) (BirdDet.Spec.stepEntry A B i j) (5*n+8) := by
  classical
  let T := entries A ∪ entries B
  have ha (a b : Fin n) : Ext T (A a b) 0 := Ext.base (Set.mem_union_left _ (mem_entries A a b))
  have hb (a b : Fin n) : Ext T (B a b) 0 := Ext.base (Set.mem_union_right _ (mem_entries B a b))
  have hd := Ext.sum (T:=T) (Finset.Ioi i) (fun k => B k k) 0 (fun k _ => hb k k)
  have hp := Ext.sum (T:=T) (Finset.Ioi i) (fun k => B i k * A k j) 1 (fun k _ => (hb i k).mul (ha k j))
  have he := ((((Ext.gate (T:=T) (Gate.const (-1:R))).mul hd).mul (ha i j)).add hp)
  have hcard : (Finset.Ioi i).card ≤ n := by simpa using Finset.card_le_univ (Finset.Ioi i)
  simp only [BirdDet.Spec.stepEntry, Matrix.of_apply]
  simpa only [map_neg, map_one, neg_one_mul] using he.widen (d:=5*n+8) (by omega)

theorem bird_iter {n : ℕ} (A : Matrix (Fin n) (Fin n) P) {s : ℕ} (ha : Holds (entries A) s) (k : ℕ) :
    Holds (entries A ∪ entries ((BirdDet.Spec.stepEntry A)^[k] A)) (s+k*(n*n*(5*n+8))) := by
  classical
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    let B := (BirdDet.Spec.stepEntry A)^[k] A
    have hc := Ext.collect (T:=entries A ∪ entries B) Finset.univ
      (fun ij : Fin n × Fin n => BirdDet.Spec.stepEntry A B ij.1 ij.2) (5*n+8)
      (fun ij _ => bird_entry A B ij.1 ij.2) ih
    have hset : entries A ∪ entries (BirdDet.Spec.stepEntry A B) ⊆
        ((fun ij : Fin n × Fin n => BirdDet.Spec.stepEntry A B ij.1 ij.2) '' (Finset.univ : Finset (Fin n × Fin n)) ∪ (entries A ∪ entries B)) := by
      intro f hf
      rcases hf with h | ⟨ij,rfl⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨ij,by simp,rfl⟩
    rw [Function.iterate_succ_apply']
    exact hc.weaken hset (by simp [Nat.succ_mul,Nat.add_assoc])

/-- The gate count includes every operation used to build, and then reuse, the matrices. -/
theorem determinant_circuit {n : ℕ} (A : Matrix (Fin n) (Fin n) P) {s : ℕ} (h : Holds (entries A) s) :
    Statement.Computes A.det (s+n*(n*n*(5*n+8))+2) := by
  classical
  rw [BirdCompat.det_spec]
  cases n with
  | zero =>
    rw [BirdDet.Spec.birdDetSpec_zero]
    have hg := h.gate (Gate.const (1:R))
    obtain ⟨l,hl,hh⟩ := hg.weaken (fun _ h => h) (show s+1 ≤ s+0*(0*0*(5*0+8))+2 by omega)
    exact ⟨l,hl,hh _ (by simp)⟩
  | succ k =>
    rw [BirdDet.Spec.birdDetSpec_succ]
    let B := (BirdDet.Spec.stepEntry A)^[k] A
    have h0 := bird_iter A h k
    have hc := h0.gate (Gate.const ((-1:R)^k))
    have hp := hc.gate (Gate.mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_union_right _ (mem_entries B 0 0))))
    have ht : s+k*((k+1)*(k+1)*(5*(k+1)+8))+1+1 ≤ s+(k+1)*((k+1)*(k+1)*(5*(k+1)+8))+2 := by
      rw [Nat.succ_mul k ((k+1)*(k+1)*(5*(k+1)+8))]
      omega
    obtain ⟨l,hl,hh⟩ := hp.weaken (fun _ h => h) ht
    refine ⟨l,hl,?_⟩
    simpa only [Has, B, map_pow, map_neg, map_one] using hh _ (Set.mem_insert _ _)

noncomputable def affine {ι : Type} [Fintype ι] (c : R) (a : ι → R) : MvPolynomial ι R :=
  C c + ∑ i, C (a i) * X i

theorem affine_size {ι : Type} [Fintype ι] (T : Set (MvPolynomial ι R)) (c : R) (a : ι → R) :
    Ext T (affine c a) (4*Fintype.card ι + 3) := by
  classical
  have h1 := Ext.sum (T:=T) Finset.univ (fun i : ι => C (a i) * X i) 3
    (fun i _ => (Ext.gate (Gate.const _)).mul (Ext.gate (Gate.var i)))
  have h2 := (Ext.gate (T:=T) (Gate.const c)).add h1
  exact h2.widen (by simp; omega)

theorem affine_det_finite {ι : Type} [Fintype ι] {n : ℕ} (c : Fin n → Fin n → R) (a : Fin n → Fin n → ι → R) :
    Statement.Computes (Matrix.of fun i j => affine (c i j) (a i j)).det ((Fintype.card ι+n+2)^8) := by
  classical
  let A := Matrix.of fun i j => affine (c i j) (a i j)
  have h := Ext.collect (T:=(∅ : Set (MvPolynomial (ι) R))) Finset.univ
    (fun ij : Fin n × Fin n => A ij.1 ij.2) (4*(Fintype.card ι)+3)
    (fun ij _ => by simpa [A] using affine_size ∅ (c ij.1 ij.2) (a ij.1 ij.2)) empty_holds
  have h' : Holds (entries A) (n*n*(4*(Fintype.card ι)+3)) := by simpa [entries] using h
  obtain ⟨l,hl,hf⟩ := determinant_circuit A h'
  have hh : Holds ({A.det} : Set _) (n*n*(4*(Fintype.card ι)+3)+n*(n*n*(5*n+8))+2) :=
    ⟨l,hl,fun f h => (Set.mem_singleton_iff.1 h) ▸ hf⟩
  obtain ⟨L,hL,hF⟩ := hh.weaken (fun _ h => h) (show _ ≤ (Fintype.card ι+n+2)^8 by ring_nf; omega)
  exact ⟨L,hL,hF _ (Set.mem_singleton _)⟩
end BorderDet

theorem solution {R V : Type} [CommRing R] [Fintype V] {n : ℕ}
    (c : Fin n → Fin n → R) (a : Fin n → Fin n → V → R) :
    Statement.Computes (Matrix.of fun i j =>
      MvPolynomial.C (c i j) + ∑ v, MvPolynomial.C (a i j v) * MvPolynomial.X v).det
      ((Fintype.card V + n + 2)^8) :=
  BorderDet.affine_det_finite c a
