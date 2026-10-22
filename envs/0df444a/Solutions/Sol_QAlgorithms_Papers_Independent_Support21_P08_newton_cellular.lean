-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.newton_cellular
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:12:23.487302+00:00
-- url     : https://prove2.me/submissions/7f9a1f06-c08a-4655-b758-5bb71f422bf0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open Polynomial

section NewtonExample

variable {R : Type*} [CommRing R] [newtonDomain : IsDomain R]

def g67e_q {n : ℕ} (c : Fin n → R) (i : ℕ) : R[X] :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), (X - C (c j))

lemma g67e_nv_eq {n : ℕ} (c : Fin n → R) (i : ℕ) :
    newtonVector c i = aeval (AdjoinRoot.root (newtonPolynomial c)) (g67e_q c i) := by
  simp [newtonVector, g67e_q, map_prod, AdjoinRoot.algebraMap_eq]

lemma g67e_q_monic {n : ℕ} (c : Fin n → R) (i : ℕ) : (g67e_q c i).Monic :=
  monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C (c j))

include newtonDomain in
lemma g67e_q_deg {n : ℕ} (c : Fin n → R) (i : Fin n) : (g67e_q c i.val).natDegree = i.val := by
  unfold g67e_q
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (c j))]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [show (Finset.univ.filter fun j : Fin n => j.val < i.val) = Finset.Iio i by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact Fin.lt_def.symm]
  exact Fin.card_Iio i

lemma g67e_nv_n {n : ℕ} (c : Fin n → R) : newtonVector c n = 0 := by
  unfold newtonVector
  rw [show (Finset.univ.filter fun j : Fin n => j.val < n) = Finset.univ by ext j; simp]
  rw [AdjoinRoot.algebraMap_eq]
  simp only [← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C, ← map_sub, ← map_prod]
  exact AdjoinRoot.mk_self

lemma g67e_nv_succ {n : ℕ} (c : Fin n → R) (i : Fin n) :
    newtonVector c (i.val + 1) = newtonVector c i.val *
      (AdjoinRoot.root (newtonPolynomial c) - algebraMap R _ (c i)) := by
  unfold newtonVector
  rw [show (Finset.univ.filter fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter fun j : Fin n => j.val < i.val) by
    ext j; simp [Fin.ext_iff]; omega]
  rw [Finset.prod_insert (by simp), mul_comm]

lemma g67e_nv_root {n : ℕ} (c : Fin n → R) (i : Fin n) :
    newtonVector c i.val * AdjoinRoot.root (newtonPolynomial c) =
      c i • newtonVector c i.val + newtonVector c (i.val + 1) := by
  rw [g67e_nv_succ, Algebra.smul_def]; ring

include newtonDomain in
lemma g67e_newton_basis {n : ℕ} (c : Fin n → R) :
    LinearIndependent R (fun i : Fin n => newtonVector c i.val) ∧
    Submodule.span R (Set.range (fun i : Fin n => newtonVector c i.val)) = ⊤ := by
  set g := newtonPolynomial c
  have hg : g.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C (c j))
  have hdeg : g.natDegree = n := by
    simp only [g, newtonPolynomial]
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (c j))]
    simp
  let pb := AdjoinRoot.powerBasis' hg
  let b : Module.Basis (Fin n) R (AdjoinRoot g) := pb.basis.reindex (finCongr hdeg)
  have hb : ∀ i : Fin n, b i = AdjoinRoot.root g ^ (i : ℕ) := by
    intro i
    simp only [b, pb, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
    rfl
  rw [b.is_basis_iff_det]
  have hv : (fun i : Fin n => newtonVector c i.val) =
      fun j => ∑ i : Fin n, (g67e_q c j.val).coeff i • b i := by
    funext j
    rw [g67e_nv_eq, aeval_eq_sum_range' (n := n) (by rw [g67e_q_deg]; exact j.isLt)]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (g67e_q c j.val).coeff i • AdjoinRoot.root g ^ i)]
    simp [hb]
  rw [Module.Basis.det_apply, hv]
  have : b.toMatrix (fun j => ∑ i : Fin n, (g67e_q c j.val).coeff i • b i) =
      Matrix.of (fun (i j : Fin n) => (g67e_q c j.val).coeff i) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, b.repr_sum_self]
    rfl
  rw [this, Matrix.det_matrixOfPolynomials (fun j : Fin n => g67e_q c j.val)
    (fun j => g67e_q_deg c j) (fun j => g67e_q_monic c j)]
  exact isUnit_one

end NewtonExample

section NewtonExample2
variable {R : Type*} [CommRing R] [newtonDomain : IsDomain R]

def g67e_E (n : ℕ) : CellIndex (Fin n) (fun _ : Fin n => Unit) ≃ Fin n where
  toFun z := z.1
  invFun i := ⟨i, ((), ())⟩
  left_inv z := by rcases z with ⟨i, ⟨⟨⟩, ⟨⟩⟩⟩; rfl
  right_inv i := rfl

/-- the span of the Newton vectors with index > l -/
lemma g67e_H_stable {n : ℕ} (c : Fin n → R) (l : Fin n) (y : NewtonAlgebra c)
    (hy : y ∈ Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val})
    (a : NewtonAlgebra c) :
    y * a ∈ Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val} := by
  set H := Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val}
  have hnext : ∀ m : Fin n, l ≤ m → newtonVector c (m.val + 1) ∈ H := by
    intro m hm
    by_cases h : m.val + 1 < n
    · exact Submodule.subset_span ⟨⟨m.val + 1, h⟩, by
        rw [Fin.lt_def]; show l.val < m.val + 1; have : l.val ≤ m.val := hm; omega, rfl⟩
    · have : m.val + 1 = n := by have := m.isLt; omega
      rw [this, g67e_nv_n]; exact H.zero_mem
  let Sa : Subalgebra R (NewtonAlgebra c) :=
    { carrier := {a | ∀ y ∈ H, y * a ∈ H}
      mul_mem' := by
        intro a b ha hb y hy
        rw [← mul_assoc]; exact hb _ (ha y hy)
      add_mem' := by
        intro a b ha hb y hy
        rw [mul_add]; exact H.add_mem (ha y hy) (hb y hy)
      algebraMap_mem' := by
        intro r y hy
        rw [← Algebra.commutes, ← Algebra.smul_def]
        exact H.smul_mem r hy }
  have hroot : AdjoinRoot.root (newtonPolynomial c) ∈ Sa := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro x ⟨m, hm, rfl⟩
      rw [g67e_nv_root]
      exact H.add_mem (H.smul_mem _ (Submodule.subset_span ⟨m, hm, rfl⟩)) (hnext m hm.le)
    · simp
    · intro x z _ _ hx hz; rw [add_mul]; exact H.add_mem hx hz
    · intro r x _ hx; rw [smul_mul_assoc]; exact H.smul_mem r hx
  have htop : Sa = ⊤ := by
    rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff]
    simpa using hroot
  have : a ∈ Sa := by rw [htop]; trivial
  exact this y hy

lemma g67e_hnext {n : ℕ} (c : Fin n → R) (l : Fin n) : newtonVector c (l.val + 1) ∈
      Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val} := by
  by_cases h : l.val + 1 < n
  · exact Submodule.subset_span ⟨⟨l.val + 1, h⟩, by rw [Fin.lt_def]; simp, rfl⟩
  · have : l.val + 1 = n := by have := l.isLt; omega
    rw [this, g67e_nv_n]; exact Submodule.zero_mem _

lemma g67e_mult {n : ℕ} (c : Fin n → R) (l : Fin n) (a : NewtonAlgebra c) :
    ∃ r : R, newtonVector c l.val * a - r • newtonVector c l.val ∈
      Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val} := by
  set H := Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val}
  set v := newtonVector c l.val
  have hnext : newtonVector c (l.val + 1) ∈ H := by
    by_cases h : l.val + 1 < n
    · exact Submodule.subset_span ⟨⟨l.val + 1, h⟩, by rw [Fin.lt_def]; simp, rfl⟩
    · have : l.val + 1 = n := by have := l.isLt; omega
      rw [this, g67e_nv_n]; exact H.zero_mem
  let Sa : Subalgebra R (NewtonAlgebra c) :=
    { carrier := {a | ∃ r : R, v * a - r • v ∈ H}
      mul_mem' := by
        rintro a b ⟨r, hr⟩ ⟨s, hs⟩
        refine ⟨r * s, ?_⟩
        have : v * (a * b) - (r * s) • v = (v * a - r • v) * b + r • (v * b - s • v) := by
          simp only [mul_smul, smul_sub, sub_mul, smul_mul_assoc, mul_assoc]; abel
        rw [this]
        exact H.add_mem (g67e_H_stable c l _ hr b) (H.smul_mem r hs)
      add_mem' := by
        rintro a b ⟨r, hr⟩ ⟨s, hs⟩
        refine ⟨r + s, ?_⟩
        have : v * (a + b) - (r + s) • v = (v * a - r • v) + (v * b - s • v) := by
          rw [mul_add, add_smul]; abel
        rw [this]; exact H.add_mem hr hs
      algebraMap_mem' := by
        intro r
        refine ⟨r, ?_⟩
        rw [← Algebra.commutes, ← Algebra.smul_def, sub_self]; exact H.zero_mem }
  have hroot : AdjoinRoot.root (newtonPolynomial c) ∈ Sa := by
    refine ⟨c l, ?_⟩
    show v * _ - _ ∈ H
    rw [g67e_nv_root, add_sub_cancel_left]; exact hnext
  have htop : Sa = ⊤ := by
    rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff]
    simpa using hroot
  have : a ∈ Sa := by rw [htop]; trivial
  exact this

end NewtonExample2

section NewtonExample3
variable {R : Type*} [CommRing R] [newtonDomain : IsDomain R]

include newtonDomain in
theorem solution {n : ℕ} (hn : 1 ≤ n) (c : Fin n → R) :
    newtonVector c n = 0 ∧
    (∀ i : Fin n, newtonVector c i.val * AdjoinRoot.root (newtonPolynomial c) =
      c i • newtonVector c i.val + newtonVector c (i.val + 1)) ∧
    ∃ D : CellDatum (R := R) (A := NewtonAlgebra c) (T := fun _ : Fin n => Unit),
      (∀ i : Fin n, D.basis ⟨i, ((), ())⟩ = newtonVector c i.val) ∧
      ∃ J : JMFamily D 1,
        (∀ i, J.L i = AdjoinRoot.root (newtonPolynomial c)) ∧
        (∀ t i, J.content t i = c t.1) ∧
        (separatesComparable J ↔ Function.Injective c) := by
  refine ⟨g67e_nv_n c, g67e_nv_root c, ?_⟩
  obtain ⟨hli, hspan⟩ := g67e_newton_basis c
  let bv := Module.Basis.mk hli hspan.ge
  let B : Module.Basis (CellIndex (Fin n) (fun _ : Fin n => Unit)) R (NewtonAlgebra c) :=
    bv.reindex (g67e_E n).symm
  have hbz : ∀ z, B z = newtonVector c z.1.val := by
    intro z
    simp [B, bv, g67e_E]
  have hH : ∀ l, higherSpan (R := R) B l =
      Submodule.span R {x | ∃ m : Fin n, l < m ∧ x = newtonVector c m.val} := by
    intro l
    unfold higherSpan
    congr 1
    ext x
    constructor
    · rintro ⟨m, s, t, hm, rfl⟩; exact ⟨m, hm, hbz _⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, (), (), hm, (hbz ⟨m, ((), ())⟩).symm⟩
  let D : CellDatum (R := R) (A := NewtonAlgebra c) (T := fun _ : Fin n => Unit) :=
    { basis := B
      star := LinearMap.id
      star_involutive := fun _ => rfl
      star_mul := fun x y => mul_comm x y
      star_basis := by intro l s t; cases s; cases t; rfl
      multiplication := by
        intro l t x
        obtain ⟨r, hr⟩ := g67e_mult c l x
        refine ⟨fun _ => r, fun s => ?_⟩
        rw [hH, Fintype.sum_unique]
        simpa [hbz] using hr }
  refine ⟨D, fun i => hbz _, ?_⟩
  let J : JMFamily D 1 :=
    { L := fun _ => AdjoinRoot.root (newtonPolynomial c)
      content := fun t _ => c t.1
      commuting := fun _ _ => rfl
      fixed := fun _ => rfl
      triangular := by
        intro l t i
        refine ⟨0, fun s => ?_⟩
        show B _ * _ - _ - _ ∈ higherSpan (R := R) B l
        simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
        rw [hH, hbz, g67e_nv_root, add_sub_cancel_left]
        exact g67e_hnext c l }
  refine ⟨J, fun _ => rfl, fun _ _ => rfl, ?_⟩
  constructor
  · intro h a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨i, hi⟩ := h ⟨b, ()⟩ ⟨a, ()⟩ (Or.inl hlt)
        (by intro e; exact hne (congrArg Sigma.fst e).symm)
      exact hi hab.symm
    · obtain ⟨i, hi⟩ := h ⟨a, ()⟩ ⟨b, ()⟩ (Or.inl hlt)
        (by intro e; exact hne (congrArg Sigma.fst e))
      exact hi hab
  · intro h s t _ hst
    refine ⟨0, ?_⟩
    show c s.1 ≠ c t.1
    intro e
    apply hst
    rcases s with ⟨a, ⟨⟩⟩; rcases t with ⟨b, ⟨⟩⟩
    have : a = b := h e
    subst this; rfl

end NewtonExample3
