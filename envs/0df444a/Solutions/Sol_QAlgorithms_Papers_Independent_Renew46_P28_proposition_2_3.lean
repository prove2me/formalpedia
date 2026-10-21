-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:50:38.006692+00:00
-- url     : https://prove2.me/submissions/d9116633-e1f6-4ebc-94ad-6441af49a586

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w


open Set Filter Topology

/-- The local continuous-inverse property at 1. -/
def G66MLoc (R : Type*) [Ring R] [TopologicalSpace R] : Prop :=
  (∃ N ∈ 𝓝 (1 : R), N ⊆ {x | IsUnit x}) ∧ ContinuousAt (Ring.inverse : R → R) 1

theorem g66m_glob {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] (h : G66MLoc R) :
    IsOpen {x : R | IsUnit x} ∧ Continuous (fun a : {a : R // IsUnit a} => Ring.inverse a.val) := by
  obtain ⟨⟨N, hN, hNu⟩, hinv⟩ := h
  have key : ∀ u : Rˣ, {y : R | ((u⁻¹ : Rˣ) : R) * y ∈ N} ∈ 𝓝 (u : R) := by
    intro u
    have hc : ContinuousAt (fun y : R => ((u⁻¹ : Rˣ) : R) * y) (u : R) :=
      (continuous_const.mul continuous_id).continuousAt
    have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by simp
    exact hc.preimage_mem_nhds (by rw [h1]; exact hN)
  have hunit : ∀ (u : Rˣ) (y : R), ((u⁻¹ : Rˣ) : R) * y ∈ N → IsUnit y := by
    intro u y hy
    obtain ⟨w, hw⟩ := hNu hy
    refine ⟨u * w, ?_⟩
    simp [hw]
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨u, rfl⟩
    exact Filter.mem_of_superset (key u) fun y hy => hunit u y hy
  · rw [continuous_iff_continuousAt]
    rintro ⟨x, ⟨u, rfl⟩⟩
    refine ContinuousAt.comp (g := (Ring.inverse : R → R)) (f := Subtype.val) ?_
      continuous_subtype_val.continuousAt
    have hc : ContinuousAt (fun y : R => ((u⁻¹ : Rˣ) : R) * y) (u : R) :=
      (continuous_const.mul continuous_id).continuousAt
    have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by simp
    have hA : ContinuousAt (fun y : R => Ring.inverse (((u⁻¹ : Rˣ) : R) * y) * ((u⁻¹ : Rˣ) : R)) (u : R) :=
      (ContinuousAt.comp_of_eq hinv hc h1).mul continuousAt_const
    refine hA.congr_of_eventuallyEq ?_
    filter_upwards [key u] with y hy
    obtain ⟨w, rfl⟩ := hunit u y hy
    rw [← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, ← Units.val_mul]
    simp

theorem g66m_of_cia {K : Type*} [Field K] [TopologicalSpace K] {A : Type*} [Ring A] [Algebra K A]
    [TopologicalSpace A] (hA : continuousInverseAlgebra K A) : G66MLoc A := by
  obtain ⟨_, _, _, hU, hI⟩ := hA
  refine ⟨⟨_, hU.mem_nhds isUnit_one, le_rfl⟩, ?_⟩
  have hon : ContinuousOn (Ring.inverse : A → A) {a | IsUnit a} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hI
  exact hon.continuousAt (hU.mem_nhds isUnit_one)

/-- Transport along a ring isomorphism which is a homeomorphism. -/
theorem g66m_transport {R R' : Type*} [Ring R] [TopologicalSpace R] [Ring R'] [TopologicalSpace R']
    (e : R ≃+* R') (he : Continuous e) (he' : Continuous e.symm) (h : G66MLoc R) : G66MLoc R' := by
  obtain ⟨⟨N, hN, hNu⟩, hinv⟩ := h
  refine ⟨⟨e.symm ⁻¹' N, ?_, ?_⟩, ?_⟩
  · apply he'.continuousAt.preimage_mem_nhds
    simpa using hN
  · intro y hy
    have := (hNu hy).map e
    simpa using this
  · have hinv' : ∀ y : R', Ring.inverse y = e (Ring.inverse (e.symm y)) := by
      intro y
      by_cases hy : IsUnit y
      · obtain ⟨w, rfl⟩ := hy
        have : e.symm (w : R') = ((Units.map e.symm.toMonoidHom w : Rˣ) : R) := rfl
        rw [this, Ring.inverse_unit, Ring.inverse_unit]
        simp
      · have hy' : ¬ IsUnit (e.symm y) := fun h => hy (by simpa using h.map e)
        rw [Ring.inverse_non_unit _ hy, Ring.inverse_non_unit _ hy', map_zero]
    have : (Ring.inverse : R' → R') = fun y => e (Ring.inverse (e.symm y)) := funext hinv'
    rw [this]
    have h1 : e.symm 1 = 1 := map_one _
    exact he.continuousAt.comp (ContinuousAt.comp_of_eq hinv he'.continuousAt h1)

open Matrix in
theorem g66m_block {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring α]
    (D : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (a a' : Matrix n n α) (S' : Matrix m m α)
    (ha1 : a * a' = 1) (ha2 : a' * a = 1) (hS1 : (D - B * a' * C) * S' = 1)
    (hS2 : S' * (D - B * a' * C) = 1) :
    fromBlocks D B C a * fromBlocks S' (-(S' * B * a')) (-(a' * C * S')) (a' + a' * C * S' * B * a') = 1 ∧
    fromBlocks S' (-(S' * B * a')) (-(a' * C * S')) (a' + a' * C * S' * B * a') * fromBlocks D B C a = 1 := by
  have hS1' : D * S' = 1 + B * (a' * (C * S')) := by
    rw [← hS1]; simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
  have hS2' : S' * D = 1 + S' * (B * (a' * C)) := by
    rw [← hS2]; simp only [Matrix.mul_sub, Matrix.mul_assoc]; abel
  rw [← Matrix.fromBlocks_one]
  constructor
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hS1']; abel
    · rw [← Matrix.mul_assoc D S', hS1']
      simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]; abel
    · rw [← Matrix.mul_assoc a a', ha1, Matrix.one_mul]; abel
    · rw [← Matrix.mul_assoc a a' (C * _), ha1, Matrix.one_mul]; abel
  · rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hS2']; abel
    · rw [ha2, Matrix.mul_one]; abel
    · rw [hS2']
      simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]; abel
    · rw [ha2, Matrix.mul_one]; abel

theorem g66m_cmul {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] {X : Type*}
    [TopologicalSpace X] {l m n : Type*} [Fintype m] {f : X → Matrix l m A} {g : X → Matrix m n A}
    {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun y => f y * g y) x :=
  ContinuousAt.comp (g := fun p : Matrix l m A × Matrix m n A => p.1 * p.2)
    (f := fun y => (f y, g y)) (continuous_fst.matrix_mul continuous_snd).continuousAt (hf.prodMk hg)

open Matrix in
theorem g66m_step {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hm : G66MLoc (Matrix m m A)) (hn : G66MLoc (Matrix n n A)) :
    G66MLoc (Matrix (m ⊕ n) (m ⊕ n) A) := by
  obtain ⟨⟨Nm, hNm, hNmu⟩, hinvm⟩ := hm
  obtain ⟨⟨Nn, hNn, hNnu⟩, hinvn⟩ := hn
  have cD : Continuous fun M : Matrix (m ⊕ n) (m ⊕ n) A => M.toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _
  have cB : Continuous fun M : Matrix (m ⊕ n) (m ⊕ n) A => M.toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _
  have cC : Continuous fun M : Matrix (m ⊕ n) (m ⊕ n) A => M.toBlocks₂₁ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _
  have cA : Continuous fun M : Matrix (m ⊕ n) (m ⊕ n) A => M.toBlocks₂₂ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _
  have h1 : (1 : Matrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 1 0 0 1 := fromBlocks_one.symm
  have e11 : (1 : Matrix (m ⊕ n) (m ⊕ n) A).toBlocks₁₁ = 1 := by rw [h1, toBlocks_fromBlocks₁₁]
  have e12 : (1 : Matrix (m ⊕ n) (m ⊕ n) A).toBlocks₁₂ = 0 := by rw [h1, toBlocks_fromBlocks₁₂]
  have e21 : (1 : Matrix (m ⊕ n) (m ⊕ n) A).toBlocks₂₁ = 0 := by rw [h1, toBlocks_fromBlocks₂₁]
  have e22 : (1 : Matrix (m ⊕ n) (m ⊕ n) A).toBlocks₂₂ = 1 := by rw [h1, toBlocks_fromBlocks₂₂]
  let ai : Matrix (m ⊕ n) (m ⊕ n) A → Matrix n n A := fun M => Ring.inverse M.toBlocks₂₂
  have cai : ContinuousAt ai 1 := ContinuousAt.comp_of_eq hinvn cA.continuousAt e22
  let S : Matrix (m ⊕ n) (m ⊕ n) A → Matrix m m A := fun M =>
    M.toBlocks₁₁ - M.toBlocks₁₂ * ai M * M.toBlocks₂₁
  have cS : ContinuousAt S 1 :=
    cD.continuousAt.sub (g66m_cmul (g66m_cmul cB.continuousAt cai) cC.continuousAt)
  have S1 : S 1 = 1 := by simp only [S, e11, e12, e21, Matrix.zero_mul, sub_zero]
  let Si : Matrix (m ⊕ n) (m ⊕ n) A → Matrix m m A := fun M => Ring.inverse (S M)
  have cSi : ContinuousAt Si 1 := ContinuousAt.comp_of_eq hinvm cS S1
  let Nf : Matrix (m ⊕ n) (m ⊕ n) A → Matrix (m ⊕ n) (m ⊕ n) A := fun M =>
    fromBlocks (Si M) (-(Si M * M.toBlocks₁₂ * ai M)) (-(ai M * M.toBlocks₂₁ * Si M))
      (ai M + ai M * M.toBlocks₂₁ * Si M * M.toBlocks₁₂ * ai M)
  have cfb : Continuous fun p : Matrix m m A × Matrix m n A × Matrix n m A × Matrix n n A =>
      fromBlocks p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    Continuous.matrix_fromBlocks continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have cN : ContinuousAt Nf 1 := by
    have := cfb.continuousAt.comp (x := 1) (cSi.prodMk
      ((g66m_cmul (g66m_cmul cSi cB.continuousAt) cai).neg.prodMk
      ((g66m_cmul (g66m_cmul cai cC.continuousAt) cSi).neg.prodMk
        (cai.add (g66m_cmul (g66m_cmul (g66m_cmul (g66m_cmul cai cC.continuousAt) cSi)
          cB.continuousAt) cai)))))
    exact this
  have hW : {M : Matrix (m ⊕ n) (m ⊕ n) A | M.toBlocks₂₂ ∈ Nn ∧ S M ∈ Nm} ∈ 𝓝 1 := by
    apply Filter.inter_mem
    · exact cA.continuousAt.preimage_mem_nhds (by rw [e22]; exact hNn)
    · exact cS.preimage_mem_nhds (by rw [S1]; exact hNm)
  have hinvW : ∀ M ∈ {M : Matrix (m ⊕ n) (m ⊕ n) A | M.toBlocks₂₂ ∈ Nn ∧ S M ∈ Nm},
      M * Nf M = 1 ∧ Nf M * M = 1 := by
    rintro M ⟨hMa, hMS⟩
    have ua : IsUnit M.toBlocks₂₂ := hNnu hMa
    have uS : IsUnit (S M) := hNmu hMS
    have := g66m_block M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ (ai M) (Si M)
      (Ring.mul_inverse_cancel _ ua) (Ring.inverse_mul_cancel _ ua)
      (Ring.mul_inverse_cancel _ uS) (Ring.inverse_mul_cancel _ uS)
    rw [fromBlocks_toBlocks] at this
    exact this
  refine ⟨⟨_, hW, fun M hM => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hinvW M hM
    exact ⟨⟨M, Nf M, h1, h2⟩, rfl⟩
  · refine cN.congr_of_eventuallyEq ?_
    filter_upwards [hW] with M hM
    obtain ⟨h1, h2⟩ := hinvW M hM
    have : M = ((⟨M, Nf M, h1, h2⟩ : (Matrix (m ⊕ n) (m ⊕ n) A)ˣ) : Matrix (m ⊕ n) (m ⊕ n) A) := rfl
    conv_lhs => rw [this, Ring.inverse_unit]
    rfl

theorem g66m_fin {K : Type*} [Field K] [TopologicalSpace K] {A : Type*} [Ring A] [Algebra K A]
    [TopologicalSpace A] [IsTopologicalRing A] (hA : G66MLoc A) (n : ℕ) :
    G66MLoc (Matrix (Fin n) (Fin n) A) := by
  induction n with
  | zero =>
    refine ⟨⟨Set.univ, Filter.univ_mem, fun x _ => ?_⟩, ?_⟩
    · have : x = 1 := Subsingleton.elim _ _
      rw [this]; exact isUnit_one
    · exact (continuous_of_const (fun x y => Subsingleton.elim _ _)).continuousAt
  | succ n ih =>
    have h1 : G66MLoc (Matrix (Fin 1) (Fin 1) A) :=
      g66m_transport (Matrix.uniqueRingEquiv (m := Fin 1) (A := A)).symm
        (by
          show Continuous fun a : A => (Matrix.uniqueRingEquiv (m := Fin 1) (A := A)).symm a
          exact continuous_pi fun i => continuous_pi fun j => continuous_id)
        (by
          show Continuous fun M : Matrix (Fin 1) (Fin 1) A => M default default
          exact continuous_apply_apply _ _)
        hA
    have hs := g66m_step ih h1
    let e := (Matrix.reindexAlgEquiv K A (finSumFinEquiv (m := n) (n := 1))).toRingEquiv
    refine g66m_transport e ?_ ?_ hs
    · show Continuous fun M => Matrix.reindex finSumFinEquiv finSumFinEquiv M
      exact continuous_id.matrix_reindex _ _
    · show Continuous fun M => Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M
      exact continuous_id.matrix_reindex _ _

/-- Proposition 2.3, PDF p.17: matrix algebras of CIAs are CIAs with their
natural entrywise product topology. The empty matrix case is not excluded. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A]
    (hA : continuousInverseAlgebra K A) (n : ℕ) :
    continuousInverseAlgebra K (Matrix (Fin n) (Fin n) A) := by
  obtain ⟨hT2, hTR, hSM, hU, hI⟩ := hA
  haveI := hT2; haveI := hTR; haveI := hSM
  have hloc := g66m_fin (K := K) (g66m_of_cia (K := K) ⟨hT2, hTR, hSM, hU, hI⟩) n
  obtain ⟨h1, h2⟩ := g66m_glob hloc
  exact ⟨inferInstance, inferInstance, inferInstance, h1, h2⟩

