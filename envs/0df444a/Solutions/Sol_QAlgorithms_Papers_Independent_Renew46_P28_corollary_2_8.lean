-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.corollary_2_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:13:51.434122+00:00
-- url     : https://prove2.me/submissions/0462dd45-893d-466f-a057-f8b5727f7e02

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

open scoped TensorProduct

section G66N

variable {K : Type*} [Field K] [TopologicalSpace K] {F : Type*} [Ring F] [Algebra K F]
  {A : Type*} [Ring A] [Algebra K A] {n : ℕ} (b : Module.Basis (Fin n) K F)

noncomputable def g66n_Φ : F ⊗[K] A →ₗ[K] (Fin n → A) :=
  TensorProduct.lift (LinearMap.mk₂ K (fun (f : F) (a : A) (k : Fin n) => b.repr f k • a)
    (fun f f' a => by funext k; simp [add_smul])
    (fun c f a => by funext k; simp [smul_smul])
    (fun f a a' => by funext k; simp [smul_add])
    (fun c f a => by funext k; simp [smul_comm c]))

theorem g66n_Φ_tmul (f : F) (a : A) : g66n_Φ (A := A) b (f ⊗ₜ a) = fun k => b.repr f k • a := rfl

theorem g66n_ΦT (a : Fin n → A) : g66n_Φ b (tensorCoordinateMap K b a) = a := by
  funext k
  simp only [tensorCoordinateMap, map_sum, g66n_Φ_tmul, Finset.sum_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  simp

theorem g66n_T_add (a a' : Fin n → A) :
    tensorCoordinateMap K b (a + a') = tensorCoordinateMap K b a + tensorCoordinateMap K b a' := by
  simp [tensorCoordinateMap, TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem g66n_T_smul (c : K) (a : Fin n → A) :
    tensorCoordinateMap K b (c • a) = c • tensorCoordinateMap K b a := by
  simp [tensorCoordinateMap, TensorProduct.tmul_smul, Finset.smul_sum]

theorem g66n_TΦ (x : F ⊗[K] A) : tensorCoordinateMap K b (g66n_Φ b x) = x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    have : g66n_Φ (A := A) b 0 = 0 := map_zero _
    rw [this]; simp [tensorCoordinateMap]
  | tmul f a =>
    rw [g66n_Φ_tmul]
    simp only [tensorCoordinateMap]
    have : ∀ k, b k ⊗ₜ[K] (b.repr f k • a) = (b.repr f k • b k) ⊗ₜ[K] a := fun k =>
      (TensorProduct.smul_tmul _ _ _).symm
    simp_rw [this, ← TensorProduct.sum_tmul]
    rw [b.sum_repr]
  | add x y hx hy =>
    rw [map_add, g66n_T_add, hx, hy]

/-- Left-regular representation in coordinates. -/
noncomputable def g66n_ρ (x : F ⊗[K] A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun k i => ∑ j, b.repr (b j * b i) k • g66n_Φ b x j

theorem g66n_L (x : F ⊗[K] A) (a : Fin n → A) :
    g66n_Φ b (x * tensorCoordinateMap K b a) = Matrix.mulVec (g66n_ρ b x) a := by
  conv_lhs => rw [← g66n_TΦ b x]
  set c := g66n_Φ b x
  simp only [tensorCoordinateMap, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum,
    g66n_Φ_tmul]
  funext k
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, g66n_ρ, Matrix.of_apply, Finset.sum_mul,
    smul_mul_assoc]
  rw [Finset.sum_comm]

end G66N

section G66N2

variable {K : Type*} [Field K] [TopologicalSpace K] {F : Type*} [Ring F] [Algebra K F]
  {A : Type*} [Ring A] [Algebra K A] {n : ℕ} (b : Module.Basis (Fin n) K F)

theorem g66n_faithful (M M' : Matrix (Fin n) (Fin n) A) (h : ∀ a, M.mulVec a = M'.mulVec a) : M = M' := by
  ext k i
  have := congrFun (h (Pi.single i 1)) k
  simpa [Matrix.mulVec_single_one] using this

theorem g66n_ρ_mul (x y : F ⊗[K] A) : g66n_ρ b (x * y) = g66n_ρ b x * g66n_ρ b y := by
  apply g66n_faithful
  intro a
  calc (g66n_ρ b (x * y)).mulVec a = g66n_Φ b (x * (y * tensorCoordinateMap K b a)) := by
        rw [← g66n_L, mul_assoc]
    _ = g66n_Φ b (x * tensorCoordinateMap K b (g66n_Φ b (y * tensorCoordinateMap K b a))) := by
        rw [g66n_TΦ]
    _ = (g66n_ρ b x * g66n_ρ b y).mulVec a := by
        rw [g66n_L, g66n_L, Matrix.mulVec_mulVec]

theorem g66n_T1 : tensorCoordinateMap K b (g66n_Φ b (1 : F ⊗[K] A)) = 1 := g66n_TΦ b 1

theorem g66n_ρ_one : g66n_ρ b (1 : F ⊗[K] A) = 1 := by
  apply g66n_faithful
  intro a
  rw [← g66n_L, one_mul, g66n_ΦT, Matrix.one_mulVec]

theorem g66n_recover (x : F ⊗[K] A) :
    x = tensorCoordinateMap K b ((g66n_ρ b x).mulVec (g66n_Φ b 1)) := by
  rw [← g66n_L, g66n_T1, mul_one, g66n_TΦ]

theorem g66n_unit (x : F ⊗[K] A) (hx : IsUnit (g66n_ρ b x)) :
    IsUnit x ∧ Ring.inverse x =
      tensorCoordinateMap K b ((Ring.inverse (g66n_ρ b x)).mulVec (g66n_Φ b 1)) := by
  set N := Ring.inverse (g66n_ρ b x)
  set y := tensorCoordinateMap K b (N.mulVec (g66n_Φ b 1))
  have h1 : g66n_ρ b x * N = 1 := Ring.mul_inverse_cancel _ hx
  have h2 : N * g66n_ρ b x = 1 := Ring.inverse_mul_cancel _ hx
  have hxy : x * y = 1 := by
    rw [← g66n_TΦ b (x * y), g66n_L, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, g66n_T1]
  have hρy : g66n_ρ b y = N := by
    have : g66n_ρ b x * g66n_ρ b y = 1 := by rw [← g66n_ρ_mul, hxy, g66n_ρ_one]
    calc g66n_ρ b y = N * (g66n_ρ b x * g66n_ρ b y) := by rw [← mul_assoc, h2, one_mul]
      _ = N := by rw [this, mul_one]
  have hyx : y * x = 1 := by
    have : g66n_ρ b (y * x) = g66n_ρ b 1 := by rw [g66n_ρ_mul, hρy, h2, g66n_ρ_one]
    calc y * x = tensorCoordinateMap K b ((g66n_ρ b (y * x)).mulVec (g66n_Φ b 1)) := g66n_recover b _
      _ = tensorCoordinateMap K b ((g66n_ρ b 1).mulVec (g66n_Φ b 1)) := by rw [this]
      _ = 1 := (g66n_recover b 1).symm
  have hu : IsUnit x := ⟨⟨x, y, hxy, hyx⟩, rfl⟩
  refine ⟨hu, ?_⟩
  have : x = ((⟨x, y, hxy, hyx⟩ : (F ⊗[K] A)ˣ) : F ⊗[K] A) := rfl
  conv_lhs => rw [this, Ring.inverse_unit]
  rfl

end G66N2

section G66N3

variable {K : Type*} [Field K] [TopologicalSpace K] {F : Type*} [Ring F] [Algebra K F]
  {A : Type*} [Ring A] [Algebra K A] [TopologicalSpace A] {n : ℕ} (b : Module.Basis (Fin n) K F)

theorem g66n_contΦ :
    Continuous[finiteTensorAlgebraTopology K A b, _] (g66n_Φ (A := A) b) := by
  apply continuous_coinduced_dom.2
  have : (⇑(g66n_Φ (A := A) b) ∘ tensorCoordinateMap K b) = id := funext (g66n_ΦT b)
  rw [this]; exact continuous_id

theorem g66n_cia (hA : continuousInverseAlgebra K A) :
    @continuousInverseAlgebra K _ _ (F ⊗[K] A) _ _ (finiteTensorAlgebraTopology K A b) := by
  obtain ⟨hT2, hTR, hSM, hU, hI⟩ := hA
  haveI := hT2; haveI := hTR; haveI := hSM
  letI τ : TopologicalSpace (F ⊗[K] A) := finiteTensorAlgebraTopology K A b
  have cT : Continuous (tensorCoordinateMap K b : (Fin n → A) → F ⊗[K] A) := continuous_coinduced_rng
  have cΦ : Continuous (g66n_Φ (A := A) b) := g66n_contΦ b
  let H : (Fin n → A) ≃ₜ F ⊗[K] A :=
    { toFun := tensorCoordinateMap K b
      invFun := g66n_Φ b
      left_inv := g66n_ΦT b
      right_inv := g66n_TΦ b
      continuous_toFun := cT
      continuous_invFun := cΦ }
  have hT2' : T2Space (F ⊗[K] A) := H.symm.isEmbedding.t2Space
  have cρ : Continuous (g66n_ρ (A := A) b) := by
    refine continuous_pi fun k => continuous_pi fun i => ?_
    simp only [g66n_ρ, Matrix.of_apply]
    exact continuous_finset_sum _ fun j _ => continuous_const.smul ((continuous_apply j).comp cΦ)
  have eadd : ∀ x y : F ⊗[K] A, x + y = tensorCoordinateMap K b (g66n_Φ b x + g66n_Φ b y) := by
    intro x y; rw [g66n_T_add, g66n_TΦ, g66n_TΦ]
  have esmul : ∀ (c : K) (x : F ⊗[K] A), c • x = tensorCoordinateMap K b (c • g66n_Φ b x) := by
    intro c x; rw [g66n_T_smul, g66n_TΦ]
  have eneg : ∀ x : F ⊗[K] A, -x = tensorCoordinateMap K b ((-1 : K) • g66n_Φ b x) := by
    intro x; rw [← esmul]; simp
  have emul : ∀ x y : F ⊗[K] A, x * y = tensorCoordinateMap K b ((g66n_ρ b x).mulVec (g66n_Φ b y)) := by
    intro x y
    rw [← g66n_L, g66n_TΦ, g66n_TΦ]
  have hadd : ContinuousAdd (F ⊗[K] A) := ⟨by
    simp_rw [eadd]
    exact cT.comp ((cΦ.comp continuous_fst).add (cΦ.comp continuous_snd))⟩
  have hneg : ContinuousNeg (F ⊗[K] A) := ⟨by
    simp_rw [eneg]
    exact cT.comp ((continuous_const_smul (-1 : K)).comp cΦ)⟩
  have hmul : ContinuousMul (F ⊗[K] A) := ⟨by
    simp_rw [emul]
    exact cT.comp ((cρ.comp continuous_fst).matrix_mulVec (cΦ.comp continuous_snd))⟩
  have hring : IsTopologicalRing (F ⊗[K] A) := {}
  have hsmul : ContinuousSMul K (F ⊗[K] A) := ⟨by
    simp_rw [esmul]
    exact cT.comp (continuous_fst.smul (cΦ.comp continuous_snd))⟩
  have hloc : G66MLoc (F ⊗[K] A) := by
    obtain ⟨⟨NM, hNM, hNMu⟩, hinvM⟩ := g66m_fin (K := K) (g66m_of_cia (K := K) ⟨hT2, hTR, hSM, hU, hI⟩) n
    have hN : g66n_ρ b ⁻¹' NM ∈ 𝓝 (1 : F ⊗[K] A) :=
      cρ.continuousAt.preimage_mem_nhds (by rw [g66n_ρ_one]; exact hNM)
    refine ⟨⟨_, hN, fun x hx => (g66n_unit b x (hNMu hx)).1⟩, ?_⟩
    have hc : ContinuousAt (fun x : F ⊗[K] A =>
        tensorCoordinateMap K b ((Ring.inverse (g66n_ρ b x)).mulVec (g66n_Φ b 1))) 1 := by
      have h1 : ContinuousAt (fun x : F ⊗[K] A => Ring.inverse (g66n_ρ b x)) 1 :=
        ContinuousAt.comp_of_eq hinvM cρ.continuousAt (g66n_ρ_one b)
      have h2 : Continuous fun p : Matrix (Fin n) (Fin n) A × (Fin n → A) => p.1.mulVec p.2 :=
        continuous_fst.matrix_mulVec continuous_snd
      exact cT.continuousAt.comp (h2.continuousAt.comp (h1.prodMk continuousAt_const))
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    exact (g66n_unit b x (hNMu hx)).2
  obtain ⟨h1, h2⟩ := g66m_glob hloc
  exact ⟨hT2', hring, hsmul, h1, h2⟩

end G66N3

theorem g66n_coord {K : Type*} [Field K] [TopologicalSpace K] {F : Type*} [Ring F] [Algebra K F]
    {A : Type*} [Ring A] [Algebra K A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul K A]
    {n m : ℕ} (b : Module.Basis (Fin n) K F) (c : Module.Basis (Fin m) K F) :
    finiteTensorAlgebraTopology K A b ≤ finiteTensorAlgebraTopology K A c := by
  show TopologicalSpace.coinduced (tensorCoordinateMap K b) inferInstance ≤ _
  rw [← continuous_iff_coinduced_le]
  letI : TopologicalSpace (F ⊗[K] A) := finiteTensorAlgebraTopology K A c
  have e : (tensorCoordinateMap K b : (Fin n → A) → F ⊗[K] A) =
      fun a => tensorCoordinateMap K c (fun k => ∑ i, c.repr (b i) k • a i) := by
    funext a
    rw [← g66n_TΦ c (tensorCoordinateMap K b a)]
    congr 1
    funext k
    simp only [tensorCoordinateMap, map_sum, g66n_Φ_tmul, Finset.sum_apply]
  rw [e]
  have hφ : Continuous (fun a : Fin n → A => fun k : Fin m => ∑ i, c.repr (b i) k • a i) := by
    refine continuous_pi fun k => ?_
    exact continuous_finset_sum _ fun i _ => continuous_const.smul (continuous_apply i)
  exact (show Continuous (tensorCoordinateMap K c : (Fin m → A) → F ⊗[K] A) from
    continuous_coinduced_rng).comp hφ

/-- Corollary 2.8, PDF pp.19–20: scalar extension of a CIA along a finite
field extension is a CIA over the extension field, with the canonical topology on
that field and the finite-tensor topology on the scalar extension algebra. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A]
    (hA : continuousInverseAlgebra K A)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : TopologicalSpace L := canonicalFiniteVectorTopology K L
    letI : TopologicalSpace (L ⊗[K] A) :=
      finiteTensorAlgebraTopology K A (Module.finBasis K L)
    continuousInverseAlgebra L (L ⊗[K] A) := by
  have hA' := hA
  obtain ⟨hT2, hTR, hSM, hU, hI⟩ := hA'
  haveI := hTR; haveI := hSM
  letI τL : TopologicalSpace L := canonicalFiniteVectorTopology K L
  set b := Module.finBasis K L with hb
  letI τ : TopologicalSpace (L ⊗[K] A) := finiteTensorAlgebraTopology K A b
  obtain ⟨h1, h2, _, h4, h5⟩ := g66n_cia (A := A) b hA
  refine ⟨h1, h2, ?_, h4, h5⟩
  have cT : Continuous (tensorCoordinateMap K b : (Fin _ → A) → L ⊗[K] A) := continuous_coinduced_rng
  have cΦ : Continuous (g66n_Φ (A := A) b) := g66n_contΦ b
  have hcoord : ∀ p, Continuous fun l : L => b.equivFun l p := by
    intro p
    exact (continuous_apply p).comp (continuous_induced_dom (t := inferInstance))
  have hrepr : ∀ i k, Continuous fun l : L => b.repr (l * b i) k := by
    intro i k
    have e : (fun l : L => b.repr (l * b i) k) = fun l => ∑ p, b.equivFun l p * b.repr (b p * b i) k := by
      funext l
      have : l * b i = ∑ p, b.repr l p • (b p * b i) := by
        conv_lhs => rw [← b.sum_repr l]
        rw [Finset.sum_mul]
        simp [smul_mul_assoc]
      rw [this, map_sum]
      simp [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul]
    rw [e]
    exact continuous_finset_sum _ fun p _ => (hcoord p).mul continuous_const
  have esmul : ∀ (l : L) (x : L ⊗[K] A), l • x =
      tensorCoordinateMap K b (fun k => ∑ i, b.repr (l * b i) k • g66n_Φ b x i) := by
    intro l x
    conv_lhs => rw [← g66n_TΦ b x]
    rw [← g66n_TΦ b (l • tensorCoordinateMap K b (g66n_Φ b x))]
    congr 1
    simp only [tensorCoordinateMap, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, map_sum,
      g66n_Φ_tmul]
    funext k
    simp [Finset.sum_apply]
  refine ⟨?_⟩
  simp_rw [esmul]
  refine cT.comp (continuous_pi fun k => ?_)
  exact continuous_finset_sum _ fun i _ =>
    ((hrepr i k).comp continuous_fst).smul ((continuous_apply i).comp (cΦ.comp continuous_snd))

