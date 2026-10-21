-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P29.canonical_right_covariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:34:18.644768+00:00
-- url     : https://prove2.me/submissions/ab807c4c-499e-4f33-8e63-3eec0b1f7a1b

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29
noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

theorem g61d_incl_self {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (q : Fin C.count) : (tokenInclusion C q)ᴴ * tokenInclusion C q = 1 := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tokenInclusion]
  rw [Finset.sum_eq_single ⟨q, b⟩]
  · by_cases h : b = b'
    · subst h; simp
    · rw [Matrix.one_apply_ne h]
      have : ¬ ((⟨q, b⟩ : TokenIndex C) = ⟨q, b'⟩) := by
        intro h'; apply h; exact eq_of_heq (Sigma.mk.inj_iff.1 h').2
      simp [this]
  · intro a _ ha; simp [ha]
  · simp

theorem g61d_incl_ne {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (q q' : Fin C.count) (hq : q ≠ q') : (tokenInclusion C q)ᴴ * tokenInclusion C q' = 0 := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tokenInclusion, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h1 : a = ⟨q, b⟩
  · have : ¬ (a = ⟨q', b'⟩) := by
      intro h2; rw [h1] at h2; exact hq (Sigma.mk.inj_iff.1 h2).1
    simp [this]
  · simp [h1]

/-- block-diagonal products -/
theorem g61d_block_mul {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (A B : (q : Fin C.count) → Matrix (Fin (C.dim q) × Fin (C.dim q)) (Fin (C.dim q) × Fin (C.dim q)) ℂ) :
    (∑ q, tokenInclusion C q * A q * (tokenInclusion C q)ᴴ) *
      (∑ q, tokenInclusion C q * B q * (tokenInclusion C q)ᴴ) =
      ∑ q, tokenInclusion C q * (A q * B q) * (tokenInclusion C q)ᴴ := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_eq_single q]
  · have e : tokenInclusion C q * A q * (tokenInclusion C q)ᴴ * (tokenInclusion C q * B q * (tokenInclusion C q)ᴴ)
        = tokenInclusion C q * A q * ((tokenInclusion C q)ᴴ * tokenInclusion C q) * B q * (tokenInclusion C q)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, g61d_incl_self, Matrix.mul_one, Matrix.mul_assoc (tokenInclusion C q) (A q)]
  · intro q' _ hq'
    have e : tokenInclusion C q * A q * (tokenInclusion C q)ᴴ * (tokenInclusion C q' * B q' * (tokenInclusion C q')ᴴ)
        = tokenInclusion C q * A q * ((tokenInclusion C q)ᴴ * tokenInclusion C q') * B q' * (tokenInclusion C q')ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, g61d_incl_ne C q q' (Ne.symm hq')]
    simp
  · simp

theorem g61d_left_right {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (g h : G) :
    tokenLeft C g * tokenRight C h = tokenRight C h * tokenLeft C g := by
  unfold tokenLeft tokenRight
  rw [g61d_block_mul, g61d_block_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 2
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.kroneckerMap_apply]
  simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem g61d_rep_mul_inv {G : Type*} [Group G] [TopologicalSpace G] {d : ℕ}
    (U : BasedUnitaryRep G d) (g h : G) :
    repMatrix U (g * h⁻¹) = repMatrix U g * star (repMatrix U h) := by
  simp only [repMatrix, map_mul, map_inv]
  rfl

theorem g61d_inclH_psi {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (q : Fin C.count) (i j : Fin (C.dim q)) :
    ((tokenInclusion C q)ᴴ.mulVec (WithLp.ofLp (canonicalKet C))) (i, j) =
      if i = j then (Real.sqrt ((C.dim q : ℝ) / tokenDimension C) : ℂ) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, tokenInclusion, canonicalKet]
  rw [Finset.sum_eq_single ⟨q, (i, j)⟩]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem g61d_key {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (q : Fin C.count) (g h : G) :
    ((((1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ).kronecker
      (fun a b => conj (repMatrix (C.rep q) h a b))) *
      ((repMatrix (C.rep q) g).kronecker (1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ))).mulVec
      ((tokenInclusion C q)ᴴ.mulVec (WithLp.ofLp (canonicalKet C)))) =
    ((repMatrix (C.rep q) (g * h⁻¹)).kronecker (1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ)).mulVec
      ((tokenInclusion C q)ᴴ.mulVec (WithLp.ofLp (canonicalKet C))) := by
  have hv : (tokenInclusion C q)ᴴ.mulVec (WithLp.ofLp (canonicalKet C)) =
      fun p => if p.1 = p.2 then (Real.sqrt ((C.dim q : ℝ) / tokenDimension C) : ℂ) else 0 := by
    funext ⟨i, j⟩; exact g61d_inclH_psi C q i j
  rw [hv, ← Matrix.mulVec_mulVec]
  set c := (Real.sqrt ((C.dim q : ℝ) / tokenDimension C) : ℂ)
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap, Matrix.of_apply, g61d_rep_mul_inv]
  simp only [Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [Matrix.mul_apply, Finset.sum_mul, Matrix.star_apply]
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem g61d_orbit {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (g h : G) :
    act (tokenRight C h) (tokenOrbit C g) = tokenOrbit C (g * h⁻¹) := by
  unfold tokenOrbit act
  rw [WithLp.ofLp_toLp]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Matrix.mulVec_mulVec]
  unfold tokenLeft tokenRight
  rw [g61d_block_mul, Matrix.sum_mulVec, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hsplit : ∀ M : Matrix (Fin (C.dim q) × Fin (C.dim q)) (Fin (C.dim q) × Fin (C.dim q)) ℂ,
      (tokenInclusion C q * M * (tokenInclusion C q)ᴴ).mulVec (WithLp.ofLp (canonicalKet C)) =
      (tokenInclusion C q).mulVec (M.mulVec ((tokenInclusion C q)ᴴ.mulVec (WithLp.ofLp (canonicalKet C)))) := by
    intro M; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hsplit, hsplit, g61d_key]

theorem g61d_incl_sum {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) :
    ∑ q, tokenInclusion C q * (tokenInclusion C q)ᴴ = 1 := by
  ext a a'
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tokenInclusion]
  obtain ⟨q0, b0⟩ := a
  rw [Finset.sum_eq_single q0]
  · rw [Finset.sum_eq_single b0]
    · by_cases h : (⟨q0, b0⟩ : TokenIndex C) = a'
      · subst h; simp
      · rw [Matrix.one_apply_ne h]; simp [Ne.symm h]
    · intro b _ hb
      have : ¬ ((⟨q0, b0⟩ : TokenIndex C) = ⟨q0, b⟩) := by
        intro h'; apply hb; exact (eq_of_heq (Sigma.mk.inj_iff.1 h').2).symm
      simp [this]
    · simp
  · intro q _ hq
    apply Finset.sum_eq_zero
    intro b _
    have : ¬ ((⟨q0, b0⟩ : TokenIndex C) = ⟨q, b⟩) := by
      intro h'; exact hq (Sigma.mk.inj_iff.1 h').1.symm
    simp [this]
  · simp

theorem g61d_right_unitary {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (h : G) :
    (tokenRight C h)ᴴ * tokenRight C h = 1 := by
  have hT : (tokenRight C h)ᴴ = ∑ q, tokenInclusion C q *
      ((1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ).kronecker
        (fun a b => conj (repMatrix (C.rep q) h a b)))ᴴ * (tokenInclusion C q)ᴴ := by
    unfold tokenRight
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hT]
  unfold tokenRight
  rw [g61d_block_mul]
  rw [← g61d_incl_sum C]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hu : star (repMatrix (C.rep q) h) * repMatrix (C.rep q) h = 1 := by
    have := ((C.rep q).hom h).2
    exact (Matrix.mem_unitaryGroup_iff').1 this
  have hB : ((1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ).kronecker
        (fun a b => conj (repMatrix (C.rep q) h a b)))ᴴ *
      ((1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ).kronecker
        (fun a b => conj (repMatrix (C.rep q) h a b))) = 1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.of_apply]
    have hjl := congrFun (congrFun hu l) j
    simp only [Matrix.mul_apply, Matrix.star_apply] at hjl
    simp [Matrix.one_apply]
    by_cases hik : k = i
    · subst hik
      simp only [if_true, RingHomCompTriple.comp_apply, RingHom.id_apply, true_and]
      have e : ∑ x, repMatrix (C.rep q) h x j * (starRingEnd ℂ) (repMatrix (C.rep q) h x l) =
          (1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ) l j := by
        rw [← hjl]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [RCLike.star_def]; ring
      try simp only [Complex.conj_conj]
      rw [e, Matrix.one_apply]
      by_cases hjl' : j = l
      · subst hjl'; simp
      · simp [hjl', Ne.symm hjl']
    · have : ¬ i = k := fun h' => hik h'.symm
      simp [hik, this]
  rw [hB, Matrix.mul_one]

theorem g61d_W_unitary {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (s : ℕ) (h : G) :
    ((tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ *
      (tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    g61d_right_unitary, Matrix.mul_one, Matrix.one_kronecker_one]

theorem g61d_WK {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) {s : ℕ}
    (U : BasedUnitaryRep G s) (g h : G) :
    (tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ) * orbitKraus C U g =
      orbitKraus C U (g * h⁻¹) * repMatrix U h := by
  have hU : repMatrix U (g * h⁻¹) * repMatrix U h = repMatrix U g := by
    simp only [repMatrix, ← Submonoid.coe_mul, ← map_mul, inv_mul_cancel_right]
  ext ⟨a, i⟩ b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, orbitKraus]
  rw [← g61d_orbit C g h]
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [← hU]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring

section GeneralResults

variable {G : Type*} [Group G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hCompact : CompactSpace G] [hT2 : T2Space G] [MeasurableSpace G] [hBorel : BorelSpace G]
  (mu : Measure G) [hHaar : Measure.IsHaarMeasure mu] [hProb : IsProbabilityMeasure mu]

include hTop hCompact hT2 hBorel hHaar hProb

theorem solution (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s) :
    (∀ g h, tokenLeft C g * tokenRight C h = tokenRight C h * tokenLeft C g) ∧
    (∀ g h, act (tokenRight C h) (tokenOrbit C g) = tokenOrbit C (g * h⁻¹)) ∧
    (∀ h rho, IsDensityMatrix rho →
      conjSuperop ((tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ))
        (canonicalEncoding mu C U rho) = canonicalEncoding mu C U (conjSuperop (repMatrix U h) rho)) := by
  refine ⟨g61d_left_right C, g61d_orbit C, ?_⟩
  intro h rho _
  -- right invariance of the Haar probability measure
  haveI hRI : mu.IsMulRightInvariant := ⟨fun g => by
    haveI : IsProbabilityMeasure (Measure.map (· * g) mu) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  set W := (tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ) with hWdef
  have hWW : Wᴴ * W = 1 := g61d_W_unitary C s h
  have hWW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hWW
  let Lin : Matrix (TokenIndex C × Fin s) (TokenIndex C × Fin s) ℂ ≃ₗ[ℂ]
      Matrix (TokenIndex C × Fin s) (TokenIndex C × Fin s) ℂ :=
    { toFun := fun X => W * X * Wᴴ
      invFun := fun X => Wᴴ * X * W
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp
      left_inv := fun X => by
        simp only
        rw [show Wᴴ * (W * X * Wᴴ) * W = (Wᴴ * W) * X * (Wᴴ * W) by simp only [Matrix.mul_assoc],
          hWW, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun X => by
        simp only
        rw [show W * (Wᴴ * X * W) * Wᴴ = (W * Wᴴ) * X * (W * Wᴴ) by simp only [Matrix.mul_assoc],
          hWW', Matrix.one_mul, Matrix.mul_one] }
  let L := Lin.toContinuousLinearEquiv
  have hL : ∀ X, L X = W * X * Wᴴ := fun X => rfl
  unfold canonicalEncoding conjSuperop
  rw [← hL, ← ContinuousLinearEquiv.integral_comp_comm]
  simp only [hL]
  have hpt : ∀ g, W * (orbitKraus C U g * rho * (orbitKraus C U g)ᴴ) * Wᴴ =
      orbitKraus C U (g * h⁻¹) * (repMatrix U h * rho * (repMatrix U h)ᴴ) *
        (orbitKraus C U (g * h⁻¹))ᴴ := by
    intro g
    have e := g61d_WK C U g h
    rw [← hWdef] at e
    calc W * (orbitKraus C U g * rho * (orbitKraus C U g)ᴴ) * Wᴴ
        = (W * orbitKraus C U g) * rho * (W * orbitKraus C U g)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [e, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  simp_rw [hpt]
  exact integral_mul_right_eq_self
    (fun x => orbitKraus C U x * (repMatrix U h * rho * (repMatrix U h)ᴴ) * (orbitKraus C U x)ᴴ) h⁻¹

end GeneralResults
