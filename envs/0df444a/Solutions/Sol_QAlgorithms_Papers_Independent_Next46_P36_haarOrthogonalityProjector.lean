-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P36.haarOrthogonalityProjector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:20:09.665413+00:00
-- url     : https://prove2.me/submissions/711295bb-1adc-461a-b21c-4acbb8d471e6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36
noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem g62i_schur_zero (A B : BasedIrrep G) (hne : ¬ BasedIrrepEquivalent A B)
    (T : Matrix (Fin A.dim) (Fin B.dim) ℂ) (hT : ∀ g, A.matrix g * T = T * B.matrix g) : T = 0 := by
  by_contra hT0
  have hker := B.irreducible (LinearMap.ker (Matrix.toLin' T)) (by
    intro g v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero])
  have hran := A.irreducible (LinearMap.range (Matrix.toLin' T)) (by
    intro g v hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨(B.matrix g).mulVec w, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hT g,
      ← Matrix.mulVec_mulVec])
  have hker' : LinearMap.ker (Matrix.toLin' T) = ⊥ := by
    rcases hker with h | h
    · exact h
    · exfalso; apply hT0
      have : Matrix.toLin' T = 0 := LinearMap.ker_eq_top.1 h
      exact Matrix.toLin'.injective (by rw [this, map_zero])
  have hran' : LinearMap.range (Matrix.toLin' T) = ⊤ := by
    rcases hran with h | h
    · exfalso; apply hT0
      have : Matrix.toLin' T = 0 := LinearMap.range_eq_bot.1 h
      exact Matrix.toLin'.injective (by rw [this, map_zero])
    · exact h
  let e := LinearEquiv.ofBijective (Matrix.toLin' T)
    ⟨LinearMap.ker_eq_bot.1 hker', LinearMap.range_eq_top.1 hran'⟩
  let S : Matrix (Fin B.dim) (Fin A.dim) ℂ := LinearMap.toMatrix' (e.symm : (Fin A.dim → ℂ) →ₗ[ℂ] _)
  apply hne
  refine ⟨T, S, ?_, ?_, hT⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact LinearMap.ext fun v => e.apply_symm_apply v
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact LinearMap.ext fun v => e.symm_apply_apply v

theorem g62i_schur_scalar (A : BasedIrrep G)
    (T : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hT : ∀ g, A.matrix g * T = T * A.matrix g) :
    ∃ c : ℂ, T = c • 1 := by
  have : Nonempty (Fin A.dim) := ⟨⟨0, A.positive⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hinv := A.irreducible (LinearMap.ker (Matrix.toLin' (T - c • 1))) (by
    intro g w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    have e1 : (T - c • 1) * A.matrix g = A.matrix g * (T - c • 1) := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, ← hT g, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero])
  rcases hinv with h | h
  · exfalso
    have hv1 : v ∈ LinearMap.ker (Matrix.toLin' (T - c • 1)) := by
      rw [LinearMap.mem_ker, map_sub, LinearMap.sub_apply, hv.apply_eq_smul, map_smul,
        Matrix.toLin'_one]
      simp
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · have : Matrix.toLin' (T - c • 1) = 0 := LinearMap.ker_eq_top.1 h
    have h2 : T - c • 1 = 0 := Matrix.toLin'.injective (by rw [this, map_zero])
    exact sub_eq_zero.1 h2

theorem g62i_inv (B : BasedIrrep G) (h : G) : B.matrix h⁻¹ = (B.matrix h)ᴴ := by
  have h1 : B.matrix h⁻¹ * B.matrix h = 1 := by rw [← B.mul, inv_mul_cancel, B.one]
  calc B.matrix h⁻¹ = B.matrix h⁻¹ * (B.matrix h * (B.matrix h)ᴴ) := by rw [(B.unitary h).2, Matrix.mul_one]
    _ = (B.matrix h)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

def g62i_avg [MeasurableSpace G] (A B : BasedIrrep G) (dg : Measure G)
    (X : Matrix (Fin A.dim) (Fin B.dim) ℂ) : Matrix (Fin A.dim) (Fin B.dim) ℂ :=
  Matrix.of fun i k => ∫ g, (A.matrix g * X * (B.matrix g)ᴴ) i k ∂dg

theorem g62i_integrable [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (dg : Measure G) [IsFiniteMeasure dg] (f : G → ℂ) (hf : Continuous f) : Integrable f dg :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g62i_cont (A B : BasedIrrep G) (X : Matrix (Fin A.dim) (Fin B.dim) ℂ) (φ : G → G)
    (hφ : Continuous φ) (i k) :
    Continuous fun g => (A.matrix g * X * (B.matrix (φ g))ᴴ) i k := by
  have hA := A.continuous
  have hB := B.continuous.comp hφ
  exact (((hA.matrix_mul continuous_const).matrix_mul hB.matrix_conjTranspose).matrix_elem i k)

theorem g62i_intertwine [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A B : BasedIrrep G) (X : Matrix (Fin A.dim) (Fin B.dim) ℂ) (h : G) :
    A.matrix h * g62i_avg A B dg X = g62i_avg A B dg X * B.matrix h := by
  ext i k
  have hint : ∀ φ : G → G, Continuous φ → ∀ i k,
      Integrable (fun g => (A.matrix g * X * (B.matrix (φ g))ᴴ) i k) dg :=
    fun φ hφ i k => g62i_integrable dg _ (g62i_cont A B X φ hφ i k)
  have hint0 := hint id continuous_id
  simp only [id] at hint0
  simp only [Matrix.mul_apply, g62i_avg, Matrix.of_apply]
  calc (∑ a, A.matrix h i a * ∫ g, (A.matrix g * X * (B.matrix g)ᴴ) a k ∂dg)
      = ∫ g, ∑ a, A.matrix h i a * (A.matrix g * X * (B.matrix g)ᴴ) a k ∂dg := by
        rw [integral_finsetSum _ (fun a _ => (hint0 a k).const_mul _)]
        simp only [integral_const_mul]
    _ = ∫ g, (A.matrix (h * g) * X * (B.matrix g)ᴴ) i k ∂dg := by
        congr 1; funext g
        rw [A.mul, show A.matrix h * A.matrix g * X * (B.matrix g)ᴴ =
          A.matrix h * (A.matrix g * X * (B.matrix g)ᴴ) by simp only [Matrix.mul_assoc],
          Matrix.mul_apply]
    _ = ∫ g, (A.matrix g * X * (B.matrix (h⁻¹ * g))ᴴ) i k ∂dg := by
        have := integral_mul_left_eq_self (μ := dg)
          (fun g => (A.matrix g * X * (B.matrix (h⁻¹ * g))ᴴ) i k) h
        simp only [inv_mul_cancel_left] at this
        exact this
    _ = ∫ g, ∑ c, (A.matrix g * X * (B.matrix g)ᴴ) i c * B.matrix h c k ∂dg := by
        congr 1; funext g
        rw [B.mul, Matrix.conjTranspose_mul, g62i_inv, Matrix.conjTranspose_conjTranspose,
          ← Matrix.mul_apply, Matrix.mul_assoc (A.matrix g * X)]
    _ = ∑ c, (∫ g, (A.matrix g * X * (B.matrix g)ᴴ) i c ∂dg) * B.matrix h c k := by
        rw [integral_finsetSum _ (fun c _ => (hint0 i c).mul_const _)]
        simp only [integral_mul_const]

theorem g62i_single_entry (A B : BasedIrrep G) (g : G) (j : Fin A.dim) (l : Fin B.dim) (i k) :
    (A.matrix g * Matrix.single j l (1 : ℂ) * (B.matrix g)ᴴ) i k =
      A.matrix g i j * conj (B.matrix g k l) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem g62i_int_entry [MeasurableSpace G] (dg : Measure G) {n : Type*} [Fintype n] [DecidableEq n]
    (F : G → Matrix n n ℂ) (hF : Integrable F dg) (a b : n) :
    (∫ g, F g ∂dg) a b = ∫ g, F g a b ∂dg := by
  let L0 : Matrix n n ℂ →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ a b
  let L : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L0
  have := L.integral_comp_comm hF
  exact this.symm

theorem g62i_kron_cont [MeasurableSpace G] (A B : BasedIrrep G) :
    Continuous fun g => A.matrix g ⊗ₖ (B.matrix g).map conj := by
  have hA := A.continuous
  have hB := B.continuous
  have hB' := hB.matrix_map Complex.continuous_conj
  refine continuous_matrix fun p q => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact (hA.matrix_elem _ _).mul (hB'.matrix_elem _ _)

theorem g62i_orth [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A B : BasedIrrep G) (hne : ¬ BasedIrrepEquivalent A B) (i j k l) :
    ∫ g, A.matrix g i j * conj (B.matrix g k l) ∂dg = 0 := by
  have hT := g62i_schur_zero A B hne (g62i_avg A B dg (Matrix.single j l 1))
    (fun h => g62i_intertwine dg A B _ h)
  have := congrFun (congrFun hT i) k
  simpa [g62i_avg, g62i_single_entry] using this

theorem g62i_same [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A : BasedIrrep G) (i j k l) :
    ∫ g, A.matrix g i j * conj (A.matrix g k l) ∂dg =
      (A.dim : ℂ)⁻¹ * ((1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) i k *
        conj ((1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) j l)) := by
  obtain ⟨c, hc⟩ := g62i_schur_scalar A (g62i_avg A A dg (Matrix.single j l 1))
    (fun h => g62i_intertwine dg A A _ h)
  have hint : ∀ a, Integrable (fun g => (A.matrix g * Matrix.single j l (1:ℂ) * (A.matrix g)ᴴ) a a) dg :=
    fun a => g62i_integrable dg _ (g62i_cont A A _ id continuous_id a a)
  have htr : (g62i_avg A A dg (Matrix.single j l 1)).trace = if j = l then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, g62i_avg, Matrix.of_apply]
    rw [← integral_finsetSum _ (fun a _ => hint a)]
    have : ∀ g, (∑ a, (A.matrix g * Matrix.single j l (1:ℂ) * (A.matrix g)ᴴ) a a) =
        if j = l then 1 else 0 := by
      intro g
      have h1 := Matrix.trace_mul_comm (A.matrix g * Matrix.single j l (1:ℂ)) (A.matrix g)ᴴ
      simp only [Matrix.trace, Matrix.diag] at h1
      rw [h1, ← Matrix.mul_assoc, (A.unitary g).1, Matrix.one_mul]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, Ne.symm hb]) (by simp)]
      by_cases h : j = l
      · subst h; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h, Ne.symm h]
    simp only [this, integral_const, probReal_univ, one_smul]
  rw [hc] at htr
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
  have hn : (A.dim : ℂ) ≠ 0 := by exact_mod_cast A.positive.ne'
  have hentry := congrFun (congrFun hc i) k
  simp only [g62i_avg, Matrix.of_apply, g62i_single_entry] at hentry
  rw [hentry]
  have hc' : c = (A.dim : ℂ)⁻¹ * (if j = l then 1 else 0) := by
    rw [← htr]; field_simp
  rw [hc']
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem solution
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∀ s, (∫ g, (D s).matrix g ⊗ₖ ((D s).matrix g).map conj ∂dg) =
      ((D s).dim : ℂ)⁻¹ • QAlgorithms.pureDensity (irrepVectorization (1 : Matrix (Fin (D s).dim) _ ℂ))) ∧
    (∀ s t, s ≠ t → (∫ g, (D s).matrix g ⊗ₖ ((D t).matrix g).map conj ∂dg) = 0) := by
  have hI : ∀ s t, Integrable (fun g => (D s).matrix g ⊗ₖ ((D t).matrix g).map conj) dg :=
    fun s t => (g62i_kron_cont (D s) (D t)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    rw [g62i_int_entry dg _ (hI s s)]
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply]
    rw [g62i_same dg (D s) i j k l]
    simp [QAlgorithms.pureDensity, irrepVectorization]
  · ext ⟨i, k⟩ ⟨j, l⟩
    rw [g62i_int_entry dg _ (hI s t)]
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply]
    rw [g62i_orth dg (D s) (D t) (hD s t hst) i j k l]
    rfl

end
