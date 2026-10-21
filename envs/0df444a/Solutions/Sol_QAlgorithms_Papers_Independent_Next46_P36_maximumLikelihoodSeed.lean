-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P36.maximumLikelihoodSeed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T21:12:29.809826+00:00
-- url     : https://prove2.me/submissions/f79db4ad-a67c-447e-a35a-50e08e32ed1c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

theorem g63b_bd_entry {S : Type*} [Fintype S] [DecidableEq S] {n : S → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
    (M N : ∀ s, Matrix (n s) (n s) ℂ) (X : Matrix (Σ s, n s) (Σ s, n s) ℂ) (s t : S)
    (p : n s) (q : n t) :
    (Matrix.blockDiagonal' M * X * Matrix.blockDiagonal' N) ⟨s, p⟩ ⟨t, q⟩ =
      ∑ r, ∑ r', M s p r * X ⟨s, r⟩ ⟨t, r'⟩ * N t r' q := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single t]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single s, Finset.sum_mul]
    · simp [Matrix.blockDiagonal'_apply_eq]
    · intro b _ hb
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb)]; simp
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hb]; simp
  · simp

section g63b_sec
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem g63b_U_entry (D : S → BasedIrrep G) (X : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (g : G) (s t : S) (a b : Fin (D s).dim) (a' b' : Fin (D t).dim) :
    (canonicalAction D g * X * (canonicalAction D g)ᴴ) ⟨s, (a, b)⟩ ⟨t, (a', b')⟩ =
      ∑ c, ∑ c', (D s).matrix g a c * conj ((D t).matrix g a' c') * X ⟨s, (c, b)⟩ ⟨t, (c', b')⟩ := by
  unfold canonicalAction
  rw [Matrix.blockDiagonal'_conjTranspose, g63b_bd_entry]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring

def g63b_conjIrrep (B : BasedIrrep G) (W : Matrix.unitaryGroup (Fin B.dim) ℂ) : BasedIrrep G where
  dim := B.dim
  positive := B.positive
  matrix g := (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * B.matrix g * W
  one := by
    rw [B.one, Matrix.mul_one]; exact by have := Matrix.mem_unitaryGroup_iff'.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
  mul g h := by
    have hW2 : (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ = 1 := by have := Matrix.mem_unitaryGroup_iff.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
    rw [B.mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ, hW2, Matrix.one_mul]
  unitary g := by
    have hW1 : (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) = 1 := by have := Matrix.mem_unitaryGroup_iff'.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hW2 : (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ = 1 := by have := Matrix.mem_unitaryGroup_iff.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    constructor
    · rw [← Matrix.mul_assoc (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ, hW2, Matrix.one_mul,
        ← Matrix.mul_assoc (B.matrix g)ᴴ, (B.unitary g).1, Matrix.one_mul, hW1]
    · rw [← Matrix.mul_assoc (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ, hW2, Matrix.one_mul,
        ← Matrix.mul_assoc (B.matrix g), (B.unitary g).2, Matrix.one_mul, hW1]
  continuous := (continuous_const.matrix_mul B.continuous).matrix_mul continuous_const
  irreducible V hV := by
    have hW1 : (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) = 1 := by have := Matrix.mem_unitaryGroup_iff'.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hW2 : (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ = 1 := by have := Matrix.mem_unitaryGroup_iff.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hinj : ∀ u v : Fin B.dim → ℂ, (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) *ᵥ u = (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) *ᵥ v → u = v := by
      intro u v h
      have := congrArg (fun x => (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ *ᵥ x) h
      simpa only [Matrix.mulVec_mulVec, hW1, Matrix.one_mulVec] using this
    have hB := B.irreducible (V.map (Matrix.toLin' (W : Matrix (Fin B.dim) (Fin B.dim) ℂ))) (by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      refine ⟨_, hV g u hu, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      congr 1
      simp only [← Matrix.mul_assoc, hW2, Matrix.one_mul])
    rcases hB with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have : Matrix.toLin' (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) v ∈ V.map (Matrix.toLin' (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)) :=
        Submodule.mem_map_of_mem hv
      rw [h, Submodule.mem_bot, Matrix.toLin'_apply] at this
      rw [Submodule.mem_bot]
      exact hinj v 0 (by rw [this, Matrix.mulVec_zero])
    · right
      rw [eq_top_iff]
      intro u _
      have : Matrix.toLin' (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) u ∈ V.map (Matrix.toLin' (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)) := by
        rw [h]; exact Submodule.mem_top
      obtain ⟨v, hv, hvu⟩ := this
      simp only [Matrix.toLin'_apply] at hvu
      rw [← hinj v u hvu]; exact hv

theorem g63b_conjIrrep_matrix (B : BasedIrrep G) (W : Matrix.unitaryGroup (Fin B.dim) ℂ) (g : G) :
    (g63b_conjIrrep B W).matrix g = (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * B.matrix g * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ) := rfl

theorem g63b_V_entry (D : S → BasedIrrep G) (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ)
    (X : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (g : G) (s t : S) (a b : Fin (D s).dim) (a' b' : Fin (D t).dim) :
    ((rightAction D W g)ᴴ * X * rightAction D W g) ⟨s, (a, b)⟩ ⟨t, (a', b')⟩ =
      ∑ y, ∑ y', ((W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ)ᴴ * (D s).matrix g * (W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ)) y b *
        conj (((W t : Matrix (Fin (D t).dim) (Fin (D t).dim) ℂ)ᴴ * (D t).matrix g * (W t : Matrix (Fin (D t).dim) (Fin (D t).dim) ℂ)) y' b') *
          X ⟨s, (a, y)⟩ ⟨t, (a', y')⟩ := by
  unfold rightAction
  rw [Matrix.blockDiagonal'_conjTranspose, g63b_bd_entry]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, g63b_conjIrrep_matrix]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring

theorem g63b_UV_comm (D : S → BasedIrrep G) (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) (g : G) :
    canonicalAction D g * rightAction D W g = rightAction D W g * canonicalAction D g := by
  unfold canonicalAction rightAction
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1; funext s
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem g63b_VV (D : S → BasedIrrep G) (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) (g : G) :
    (rightAction D W g)ᴴ * rightAction D W g = 1 := by
  unfold rightAction
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1; funext s
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul]
  set M := (W s : Matrix _ _ ℂ)ᴴ * (D s).matrix g * (W s : Matrix _ _ ℂ)
  have hu : Mᴴ * M = 1 := ((g63b_conjIrrep (D s) (W s)).unitary g).1
  have h1 : (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_kronecker_one]
  rfl

theorem g63b_UU (D : S → BasedIrrep G) (g : G) :
    canonicalAction D g * (canonicalAction D g)ᴴ = 1 := by
  unfold canonicalAction
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1; funext s
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul, ((D s).unitary g).2, Matrix.one_kronecker_one]
  rfl

theorem g63b_term_int [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (dg : Measure G) [IsFiniteMeasure dg] (A : BasedIrrep G) (i j k l) (z : ℂ) :
    Integrable (fun g => A.matrix g i j * conj (A.matrix g k l) * z) dg :=
  g62i_integrable dg _ (((A.continuous.matrix_elem i j).mul
    (Complex.continuous_conj.comp (A.continuous.matrix_elem k l))).mul continuous_const)

theorem g63b_int1 [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A : BasedIrrep G) (f : Fin A.dim → Fin A.dim → ℂ) (a a' : Fin A.dim) :
    ∫ g, ∑ c, ∑ c', A.matrix g a c * conj (A.matrix g a' c') * f c c' ∂dg =
      (A.dim : ℂ)⁻¹ * ((if a = a' then 1 else 0) * ∑ c, f c c) := by
  rw [integral_finsetSum _ (fun c _ => integrable_finset_sum _ (fun c' _ => g63b_term_int dg A _ _ _ _ _))]
  simp_rw [integral_finsetSum _ (fun c' _ => g63b_term_int dg A _ _ _ _ _), integral_mul_const,
    g62i_same dg A, Matrix.one_apply]
  simp [Finset.mul_sum, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem g63b_int2 [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A : BasedIrrep G) (f : Fin A.dim → Fin A.dim → ℂ) (b b' : Fin A.dim) :
    ∫ g, ∑ y, ∑ y', A.matrix g y b * conj (A.matrix g y' b') * f y y' ∂dg =
      (A.dim : ℂ)⁻¹ * ((if b = b' then 1 else 0) * ∑ y, f y y) := by
  rw [integral_finsetSum _ (fun c _ => integrable_finset_sum _ (fun c' _ => g63b_term_int dg A _ _ _ _ _))]
  simp_rw [integral_finsetSum _ (fun c' _ => g63b_term_int dg A _ _ _ _ _), integral_mul_const,
    g62i_same dg A, Matrix.one_apply]
  simp [Finset.mul_sum, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem g63b_int2c [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (B : BasedIrrep G) (W : Matrix.unitaryGroup (Fin B.dim) ℂ)
    (f : Fin B.dim → Fin B.dim → ℂ) (b b' : Fin B.dim) :
    ∫ g, ∑ y, ∑ y', ((W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * B.matrix g * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)) y b *
      conj (((W : Matrix (Fin B.dim) (Fin B.dim) ℂ)ᴴ * B.matrix g * (W : Matrix (Fin B.dim) (Fin B.dim) ℂ)) y' b') * f y y' ∂dg =
      (B.dim : ℂ)⁻¹ * ((if b = b' then 1 else 0) * ∑ y, f y y) :=
  g63b_int2 dg (g63b_conjIrrep B W) f b b'

end g63b_sec

section g63b_sec3
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem g63b_int_ne [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (A B : BasedIrrep G) (hne : ¬ BasedIrrepEquivalent A B)
    (f : Fin A.dim → Fin B.dim → ℂ) (a : Fin A.dim) (a' : Fin B.dim) :
    ∫ g, ∑ c, ∑ c', A.matrix g a c * conj (B.matrix g a' c') * f c c' ∂dg = 0 := by
  have hI : ∀ c c', Integrable (fun g => A.matrix g a c * conj (B.matrix g a' c') * f c c') dg :=
    fun c c' => g62i_integrable dg _ (((A.continuous.matrix_elem a c).mul
      (Complex.continuous_conj.comp (B.continuous.matrix_elem a' c'))).mul continuous_const)
  rw [integral_finsetSum _ (fun c _ => integrable_finset_sum _ (fun c' _ => hI c c'))]
  simp_rw [integral_finsetSum _ (fun c' _ => hI _ c'), integral_mul_const, g62i_orth dg A B hne]
  simp

theorem g63b_pd_psd {n : Type*} [Fintype n] (a : EuclideanSpace ℂ n) :
    (QAlgorithms.pureDensity a).PosSemidef := by
  have : QAlgorithms.pureDensity a = Matrix.vecMulVec (WithLp.ofLp a) (star (WithLp.ofLp a)) := by
    ext i j; simp [QAlgorithms.pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

theorem g63b_eff {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ) (hU : U * Uᴴ = 1)
    (ψ : EuclideanSpace ℂ n) :
    QAlgorithms.effectProb (QAlgorithms.conjSuperop U X)
      (QAlgorithms.conjSuperop U (QAlgorithms.pureDensity ψ)) =
      (∑ p, ∑ q, conj (ψ p) * X p q * ψ q).re := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  unfold QAlgorithms.effectProb QAlgorithms.conjSuperop
  have : U * X * Uᴴ * (U * QAlgorithms.pureDensity ψ * Uᴴ) = U * (X * QAlgorithms.pureDensity ψ) * Uᴴ := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU', Matrix.one_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem g63b_phase (z : ℂ) : coefficientPhase z * conj (coefficientPhase z) = 1 := by
  unfold coefficientPhase
  split_ifs with h
  · simp
  · rw [map_div₀, Complex.conj_ofReal]
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    field_simp
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem g63b_phase2 (z : ℂ) : conj (coefficientPhase z) * z = (‖z‖ : ℂ) := by
  unfold coefficientPhase
  split_ifs with h
  · simp [h]
  · rw [map_div₀, Complex.conj_ofReal]
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    field_simp
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem g63b_unit_sum {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) (b b' : Fin n) :
    ∑ c, (W : Matrix (Fin n) (Fin n) ℂ) c b * conj ((W : Matrix (Fin n) (Fin n) ℂ) c b') =
      if b = b' then 1 else 0 := by
  have h1 : (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * (W : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 W.2; rwa [Matrix.star_eq_conjTranspose] at this
  have := congrFun (congrFun h1 b') b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  rw [show (if b = b' then (1:ℂ) else 0) = if b' = b then 1 else 0 by simp [eq_comm], ← this]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Complex.star_def, mul_comm]

theorem g63b_unit_normsq {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ x : Fin n × Fin n, ‖(W : Matrix (Fin n) (Fin n) ℂ) x.1 x.2‖ ^ 2 = n := by
  have h : ∀ b, ∑ c, (W : Matrix (Fin n) (Fin n) ℂ) c b * conj ((W : Matrix (Fin n) (Fin n) ℂ) c b) = 1 := by
    intro b; rw [g63b_unit_sum]; simp
  have h2 : ∀ b, ∑ c, ‖(W : Matrix (Fin n) (Fin n) ℂ) c b‖ ^ 2 = (1 : ℝ) := by
    intro b
    have := h b
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [h2]

end g63b_sec3

section g63b_sec4
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem g63b_cont (D : S → BasedIrrep G) (X : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) :
    Continuous fun g => QAlgorithms.conjSuperop (canonicalAction D g) X := by
  refine continuous_matrix fun p q => ?_
  rcases p with ⟨s, a, b⟩
  rcases q with ⟨t, a', b'⟩
  simp only [QAlgorithms.conjSuperop, g63b_U_entry]
  exact continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun c' _ =>
    (((D s).continuous.matrix_elem a c).mul
      (Complex.continuous_conj.comp ((D t).continuous.matrix_elem a' c'))).mul continuous_const

/-- diagonal normalization of a seed: Σ_c Xi(s,c,b)(s,c,b) = d_s -/
theorem g63b_diag_norm [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (D : S → BasedIrrep G) (dg : Measure G) [IsProbabilityMeasure dg] [Measure.IsMulLeftInvariant dg]
    (Xi : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ)
    (hint : Integrable (fun g => QAlgorithms.conjSuperop (canonicalAction D g) Xi) dg)
    (hone : (∫ g, QAlgorithms.conjSuperop (canonicalAction D g) Xi ∂dg) = 1) (s : S) (b : Fin (D s).dim) :
    ∑ c, Xi ⟨s, (c, b)⟩ ⟨s, (c, b)⟩ = (D s).dim := by
  let a0 : Fin (D s).dim := ⟨0, (D s).positive⟩
  have h := congrFun (congrFun hone ⟨s, (a0, b)⟩) ⟨s, (a0, b)⟩
  rw [g62i_int_entry dg _ hint] at h
  simp only [QAlgorithms.conjSuperop, g63b_U_entry] at h
  have hi := g63b_int1 dg (D s) (fun c c' => Xi ⟨s, (c, b)⟩ ⟨s, (c', b)⟩) a0 a0
  simp only at hi
  rw [hi] at h
  have hd : ((D s).dim : ℂ) ≠ 0 := by exact_mod_cast (D s).positive.ne'
  simp only [if_true, one_mul, Matrix.one_apply_eq] at h
  field_simp at h
  exact h

end g63b_sec4

theorem solution
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (c : S → ℂ) (hn : (∑ s, Complex.normSq (c s)) = 1)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) :
    NormalizedSeed D dg (QAlgorithms.pureDensity (likelihoodVector D c W)) ∧
    ∀ Xi, NormalizedSeed D dg Xi → ∀ g,
      QAlgorithms.effectProb (QAlgorithms.conjSuperop (canonicalAction D g) Xi)
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (canonicalInput D c W))) ≤
      QAlgorithms.effectProb
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (likelihoodVector D c W)))
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (canonicalInput D c W))) := by
  have hsqrt : ∀ s, (Real.sqrt (D s).dim : ℂ) ≠ 0 := fun s => by
    have : 0 < Real.sqrt (D s).dim := Real.sqrt_pos.2 (by exact_mod_cast (D s).positive)
    exact_mod_cast this.ne'
  have hsq : ∀ s, (Real.sqrt (D s).dim : ℂ) * (Real.sqrt (D s).dim : ℂ) = (D s).dim := by
    intro s
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  set L := likelihoodVector D c W with hL
  set ψ := canonicalInput D c W with hψ
  have hLe : ∀ s (x : Fin (D s).dim × Fin (D s).dim), L ⟨s, x⟩ =
      (Real.sqrt (D s).dim : ℂ) * coefficientPhase (c s) * (W s : Matrix _ _ ℂ) x.1 x.2 := by
    intro s x; simp [hL, likelihoodVector]
  have hψe : ∀ s (x : Fin (D s).dim × Fin (D s).dim), ψ ⟨s, x⟩ =
      c s / (Real.sqrt (D s).dim : ℂ) * (W s : Matrix _ _ ℂ) x.1 x.2 := by
    intro s x; simp [hψ, canonicalInput]
  constructor
  · -- seed legality
    have hcont := g63b_cont D (QAlgorithms.pureDensity L)
    have hint : Integrable (fun g => QAlgorithms.conjSuperop (canonicalAction D g)
        (QAlgorithms.pureDensity L)) dg :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine ⟨g63b_pd_psd L, hcont, hint, ?_⟩
    ext ⟨s, a, b⟩ ⟨t, a', b'⟩
    rw [g62i_int_entry dg _ hint]
    simp only [QAlgorithms.conjSuperop, g63b_U_entry]
    by_cases hst : s = t
    · subst hst
      have hi := g63b_int1 dg (D s)
        (fun e e' => QAlgorithms.pureDensity L ⟨s, (e, b)⟩ ⟨s, (e', b')⟩) a a'
      try simp only at hi
      rw [hi]
      have hsum : ∑ e, QAlgorithms.pureDensity L ⟨s, (e, b)⟩ ⟨s, (e, b')⟩ =
          (D s).dim * (if b = b' then 1 else 0) := by
        simp only [QAlgorithms.pureDensity, Matrix.of_apply, hLe, map_mul, Complex.conj_ofReal]
        rw [← g63b_unit_sum (W s) b b', Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        have h1 := g63b_phase (c s)
        rw [← hsq s]
        linear_combination ((Real.sqrt (D s).dim : ℂ) * (Real.sqrt (D s).dim : ℂ) *
          (W s : Matrix _ _ ℂ) e b * conj ((W s : Matrix _ _ ℂ) e b')) * h1
      rw [hsum]
      have hd : ((D s).dim : ℂ) ≠ 0 := by exact_mod_cast (D s).positive.ne'
      rw [Matrix.one_apply]
      by_cases hab : a = a' <;> by_cases hbb : b = b' <;> simp [hab, hbb, hd]
    · rw [g63b_int_ne dg (D s) (D t) (hD s t hst)]
      rw [Matrix.one_apply, if_neg]
      intro he; exact hst (congrArg Sigma.fst he)
  · intro Xi hX g
    obtain ⟨hpsd, _, hint, hone⟩ := hX
    have hUU := g63b_UU D g
    rw [g63b_eff _ _ hUU, g63b_eff _ _ hUU]
    -- right-hand side value
    have hw : (∑ q, conj (L q) * ψ q) = ((∑ s, ((D s).dim : ℝ) * ‖c s‖ : ℝ) : ℂ) := by
      rw [Fintype.sum_sigma]; push_cast
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hLe, hψe, map_mul, Complex.conj_ofReal]
      have hW := g63b_unit_normsq (W s)
      have hW' : ∑ x : Fin (D s).dim × Fin (D s).dim,
          conj ((W s : Matrix _ _ ℂ) x.1 x.2) * (W s : Matrix _ _ ℂ) x.1 x.2 = (D s).dim := by
        simp only [Complex.conj_mul']; exact_mod_cast hW
      rw [← hW', Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h2 := g63b_phase2 (c s)
      have e : (Real.sqrt (D s).dim : ℂ) * (c s / (Real.sqrt (D s).dim : ℂ)) = c s := by
        field_simp [hsqrt s]
      linear_combination (conj ((W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) x.1 x.2) *
        (W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) x.1 x.2 * conj (coefficientPhase (c s))) * e +
        conj ((W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) x.1 x.2) *
        (W s : Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) x.1 x.2 * h2
    have hR : (∑ p, ∑ q, conj (ψ p) * QAlgorithms.pureDensity L p q * ψ q) =
        conj (∑ q, conj (L q) * ψ q) * (∑ q, conj (L q) * ψ q) := by
      simp only [QAlgorithms.pureDensity, Matrix.of_apply, map_sum, map_mul, Complex.conj_conj,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hR, hw, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    -- left-hand side
    obtain ⟨B, hB⟩ : ∃ B : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ, Xi = Bᴴ * B := by
      open scoped MatrixOrder in
      obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
      exact ⟨B, hB⟩
    set z : CanonicalIndex D → ℂ := fun k => ∑ q, B k q * ψ q with hz
    have hQ : (∑ p, ∑ q, conj (ψ p) * Xi p q * ψ q) = ((∑ k, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp only [← Complex.conj_mul', hz, hB, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      calc _ = ∑ p, ∑ k, ∑ q, conj (B k p) * conj (ψ p) * (B k q * ψ q) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q _ => ?_
            ring
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    rw [hQ, Complex.ofReal_re]
    -- decomposition of z
    set T : CanonicalIndex D → S → ℂ := fun k s =>
      ∑ x : Fin (D s).dim × Fin (D s).dim, B k ⟨s, x⟩ * (W s : Matrix _ _ ℂ) x.1 x.2 with hT
    have hzT : ∀ k, z k = ∑ s, (c s / (Real.sqrt (D s).dim : ℂ)) * T k s := by
      intro k
      simp only [hz, hT, Fintype.sum_sigma, hψe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
      ring
    -- normalization of B
    have hBn : ∀ s, ∑ k, ∑ x : Fin (D s).dim × Fin (D s).dim, ‖B k ⟨s, x⟩‖ ^ 2 =
        ((D s).dim : ℝ) * (D s).dim := by
      intro s
      have hdiag : ∀ p, Xi p p = ((∑ k, ‖B k p‖ ^ 2 : ℝ) : ℂ) := by
        intro p
        rw [hB, Matrix.mul_apply]; push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      have h1 : ∀ b, ∑ e, Xi ⟨s, (e, b)⟩ ⟨s, (e, b)⟩ = (D s).dim :=
        g63b_diag_norm D dg Xi hint hone s
      have h2 : ((∑ k, ∑ x : Fin (D s).dim × Fin (D s).dim, ‖B k ⟨s, x⟩‖ ^ 2 : ℝ) : ℂ) =
          ((D s).dim : ℂ) * (D s).dim := by
        rw [Finset.sum_comm]; push_cast
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [← Complex.ofReal_pow]
        have : ∀ b : Fin (D s).dim, ∑ e : Fin (D s).dim, ∑ k, ((‖B k ⟨s, (e, b)⟩‖ ^ 2 : ℝ) : ℂ) =
            (D s).dim := by
          intro b; rw [← h1 b]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hdiag]; push_cast; rfl
        rw [Finset.sum_congr rfl fun b _ => this b]
        simp
      exact_mod_cast h2
    -- bound on T
    have hTk : ∀ k s, ‖T k s‖ ^ 2 ≤
        (∑ x : Fin (D s).dim × Fin (D s).dim, ‖B k ⟨s, x⟩‖ ^ 2) * (D s).dim := by
      intro k s
      have h1 : ‖T k s‖ ≤ ∑ x : Fin (D s).dim × Fin (D s).dim,
          ‖B k ⟨s, x⟩‖ * ‖(W s : Matrix _ _ ℂ) x.1 x.2‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
      have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun x : Fin (D s).dim × Fin (D s).dim => ‖B k ⟨s, x⟩‖)
        (fun x => ‖(W s : Matrix _ _ ℂ) x.1 x.2‖)
      rw [g63b_unit_normsq (W s)] at h2
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    have hTs : ∀ s, ∑ k, ‖T k s‖ ^ 2 ≤ ((D s).dim : ℝ) * (D s).dim * (D s).dim := by
      intro s
      calc ∑ k, ‖T k s‖ ^ 2 ≤ ∑ k, (∑ x : Fin (D s).dim × Fin (D s).dim, ‖B k ⟨s, x⟩‖ ^ 2) * (D s).dim :=
            Finset.sum_le_sum fun k _ => hTk k s
        _ = _ := by rw [← Finset.sum_mul, hBn s]
    -- Minkowski in EuclideanSpace
    let Tv : S → EuclideanSpace ℂ (CanonicalIndex D) := fun s => WithLp.toLp 2 (fun k => T k s)
    let Z : EuclideanSpace ℂ (CanonicalIndex D) := ∑ s, (c s / (Real.sqrt (D s).dim : ℂ)) • Tv s
    have hZ : ∀ k, Z k = z k := by
      intro k; rw [hzT k]; simp [Z, Tv]
    have hnorm : ∑ k, ‖z k‖ ^ 2 = ‖Z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp only [hZ]
    have hTv : ∀ s, ‖Tv s‖ ≤ (D s).dim * Real.sqrt (D s).dim := by
      intro s
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simpa [Tv, sq] using hTs s
    have hZle : ‖Z‖ ≤ ∑ s, ((D s).dim : ℝ) * ‖c s‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_smul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hpos : 0 < Real.sqrt (D s).dim := Real.sqrt_pos.2 (by exact_mod_cast (D s).positive)
      calc ‖c s‖ / Real.sqrt (D s).dim * ‖Tv s‖
          ≤ ‖c s‖ / Real.sqrt (D s).dim * ((D s).dim * Real.sqrt (D s).dim) :=
            mul_le_mul_of_nonneg_left (hTv s) (by positivity)
        _ = ((D s).dim : ℝ) * ‖c s‖ := by field_simp
    rw [hnorm, sq]
    exact mul_self_le_mul_self (norm_nonneg _) hZle
