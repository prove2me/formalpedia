-- Prove2me | solution 1 for compiler_abstract_adversary_identification
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-23T21:56:39.099797+00:00
-- url     : https://prove2.me/submissions/ce94b0da-2ca9-4d35-b370-f7a96872a1a0

import Definitions.Def_QuantumLTF_Majority_CompilerModel

set_option autoImplicit false

/- Simultaneous finite Gram factors for a family of real PSD matrices. -/
theorem compiler_gram_factorization {ι σ : Type*} [Finite ι]
    (X : σ → Matrix ι ι ℝ) (hX : ∀ s, (X s).PosSemidef) :
    ∃ (d : σ → ℕ) (v : (s : σ) → Fin (d s) → ι → ℝ),
      ∀ s a b, X s a b = ∑ j : Fin (d s), v s j a * v s j b := by
  classical
  have hf (s : σ) := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hX s)
  choose d v hv using hf
  refine ⟨d, v, ?_⟩
  intro s a b
  have h := congrArg (fun M : Matrix ι ι ℝ => M a b) (hv s)
  simpa only [Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply,
    Pi.star_apply, star_trivial] using h

/- A finite query family has Gram factors in one common finite workspace. -/
theorem compiler_common_gram_factorization {ι σ : Type} [Finite ι] [Fintype σ]
    (X : σ → Matrix ι ι ℝ) (hX : ∀ s, (X s).PosSemidef) :
    ∃ (ω : Type) (_ : Fintype ω) (w : σ → ι → ω → ℝ),
      ∀ s a b, X s a b = ∑ j : ω, w s a j * w s b j := by
  classical
  obtain ⟨d, v, hv⟩ := compiler_gram_factorization X hX
  let ω := (s : σ) × Fin (d s)
  let w : σ → ι → ω → ℝ := fun s a j =>
    if h : j.1 = s then v s (h ▸ j.2) a else 0
  refine ⟨ω, inferInstance, w, ?_⟩
  intro s a b
  rw [hv s a b]
  simp [ω, w, Fintype.sum_sigma]

/- The adversary constraint equates the input and output transducer Gram entries.
The phase-oracle product is +1 on agreeing queries and -1 otherwise. -/
theorem compiler_transducer_gram_identity {σ : Type*} [Fintype σ]
    (different : σ → Prop) [DecidablePred different] (x : σ → ℝ)
    (δ : ℝ) (h : (∑ s, if different s then x s else 0) = 1 - δ) :
    1 + (1 / 2 : ℝ) * (∑ s, (if different s then (-1 : ℝ) else 1) * x s) =
      δ + (1 / 2 : ℝ) * ∑ s, x s := by
  have hs : (∑ s, (if different s then (-1 : ℝ) else 1) * x s) =
      (∑ s, x s) - 2 * (∑ s, if different s then x s else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  rw [hs, h]
  ring

/- Omitting an exactly restored catalyst incurs at most twice its norm.
This estimate applies after the clock construction has reduced that norm. -/
theorem compiler_catalyst_omission_bound {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (U : E →ₗᵢ[𝕜] E) (input output catalyst : E)
    (h : U (input + catalyst) = output + catalyst) :
    ‖U input - output‖ ≤ 2 * ‖catalyst‖ := by
  have heq : U input - output = catalyst - U catalyst := by
    have hh := h
    rw [map_add] at hh
    exact (sub_eq_sub_iff_add_eq_add).2 (by simpa [add_comm] using hh)
  rw [heq]
  calc
    ‖catalyst - U catalyst‖ ≤ ‖catalyst‖ + ‖U catalyst‖ := norm_sub_le _ _
    _ = 2 * ‖catalyst‖ := by rw [U.norm_map]; ring

/- Equal Gram matrices preserve inner products of all finite linear combinations. -/
theorem compiler_gram_linear_combinations {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℝ (u i) (u j) = inner ℝ (v i) (v j))
    (a b : ι → ℝ) :
    inner ℝ (∑ i, a i • u i) (∑ j, b j • u j) =
      inner ℝ (∑ i, a i • v i) (∑ j, b j • v j) := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, h]

/- Equal Gram matrices give the same linear relations, ensuring that the
transducer map on the span is well-defined even for dependent families. -/
theorem compiler_gram_relation_iff {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℝ (u i) (u j) = inner ℝ (v i) (v j))
    (a : ι → ℝ) : (∑ i, a i • u i) = 0 ↔ (∑ i, a i • v i) = 0 := by
  have hh := compiler_gram_linear_combinations u v h a a
  constructor
  · intro hz
    rw [hz, inner_zero_left] at hh
    exact (inner_self_eq_zero).mp hh.symm
  · intro hz
    rw [hz, inner_zero_left] at hh
    exact (inner_self_eq_zero).mp hh

/- The proposed map between the spans is independent of the chosen coefficients. -/
theorem compiler_gram_representation_iff {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℝ (u i) (u j) = inner ℝ (v i) (v j))
    (a b : ι → ℝ) :
    (∑ i, a i • u i) = (∑ i, b i • u i) ↔
      (∑ i, a i • v i) = (∑ i, b i • v i) := by
  have hh := compiler_gram_relation_iff u v h (fun i => a i - b i)
  simpa only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hh

/- Equal Gram data also preserve distances between represented span vectors. -/
theorem compiler_gram_norm_linear_combination {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℝ (u i) (u j) = inner ℝ (v i) (v j))
    (a : ι → ℝ) : ‖∑ i, a i • u i‖ = ‖∑ i, a i • v i‖ := by
  have hh := compiler_gram_linear_combinations u v h a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (∑ i, a i • u i), norm_nonneg (∑ i, a i • v i)]

/- Two linear maps with equal pullback norms induce an isometry between their ranges. -/
noncomputable def compiler_range_isometry {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) : LinearMap.range f →ₗᵢ[𝕜] LinearMap.range g := by
  classical
  have hrel (a b : D) (hab : f a = f b) : g a = g b := by
    have hh := hn (a - b)
    rw [map_sub, map_sub, hab, sub_self, norm_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp hh.symm)
  let pre (x : LinearMap.range f) : D := x.2.choose
  have hpre (x : LinearMap.range f) : f (pre x) = x.1 := x.2.choose_spec
  let toFun : LinearMap.range f → LinearMap.range g :=
    fun x => ⟨g (pre x), ⟨pre x, rfl⟩⟩
  refine { toFun := toFun, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro x y
    apply Subtype.ext
    change g (pre (x + y)) = g (pre x) + g (pre y)
    rw [← map_add]
    apply hrel
    simp only [map_add, hpre, Submodule.coe_add]
  · intro c x
    apply Subtype.ext
    change g (pre (c • x)) = c • g (pre x)
    rw [← map_smul]
    apply hrel
    simp only [map_smul, hpre, Submodule.coe_smul]
  · intro x
    change ‖g (pre x)‖ = ‖x.1‖
    rw [← hn, hpre]

theorem compiler_range_isometry_apply {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) (a : D) :
    (compiler_range_isometry f g hn ⟨f a, ⟨a, rfl⟩⟩ : F) = g a := by
  classical
  let x : LinearMap.range f := ⟨f a, ⟨a, rfl⟩⟩
  change g x.2.choose = g a
  have hx : f x.2.choose = f a := x.2.choose_spec
  have hh := hn (x.2.choose - a)
  rw [map_sub, map_sub, hx, sub_self, norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp hh.symm)

theorem compiler_range_isometry_surjective {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    Function.Surjective (compiler_range_isometry f g hn) := by
  intro y
  obtain ⟨a, ha⟩ := y.2
  refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  rw [compiler_range_isometry_apply, ha]

/- An input-independent isometry on the entire workspace realizing the
prescribed state conversion whenever its two Gram forms agree. -/
theorem compiler_exists_workspace_isometry {𝕜 D E : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (f g : D →ₗ[𝕜] E) (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    ∃ U : E →ₗᵢ[𝕜] E, ∀ a, U (f a) = g a := by
  let L : LinearMap.range f →ₗᵢ[𝕜] E :=
    (LinearMap.range g).subtypeₗᵢ.comp (compiler_range_isometry f g hn)
  refine ⟨L.extend, ?_⟩
  intro a
  have hh := LinearIsometry.extend_apply L (⟨f a, ⟨a, rfl⟩⟩ : LinearMap.range f)
  exact hh.trans (compiler_range_isometry_apply f g hn a)

/- The finite-dimensional workspace map is onto, hence is a unitary
equivalence (over either the real or complex field). -/
theorem compiler_exists_workspace_unitary {𝕜 D E : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (f g : D →ₗ[𝕜] E) (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ a, U (f a) = g a := by
  obtain ⟨U, hU⟩ := compiler_exists_workspace_isometry f g hn
  have hsurj : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) U.injective
  exact ⟨LinearIsometryEquiv.ofSurjective U hsurj, hU⟩

/- Matching Gram matrices give a single unitary taking every prescribed
input vector to its prescribed output vector, including dependent families. -/
theorem compiler_unitary_of_equal_gram {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (u v : ι → E) (h : ∀ a b, inner 𝕜 (u a) (u b) = inner 𝕜 (v a) (v b)) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ a, U (u a) = v a := by
  classical
  let f := Fintype.linearCombination 𝕜 u
  let g := Fintype.linearCombination 𝕜 v
  have hn (c : ι → 𝕜) : ‖f c‖ = ‖g c‖ := by
    have hh : inner 𝕜 (f c) (f c) = inner 𝕜 (g c) (g c) := by
      simp only [f, g, Fintype.linearCombination_apply, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, h]
    have hsq : ‖f c‖ ^ 2 = ‖g c‖ ^ 2 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜),
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜), hh]
    nlinarith [norm_nonneg (f c), norm_nonneg (g c)]
  obtain ⟨U, hU⟩ := compiler_exists_workspace_unitary f g hn
  refine ⟨U, ?_⟩
  intro a
  simpa [f, g, Fintype.linearCombination_apply] using hU (Pi.single a 1)

/- The clock algorithm consists of one oracle application and one
input-independent unitary at each step. -/


/- Equal Gram matrices at each clock transition produce a sequence of
input-independent unitaries that restores the shared catalyst exactly. -/
theorem compiler_clock_exact_transduction {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (N : ℕ) (O : ι → E ≃ₗᵢ[𝕜] E) (p : ℕ → ι → E) (c : ι → E)
    (hgram : ∀ j, j < N → ∀ a b,
      inner 𝕜 (O a (p j a + c a)) (O b (p j b + c b)) =
        inner 𝕜 (p (j+1) a + c a) (p (j+1) b + c b)) :
    ∃ U : ℕ → E ≃ₗᵢ[𝕜] E, ∀ a,
      compiler_clock_run U (O a) N (p 0 a + c a) = p N a + c a := by
  classical
  have hex (j : ℕ) : ∃ U : E ≃ₗᵢ[𝕜] E, ∀ a, j < N →
      U (O a (p j a + c a)) = p (j+1) a + c a := by
    by_cases hj : j < N
    · obtain ⟨U, hU⟩ := compiler_unitary_of_equal_gram
        (fun a => O a (p j a + c a)) (fun a => p (j+1) a + c a) (hgram j hj)
      exact ⟨U, fun a _ => hU a⟩
    · exact ⟨LinearIsometryEquiv.refl 𝕜 E, fun _ h => (hj h).elim⟩
  choose U hU using hex
  refine ⟨U, ?_⟩
  have hind (j : ℕ) (hj : j ≤ N) (a : ι) :
      compiler_clock_run U (O a) j (p 0 a + c a) = p j a + c a := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change U j (O a (compiler_clock_run U (O a) j (p 0 a + c a))) = _
      rw [ih (by omega)]
      exact hU j a (by omega)
  exact fun a => hind N le_rfl a

/- Running the clock algorithm without the shared catalyst has error at most
twice the catalyst norm, with exactly N oracle slots in the recursive run. -/
theorem compiler_clock_omission_bound {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (N : ℕ) (O : ι → E ≃ₗᵢ[𝕜] E) (p : ℕ → ι → E) (c : ι → E)
    (hgram : ∀ j, j < N → ∀ a b,
      inner 𝕜 (O a (p j a + c a)) (O b (p j b + c b)) =
        inner 𝕜 (p (j+1) a + c a) (p (j+1) b + c b)) :
    ∃ U : ℕ → E ≃ₗᵢ[𝕜] E, ∀ a,
      ‖compiler_clock_run U (O a) N (p 0 a) - p N a‖ ≤ 2 * ‖c a‖ := by
  obtain ⟨U, hU⟩ := compiler_clock_exact_transduction N O p c hgram
  refine ⟨U, ?_⟩
  intro a
  exact compiler_catalyst_omission_bound
    (compiler_clock_run U (O a) N).toLinearIsometry (p 0 a) (p N a) (c a) (hU a)

/- The public clock register: the first t slots contain the learned label,
and the remaining slots contain the distinguished initial symbol. -/


theorem compiler_clock_public_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N t : ℕ) (a b : ι) :
    inner ℂ (compiler_clock_public N t a) (compiler_clock_public N t b) =
      ∑ j : Fin N, if (j : ℕ) < t then (if a = b then (1 : ℂ) else 0) else 1 := by
  classical
  simp only [compiler_clock_public, sum_inner, inner_sum,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ k : Fin N,
      if (k, if (k : ℕ) < t then some a else none) =
          (j, if (j : ℕ) < t then some b else none) then (1 : ℂ) else 0) =
      (if (if (j : ℕ) < t then some a else none) =
          (if (j : ℕ) < t then some b else none) then (1 : ℂ) else 0) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Prod.mk.injEq, hkj]
    · simp
  rw [hs]
  split_ifs <;> simp_all

theorem compiler_clock_public_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N t : ℕ) (ht : t < N) (a b : ι) :
    inner ℂ (compiler_clock_public N t a) (compiler_clock_public N t b) -
      inner ℂ (compiler_clock_public N (t+1) a) (compiler_clock_public N (t+1) b) =
        1 - (if a = b then (1 : ℂ) else 0) := by
  rw [compiler_clock_public_inner, compiler_clock_public_inner,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (⟨t, ht⟩ : Fin N)]
  · simp
  · intro j _ hj
    have hjval : (j : ℕ) ≠ t := by
      intro heq
      exact hj (Fin.ext heq)
    have hiff : (j : ℕ) < t ↔ (j : ℕ) < t+1 := by omega
    simp only [hiff, sub_self]
  · simp

theorem compiler_clock_public_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N t : ℕ) (a : ι) : ‖compiler_clock_public N t a‖ ^ 2 = N := by
  have hh := compiler_clock_public_inner N t a a
  simp at hh
  have hr := congrArg Complex.re hh
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using hr

/- A Boolean phase oracle is a genuine unitary on the finite query workspace. -/


@[simp] theorem compiler_sign_oracle_apply {κ : Type*} [Fintype κ]
    (bit : κ → Bool) (x : EuclideanSpace ℂ κ) (j : κ) :
    compiler_sign_oracle bit x j = (if bit j then (-1 : ℂ) else 1) * x j := rfl

/- The clock Gram condition follows from the public-register decrement and
the corresponding oracle-induced decrement on the catalyst Gram matrix. -/
theorem compiler_clock_gram_from_moments {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : ℕ) (O : ι → E ≃ₗᵢ[ℂ] E) (p : ℕ → ι → E) (c : ι → E)
    (hfix : ∀ a j, O a (p j a) = p j a)
    (horth : ∀ j a b, inner ℂ (p j a) (c b) = 0)
    (horthO : ∀ j a b, inner ℂ (p j a) (O b (c b)) = 0)
    (hpublic : ∀ j, j < N → ∀ a b,
      inner ℂ (p j a) (p j b) - inner ℂ (p (j+1) a) (p (j+1) b) =
        1 - (if a = b then (1 : ℂ) else 0))
    (hcatalyst : ∀ a b,
      inner ℂ (c a) (c b) - inner ℂ (O a (c a)) (O b (c b)) =
        1 - (if a = b then (1 : ℂ) else 0)) :
    ∀ j, j < N → ∀ a b,
      inner ℂ (O a (p j a + c a)) (O b (p j b + c b)) =
        inner ℂ (p (j+1) a + c a) (p (j+1) b + c b) := by
  intro j hj a b
  have hp := hpublic j hj a b
  have hc := hcatalyst a b
  have horth' (j : ℕ) (a b : ι) : inner ℂ (c a) (p j b) = 0 := by
    rw [← inner_conj_symm, horth j b a, map_zero]
  have horthO' (j : ℕ) (a b : ι) : inner ℂ (O a (c a)) (p j b) = 0 := by
    rw [← inner_conj_symm, horthO j b a, map_zero]
  simp only [map_add, hfix, inner_add_left, inner_add_right, horth, horth',
    horthO, horthO', add_zero, zero_add]
  linear_combination hp - hc

/- Real Gram factors embedded in the complex query workspace. -/
noncomputable def compiler_complex_factor {ι σ ω : Type*} [Fintype σ] [Fintype ω]
    (v : σ → ι → ω → ℝ) (a : ι) : EuclideanSpace ℂ (σ × ω) :=
  WithLp.toLp 2 (fun j => (v j.1 a j.2 : ℂ))

theorem compiler_complex_factor_inner {ι σ ω : Type*} [Fintype σ] [Fintype ω]
    (X : σ → Matrix ι ι ℝ) (v : σ → ι → ω → ℝ)
    (hv : ∀ s a b, X s a b = ∑ j, v s a j * v s b j) (a b : ι) :
    inner ℂ (compiler_complex_factor v a) (compiler_complex_factor v b) =
      ∑ s, (X s a b : ℂ) := by
  simp only [PiLp.inner_apply, compiler_complex_factor, WithLp.ofLp_toLp,
    RCLike.inner_apply, Complex.conj_ofReal, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [hv s a b]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  ring

/- The diagonal norm is exactly the dual objective before the 1/sqrt(2) scaling. -/
theorem compiler_complex_factor_norm_sq {ι σ ω : Type*} [Fintype σ] [Fintype ω]
    (X : σ → Matrix ι ι ℝ) (v : σ → ι → ω → ℝ)
    (hv : ∀ s a b, X s a b = ∑ j, v s a j * v s b j) (a : ι) :
    ‖compiler_complex_factor v a‖ ^ 2 = ∑ s, X s a a := by
  have hh := compiler_complex_factor_inner X v hv a a
  have hr := congrArg Complex.re hh
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, map_sum] using hr

/- The oracle changes a Gram entry by twice the distinguishing-query sum. -/
theorem compiler_phase_factor_gram_difference {ι σ ω : Type*}
    [Fintype σ] [Fintype ω] (f : ι → σ → Bool)
    (X : σ → Matrix ι ι ℝ) (v : σ → ι → ω → ℝ)
    (hv : ∀ s a b, X s a b = ∑ j, v s a j * v s b j) (a b : ι) :
    inner ℂ (compiler_complex_factor v a) (compiler_complex_factor v b) -
      inner ℂ (compiler_sign_oracle (fun j : σ × ω => f a j.1) (compiler_complex_factor v a))
        (compiler_sign_oracle (fun j : σ × ω => f b j.1) (compiler_complex_factor v b)) =
      2 * ∑ s, if f a s ≠ f b s then (X s a b : ℂ) else 0 := by
  rw [compiler_complex_factor_inner X v hv]
  simp only [PiLp.inner_apply, RCLike.inner_apply, compiler_sign_oracle_apply,
    compiler_complex_factor, WithLp.ofLp_toLp, map_mul, Complex.conj_ofReal,
    Fintype.sum_prod_type]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [hv s a b]
  by_cases ha : f a s = true <;> by_cases hb : f b s = true <;>
    simp_all only [Bool.not_eq_true, ha, hb, Bool.false_eq_true, ite_true,
      ite_false, ne_eq, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
      sub_self, mul_zero, one_mul, neg_one_mul, map_one, map_neg, neg_neg]
  all_goals push_cast
  all_goals simp only [mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib,
    mul_comm (v s b _ : ℂ)]
  all_goals ring



noncomputable def compiler_right {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℂ β) : EuclideanSpace ℂ (α ⊕ β) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun b => x b))

@[simp] theorem compiler_inner_left_left {α β : Type*} [Fintype α] [Fintype β]
    (x y : EuclideanSpace ℂ α) :
    inner ℂ (compiler_left (β := β) x) (compiler_left y) = inner ℂ x y := by
  simp [compiler_left, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] theorem compiler_inner_right_right {α β : Type*} [Fintype α] [Fintype β]
    (x y : EuclideanSpace ℂ β) :
    inner ℂ (compiler_right (α := α) x) (compiler_right y) = inner ℂ x y := by
  simp [compiler_right, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] theorem compiler_inner_left_right {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    inner ℂ (compiler_left x) (compiler_right y) = 0 := by
  simp [compiler_left, compiler_right, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] theorem compiler_inner_right_left {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℂ β) (y : EuclideanSpace ℂ α) :
    inner ℂ (compiler_right x) (compiler_left y) = 0 := by
  simp [compiler_left, compiler_right, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] theorem compiler_oracle_left {α β : Type*} [Fintype α] [Fintype β]
    (f : β → Bool) (x : EuclideanSpace ℂ α) :
    compiler_sign_oracle (Sum.elim (fun _ : α => false) f) (compiler_left x) =
      compiler_left x := by
  ext j
  cases j <;> simp [compiler_left]

@[simp] theorem compiler_oracle_right {α β : Type*} [Fintype α] [Fintype β]
    (f : β → Bool) (x : EuclideanSpace ℂ β) :
    compiler_sign_oracle (Sum.elim (fun _ : α => false) f) (compiler_right x) =
      compiler_right (compiler_sign_oracle f x) := by
  ext j
  cases j with
  | inl j => simp [compiler_right]
  | inr j =>
    change (if f j then (-1 : ℂ) else 1) * x j =
      (if f j then (-1 : ℂ) else 1) * x j
    rfl

/- The catalyst scaling used by the adversary compiler. -/
noncomputable def compiler_catalyst_scale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem compiler_catalyst_scale_sq :
    compiler_catalyst_scale * compiler_catalyst_scale = (1/2 : ℂ) := by
  have hh : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1/2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  unfold compiler_catalyst_scale
  rw [← Complex.ofReal_mul, hh]
  norm_num

@[simp] theorem compiler_catalyst_scale_star :
    (starRingEnd ℂ) compiler_catalyst_scale = compiler_catalyst_scale :=
  Complex.conj_ofReal _

theorem compiler_scaled_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) :
    inner ℂ (compiler_catalyst_scale • x) (compiler_catalyst_scale • y) =
      (1/2 : ℂ) * inner ℂ x y := by
  rw [inner_smul_left, inner_smul_right, compiler_catalyst_scale_star,
    ← mul_assoc, compiler_catalyst_scale_sq]

/- The full finite-dimensional Gram/transducer construction from a dual
adversary solution, with one shared catalyst and N oracle slots. -/
theorem compiler_dual_to_clock_transduction {ι σ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] (f : ι → σ → Bool) (X : σ → Matrix ι ι ℝ)
    (hPSD : ∀ s, (X s).PosSemidef)
    (hdual : ∀ a b, a ≠ b → (∑ s, if f a s ≠ f b s then X s a b else 0) = 1) :
    ∃ (ω : Type) (_ : Fintype ω) (v : σ → ι → ω → ℝ),
      (∀ s a b, X s a b = ∑ j, v s a j * v s b j) ∧
      ∀ N : ℕ,
        let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω))
        let O : ι → E ≃ₗᵢ[ℂ] E := fun a => compiler_sign_oracle
          (Sum.elim (fun _ => false) (fun j : σ × ω => f a j.1))
        let p : ℕ → ι → E := fun t a => compiler_left (compiler_clock_public N t a)
        let c : ι → E := fun a => compiler_right
          (compiler_catalyst_scale • compiler_complex_factor v a)
        ∃ U : ℕ → E ≃ₗᵢ[ℂ] E,
          (∀ a, compiler_clock_run U (O a) N (p 0 a + c a) = p N a + c a) ∧
          (∀ a, ‖c a‖ ^ 2 = (1/2 : ℝ) * ∑ s, X s a a) := by
  classical
  obtain ⟨ω, hω, v, hv⟩ := compiler_common_gram_factorization X hPSD
  letI : Fintype ω := hω
  refine ⟨ω, hω, v, hv, ?_⟩
  intro N
  dsimp only
  let O : ι → EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω)) := fun a => compiler_sign_oracle
    (Sum.elim (fun _ => false) (fun j : σ × ω => f a j.1))
  let p : ℕ → ι → EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω)) :=
    fun t a => compiler_left (compiler_clock_public N t a)
  let c : ι → EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω)) := fun a => compiler_right
    (compiler_catalyst_scale • compiler_complex_factor v a)
  have hcat (a b : ι) : inner ℂ (c a) (c b) -
      inner ℂ (O a (c a)) (O b (c b)) =
        1 - (if a = b then (1 : ℂ) else 0) := by
    have hweight : (∑ s, if f a s ≠ f b s then (X s a b : ℂ) else 0) =
        1 - (if a = b then (1 : ℂ) else 0) := by
      by_cases hab : a = b
      · subst b; simp
      · simp only [if_neg hab, sub_zero]
        have hh := congrArg Complex.ofReal (hdual a b hab)
        push_cast at hh
        simpa only [apply_ite, Complex.ofReal_zero] using hh
    simp only [c, O, compiler_oracle_right, map_smul,
      compiler_inner_right_right, compiler_scaled_inner]
    rw [← mul_sub, compiler_phase_factor_gram_difference f X v hv a b, hweight]
    ring
  have hgram := compiler_clock_gram_from_moments N O p c
    (by intro a t; simp [O, p])
    (by intro t a b; simp [p, c])
    (by intro t a b; simp [p, c, O])
    (by intro t ht a b; simpa [p] using compiler_clock_public_step N t ht a b)
    hcat
  obtain ⟨U, hU⟩ := compiler_clock_exact_transduction N O p c hgram
  refine ⟨U, hU, ?_⟩
  intro a
  have hh : inner ℂ (c a) (c a) =
      (1/2 : ℂ) * ∑ s, (X s a a : ℂ) := by
    simp only [c, compiler_inner_right_right, compiler_scaled_inner,
      compiler_complex_factor_inner X v hv]
  have hr := congrArg Complex.re hh
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, map_sum,
    Complex.mul_re] using hr

/- Normalizing the N clock slots reduces the squared error to 2T/N. -/
theorem compiler_normalized_clock_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) (input output catalyst : E) (T : ℝ)
    (htrans : R (input + catalyst) = output + catalyst)
    (hcost : ‖catalyst‖ ^ 2 ≤ T / 2) (N : ℕ) (hN : 0 < N) :
    ‖R ((((Real.sqrt N)⁻¹ : ℝ) : ℂ) • input) -
      (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • output‖ ^ 2 ≤ 2 * T / N := by
  have herr := compiler_catalyst_omission_bound R.toLinearIsometry
    input output catalyst htrans
  change ‖R input - output‖ ≤ 2 * ‖catalyst‖ at herr
  have herrsq := mul_self_le_mul_self (norm_nonneg (R input - output)) herr
  have herr2 : ‖R input - output‖ ^ 2 ≤ 2 * T := by
    nlinarith
  have hscale : ‖(((Real.sqrt N)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / (N : ℝ) := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    _ = (1 / (N : ℝ)) * ‖R input - output‖ ^ 2 := by
      rw [map_smul, ← smul_sub, norm_smul, mul_pow, hscale]
    _ ≤ (1 / (N : ℝ)) * (2 * T) :=
      mul_le_mul_of_nonneg_left herr2 (by positivity)
    _ = 2 * T / N := by ring

/- A concrete linear query budget makes the squared error at most 1/36.
This leaves success at least (1-1/6)^2 = 25/36 > 2/3. -/
theorem compiler_clock_budget (T : ℝ) (hT : 0 ≤ T) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 73 * (T + 1) ∧ 2 * T / N ≤ 1/36 := by
  let N := ⌈72 * (T + 1)⌉₊
  have hlo : 72 * (T + 1) ≤ (N : ℝ) := Nat.le_ceil _
  have hhi : (N : ℝ) < 72 * (T + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNreal : (0 : ℝ) < N := by linarith
  refine ⟨N, by exact_mod_cast hNreal, by linarith, ?_⟩
  apply (div_le_iff₀ hNreal).2
  linarith

/- The initial public clock state is independent of the hidden label. -/


@[simp] theorem compiler_clock_public_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (a : ι) : compiler_clock_public N 0 a = compiler_clock_start N := by
  simp [compiler_clock_public, compiler_clock_start]

/- Abstract general-adversary query compiler. It produces a single
input-independent sequence of complex unitaries with at most 73(T+1)
phase-oracle slots and squared state error at most 1/36. The query oracle
acts only on the private summand; the initial public state is label-independent. -/
theorem compiler_dual_to_query_algorithm {ι σ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] (f : ι → σ → Bool) (X : σ → Matrix ι ι ℝ)
    (hPSD : ∀ s, (X s).PosSemidef)
    (hdual : ∀ a b, a ≠ b → (∑ s, if f a s ≠ f b s then X s a b else 0) = 1)
    (T : ℝ) (hT : 0 ≤ T) (hcost : ∀ a, ∑ s, X s a a ≤ T) :
    ∃ (ω : Type) (_ : Fintype ω) (N : ℕ), 0 < N ∧ (N : ℝ) ≤ 73 * (T+1) ∧
      let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω))
      let O : ι → E ≃ₗᵢ[ℂ] E := fun a => compiler_sign_oracle
        (Sum.elim (fun _ => false) (fun j : σ × ω => f a j.1))
      let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
      let target : ι → E := fun a => (((Real.sqrt N)⁻¹ : ℝ) : ℂ) •
        compiler_left (compiler_clock_public N N a)
      ∃ U : ℕ → E ≃ₗᵢ[ℂ] E, ∀ a,
        ‖compiler_clock_run U (O a) N start - target a‖ ^ 2 ≤ 1/36 := by
  obtain ⟨ω, hω, v, hv, htrans⟩ := compiler_dual_to_clock_transduction f X hPSD hdual
  letI : Fintype ω := hω
  obtain ⟨N, hN, hNbound, herr⟩ := compiler_clock_budget T hT
  obtain ⟨U, hU, hcat⟩ := htrans N
  refine ⟨ω, hω, N, hN, hNbound, U, ?_⟩
  intro a
  have hc : ‖compiler_right (α := Fin N × Option ι)
      (compiler_catalyst_scale • compiler_complex_factor v a)‖ ^ 2 ≤ T/2 := by
    rw [hcat a]
    linarith [hcost a]
  have he := compiler_normalized_clock_error _ _ _ _ T (hU a) hc N hN
  simpa only [compiler_clock_public_zero] using he.trans herr

theorem compiler_normalized_public_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (hN : 0 < N) (a b : ι) :
    inner ℂ ((((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_clock_public N N a)
      ((((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_clock_public N N b) =
      (if a = b then (1 : ℂ) else 0) := by
  have hsq : (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * (((Real.sqrt N)⁻¹ : ℝ) : ℂ) =
      (1 / (N : ℝ) : ℝ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    simp
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, hsq,
    compiler_clock_public_inner]
  have hlt (j : Fin N) : (j : ℕ) < N := j.isLt
  simp only [hlt, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases hab : a = b
  · simp [hab, Nat.ne_of_gt hN]
  · simp [hab]

/- Restricting a state to a measurement event. -/
noncomputable def compiler_event_projection {κ : Type*} [Fintype κ]
    (event : κ → Prop) [DecidablePred event] (x : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ κ := WithLp.toLp 2 (fun j => if event j then x j else 0)

theorem compiler_event_projection_norm_le {κ : Type*} [Fintype κ]
    (event : κ → Prop) [DecidablePred event] (x : EuclideanSpace ℂ κ) :
    ‖compiler_event_projection event x‖ ≤ ‖x‖ := by
  have hs : ‖compiler_event_projection event x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro j _
    change ‖if event j then x j else (0 : ℂ)‖ ^ 2 ≤ ‖x j‖ ^ 2
    split_ifs <;> simp
  nlinarith [norm_nonneg (compiler_event_projection event x), norm_nonneg x]

/- State error at most 1/6 implies success probability at least 2/3 for
every event containing the support of the unit target state. -/
theorem compiler_measurement_success {κ : Type*} [Fintype κ]
    (event : κ → Prop) [DecidablePred event] (ψ target : EuclideanSpace ℂ κ)
    (htarget : ‖target‖ = 1) (hsupport : ∀ j, ¬ event j → target j = 0)
    (herror : ‖ψ - target‖ ^ 2 ≤ 1/36) :
    (∑ j, if event j then ‖ψ j‖ ^ 2 else 0) ≥ (2/3 : ℝ) := by
  have hprojtarget : compiler_event_projection event target = target := by
    ext j
    change (if event j then target j else 0) = target j
    split_ifs with hj
    · rfl
    · exact (hsupport j hj).symm
  have hprojsub : compiler_event_projection event (ψ - target) =
      compiler_event_projection event ψ - target := by
    rw [← hprojtarget]
    ext j
    change (if event j then ψ j - (if event j then target j else 0) else 0) =
      (if event j then ψ j else 0) - (if event j then target j else 0)
    split_ifs <;> simp
  have herr : ‖ψ - target‖ ≤ 1/6 := by
    nlinarith [norm_nonneg (ψ - target)]
  have hprojnorm : ‖compiler_event_projection event ψ - target‖ ≤ 1/6 := by
    rw [← hprojsub]
    exact (compiler_event_projection_norm_le event (ψ-target)).trans herr
  have hnorm := norm_sub_norm_le target (compiler_event_projection event ψ)
  rw [norm_sub_rev, htarget] at hnorm
  have hlower : (5/6 : ℝ) ≤ ‖compiler_event_projection event ψ‖ := by linarith
  have hs : (∑ j, if event j then ‖ψ j‖ ^ 2 else 0) =
      ‖compiler_event_projection event ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    change (if event j then ‖ψ j‖ ^ 2 else 0) =
      ‖if event j then ψ j else (0 : ℂ)‖ ^ 2
    split_ifs <;> simp
  rw [hs]
  nlinarith





theorem compiler_public_target_supported {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] (N : ℕ) (a : ι) (j : (Fin N × Option ι) ⊕ β)
    (hj : ¬ compiler_success_event a j) :
    compiler_left (β := β) (compiler_clock_public N N a) j = 0 := by
  cases j with
  | inr j => rfl
  | inl j =>
    have hlabel : j.2 ≠ some a := hj
    change compiler_clock_public N N a j = 0
    simp only [compiler_clock_public, WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hne : j ≠ (k, if (k : ℕ) < N then some a else none) := by
      simp only [k.isLt, ite_true]
      intro heq
      exact hlabel (congrArg Prod.snd heq)
    exact if_neg hne

@[simp] theorem compiler_left_norm {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℂ α) : ‖compiler_left (β := β) x‖ = ‖x‖ := by
  simp [compiler_left, EuclideanSpace.norm_eq, Fintype.sum_sum_type]

theorem compiler_left_smul {α β : Type*} [Fintype α] [Fintype β]
    (r : ℂ) (x : EuclideanSpace ℂ α) :
    r • compiler_left (β := β) x = compiler_left (r • x) := by
  ext j
  cases j <;> simp [compiler_left]

/- Complete identification algorithm in the unrestricted finite-dimensional
query model: a feasible dual of cost T yields success at least 2/3 after
at most 73(T+1) phase queries, using fixed inter-query unitaries. -/
theorem solution {ι σ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype σ]
    (f : ι → σ → Bool) (X : σ → Matrix ι ι ℝ)
    (hPSD : ∀ s, (X s).PosSemidef)
    (hdual : ∀ a b, a ≠ b → (∑ s, if f a s ≠ f b s then X s a b else 0) = 1)
    (T : ℝ) (hT : 0 ≤ T) (hcost : ∀ a, ∑ s, X s a a ≤ T) :
    ∃ (ω : Type) (_ : Fintype ω) (N : ℕ), 0 < N ∧ (N : ℝ) ≤ 73 * (T+1) ∧
      let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (σ × ω))
      let O : ι → E ≃ₗᵢ[ℂ] E := fun a => compiler_sign_oracle
        (Sum.elim (fun _ => false) (fun j : σ × ω => f a j.1))
      let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
      ∃ U : ℕ → E ≃ₗᵢ[ℂ] E, ∀ a,
        (∑ j, if compiler_success_event a j then
          ‖compiler_clock_run U (O a) N start j‖ ^ 2 else 0) ≥ (2/3 : ℝ) := by
  classical
  obtain ⟨ω, hω, N, hN, hNbound, U, hU⟩ :=
    compiler_dual_to_query_algorithm f X hPSD hdual T hT hcost
  letI : Fintype ω := hω
  refine ⟨ω, hω, N, hN, hNbound, U, ?_⟩
  intro a
  apply compiler_measurement_success _ _
    ((((Real.sqrt N)⁻¹ : ℝ) : ℂ) •
      compiler_left (β := σ × ω) (compiler_clock_public N N a))
  · rw [compiler_left_smul, compiler_left_norm]
    have hh := compiler_normalized_public_inner N hN a a
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at hh
    have hr := congrArg Complex.re hh
    simp [← Complex.ofReal_pow] at hr
    rcases hr with hr | hr
    · simpa only [Complex.ofReal_inv] using hr
    · have hn := norm_nonneg
        (((Real.sqrt (N : ℝ) : ℂ)⁻¹) • compiler_clock_public N N a)
      linarith
  · intro j hj
    change (((Real.sqrt N)⁻¹ : ℝ) : ℂ) *
      compiler_left (β := σ × ω) (compiler_clock_public N N a) j = 0
    rw [compiler_public_target_supported N a j hj, mul_zero]
  · exact hU a

