-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nucNorm_le_sqrt_two_r_frob_of_mem_Mbar
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:03:02.821403+00:00
-- url     : https://prove2.me/submissions/1884efcd-d688-4612-b2e7-9dedba14f377

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_Mbar

open WainwrightHDS.NucNorm

lemma traceInner_eq_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = (A.transpose * B).trace := by
  dsimp [traceInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma toEuclideanLin_mul {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

lemma toEuclideanLin_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Matrix.toEuclideanLin A.transpose = (Matrix.toEuclideanLin A).adjoint := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma trace_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun n ℝ).toBasis

lemma traceInner_eq_linearMap_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂))
      ((Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin B)) := by
  rw [traceInner_eq_trace]
  rw [← trace_toEuclideanLin]
  rw [toEuclideanLin_mul, toEuclideanLin_transpose]

lemma frobSq_eq_traceInner_self {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq A = traceInner A A := by
  dsimp [frobSq, traceInner]
  simp_rw [sq]

lemma frobSq_eq_zero_iff {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq A = 0 ↔ A = 0 := by
  dsimp [frobSq]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp_rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _), sq_eq_zero_iff]
    constructor
    · intro h
      ext i j
      exact h i (Finset.mem_univ _) j (Finset.mem_univ _)
    · rintro rfl i _ j _
      rfl
  · intro i _
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma frobSq_eq_trace {d₁ d₂ : ℕ} (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq Θ = (Θ.transpose * Θ).trace := by
  dsimp [Matrix.trace, Matrix.mul_apply, frobSq, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  congr 1; ext i
  congr 1; ext j
  ring

lemma linearMap_trace_adjoint_comp_self {d₁ d₂ : ℕ} (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin Θ).adjoint.comp (Matrix.toEuclideanLin Θ)) =
    frobSq Θ := by
  rw [← toEuclideanLin_transpose, ← toEuclideanLin_mul]
  rw [trace_toEuclideanLin]
  rw [frobSq_eq_trace]

lemma starProjection_toLinearMap_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Submodule ℝ E) :
    ((U.starProjection : E →L[ℝ] E).toLinearMap).adjoint = (U.starProjection : E →L[ℝ] E).toLinearMap := by
  rw [ContinuousLinearMap.adjoint_toLinearMap]
  congr 1
  have h : star U.starProjection = U.starProjection := (isSelfAdjoint_starProjection U).star_eq
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

lemma starProjection_toLinearMap_idempotent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Submodule ℝ E) :
    ((U.starProjection : E →L[ℝ] E).toLinearMap).comp (U.starProjection : E →L[ℝ] E).toLinearMap =
    (U.starProjection : E →L[ℝ] E).toLinearMap := by
  have h := congr_arg ContinuousLinearMap.toLinearMap (Submodule.isIdempotentElem_starProjection U)
  exact h

lemma comp_PVperp_PUperp_eq_zero {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) (hΘ : Θ ∈ Mbar U V) :
    ((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp
      ((Matrix.toEuclideanLin Θ).comp ((Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap)) = 0 := by
  let T := Matrix.toEuclideanLin Θ
  let PUperp := (Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap
  let PVperp := (Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap
  let B_lin := PUperp.comp (T.comp PVperp)
  let B := Matrix.toEuclideanLin.symm B_lin
  have hB_lin : Matrix.toEuclideanLin B = B_lin := Matrix.toEuclideanLin.apply_symm_apply B_lin
  have hB_adj : B_lin.adjoint = PVperp.comp (T.adjoint.comp PUperp) := by
    dsimp [B_lin]
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp]
    rw [starProjection_toLinearMap_adjoint, starProjection_toLinearMap_adjoint]
    exact LinearMap.comp_assoc _ _ _
  have hB_mem : B ∈ MbarPerp U V := by
    dsimp [MbarPerp]
    constructor
    · rw [toEuclideanLin_transpose, hB_lin, hB_adj]
      refine le_trans (LinearMap.range_comp_le_range _ _) ?_
      rw [Submodule.range_starProjection]
    · rw [hB_lin]
      refine le_trans (LinearMap.range_comp_le_range _ _) ?_
      rw [Submodule.range_starProjection]
  have h_inner_zero : traceInner Θ B = 0 := hΘ B hB_mem
  have h_inner_eq : traceInner B B = traceInner Θ B := by
    rw [traceInner_eq_linearMap_trace, traceInner_eq_linearMap_trace]
    rw [hB_lin]
    have h_comp : B_lin.adjoint.comp B_lin = PVperp.comp (T.adjoint.comp B_lin) := by
      refine LinearMap.ext fun x => ?_
      have hPU_x : PUperp (PUperp (T (PVperp x))) = PUperp (T (PVperp x)) := by
        have := LinearMap.congr_fun (starProjection_toLinearMap_idempotent Uᗮ) (T (PVperp x))
        exact this
      calc (B_lin.adjoint.comp B_lin) x
        _ = B_lin.adjoint (B_lin x) := rfl
        _ = (PVperp.comp (T.adjoint.comp PUperp)) (PUperp (T (PVperp x))) := by rw [hB_adj]; rfl
        _ = PVperp (T.adjoint (PUperp (PUperp (T (PVperp x))))) := rfl
        _ = PVperp (T.adjoint (PUperp (T (PVperp x)))) := by rw [hPU_x]
        _ = (PVperp.comp (T.adjoint.comp B_lin)) x := rfl
    rw [h_comp]
    have h_comm : (T.adjoint ∘ₗ B_lin) ∘ₗ PVperp = T.adjoint ∘ₗ B_lin := by
      refine LinearMap.ext fun x => ?_
      have hPV_x : PVperp (PVperp x) = PVperp x := by
        have := LinearMap.congr_fun (starProjection_toLinearMap_idempotent Vᗮ) x
        exact this
      calc ((T.adjoint ∘ₗ B_lin) ∘ₗ PVperp) x
        _ = T.adjoint (PUperp (T (PVperp (PVperp x)))) := rfl
        _ = T.adjoint (PUperp (T (PVperp x))) := by rw [hPV_x]
        _ = (T.adjoint ∘ₗ B_lin) x := rfl
    have h_assoc : PVperp.comp (T.adjoint.comp B_lin) = PVperp ∘ₗ (T.adjoint ∘ₗ B_lin) := rfl
    rw [h_assoc, LinearMap.trace_comp_comm' (T.adjoint ∘ₗ B_lin) PVperp, h_comm]
  have h_frob : frobSq B = 0 := by
    rw [frobSq_eq_traceInner_self, h_inner_eq, h_inner_zero]
  have hB_zero : B = 0 := (frobSq_eq_zero_iff B).mp h_frob
  show B_lin = 0
  rw [← hB_lin, hB_zero, map_zero]

lemma finrank_sup_le {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
    Module.finrank K ↥(s ⊔ t) ≤ Module.finrank K ↥s + Module.finrank K ↥t := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq s t
  omega

lemma range_le_sup_of_comp_zero {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (T : EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁))
    (hB : ((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp
      (T.comp ((Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap)) = 0) :
    LinearMap.range T ≤ U ⊔ Submodule.map (((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp T) V := by
  let PU := (U.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap
  let PUperp := (Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap
  let PV := (V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap
  let PVperp := (Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap
  rintro y ⟨x, rfl⟩
  have hU_add : PU + PUperp = LinearMap.id := by
    refine LinearMap.ext fun z => U.starProjection_add_starProjection_orthogonal z
  have hV_add : PV + PVperp = LinearMap.id := by
    refine LinearMap.ext fun z => V.starProjection_add_starProjection_orthogonal z
  have hx : x = PV x + PVperp x := by
    have := LinearMap.congr_fun hV_add x
    simpa using this.symm
  have hB_x : PUperp (T (PVperp x)) = 0 := by
    have := LinearMap.congr_fun hB x
    exact this
  have hy : T x = PU (T x) + PUperp (T (PV x)) := by
    calc T x = (LinearMap.id.comp T) x := by rw [LinearMap.id_comp]
    _ = ((PU + PUperp).comp T) x := by rw [hU_add]
    _ = PU (T x) + PUperp (T x) := by rfl
    _ = PU (T x) + PUperp (T (PV x + PVperp x)) := by rw [← hx]
    _ = PU (T x) + (PUperp (T (PV x)) + PUperp (T (PVperp x))) := by rw [map_add, map_add]
    _ = PU (T x) + PUperp (T (PV x)) := by rw [hB_x, add_zero]
  rw [hy]
  refine Submodule.add_mem_sup ?_ ?_
  · have : PU (T x) ∈ LinearMap.range PU := LinearMap.mem_range_self _ _
    rw [Submodule.range_starProjection] at this
    exact this
  · refine Submodule.mem_map.mpr ⟨PV x, ?_, rfl⟩
    have : PV x ∈ LinearMap.range PV := LinearMap.mem_range_self _ _
    rw [Submodule.range_starProjection] at this
    exact this

lemma finrank_range_le_two_r {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (r : ℕ) (hU : Module.finrank ℝ U ≤ r) (hV : Module.finrank ℝ V ≤ r)
    (T : EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁))
    (hB : ((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp
      (T.comp ((Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap)) = 0) :
    Module.finrank ℝ (LinearMap.range T) ≤ 2 * r := by
  have h_le := range_le_sup_of_comp_zero U V T hB
  have h_rank := Submodule.finrank_mono h_le
  have h_sup := finrank_sup_le U (Submodule.map (((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp T) V)
  have h_map := Submodule.finrank_map_le (((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp T) V
  omega

lemma sum_sq_singVal_le_trace {d₁ d₂ : ℕ} (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) (k : ℕ) (hk : k ≤ d₂) :
    ∑ j ∈ Finset.range k, (singVal j Θ) ^ 2 ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin Θ).adjoint.comp (Matrix.toEuclideanLin Θ)) := by
  let T := Matrix.toEuclideanLin Θ
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  have h_tr : (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂))) (T.adjoint.comp T) =
      ∑ i : Fin d₂, T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
    have := T.isSymmetric_adjoint_comp_self.trace_eq_sum_eigenvalues hn
    simpa using this
  rw [h_tr]
  let emb : Fin k ↪ Fin d₂ := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  rw [← Fin.sum_univ_eq_sum_range (fun j => (singVal j Θ) ^ 2) k]
  have h_term : ∀ (i : Fin k), (singVal i.val Θ) ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn (emb i) := by
    intro i
    dsimp [singVal, emb]
    exact LinearMap.sq_singularValues_of_lt T hn (lt_of_lt_of_le i.isLt hk)
  simp_rw [h_term]
  rw [← Finset.sum_map]
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => ?_)
  exact T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i

lemma nucNorm_eq_sum_range_min {d₁ d₂ : ℕ} (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) (r : ℕ)
    (hrank : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin Θ)) ≤ 2 * r) :
    nucNorm Θ = ∑ j ∈ Finset.range (min (min d₁ d₂) (2 * r)), singVal j Θ := by
  dsimp [nucNorm]
  let k := min (min d₁ d₂) (2 * r)
  have hk_le : k ≤ min d₁ d₂ := min_le_left _ _
  refine (Finset.sum_subset (Finset.range_mono hk_le) ?_).symm
  intro j hj hj_not
  rw [Finset.mem_range] at hj
  rw [Finset.mem_range] at hj_not
  dsimp [singVal]
  rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
  have hk_def : k = 2 * r := by
    apply le_antisymm (min_le_right _ _)
    by_contra! h
    have : min (min d₁ d₂) (2 * r) = min d₁ d₂ := min_eq_left (by omega)
    omega
  omega

open WainwrightHDS.NucNorm in
theorem solution {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (r : ℕ) (hU : Module.finrank ℝ U ≤ r) (hV : Module.finrank ℝ V ≤ r)
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) (hΘ : Θ ∈ Mbar U V) :
    nucNorm Θ ≤ Real.sqrt (2 * (r : ℝ)) * Real.sqrt (frobSq Θ) := by
  let T := Matrix.toEuclideanLin Θ
  have hB : ((Uᗮ.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap).comp
      (T.comp ((Vᗮ.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap)) = 0 :=
    comp_PVperp_PUperp_eq_zero U V Θ hΘ
  have hrank : Module.finrank ℝ (LinearMap.range T) ≤ 2 * r :=
    finrank_range_le_two_r U V r hU hV T hB
  let k := min (min d₁ d₂) (2 * r)
  have hk_d2 : k ≤ d₂ := by
    dsimp [k]
    have : min d₁ d₂ ≤ d₂ := min_le_right _ _
    exact le_trans (min_le_left _ _) this
  have h_frob : ∑ j ∈ Finset.range k, (singVal j Θ) ^ 2 ≤ frobSq Θ := by
    have h1 := sum_sq_singVal_le_trace Θ k hk_d2
    have h2 := linearMap_trace_adjoint_comp_self Θ
    linarith
  rw [nucNorm_eq_sum_range_min Θ r hrank]
  let s := Finset.range k
  have h_cs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ)) (fun j => singVal j Θ)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h_cs
  have hs_card : (s.card : ℝ) ≤ 2 * (r : ℝ) := by
    dsimp [s, k]
    rw [Finset.card_range]
    have : min (min d₁ d₂) (2 * r) ≤ 2 * r := min_le_right _ _
    exact_mod_cast this
  have h_sqrt1 : Real.sqrt (s.card : ℝ) ≤ Real.sqrt (2 * (r : ℝ)) :=
    Real.sqrt_le_sqrt hs_card
  have h_sqrt2 : Real.sqrt (∑ j ∈ s, singVal j Θ ^ 2) ≤ Real.sqrt (frobSq Θ) :=
    Real.sqrt_le_sqrt h_frob
  refine le_trans h_cs ?_
  refine mul_le_mul h_sqrt1 h_sqrt2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
