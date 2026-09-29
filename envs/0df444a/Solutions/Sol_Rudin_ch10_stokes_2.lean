-- Prove2me | solution 2 for Rudin.ch10_stokes
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T02:52:03.692596+00:00
-- url     : https://prove2.me/submissions/22ff749c-a429-4083-b06b-4fd58d5c67f1

import Mathlib
import Definitions.Def_Rudin_ch10_forms
import Theorems.Thm_Rudin_ch10_pullback_integral
import Theorems.Thm_Rudin_ch10_pullback_extDeriv
import Theorems.Thm_Rudin_ch10_stokes_simplex

open Filter Topology MeasureTheory Set

namespace Rudin


/-- The integral of a form over the boundary of a chain is the sum, over the terms of the chain,
of the integrals over the boundaries of the individual surfaces. -/
lemma chain_integral_boundary_terms {m n : ℕ} (ω : KForm m n)
    (L : List (ℤ × SimplexSurface (m + 1) n)) :
    ((L.flatMap fun t => (surfaceBoundary t.2).terms.map fun s => (t.1 * s.1, s.2)).map
        fun t => (t.1 : ℝ) * integralOverSimplex ω t.2).sum
      = (L.map fun t => (t.1 : ℝ) * Chain.integral ω (surfaceBoundary t.2)).sum := by
  induction L with
  | nil => simp
  | cons t ts ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.map_map, ih, List.sum_cons]
      congr 1
      simp only [Chain.integral, Function.comp_def]
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
      push_cast
      ring

/-- Rudin, Theorem 10.33 (Stokes' theorem) for chains, reduced to the case of a single surface:
given Stokes' formula for every `C''` surface with values in the open set `V`, it holds for every
`(m+1)`-chain of class `C''` in `V`. -/
theorem stokes_of_stokes_surface (m n : ℕ) (V : Set (Fin n → ℝ))
    (stokes_surface : ∀ (Φ : SimplexSurface (m + 1) n), ContDiff ℝ 2 Φ.map →
      (∀ u ∈ stdSimplex (m + 1), Φ.map u ∈ V) → ∀ ω : KForm m n,
        (∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) →
        integralOverSimplex (extDeriv ω) Φ = Chain.integral ω (surfaceBoundary Φ))
    (Ψ : Chain (m + 1) n)
    (hΨ : ∀ t ∈ Ψ.terms, ContDiff ℝ 2 t.2.map ∧ ∀ u ∈ stdSimplex (m + 1), t.2.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Chain.integral (extDeriv ω) Ψ = Chain.integral ω Ψ.boundary := by
  rw [Chain.integral, Chain.integral, Chain.boundary, chain_integral_boundary_terms ω Ψ.terms]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨hsmooth, hmem⟩ := hΨ t ht
  rw [stokes_surface t.2 hsmooth hmem ω hω]



/-! ### The standard simplex -/

lemma isClosed_stdSimplex (k : ℕ) : IsClosed (stdSimplex k) := by
  have h1 : IsClosed {u : Fin k → ℝ | ∀ i, 0 ≤ u i} := by
    have h : {u : Fin k → ℝ | ∀ i, 0 ≤ u i} = ⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i} := by
      ext u; simp
    rw [h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {u : Fin k → ℝ | ∑ i, u i ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (stdSimplex k) :=
  (isClosed_stdSimplex k).measurableSet

lemma isCompact_stdSimplex (k : ℕ) : IsCompact (stdSimplex k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_stdSimplex k, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun u hu => ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  calc u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
    _ ≤ 1 := hu.2

lemma convex_stdSimplex (k : ℕ) : Convex ℝ (stdSimplex k) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hx.1 i
    have h2 := hy.1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

/-! ### Affine simplices -/

/-- An oriented affine simplex, evaluated at a point of `Qᵏ`, is the convex combination of its
vertices with weights `1 - ∑ uᵢ, u₁, …, u_k`. -/
lemma affineSimplexMap_eq_combination {k N : ℕ} (p : Fin (k + 1) → (Fin N → ℝ))
    (u : Fin k → ℝ) :
    affineSimplexMap p u
      = ∑ i : Fin (k + 1), (Fin.cons (1 - ∑ j, u j) u : Fin (k + 1) → ℝ) i • p i := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, affineSimplexMap, smul_sub, sub_smul, one_smul,
    Finset.sum_sub_distrib, Finset.sum_smul]
  abel

/-- An oriented affine simplex maps `Qᵏ` into any convex set containing its vertices. -/
lemma affineSimplexMap_mem_of_convex {k N : ℕ} {S : Set (Fin N → ℝ)} (hS : Convex ℝ S)
    (p : Fin (k + 1) → (Fin N → ℝ)) (hp : ∀ i, p i ∈ S) {u : Fin k → ℝ}
    (hu : u ∈ stdSimplex k) : affineSimplexMap p u ∈ S := by
  rw [affineSimplexMap_eq_combination]
  refine hS.sum_mem (fun i _ => ?_) ?_ fun i _ => hp i
  · refine Fin.cases ?_ ?_ i
    · simpa using hu.2
    · intro j; simpa using hu.1 j
  · rw [Fin.sum_univ_succ]
    simp

lemma stdVertices_mem (k : ℕ) (l : Fin (k + 1)) : stdVertices k l ∈ stdSimplex k := by
  refine Fin.cases ?_ ?_ l
  · exact ⟨fun i => by simp [stdVertices], by simp [stdVertices]⟩
  · intro j
    refine ⟨fun i => ?_, ?_⟩
    · simp only [stdVertices, Fin.cases_succ]
      rcases eq_or_ne i j with rfl | h
      · simp
      · simp [h]
    · simp [stdVertices]

/-- The `j`-th face of the standard simplex maps `Qᵐ` into `Q^{m+1}`. -/
lemma faceMap_mem_stdSimplex {m : ℕ} (j : Fin (m + 2)) {u : Fin m → ℝ}
    (hu : u ∈ stdSimplex m) :
    affineSimplexMap (fun i : Fin (m + 1) => stdVertices (m + 1) (j.succAbove i)) u
      ∈ stdSimplex (m + 1) :=
  affineSimplexMap_mem_of_convex (convex_stdSimplex (m + 1)) _
    (fun _ => stdVertices_mem (m + 1) _) hu

lemma contDiff_affineSimplexMap {k N : ℕ} (p : Fin (k + 1) → (Fin N → ℝ)) :
    ContDiff ℝ 1 (affineSimplexMap p) := by
  unfold affineSimplexMap
  exact contDiff_const.add (ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul contDiff_const)

/-! ### Smoothness of pullbacks -/

lemma contDiff_partialDeriv {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (s : Fin k) :
    ContDiff ℝ 1 (partialDeriv f s) := by
  have h : ContDiff ℝ 1 fun x => fderiv ℝ f x := hf.fderiv_right (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single s (1 : ℝ))).contDiff.comp h

/-- The pullback of a `C'` form along a `C''` map has `C'` coefficients. -/
lemma contDiff_pullback_coeff {k m n : ℕ} {T : (Fin m → ℝ) → (Fin n → ℝ)} (hT : ContDiff ℝ 2 T)
    {ω : KForm k n} (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) (j : Fin k → Fin m) :
    ContDiff ℝ 1 ((pullback T ω).coeff j) := by
  simp only [pullback]
  refine ContDiff.sum fun i _ => ?_
  refine ((hω i).comp (hT.of_le one_le_two)).mul ?_
  exact contDiff_prod fun r _ =>
    contDiff_partialDeriv ((contDiff_apply ℝ ℝ (i r)).comp hT) (j r)

/-! ### A smooth cut-off -/

/-- A smooth function equal to `1` on a neighbourhood of a compact set `K` and vanishing on a
neighbourhood of the complement of an open set `V ⊇ K`. -/
lemma exists_cutoff {n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ (χ : (Fin n → ℝ) → ℝ) (U W : Set (Fin n → ℝ)), ContDiff ℝ 1 χ ∧
      IsOpen U ∧ K ⊆ U ∧ (∀ x ∈ U, χ x = 1) ∧
      IsOpen W ∧ Vᶜ ⊆ W ∧ (∀ x ∈ W, χ x = 0) := by
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (n := ⊤)
      (modelWithCornersSelf ℝ (Fin n → ℝ)) (s := (interior L)ᶜ) (t := K)
      isOpen_interior.isClosed_compl hK.isClosed
      (by rw [Set.disjoint_compl_left_iff_subset]; exact hKL)
  obtain ⟨U, hU, hKU, hU1⟩ := eventually_nhdsSet_iff_exists.1 hf1
  obtain ⟨W, hW, hsW, hW0⟩ := eventually_nhdsSet_iff_exists.1 hf0
  refine ⟨f, U, W, ?_, hU, hKU, hU1, hW, ?_, hW0⟩
  · exact (contMDiff_iff_contDiff.1 f.contMDiff).of_le (by simp)
  · exact fun x hx => hsW fun hxi => hx (hLV (interior_subset hxi))

/-- A form whose coefficients are `C'` on an open set `V` agrees, on a neighbourhood of any
compact `K ⊆ V`, with a form whose coefficients are `C'` on all of `ℝⁿ`. -/
lemma exists_globalForm {k n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKV : K ⊆ V) (ω : KForm k n)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    ∃ (ω' : KForm k n) (U : Set (Fin n → ℝ)), (∀ i, ContDiff ℝ 1 (ω'.coeff i)) ∧
      IsOpen U ∧ K ⊆ U ∧ ∀ i, ∀ x ∈ U, ω'.coeff i x = ω.coeff i x := by
  obtain ⟨χ, U, W, hχ, hU, hKU, hU1, hW, hVW, hW0⟩ := exists_cutoff hV hK hKV
  refine ⟨⟨fun i x => χ x * ω.coeff i x⟩, U, fun i => ?_, hU, hKU, fun i x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ V
    · exact hχ.contDiffAt.mul ((hω i).contDiffAt (hV.mem_nhds hx))
    · refine ContDiffAt.congr_of_eventuallyEq (f := fun _ => (0 : ℝ)) contDiffAt_const ?_
      filter_upwards [hW.mem_nhds (hVW hx)] with y hy
      simp [hW0 y hy]
  · simp [hU1 x hx]

/-- Replacing a form by one with the same values near a set does not change the exterior
derivative there. -/
lemma extDeriv_coeff_congr {k n : ℕ} {ω ω' : KForm k n} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (h : ∀ i, ∀ x ∈ U, ω'.coeff i x = ω.coeff i x) :
    ∀ i, ∀ x ∈ U, (extDeriv ω').coeff i x = (extDeriv ω).coeff i x := by
  intro i x hx
  have hev : (ω'.coeff fun r : Fin k => i r.succ) =ᶠ[𝓝 x] (ω.coeff fun r : Fin k => i r.succ) :=
    eventually_of_mem (hU.mem_nhds hx) fun y hy => h _ y hy
  simp only [extDeriv]
  rw [hev.fderiv_eq]

/-- Two forms with the same coefficients on the image of a surface have the same integral over
that surface. -/
lemma integralOverSimplex_congr {k n : ℕ} {ω ω' : KForm k n} (Φ : SimplexSurface k n)
    (h : ∀ i, ∀ u ∈ stdSimplex k, ω'.coeff i (Φ.map u) = ω.coeff i (Φ.map u)) :
    integralOverSimplex ω' Φ = integralOverSimplex ω Φ := by
  refine setIntegral_congr_fun (measurableSet_stdSimplex k) fun u hu => ?_
  exact Finset.sum_congr rfl fun i _ => by rw [h i u hu]

/-! ### Stokes' formula for a single surface -/

/-- Stokes' formula for a single surface, for a form with globally `C'` coefficients, deduced
from Rudin's Theorems 10.22(c) and 10.25 and Stokes' formula on the identity simplex. -/
theorem stokes_surface_of_contDiff {m n : ℕ}
    (pullback_integral : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 1 T →
      ∀ (ν : KForm k n') (S : SimplexSurface k m'), ContDiff ℝ 1 S.map →
        integralOverSimplex ν ⟨T ∘ S.map⟩ = integralOverSimplex (pullback T ν) S)
    (pullback_extDeriv : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 2 T →
      ∀ ν : KForm k n', (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
        ∀ S : SimplexSurface (k + 1) m', ContDiff ℝ 1 S.map →
          integralOverSimplex (pullback T (extDeriv ν)) S
            = integralOverSimplex (extDeriv (pullback T ν)) S)
    (stokes_simplex : ∀ (k : ℕ) (ν : KForm k (k + 1)), (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
      integralOverSimplex (extDeriv ν) ⟨id⟩ = Chain.integral ν (surfaceBoundary ⟨id⟩))
    (Φ : SimplexSurface (m + 1) n) (hΦ : ContDiff ℝ 2 Φ.map) (ω : KForm m n)
    (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    integralOverSimplex (extDeriv ω) Φ = Chain.integral ω (surfaceBoundary Φ) := by
  have hΦ1 : ContDiff ℝ 1 Φ.map := hΦ.of_le one_le_two
  have e1 : integralOverSimplex (extDeriv ω) Φ
      = integralOverSimplex (pullback Φ.map (extDeriv ω)) ⟨id⟩ :=
    pullback_integral (m + 1) (m + 1) n Φ.map hΦ1 (extDeriv ω) ⟨id⟩ contDiff_id
  have e2 : integralOverSimplex (pullback Φ.map (extDeriv ω)) ⟨id⟩
      = integralOverSimplex (extDeriv (pullback Φ.map ω)) ⟨id⟩ :=
    pullback_extDeriv m (m + 1) n Φ.map hΦ ω hω ⟨id⟩ contDiff_id
  have e3 : integralOverSimplex (extDeriv (pullback Φ.map ω)) ⟨id⟩
      = Chain.integral (pullback Φ.map ω) (surfaceBoundary ⟨id⟩) :=
    stokes_simplex m (pullback Φ.map ω) (contDiff_pullback_coeff hΦ hω)
  have e4 : Chain.integral (pullback Φ.map ω) (surfaceBoundary ⟨id⟩)
      = Chain.integral ω (surfaceBoundary Φ) := by
    simp only [Chain.integral, surfaceBoundary, List.map_ofFn, Function.comp_def]
    refine congrArg List.sum (congrArg (List.ofFn) (funext fun j => ?_))
    have hface : integralOverSimplex ω (boundaryFace Φ.map j)
        = integralOverSimplex (pullback Φ.map ω)
            (boundaryFace (id : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) j) :=
      pullback_integral m (m + 1) n Φ.map hΦ1 ω
        ⟨affineSimplexMap fun i : Fin (m + 1) => stdVertices (m + 1) (j.succAbove i)⟩
        (contDiff_affineSimplexMap fun i : Fin (m + 1) => stdVertices (m + 1) (j.succAbove i))
    rw [hface]
  rw [e1, e2, e3, e4]

/-- Stokes' formula for a single surface with values in an open set `V`, for a form whose
coefficients are only assumed `C'` on `V`: a smooth cut-off reduces it to the previous
statement. -/
theorem stokes_surface_of_contDiffOn {m n : ℕ}
    (pullback_integral : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 1 T →
      ∀ (ν : KForm k n') (S : SimplexSurface k m'), ContDiff ℝ 1 S.map →
        integralOverSimplex ν ⟨T ∘ S.map⟩ = integralOverSimplex (pullback T ν) S)
    (pullback_extDeriv : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 2 T →
      ∀ ν : KForm k n', (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
        ∀ S : SimplexSurface (k + 1) m', ContDiff ℝ 1 S.map →
          integralOverSimplex (pullback T (extDeriv ν)) S
            = integralOverSimplex (extDeriv (pullback T ν)) S)
    (stokes_simplex : ∀ (k : ℕ) (ν : KForm k (k + 1)), (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
      integralOverSimplex (extDeriv ν) ⟨id⟩ = Chain.integral ν (surfaceBoundary ⟨id⟩))
    (V : Set (Fin n → ℝ)) (hV : IsOpen V) (Φ : SimplexSurface (m + 1) n)
    (hΦ : ContDiff ℝ 2 Φ.map) (hΦV : ∀ u ∈ stdSimplex (m + 1), Φ.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    integralOverSimplex (extDeriv ω) Φ = Chain.integral ω (surfaceBoundary Φ) := by
  have hK : IsCompact (Φ.map '' stdSimplex (m + 1)) :=
    (isCompact_stdSimplex (m + 1)).image (hΦ.continuous)
  have hKV : Φ.map '' stdSimplex (m + 1) ⊆ V := by
    rintro _ ⟨u, hu, rfl⟩
    exact hΦV u hu
  obtain ⟨ω', U, hω', hU, hKU, hUeq⟩ := exists_globalForm hV hK hKV ω hω
  have hmemU : ∀ u ∈ stdSimplex (m + 1), Φ.map u ∈ U := fun u hu => hKU ⟨u, hu, rfl⟩
  have hleft : integralOverSimplex (extDeriv ω') Φ = integralOverSimplex (extDeriv ω) Φ :=
    integralOverSimplex_congr Φ fun i u hu =>
      extDeriv_coeff_congr hU hUeq i (Φ.map u) (hmemU u hu)
  have hright : Chain.integral ω' (surfaceBoundary Φ) = Chain.integral ω (surfaceBoundary Φ) := by
    simp only [Chain.integral, surfaceBoundary, List.map_ofFn, Function.comp_def]
    refine congrArg List.sum (congrArg (List.ofFn) (funext fun j => ?_))
    have : integralOverSimplex ω' (boundaryFace Φ.map j)
        = integralOverSimplex ω (boundaryFace Φ.map j) := by
      refine integralOverSimplex_congr _ fun i u hu => ?_
      exact hUeq i _ (hmemU _ (faceMap_mem_stdSimplex j hu))
    rw [this]
  rw [← hleft, ← hright]
  exact stokes_surface_of_contDiff pullback_integral pullback_extDeriv stokes_simplex Φ hΦ ω' hω'

/-- Rudin, Theorem 10.33 (Stokes' theorem) for chains, reduced to Rudin's Theorems 10.22(c) and
10.25 together with Stokes' formula on the standard simplex. -/
theorem stokes_of_stokes_simplex
    (pullback_integral : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 1 T →
      ∀ (ν : KForm k n') (S : SimplexSurface k m'), ContDiff ℝ 1 S.map →
        integralOverSimplex ν ⟨T ∘ S.map⟩ = integralOverSimplex (pullback T ν) S)
    (pullback_extDeriv : ∀ (k m' n' : ℕ) (T : (Fin m' → ℝ) → (Fin n' → ℝ)), ContDiff ℝ 2 T →
      ∀ ν : KForm k n', (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
        ∀ S : SimplexSurface (k + 1) m', ContDiff ℝ 1 S.map →
          integralOverSimplex (pullback T (extDeriv ν)) S
            = integralOverSimplex (extDeriv (pullback T ν)) S)
    (stokes_simplex : ∀ (k : ℕ) (ν : KForm k (k + 1)), (∀ i, ContDiff ℝ 1 (ν.coeff i)) →
      integralOverSimplex (extDeriv ν) ⟨id⟩ = Chain.integral ν (surfaceBoundary ⟨id⟩))
    (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V) (Ψ : Chain (m + 1) n)
    (hΨ : ∀ t ∈ Ψ.terms, ContDiff ℝ 2 t.2.map ∧ ∀ u ∈ stdSimplex (m + 1), t.2.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Chain.integral (extDeriv ω) Ψ = Chain.integral ω Ψ.boundary :=
  stokes_of_stokes_surface m n V
    (fun Φ hΦ hΦV ν hν => stokes_surface_of_contDiffOn pullback_integral pullback_extDeriv
      stokes_simplex V hV Φ hΦ hΦV ν hν) Ψ hΨ ω hω


end Rudin

/-- Rudin, Theorem 10.33 (Stokes' theorem) for chains. -/
theorem solution (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V) (Ψ : Rudin.Chain (m + 1) n)
    (hΨ : ∀ t ∈ Ψ.terms, ContDiff ℝ 2 t.2.map ∧
      ∀ u ∈ Rudin.stdSimplex (m + 1), t.2.map u ∈ V)
    (ω : Rudin.KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Rudin.Chain.integral (Rudin.extDeriv ω) Ψ = Rudin.Chain.integral ω Ψ.boundary :=
  Rudin.stokes_of_stokes_simplex
    (fun k m' n' T hT ν S hS => Rudin.ch10_pullback_integral k m' n' T hT ν S hS)
    (fun k m' n' T hT ν hν S hS => Rudin.ch10_pullback_extDeriv k m' n' T hT ν hν S hS)
    (fun k ν hν => Rudin.ch10_stokes_simplex k ν hν)
    m n V hV Ψ hΨ ω hω
