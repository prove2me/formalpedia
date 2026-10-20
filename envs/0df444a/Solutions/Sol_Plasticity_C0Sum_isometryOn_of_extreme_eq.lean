-- Prove2me | solution 1 for Plasticity.C0Sum.isometryOn_of_extreme_eq
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:06.769429+00:00
-- url     : https://prove2.me/submissions/8a2571b0-becc-43a2-b3a5-37de121cc8b4

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero
import Theorems.Thm_Plasticity_C0Sum_isometryOn_of_support

open Plasticity

namespace Sol_Plasticity_C0Sum_isometryOn_of_extreme_eq

variable {ι κ : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {E' : κ → Type*} [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]

/-- Reindex the blocks of `y` along `σ` and transport them back to `E` by `(L i).symm`. -/
def pullFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : ∀ k, E' k) : ∀ i, E i :=
  fun i => (L i).symm (y (σ i))

lemma norm_pullFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : ∀ k, E' k) (i : ι) :
    ‖pullFun σ L y i‖ = ‖y (σ i)‖ :=
  (L i).symm.norm_map _

lemma memℓp_pullFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : lp E' ⊤) :
    Memℓp (pullFun σ L ⇑y) ⊤ := by
  refine memℓp_infty ⟨‖y‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  show ‖pullFun σ L ⇑y i‖ ≤ ‖y‖
  rw [norm_pullFun]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ _

lemma mem_c0Sum_pullFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : c0Sum E') :
    (⟨pullFun σ L ⇑(y : lp E' ⊤), memℓp_pullFun σ L y⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun i => ‖pullFun σ L ⇑(y : lp E' ⊤) i‖) Filter.cofinite (nhds 0)
  simp only [norm_pullFun]
  have hy : Filter.Tendsto (fun k => ‖(y : lp E' ⊤) k‖) Filter.cofinite (nhds 0) := y.2
  exact hy.comp σ.injective.tendsto_cofinite

/-- The block-diagonal reindexing map `c0Sum E' → c0Sum E`. -/
def pull (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : c0Sum E') : c0Sum E :=
  ⟨⟨pullFun σ L ⇑(y : lp E' ⊤), memℓp_pullFun σ L y⟩, mem_c0Sum_pullFun σ L y⟩

lemma pull_apply (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : c0Sum E') (i : ι) :
    ((pull σ L y : c0Sum E) : lp E ⊤) i = (L i).symm ((y : lp E' ⊤) (σ i)) := rfl

/-- `pull` as a linear isometry. -/
def pullLI (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) : c0Sum E' →ₗᵢ[ℝ] c0Sum E where
  toFun := pull σ L
  map_add' y z := by
    apply Subtype.ext; apply lp.ext; funext i
    simp [pull_apply]
  map_smul' c y := by
    apply Subtype.ext; apply lp.ext; funext i
    simp [pull_apply]
  norm_map' y := by
    show ‖pull σ L y‖ = ‖y‖
    rw [Submodule.coe_norm, Submodule.coe_norm, lp.norm_eq_ciSup, lp.norm_eq_ciSup]
    simp_rw [pull_apply, LinearIsometryEquiv.norm_map]
    exact σ.iSup_comp (g := fun k => ‖(y : lp E' ⊤) k‖)

/-- The forward reindexing of blocks: `pushFun x (σ i) = L i (x i)`. -/
def pushFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : ∀ i, E i) : ∀ k, E' k :=
  Equiv.piCongrLeft E' σ (fun i => L i (x i))

lemma pushFun_apply (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : ∀ i, E i) (i : ι) :
    pushFun σ L x (σ i) = L i (x i) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

lemma norm_pushFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : ∀ i, E i) :
    (fun k => ‖pushFun σ L x k‖) = fun k => ‖x (σ.symm k)‖ := by
  funext k
  obtain ⟨i, rfl⟩ := σ.surjective k
  rw [pushFun_apply, LinearIsometryEquiv.norm_map, Equiv.symm_apply_apply]

lemma memℓp_pushFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : lp E ⊤) :
    Memℓp (pushFun σ L ⇑x) ⊤ := by
  refine memℓp_infty ⟨‖x‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  show ‖pushFun σ L ⇑x k‖ ≤ ‖x‖
  rw [show ‖pushFun σ L ⇑x k‖ = ‖x (σ.symm k)‖ from congrFun (norm_pushFun σ L ⇑x) k]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ _

lemma mem_c0Sum_pushFun (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : c0Sum E) :
    (⟨pushFun σ L ⇑(x : lp E ⊤), memℓp_pushFun σ L x⟩ : lp E' ⊤) ∈ c0Sum E' := by
  show Filter.Tendsto (fun k => ‖pushFun σ L ⇑(x : lp E ⊤) k‖) Filter.cofinite (nhds 0)
  rw [norm_pushFun]
  have hx : Filter.Tendsto (fun i => ‖(x : lp E ⊤) i‖) Filter.cofinite (nhds 0) := x.2
  exact hx.comp σ.symm.injective.tendsto_cofinite

/-- The block-diagonal reindexing map `c0Sum E → c0Sum E'`. -/
def push (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : c0Sum E) : c0Sum E' :=
  ⟨⟨pushFun σ L ⇑(x : lp E ⊤), memℓp_pushFun σ L x⟩, mem_c0Sum_pushFun σ L x⟩

lemma pull_push (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (x : c0Sum E) :
    pull σ L (push σ L x) = x := by
  apply Subtype.ext; apply lp.ext; funext i
  show (L i).symm (pushFun σ L ⇑(x : lp E ⊤) (σ i)) = (x : lp E ⊤) i
  rw [pushFun_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The block-diagonal linear isometry equivalence `c0Sum E' ≃ c0Sum E`. -/
noncomputable def pullEquiv (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) :
    c0Sum E' ≃ₗᵢ[ℝ] c0Sum E :=
  LinearIsometryEquiv.ofSurjective (pullLI σ L) (fun x => ⟨push σ L x, pull_push σ L x⟩)

lemma pullEquiv_apply (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i)) (y : c0Sum E') (i : ι) :
    ((pullEquiv σ L y : c0Sum E) : lp E ⊤) i = (L i).symm ((y : lp E' ⊤) (σ i)) := rfl

/-- A linear isometry equivalence maps the closed unit ball bijectively onto the closed unit
ball. -/
lemma bijOn_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (Ψ : V ≃ₗᵢ[ℝ] W) :
    Set.BijOn Ψ (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  have h := (Ψ.injective.injOn (s := Metric.closedBall 0 1)).bijOn_image
  rwa [LinearIsometryEquiv.image_closedBall, map_zero] at h

/-- Linear isometry equivalences map extreme points of the unit ball to extreme points. -/
lemma map_mem_extremePoints {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (Ψ : V ≃ₗᵢ[ℝ] W) {v : V}
    (hv : v ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) :
    Ψ v ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1) := by
  have h := image_extremePoints (𝕜 := ℝ) Ψ.toLinearEquiv (Metric.closedBall (0 : V) 1)
  have himg : (Ψ.toLinearEquiv : V → W) '' Metric.closedBall (0 : V) 1 =
      Metric.closedBall (0 : W) 1 := by
    have := Ψ.image_closedBall 0 1
    rwa [map_zero] at this
  rw [himg] at h
  rw [← h]
  exact ⟨v, hv, rfl⟩

end Sol_Plasticity_C0Sum_isometryOn_of_extreme_eq

open Sol_Plasticity_C0Sum_isometryOn_of_extreme_eq in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (σ : ι ≃ κ) (L : ∀ i, E i ≃ₗᵢ[ℝ] E' (σ i))
    (hnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖)
    (hext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (F x : lp E' ⊤) (σ i) ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) →
        L i ((x : lp E ⊤) i) = (F x : lp E' ⊤) (σ i)) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by
  have : ∀ i, FiniteDimensional ℝ (E i) := fun i =>
    Module.finite_of_finrank_pos (by rcases hE i with h | ⟨h, -⟩ <;> omega)
  set Ψ := pullEquiv σ L with hΨ
  set G : c0Sum E → c0Sum E := fun x => Ψ (F x) with hG
  have hGapply : ∀ x i, ((G x : c0Sum E) : lp E ⊤) i = (L i).symm ((F x : lp E' ⊤) (σ i)) :=
    fun x i => rfl
  have hGbij : Set.BijOn G (Metric.closedBall 0 1) (Metric.closedBall 0 1) :=
    (bijOn_closedBall Ψ).comp hbij
  have hGlip : LipschitzOnWith 1 G (Metric.closedBall 0 1) := by
    have h := Ψ.lipschitz.comp_lipschitzOnWith hlip
    rw [one_mul] at h
    exact h
  have hGnorm : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      ‖(G x : lp E ⊤) i‖ ≤ ‖(x : lp E ⊤) i‖ := by
    intro x hx i
    rw [hGapply, LinearIsometryEquiv.norm_map]
    exact hnorm x hx i
  have hGext : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (G x : lp E ⊤) i ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1) →
        (x : lp E ⊤) i = (G x : lp E ⊤) i := by
    intro x hx i hi
    have h1 : (F x : lp E' ⊤) (σ i) ∈
        Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) := by
      have := map_mem_extremePoints (L i) hi
      rwa [hGapply, LinearIsometryEquiv.apply_symm_apply] at this
    rw [hGapply, ← hext x hx i h1, LinearIsometryEquiv.symm_apply_apply]
  have hsupp : ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
      (G x : lp E ⊤) i = 0 ↔ (x : lp E ⊤) i = 0 := by
    intro x hx i
    refine ⟨Plasticity.C0Sum.eq_zero_of_map_eq_zero E hE G hGbij hGlip hGnorm hGext x hx i,
      fun h => ?_⟩
    have := hGnorm x hx i
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hiso := Plasticity.C0Sum.isometryOn_of_support E G hGbij hGlip hsupp
  intro x hx y hy
  rw [← hiso x hx y hy]
  show ‖F x - F y‖ = ‖Ψ (F x) - Ψ (F y)‖
  rw [← map_sub, LinearIsometryEquiv.norm_map]
