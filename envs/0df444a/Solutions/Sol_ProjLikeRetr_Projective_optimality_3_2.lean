-- Prove2me | solution 1 for ProjLikeRetr.Projective.optimality_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:34:39.628693+00:00
-- url     : https://prove2.me/submissions/e72dc0a6-ca99-4750-9eac-f43b5e41480c

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

set_option autoImplicit false

open RandomGradFree.Nonsmooth

open Filter Topology in
theorem P2M0c1c1cfb_key {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (x p : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M p) (hp : IsMetricProjection M x p)
    (v : E) (hv : v ∈ tangentConeAt ℝ M p) : inner ℝ (x - p) v = 0 := by
  obtain ⟨-, hpM, φ, hpS, hφ, hψ, hslice⟩ := hM
  have hk1 : ((k : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hSn : φ.source ∈ 𝓝 p := φ.open_source.mem_nhds hpS
  have hpT : φ p ∈ φ.target := φ.map_source hpS
  have hTn : φ.target ∈ 𝓝 (φ p) := φ.open_target.mem_nhds hpT
  have hφd : DifferentiableAt ℝ φ p := (hφ.differentiableOn hk1).differentiableAt hSn
  have hψd : DifferentiableAt ℝ φ.symm (φ p) := (hψ.differentiableOn hk1).differentiableAt hTn
  set A := fderiv ℝ φ p with hA
  set B := fderiv ℝ φ.symm (φ p) with hB
  have hsl : ∀ y, y ∈ M ∩ φ.source ↔
      (y ∈ φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ y i = 0) := by
    intro y; rw [hslice]; rfl
  have hpφ : ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ p i = 0 := ((hsl p).1 ⟨hpM, hpS⟩).2
  -- B ∘ A = id
  have hBA : ∀ u, B (A u) = u := by
    have h1 : HasFDerivAt (φ.symm ∘ φ) (B.comp A) p := hψd.hasFDerivAt.comp p hφd.hasFDerivAt
    have h2 : HasFDerivAt (φ.symm ∘ φ) (ContinuousLinearMap.id ℝ E) p :=
      (hasFDerivAt_id p).congr_of_eventuallyEq (by
        filter_upwards [φ.eventually_left_inverse hpS] with y hy
        exact hy)
    have h3 := h1.unique h2
    intro u
    have := congrArg (fun L : E →L[ℝ] E => L u) h3
    simpa using this
  -- A v lies in the slice
  have hAv : ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → (A v) i = 0 := by
    intro i hi
    have hg : HasFDerivAt (fun y => (EuclideanSpace.proj i : _ →L[ℝ] ℝ) (φ y))
        ((EuclideanSpace.proj i : _ →L[ℝ] ℝ).comp A) p :=
      (EuclideanSpace.proj i : _ →L[ℝ] ℝ).hasFDerivAt.comp p hφd.hasFDerivAt
    have hg0 : HasFDerivWithinAt (fun y => (EuclideanSpace.proj i : _ →L[ℝ] ℝ) (φ y))
        (0 : E →L[ℝ] ℝ) (M ∩ φ.source) p := by
      refine (hasFDerivWithinAt_const (0 : ℝ) p (M ∩ φ.source)).congr ?_ ?_
      · intro y hy
        have := ((hsl y).1 hy).2 i hi
        simpa using this
      · simpa using hpφ i hi
    have hv' : v ∈ tangentConeAt ℝ (M ∩ φ.source) p := by
      rw [tangentConeAt_inter_nhds hSn]; exact hv
    have := hg.hasFDerivWithinAt.unique_on hg0 hv'
    simpa using this
  -- the curve
  set w := A v with hw
  let c : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun t => φ p + t • w
  have hc0 : c 0 = φ p := by simp [c]
  have hcd : HasDerivAt c w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (φ p)
    simpa [c] using this
  have hct : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ φ.target := by
    have hcont : Continuous c := by fun_prop
    have := hcont.tendsto 0
    rw [hc0] at this
    exact this hTn
  have hγ : HasDerivAt (φ.symm ∘ c) (B w) 0 :=
    hψd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcd hc0.symm
  have hγ0 : (φ.symm ∘ c) 0 = p := by
    simp only [Function.comp, hc0]; exact φ.left_inv hpS
  have hmin : IsLocalMin (fun t => ‖x - (φ.symm ∘ c) t‖ ^ 2) 0 := by
    filter_upwards [hct] with t ht
    have hs : φ.symm (c t) ∈ φ.source := φ.map_target ht
    have hr : φ (φ.symm (c t)) = c t := φ.right_inv ht
    have hmem : φ.symm (c t) ∈ M ∩ φ.source := by
      refine (hsl _).2 ⟨hs, ?_⟩
      intro i hi
      rw [hr]
      simp [c, hpφ i hi, hAv i hi]
    have := hp.2 _ hmem.1
    rw [hγ0]
    simp only [Function.comp]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hd := (hγ.const_sub x).norm_sq
  have h0 := hmin.hasDerivAt_eq_zero hd
  rw [hγ0, hBA] at h0
  rw [inner_neg_right] at h0
  linarith

open RandomGradFree.Nonsmooth in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (x p : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M p) (hp : IsMetricProjection M x p) :
    p ∈ M ∧ x - p ∈ ProjLikeRetr.Retractor.normalSpace M p := by
  refine ⟨hp.1, ?_⟩
  unfold ProjLikeRetr.Retractor.normalSpace ProjLikeRetr.Retractor.tangentSpace
  rw [Submodule.mem_orthogonal']
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv => exact P2M0c1c1cfb_key k d hk M x p hM hp v hv
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
  | smul r a _ ha => rw [inner_smul_right, ha, mul_zero]
