-- Prove2me | solution 1 for SupplyCorr.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T12:21:15.716194+00:00
-- url     : https://prove2.me/submissions/35f583a1-0b67-40df-8230-8f42b71a74e0

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

set_option autoImplicit false

namespace SupplyCorrAux

open SupplyCorr

/-- Euclidean projection onto a nonempty closed convex subset of `Fin N → ℝ`
(variational form, with the dot product). -/
lemma proj_exists {N : ℕ} (Y : Set (Fin N → ℝ)) (hne : Y.Nonempty) (hc : Convex ℝ Y)
    (hcl : IsClosed Y) (x : Fin N → ℝ) : ∃ z ∈ Y, ∀ w ∈ Y, (x - z) ⬝ᵥ (w - z) ≤ 0 := by
  let L : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] (Fin N → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).toLinearMap
  have hL : ∀ v, L v = WithLp.ofLp v := fun v => rfl
  let K : Set (EuclideanSpace ℝ (Fin N)) := L ⁻¹' Y
  have hKne : K.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨WithLp.toLp 2 w, by simpa [K, hL] using hw⟩
  have hKc : Convex ℝ K := hc.linear_preimage L
  have hKcl : IsClosed K := by
    have hcont : Continuous L := L.continuous_of_finiteDimensional
    exact hcl.preimage hcont
  obtain ⟨v, hvK, hv⟩ :=
    exists_norm_eq_iInf_of_complete_convex hKne hKcl.isComplete hKc (WithLp.toLp 2 x)
  have key := (norm_eq_iInf_iff_real_inner_le_zero hKc hvK).1 hv
  refine ⟨WithLp.ofLp v, hvK, fun w hw => ?_⟩
  have h1 := key (WithLp.toLp 2 w) (by simpa [K, hL] using hw)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
  simp only [star_trivial, WithLp.ofLp_sub] at h1
  rw [dotProduct_comm]
  exact h1

lemma optSet_mono {N : ℕ} (Y : Set (Fin N → ℝ)) :
    IsMonotoneSet (graph (optSet Y)) := by
  rintro ⟨z, p⟩ ⟨hz, hzp⟩ ⟨z', p'⟩ ⟨hz', hzp'⟩
  have h1 := hzp z' hz'
  have h2 := hzp' z hz
  simp only [sub_dotProduct, dotProduct_sub] at *
  have e1 : z ⬝ᵥ p = p ⬝ᵥ z := dotProduct_comm _ _
  have e2 : z' ⬝ᵥ p = p ⬝ᵥ z' := dotProduct_comm _ _
  have e3 : z ⬝ᵥ p' = p' ⬝ᵥ z := dotProduct_comm _ _
  have e4 : z' ⬝ᵥ p' = p' ⬝ᵥ z' := dotProduct_comm _ _
  linarith

lemma optSet_maxmono {N : ℕ} (Y : Set (Fin N → ℝ)) (hne : Y.Nonempty) (hc : Convex ℝ Y)
    (hcl : IsClosed Y) : IsMaximalMonotone (optSet Y) := by
  refine ⟨optSet_mono Y, fun G' hG' hsub => ?_⟩
  refine Set.Subset.antisymm (fun q hq => ?_) hsub
  obtain ⟨z0, p0⟩ := q
  obtain ⟨z, hzY, hz⟩ := proj_exists Y hne hc hcl (z0 + p0)
  have hzopt : z ∈ optSet Y (z0 + p0 - z) := by
    refine ⟨hzY, fun w hw => ?_⟩
    have := hz w hw
    rw [dotProduct_sub] at this
    linarith
  have hmem : ((z, z0 + p0 - z) : (Fin N → ℝ) × (Fin N → ℝ)) ∈ G' := hsub hzopt
  have hm := hG' _ hq _ hmem
  simp only at hm
  have hpe : p0 - (z0 + p0 - z) = -(z0 - z) := by abel
  rw [hpe, dotProduct_neg] at hm
  have hnn : 0 ≤ (z0 - z) ⬝ᵥ (z0 - z) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((z0 - z) i))
  have hsq : (z0 - z) ⬝ᵥ (z0 - z) = 0 := le_antisymm (by linarith) hnn
  have hzz : z0 - z = 0 := dotProduct_self_eq_zero.1 hsq
  have hz0 : z0 = z := sub_eq_zero.1 hzz
  subst hz0
  show z0 ∈ optSet Y p0
  have : z0 + p0 - z0 = p0 := by abel
  rw [this] at hzopt
  exact hzopt

lemma dot_continuous {N : ℕ} (p : Fin N → ℝ) : Continuous fun w : Fin N → ℝ => p ⬝ᵥ w := by
  unfold dotProduct
  fun_prop

lemma halfspace_closed {N : ℕ} (p : Fin N → ℝ) (c : ℝ) :
    IsClosed {w : Fin N → ℝ | p ⬝ᵥ w ≤ c} :=
  isClosed_le (dot_continuous p) continuous_const

lemma halfspace_convex {N : ℕ} (p : Fin N → ℝ) (c : ℝ) :
    Convex ℝ {w : Fin N → ℝ | p ⬝ᵥ w ≤ c} := by
  apply convex_halfSpace_le
  exact ⟨fun x y => dotProduct_add p x y, fun t x => dotProduct_smul t p x⟩

/-- Homogeneity plus monotonicity: each graph point is optimal against the whole image. -/
lemma opt_against_image {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hmon : IsMonotoneSet (graph y)) (hhom : IsHomogeneousZero y)
    (z p z' p' : Fin N → ℝ) (hz : z ∈ y p) (hz' : z' ∈ y p') : p' ⬝ᵥ z ≤ p' ⬝ᵥ z' := by
  by_contra hlt
  rw [not_le] at hlt
  set c := p' ⬝ᵥ z - p' ⬝ᵥ z' with hcdef
  have hc : 0 < c := by linarith
  set a := (z - z') ⬝ᵥ p with hadef
  set t : ℝ := c / (2 * (|a| + 1)) with htdef
  have hpos : 0 < 2 * (|a| + 1) := by positivity
  have ht : 0 < t := div_pos hc hpos
  have hzt : z ∈ y (t • p) := by rw [hhom p t ht]; exact hz
  have hm := hmon (z, t • p) hzt (z', p') hz'
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hm
  have hc2 : (z - z') ⬝ᵥ p' = c := by
    rw [hcdef, sub_dotProduct, dotProduct_comm z p', dotProduct_comm z' p']
  rw [hc2] at hm
  have hta : t * a ≤ c / 2 := by
    have h1 : t * a ≤ t * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) ht.le
    have h2 : t * |a| ≤ t * (|a| + 1) := by nlinarith
    have h3 : t * (|a| + 1) = c / 2 := by
      rw [htdef]; field_simp
    linarith
  have : (z - z') ⬝ᵥ (t • p) = t * a := by rw [dotProduct_smul, smul_eq_mul]
  linarith

theorem main {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) :
    IsStronglyRationalizable y ↔ IsMaximalMonotone y ∧ IsHomogeneousZero y := by
  constructor
  · rintro ⟨Y, hne, hc, hcl, hy⟩
    have hyeq : y = optSet Y := funext hy
    subst hyeq
    refine ⟨optSet_maxmono Y hne hc hcl, fun p t ht => ?_⟩
    ext z
    simp only [optSet, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun w hw => le_of_mul_le_mul_left (h w hw) ht⟩
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun w hw => mul_le_mul_of_nonneg_left (h w hw) ht.le⟩
  · rintro ⟨⟨hmon, hmax⟩, hhom⟩
    -- image is nonempty
    have hIne : (image y).Nonempty := by
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      have hg : graph y = ∅ := by
        ext ⟨z, p⟩
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h
        have : z ∈ image y := ⟨p, h⟩
        rw [hE] at this
        exact this
      have hmon0 : IsMonotoneSet ({(0, 0)} : Set ((Fin N → ℝ) × (Fin N → ℝ))) := by
        intro a ha b hb
        rw [Set.mem_singleton_iff] at ha hb
        subst ha; subst hb
        simp
      have := hmax {(0, 0)} hmon0 (by rw [hg]; exact Set.empty_subset _)
      rw [hg] at this
      exact Set.singleton_ne_empty _ this
    set Y := closure (convexHull ℝ (image y)) with hYdef
    have hYc : Convex ℝ Y := (convex_convexHull ℝ _).closure
    have hYcl : IsClosed Y := isClosed_closure
    have hIY : image y ⊆ Y := (subset_convexHull ℝ _).trans subset_closure
    have hYne : Y.Nonempty := hIne.mono hIY
    have hsub : ∀ p, y p ⊆ optSet Y p := by
      intro p z hz
      refine ⟨hIY ⟨p, hz⟩, ?_⟩
      have hYH : Y ⊆ {w | p ⬝ᵥ w ≤ p ⬝ᵥ z} := by
        apply closure_minimal _ (halfspace_closed p _)
        apply convexHull_min _ (halfspace_convex p _)
        rintro w ⟨p', hw⟩
        exact opt_against_image y hmon hhom w p' z p hw hz
      exact fun w hw => hYH hw
    have hG : graph (optSet Y) = graph y :=
      hmax _ (optSet_mono Y) (fun q hq => hsub q.2 hq)
    refine ⟨Y, hYne, hYc, hYcl, fun p => ?_⟩
    ext z
    have := congrArg (fun G => ((z, p) : (Fin N → ℝ) × (Fin N → ℝ)) ∈ G) hG
    simp only [graph, Set.mem_ofPred_eq, eq_iff_iff] at this
    exact this.symm

end SupplyCorrAux

open SupplyCorr in
theorem solution {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) :
    IsStronglyRationalizable y ↔ IsMaximalMonotone y ∧ IsHomogeneousZero y := by
  exact SupplyCorrAux.main y
