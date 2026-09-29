-- Prove2me | solution 1 for Rudin.ch10_orientation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T04:28:21.074895+00:00
-- url     : https://prove2.me/submissions/a49d1388-5b41-418a-ac92-16282f70bf18

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Rudin

/-!
# Reordering the vertices of an oriented affine simplex (Rudin 10.27)

Rudin's concrete differential forms are not in Mathlib; neither is the behaviour of the integral
of a form over an affine simplex under a permutation of the vertices.  Both the affine calculus
and the affine change of variables are built here in a private namespace.
-/

namespace Orient


variable {k n : ℕ}

/-- The affine map `u ↦ b + C u` given by a matrix of coefficients. -/
def affMap (C : Fin n → Fin k → ℝ) (b : Fin n → ℝ) : (Fin k → ℝ) → (Fin n → ℝ) :=
  fun u a => b a + ∑ s, C a s * u s

theorem hasFDerivAt_affMap (C : Fin n → Fin k → ℝ) (b : Fin n → ℝ) (a : Fin n)
    (u : Fin k → ℝ) :
    HasFDerivAt (fun v : Fin k → ℝ => affMap C b v a)
      (∑ s, (C a s) • (ContinuousLinearMap.proj s : (Fin k → ℝ) →L[ℝ] ℝ)) u := by
  have h : ∀ s : Fin k, HasFDerivAt (fun v : Fin k → ℝ => C a s * v s)
      ((C a s) • (ContinuousLinearMap.proj s : (Fin k → ℝ) →L[ℝ] ℝ)) u := by
    intro s
    exact (((ContinuousLinearMap.proj s : (Fin k → ℝ) →L[ℝ] ℝ)).hasFDerivAt).const_mul (C a s)
  have hs := HasFDerivAt.sum (fun s (_ : s ∈ Finset.univ) => h s)
  have heq : (fun v : Fin k → ℝ => affMap C b v a)
      = fun v : Fin k → ℝ => b a + (∑ i : Fin k, fun w : Fin k → ℝ => C a i * w i) v := by
    funext v
    simp [affMap, Finset.sum_apply]
  rw [heq]
  exact hs.const_add (b a)

theorem partialDeriv_affMap (C : Fin n → Fin k → ℝ) (b : Fin n → ℝ) (a : Fin n)
    (s : Fin k) (u : Fin k → ℝ) :
    partialDeriv (fun v => affMap C b v a) s u = C a s := by
  rw [partialDeriv, (hasFDerivAt_affMap C b a u).fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    rw [Pi.single_apply]
    rw [if_neg hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem jacobian_affMap (C : Fin n → Fin k → ℝ) (b : Fin n → ℝ) (i : Fin k → Fin n)
    (u : Fin k → ℝ) :
    jacobian (affMap C b) i u = Matrix.det (Matrix.of fun r s => C (i r) s) := by
  rw [jacobian]
  congr 1
  ext r s
  exact partialDeriv_affMap C b (i r) s u

theorem affineSimplexMap_eq (p : Fin (k + 1) → (Fin n → ℝ)) :
    affineSimplexMap p = affMap (fun a s => p s.succ a - p 0 a) (p 0) := by
  funext u a
  simp only [affineSimplexMap, affMap, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

theorem affMap_comp (C : Fin n → Fin k → ℝ) (b : Fin n → ℝ)
    (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ) :
    (fun u => affMap C b (affMap L c u))
      = affMap (fun a t => ∑ s, C a s * L s t) (fun a => b a + ∑ s, C a s * c s) := by
  funext u a
  simp only [affMap]
  rw [add_assoc]
  congr 1
  have hterm : ∀ s : Fin k, C a s * (c s + ∑ t, L s t * u t)
      = C a s * c s + ∑ t, (C a s * L s t) * u t := by
    intro s
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hterm s), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]

/-! ## Affine changes of variable on `ℝᵏ` -/

section CoV

theorem affMap_eq_mulVec (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ) (u : Fin k → ℝ) :
    affMap L c u = c + (Matrix.of L).mulVec u := by
  funext a
  simp [affMap, Matrix.mulVec, dotProduct]

theorem continuous_affMapSelf (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ) :
    Continuous (affMap L c) := by
  refine continuous_pi fun a => ?_
  simp only [affMap]
  fun_prop

/-- An affine self-map of `ℝᵏ` with invertible linear part, as a homeomorphism. -/
noncomputable def affHomeo (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ)
    (h : IsUnit (Matrix.of L).det) : (Fin k → ℝ) ≃ₜ (Fin k → ℝ) where
  toFun := fun u => c + (Matrix.of L).mulVec u
  invFun := fun v => (Matrix.of L)⁻¹.mulVec (v - c)
  left_inv := by
    intro u
    show (Matrix.of L)⁻¹.mulVec (c + (Matrix.of L).mulVec u - c) = u
    simp only [add_sub_cancel_left]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  right_inv := by
    intro v
    show c + (Matrix.of L).mulVec ((Matrix.of L)⁻¹.mulVec (v - c)) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
    abel
  continuous_toFun := by
    refine continuous_pi fun a => ?_
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    fun_prop
  continuous_invFun := by
    refine continuous_pi fun a => ?_
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
    fun_prop

theorem measurePreserving_affMapSelf (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ)
    (hdet : |(Matrix.of L).det| = 1) :
    MeasurePreserving (affMap L c) volume volume := by
  have hne : (Matrix.of L).det ≠ 0 := by
    intro hc
    rw [hc] at hdet
    norm_num at hdet
  have hlin : MeasurePreserving (fun u => (Matrix.of L).mulVec u)
      (volume : Measure (Fin k → ℝ)) volume := by
    have hdl : LinearMap.det (Matrix.toLin' (Matrix.of L)) ≠ 0 := by
      rwa [LinearMap.det_toLin']
    have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdl
    rw [LinearMap.det_toLin'] at hmap
    have habs : |((Matrix.of L).det)⁻¹| = 1 := by
      rw [abs_inv, hdet, inv_one]
    rw [habs] at hmap
    simp only [ENNReal.ofReal_one, one_smul] at hmap
    have hfun : (fun u => (Matrix.of L).mulVec u) = ⇑(Matrix.toLin' (Matrix.of L)) := by
      funext u
      rw [Matrix.toLin'_apply]
    refine ⟨by rw [hfun]; fun_prop, ?_⟩
    rw [hfun]
    exact hmap
  have htr : MeasurePreserving (fun v : Fin k → ℝ => c + v) volume volume :=
    measurePreserving_add_left volume c
  have heq : (affMap L c) = (fun v : Fin k → ℝ => c + v) ∘ (fun u => (Matrix.of L).mulVec u) := by
    funext u
    rw [affMap_eq_mulVec]
    rfl
  rw [heq]
  exact htr.comp hlin

/-- The change-of-variables formula for an affine self-map of `ℝᵏ` of determinant `±1`
preserving the parameter domain. -/
theorem integral_comp_affine (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ)
    (hdet : |(Matrix.of L).det| = 1) {Q : Set (Fin k → ℝ)}
    (hQ : (affMap L c) ⁻¹' Q = Q) (g : (Fin k → ℝ) → ℝ) :
    (∫ u in Q, g (affMap L c u)) = ∫ v in Q, g v := by
  have hunit : IsUnit (Matrix.of L).det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro hc
    rw [hc] at hdet
    norm_num at hdet
  have hfe : ⇑(affHomeo L c hunit) = affMap L c := by
    funext u
    rw [affMap_eq_mulVec]
    rfl
  have hemb : MeasurableEmbedding (affMap L c) := by
    rw [← hfe]
    exact (affHomeo L c hunit).measurableEmbedding
  have hmp := measurePreserving_affMapSelf L c hdet
  have := hmp.setIntegral_preimage_emb hemb g Q
  rw [hQ] at this
  exact this

end CoV

/-! ## One transposition of the vertices -/

section Swap

theorem measurableSet_Q (k : ℕ) : MeasurableSet (stdSimplex k) := by
  have he : stdSimplex k
      = (⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i}) ∩ {u : Fin k → ℝ | ∑ i, u i ≤ 1} := by
    ext u
    simp [Rudin.stdSimplex, Set.mem_iInter]
  rw [he]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply i)
  · exact measurableSet_le (by fun_prop) measurable_const

theorem swap_step (p : Fin (k + 1) → (Fin n → ℝ)) (τ : Equiv.Perm (Fin (k + 1)))
    (L : Fin k → Fin k → ℝ) (c : Fin k → ℝ)
    (hdet : (Matrix.of L).det = -1)
    (hQ : (affMap L c) ⁻¹' (stdSimplex k) = stdSimplex k)
    (hcomp : ∀ u, affineSimplexMap (p ∘ τ) u = affineSimplexMap p (affMap L c u))
    (ω : KForm k n) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ τ)⟩
      = - integralOverSimplex ω ⟨affineSimplexMap p⟩ := by
  classical
  set C : Fin n → Fin k → ℝ := fun a s => p s.succ a - p 0 a with hC
  have hA : affineSimplexMap p = affMap C (p 0) := affineSimplexMap_eq p
  have hB : affineSimplexMap (p ∘ τ)
      = affMap (fun a t => ∑ s, C a s * L s t) (fun a => p 0 a + ∑ s, C a s * c s) := by
    funext u
    rw [hcomp u, hA]
    exact congrFun (affMap_comp C (p 0) L c) u
  have hjacB : ∀ (i : Fin k → Fin n) (u : Fin k → ℝ),
      jacobian (affineSimplexMap (p ∘ τ)) i u
        = - Matrix.det (Matrix.of fun r s => C (i r) s) := by
    intro i u
    rw [hB, jacobian_affMap]
    have : (Matrix.of fun r s => ∑ t, C (i r) t * L t s)
        = (Matrix.of fun r s => C (i r) s) * (Matrix.of L) := by
      ext r s
      rw [Matrix.mul_apply]
      rfl
    rw [this, Matrix.det_mul, hdet]
    ring
  have hjacA : ∀ (i : Fin k → Fin n) (u : Fin k → ℝ),
      jacobian (affineSimplexMap p) i u = Matrix.det (Matrix.of fun r s => C (i r) s) := by
    intro i u
    rw [hA, jacobian_affMap]
  set g : (Fin k → ℝ) → ℝ := fun v =>
    ∑ i : Fin k → Fin n, ω.coeff i (affineSimplexMap p v)
      * Matrix.det (Matrix.of fun r s => C (i r) s) with hg
  have hIB : integralOverSimplex ω ⟨affineSimplexMap (p ∘ τ)⟩
      = ∫ u in stdSimplex k, (- g (affMap L c u)) := by
    rw [integralOverSimplex]
    refine setIntegral_congr_fun (measurableSet_Q k) ?_
    intro u hu
    show (∑ i : Fin k → Fin n, ω.coeff i (affineSimplexMap (p ∘ τ) u)
        * jacobian (affineSimplexMap (p ∘ τ)) i u) = _
    rw [hg]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hjacB i u, hcomp u]
    ring
  have hIA : integralOverSimplex ω ⟨affineSimplexMap p⟩ = ∫ v in stdSimplex k, g v := by
    rw [integralOverSimplex]
    refine setIntegral_congr_fun (measurableSet_Q k) ?_
    intro v hv
    show (∑ i : Fin k → Fin n, ω.coeff i (affineSimplexMap p v)
        * jacobian (affineSimplexMap p) i v) = _
    rw [hg]
    exact Finset.sum_congr rfl fun i _ => by rw [hjacA i v]
  rw [hIB, hIA]
  rw [integral_neg]
  rw [integral_comp_affine L c (by rw [hdet]; norm_num) hQ g]

/-- The coordinate-permutation matrix of `Equiv.swap i j`. -/
def P1 (i j : Fin k) : Fin k → Fin k → ℝ :=
  fun m t => if t = Equiv.swap i j m then 1 else 0

theorem affMap_P1 (i j : Fin k) (u : Fin k → ℝ) :
    affMap (P1 i j) 0 u = fun m => u (Equiv.swap i j m) := by
  funext m
  simp only [affMap, P1, Pi.zero_apply, zero_add]
  rw [Finset.sum_eq_single (Equiv.swap i j m)]
  · simp
  · intro t _ ht
    rw [if_neg ht, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem det_P1 {i j : Fin k} (hij : i ≠ j) : (Matrix.of (P1 i j)).det = -1 := by
  have he : Matrix.of (P1 i j)
      = (1 : Matrix (Fin k) (Fin k) ℝ).submatrix (Equiv.swap i j) id := by
    ext m t
    simp only [Matrix.of_apply, P1, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
    by_cases h : t = Equiv.swap i j m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [he, Matrix.det_permute, Matrix.det_one, Equiv.Perm.sign_swap hij]
  norm_num

theorem preimage_P1 (i j : Fin k) :
    (affMap (P1 i j) 0) ⁻¹' (stdSimplex k) = stdSimplex k := by
  ext u
  simp only [Set.mem_preimage, affMap_P1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun m => ?_, ?_⟩
    · have := h1 (Equiv.swap i j m)
      simpa using this
    · rwa [Equiv.sum_comp (Equiv.swap i j) u] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun m => h1 _, ?_⟩
    rwa [Equiv.sum_comp (Equiv.swap i j) u]

theorem swap_succ_apply {i j m : Fin k} :
    (Equiv.swap (Fin.succ i) (Fin.succ j)) (Fin.succ m) = Fin.succ (Equiv.swap i j m) := by
  by_cases h1 : m = i
  · subst h1; simp
  · by_cases h2 : m = j
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using h1) (by simpa using h2),
        Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swap_succ_zero {i j : Fin k} :
    (Equiv.swap (Fin.succ i) (Fin.succ j)) 0 = 0 := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> exact fun h => Fin.succ_ne_zero _ h.symm

theorem case1 (p : Fin (k + 1) → (Fin n → ℝ)) {i j : Fin k} (hij : i ≠ j) (ω : KForm k n) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ (Equiv.swap (Fin.succ i) (Fin.succ j)))⟩
      = - integralOverSimplex ω ⟨affineSimplexMap p⟩ := by
  refine swap_step p _ (P1 i j) 0 (det_P1 hij) (preimage_P1 i j) ?_ ω
  intro u
  simp only [affineSimplexMap, Function.comp_apply, swap_succ_zero, affMap_P1]
  congr 1
  rw [← Equiv.sum_comp (Equiv.swap i j)
    (fun m => u (Equiv.swap i j m) • (p (Fin.succ m) - p 0))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Equiv.swap_apply_self, swap_succ_apply]

theorem sum_ite_replace (j : Fin k) (A B : Fin k → ℝ) :
    ∑ m, (if m = j then A m else B m) = A j - B j + ∑ m, B m := by
  classical
  have h1 : ∑ m, (if m = j then A m else B m)
      = A j + ∑ m ∈ Finset.univ.erase j, B m := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl fun m hm => if_neg (Finset.ne_of_mem_erase hm)
  have h2 : ∑ m, B m = B j + ∑ m ∈ Finset.univ.erase j, B m :=
    (Finset.add_sum_erase _ B (Finset.mem_univ j)).symm
  rw [h1, h2]
  ring

theorem sum_mul_sub (u R : Fin k → ℝ) (c : ℝ) :
    ∑ m, u m * (R m - c) = (∑ m, u m * R m) - (∑ m, u m) * c := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The linear part of the barycentric reflection exchanging the vertex `0` with `eⱼ`. -/
def P2 (j : Fin k) : Fin k → Fin k → ℝ :=
  fun m t => if m = j then -1 else (if t = m then 1 else 0)

theorem affMap_P2 (j : Fin k) (u : Fin k → ℝ) (m : Fin k) :
    affMap (P2 j) (Pi.single j 1) u m = if m = j then 1 - ∑ t, u t else u m := by
  simp only [affMap, P2]
  by_cases h : m = j
  · subst h
    simp only [Pi.single_eq_same, if_true]
    rw [show ∑ x, (-1 : ℝ) * u x = - ∑ x, u x by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring]
    ring
  · rw [if_neg h]
    simp only [if_neg h]
    have hz : (Pi.single j (1 : ℝ) : Fin k → ℝ) m = 0 := by
      simp [Pi.single_apply, h]
    rw [hz, zero_add]
    rw [Finset.sum_eq_single m]
    · simp
    · intro t _ ht
      rw [if_neg ht, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ m) hmem

theorem det_P2 (j : Fin k) : (Matrix.of (P2 j)).det = -1 := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
      id_eq]
    rw [Finset.prod_eq_single j]
    · simp [P2]
    · intro t _ ht
      simp [P2, ht]
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem
  · intro σ _ hσ
    have hmove : ∃ i : Fin k, σ i ≠ i ∧ σ i ≠ j := by
      obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
        by_contra hc
        push Not at hc
        exact hσ (Equiv.ext fun x => by simpa using hc x)
      set c := σ a with hc
      have hca : c ≠ a := ha
      have hσc : σ c ≠ c := by
        intro hcc
        apply hca
        have : σ c = σ a := by rw [hcc, hc]
        exact (σ.injective this).symm ▸ rfl
      have hne : σ a ≠ σ c := fun h => hca (σ.injective h).symm
      by_cases hj : σ a = j
      · exact ⟨c, hσc, fun h => hne (hj.trans h.symm)⟩
      · exact ⟨a, ha, hj⟩
    obtain ⟨i, hi1, hi2⟩ := hmove
    have : ∏ t, (Matrix.of (P2 j)) (σ t) t = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [Matrix.of_apply, P2]
      rw [if_neg hi2, if_neg (fun hc : i = σ i => hi1 hc.symm)]
    rw [this, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem sum_P2 (j : Fin k) (u : Fin k → ℝ) :
    ∑ m, affMap (P2 j) (Pi.single j 1) u m = 1 - u j := by
  simp only [affMap_P2]
  rw [sum_ite_replace j (fun _ => 1 - ∑ t, u t) u]
  ring

theorem P2_involutive (j : Fin k) (u : Fin k → ℝ) :
    affMap (P2 j) (Pi.single j 1) (affMap (P2 j) (Pi.single j 1) u) = u := by
  funext m
  rw [affMap_P2, sum_P2]
  by_cases h : m = j
  · subst h; rw [if_pos rfl]; ring
  · rw [if_neg h, affMap_P2, if_neg h]

theorem mapsTo_P2 (j : Fin k) {u : Fin k → ℝ} (hu : u ∈ stdSimplex k) :
    affMap (P2 j) (Pi.single j 1) u ∈ stdSimplex k := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun m => ?_, ?_⟩
  · rw [affMap_P2]
    by_cases h : m = j
    · rw [if_pos h]; linarith
    · rw [if_neg h]; exact h1 m
  · rw [sum_P2]
    linarith [h1 j]

theorem preimage_P2 (j : Fin k) :
    (affMap (P2 j) (Pi.single j 1)) ⁻¹' (stdSimplex k) = stdSimplex k := by
  ext u
  simp only [Set.mem_preimage]
  constructor
  · intro hu
    have := mapsTo_P2 j hu
    rwa [P2_involutive] at this
  · exact mapsTo_P2 j

theorem swap_zero_succ_apply {j m : Fin k} :
    (Equiv.swap (0 : Fin (k + 1)) (Fin.succ j)) (Fin.succ m)
      = if m = j then 0 else Fin.succ m := by
  by_cases h : m = j
  · subst h
    rw [if_pos rfl, Equiv.swap_apply_right]
  · rw [if_neg h]
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero m)
      (fun hc => h (Fin.succ_injective _ hc))

theorem case2 (p : Fin (k + 1) → (Fin n → ℝ)) (j : Fin k) (ω : KForm k n) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ (Equiv.swap (0 : Fin (k + 1)) (Fin.succ j)))⟩
      = - integralOverSimplex ω ⟨affineSimplexMap p⟩ := by
  refine swap_step p _ (P2 j) (Pi.single j 1) (det_P2 j) (preimage_P2 j) ?_ ω
  intro u
  funext a
  have hzero : (Equiv.swap (0 : Fin (k + 1)) (Fin.succ j)) 0 = Fin.succ j :=
    Equiv.swap_apply_left _ _
  have hsw : ∀ m : Fin k, p ((Equiv.swap (0 : Fin (k + 1)) (Fin.succ j)) (Fin.succ m)) a
      = if m = j then p 0 a else p (Fin.succ m) a := by
    intro m
    rw [swap_zero_succ_apply]
    split <;> rfl
  simp only [affineSimplexMap, Function.comp_apply, hzero, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, affMap_P2, hsw]
  have hL : ∑ m, u m * ((if m = j then p 0 a else p (Fin.succ m) a) - p (Fin.succ j) a)
      = u j * (p 0 a - p (Fin.succ j) a) - u j * (p (Fin.succ j) a - p (Fin.succ j) a)
        + ∑ m, u m * (p (Fin.succ m) a - p (Fin.succ j) a) := by
    rw [show (∑ m, u m * ((if m = j then p 0 a else p (Fin.succ m) a) - p (Fin.succ j) a))
        = ∑ m, (if m = j then u m * (p 0 a - p (Fin.succ j) a)
                        else u m * (p (Fin.succ m) a - p (Fin.succ j) a)) from
      Finset.sum_congr rfl fun m _ => by split_ifs <;> ring]
    exact sum_ite_replace j _ _
  have hR : ∑ m, (if m = j then 1 - ∑ t, u t else u m) * (p (Fin.succ m) a - p 0 a)
      = (1 - ∑ t, u t) * (p (Fin.succ j) a - p 0 a) - u j * (p (Fin.succ j) a - p 0 a)
        + ∑ m, u m * (p (Fin.succ m) a - p 0 a) := by
    rw [show (∑ m, (if m = j then 1 - ∑ t, u t else u m) * (p (Fin.succ m) a - p 0 a))
        = ∑ m, (if m = j then (1 - ∑ t, u t) * (p (Fin.succ m) a - p 0 a)
                        else u m * (p (Fin.succ m) a - p 0 a)) from
      Finset.sum_congr rfl fun m _ => by split_ifs <;> ring]
    exact sum_ite_replace j _ _
  rw [hL, hR, sum_mul_sub u (fun m => p (Fin.succ m) a) (p (Fin.succ j) a),
    sum_mul_sub u (fun m => p (Fin.succ m) a) (p 0 a)]
  ring

theorem swap_case (p : Fin (k + 1) → (Fin n → ℝ)) {x y : Fin (k + 1)} (hxy : x ≠ y)
    (ω : KForm k n) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ (Equiv.swap x y))⟩
      = - integralOverSimplex ω ⟨affineSimplexMap p⟩ := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨j, rfl⟩
  · exact absurd rfl hxy
  · exact case2 p j ω
  · rw [Equiv.swap_comm]
    exact case2 p i ω
  · exact case1 p (fun hc => hxy (by rw [hc])) ω

/-- **Rudin, Theorem 10.27.**  Reordering the vertices of an oriented affine simplex multiplies
the integral of every form by the sign of the permutation. -/
theorem orientation (τ : Equiv.Perm (Fin (k + 1))) (ω : KForm k n)
    (p : Fin (k + 1) → (Fin n → ℝ)) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ τ)⟩
      = (Equiv.Perm.sign τ : ℤ) * integralOverSimplex ω ⟨affineSimplexMap p⟩ := by
  revert p
  refine Equiv.Perm.swap_induction_on τ ?_ ?_
  · intro p
    simp
  · intro f x y hxy ih p
    have hcomp : p ∘ (Equiv.swap x y * f) = (p ∘ (Equiv.swap x y)) ∘ f := by
      funext m
      rfl
    rw [hcomp, ih (p ∘ (Equiv.swap x y)), swap_case p hxy ω, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hxy]
    push_cast
    ring

end Swap


end Orient

open Filter Topology MeasureTheory in
theorem solution (k n : ℕ) (p : Fin (k + 1) → (Fin n → ℝ)) (τ : Equiv.Perm (Fin (k + 1)))
    (ω : Rudin.KForm k n) :
    Rudin.integralOverSimplex ω ⟨Rudin.affineSimplexMap (p ∘ τ)⟩ =
      (Equiv.Perm.sign τ : ℤ) * Rudin.integralOverSimplex ω ⟨Rudin.affineSimplexMap p⟩ :=
  Orient.orientation τ ω p
