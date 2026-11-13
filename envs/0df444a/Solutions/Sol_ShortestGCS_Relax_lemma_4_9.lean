-- Prove2me | solution 1 for ShortestGCS.Relax.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:20:01.476207+00:00
-- url     : https://prove2.me/submissions/08526227-259d-4cf9-ae19-a06f295f56c2

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

open ShortestGCS.Relax ShortestGCS.MICP Matrix
open scoped BigOperators Pointwise

private theorem linear_dot {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  have hx : (∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [← hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct, mul_comm]

private theorem mem_of_valid {n : ℕ} (X : Set (Fin n → ℝ))
    (hXc : IsClosed X) (hXcv : Convex ℝ X) (x : Fin n → ℝ)
    (hx : ∀ ab ∈ validCone X, 0 ≤ ab.1 ⬝ᵥ x + ab.2) : x ∈ X := by
  by_contra hout
  obtain ⟨f, t, hfx, ht⟩ := geometric_hahn_banach_point_closed hXcv hXc hout
  let a : Fin n → ℝ := fun i => f (Pi.single i 1)
  have hvalid : (a, -t) ∈ validCone X := by
    intro z hz
    change 0 ≤ a ⬝ᵥ z + -t
    rw [← linear_dot f z]
    linarith [ht z hz]
  have h := hx (a, -t) hvalid
  change 0 ≤ a ⬝ᵥ x + -t at h
  rw [← linear_dot f x] at h
  linarith

private theorem pair_expansion {n : ℕ} (f : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (q : (Fin n → ℝ) × ℝ) :
    f q = (fun i => f (Pi.single i 1, 0)) ⬝ᵥ q.1 + f (0, 1) * q.2 := by
  have hl := linear_dot (f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) q.1
  change f (q.1, 0) = (fun i => f (Pi.single i 1, 0)) ⬝ᵥ q.1 at hl
  have hr : f (0, q.2) = q.2 * f (0, 1) := by
    simpa using f.map_smul q.2 ((0, 1) : (Fin n → ℝ) × ℝ)
  calc
    f q = f (q.1, 0) + f (0, q.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    _ = _ := by rw [hl, hr]; ring

private theorem mem_perspective_of_valid {n : ℕ} (X : Set (Fin n → ℝ))
    (hXcv : Convex ℝ X) (hXne : X.Nonempty) (q : (Fin n → ℝ) × ℝ)
    (hq : ∀ ab ∈ validCone X, 0 ≤ ab.1 ⬝ᵥ q.1 + ab.2 * q.2) :
    q ∈ perspectiveSet X := by
  let S : Set ((Fin n → ℝ) × ℝ) := X ×ˢ ({1} : Set ℝ)
  have hS : Convex ℝ S := hXcv.prod (convex_singleton 1)
  let K := (ConvexCone.hull ℝ S).closure
  have hKne : (K : Set ((Fin n → ℝ) × ℝ)).Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    exact ⟨(x, 1), subset_closure (ConvexCone.subset_hull ⟨hx, rfl⟩)⟩
  have hKclosed : IsClosed (K : Set ((Fin n → ℝ) × ℝ)) := isClosed_closure
  have hKP : (K : Set ((Fin n → ℝ) × ℝ)) ⊆ perspectiveSet X := by
    apply closure_minimal
    · intro z hz
      obtain ⟨t, ht, p, hp, rfl⟩ := (ConvexCone.mem_hull_of_convex hS).mp hz
      have hp2 : p.2 = 1 := hp.2
      apply subset_closure
      refine ⟨?_, ?_⟩
      · change 0 ≤ t * p.2
        rw [hp2, mul_one]
        exact ht.le
      · change t • p.1 ∈ (t * p.2) • X
        rw [hp2, mul_one]
        exact Set.smul_mem_smul_set hp.1
    · exact isClosed_closure
  let C : ProperCone ℝ ((Fin n → ℝ) × ℝ) :=
    ⟨K.toPointedCone (.of_nonempty_of_isClosed hKne hKclosed), hKclosed⟩
  by_contra hout
  obtain ⟨f, hf, hfq⟩ := C.hyperplane_separation_point (fun h => hout (hKP h))
  let ab : (Fin n → ℝ) × ℝ := ((fun i => f (Pi.single i 1, 0)), f (0, 1))
  have hab : ab ∈ validCone X := by
    intro x hx
    have h := hf (x, 1) (subset_closure (ConvexCone.subset_hull ⟨hx, rfl⟩))
    rw [pair_expansion f] at h
    simpa [ab] using h
  have h := hq ab hab
  have heq := pair_expansion f q
  change f q = ab.1 ⬝ᵥ q.1 + ab.2 * q.2 at heq
  linarith

private theorem valid_on_perspective {n : ℕ} (X : Set (Fin n → ℝ))
    (ab : (Fin n → ℝ) × ℝ) (hab : ab ∈ validCone X) :
    ∀ q ∈ perspectiveSet X, 0 ≤ ab.1 ⬝ᵥ q.1 + ab.2 * q.2 := by
  change closure {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X} ⊆
    {q : (Fin n → ℝ) × ℝ | 0 ≤ ab.1 ⬝ᵥ q.1 + ab.2 * q.2}
  apply closure_minimal
  · intro q hq
    change 0 ≤ ab.1 ⬝ᵥ q.1 + ab.2 * q.2
    obtain ⟨z, hz, heq⟩ := hq.2
    have h := mul_nonneg hq.1 (hab z hz)
    rw [← heq]
    simpa only [dotProduct_smul, smul_eq_mul, mul_add, mul_comm] using (show 0 ≤ q.2 * (ab.1 ⬝ᵥ z + ab.2) from h)
  · exact isClosed_le continuous_const (by simp only [dotProduct]; fun_prop)

theorem solution {n : ℕ} (X : Set (Fin n → ℝ)) (hXne : X.Nonempty) (hXc : IsClosed X)
    (hXcv : Convex ℝ X) :
    dualCone (ShortestGCS.MICP.perspectiveSet X) = validCone X ∧ dualCone (validCone X) = ShortestGCS.MICP.perspectiveSet X := by
  constructor
  · ext ab
    constructor
    · intro h x hx
      have hq : (x, (1 : ℝ)) ∈ perspectiveSet X := subset_closure ⟨by norm_num, by simpa using hx⟩
      simpa only [mul_one] using h (x, 1) hq
    · intro h
      exact valid_on_perspective X ab h
  · ext q
    constructor
    · intro h
      exact mem_perspective_of_valid X hXcv hXne q (fun ab hab => by
        simpa only [dotProduct_comm, mul_comm] using h ab hab)
    · intro h ab hab
      simpa only [dotProduct_comm, mul_comm] using valid_on_perspective X ab hab q h

#print axioms solution


