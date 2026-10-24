-- Prove2me | solution 1 for SimplexProj.Condat.projections_exist_unique
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T01:45:16.585312+00:00
-- url     : https://prove2.me/submissions/43c056d5-efea-4291-bdbb-7d799a09bfd6

import Init
import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection
import Definitions.Def_SimplexProj_Condat_IsL1Projection

open scoped BigOperators
namespace CondatProjection

theorem hilbert_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K : Set E} (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (y : E) :
    ∃! x, x ∈ K ∧ ∀ z ∈ K, ‖y-x‖ ≤ ‖y-z‖ := by
  letI : Nonempty K := hne.to_subtype
  obtain ⟨v, hvm, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv y
  have hbd : BddBelow (Set.range fun w : K => ‖y - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hmin : ∀ z ∈ K, ‖y-v‖ ≤ ‖y-z‖ := by
    intro z hz
    rw [hvmin]
    exact ciInf_le hbd (⟨z,hz⟩ : K)
  refine ⟨v, ⟨hvm, hmin⟩, ?_⟩
  rintro z ⟨hzm, hzmin⟩
  have hzeq : ‖y-z‖ = ⨅ w : K, ‖y-(w:E)‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w => hzmin w w.property)
    · exact ciInf_le hbd (⟨z,hzm⟩ : K)
  have h1 := (norm_eq_iInf_iff_real_inner_le_zero hv hvm).mp hvmin z hzm
  have h2 := (norm_eq_iInf_iff_real_inner_le_zero hv hzm).mp hzeq v hvm
  have hn : v-z = -(z-v) := by abel
  rw [hn, inner_neg_right] at h2
  have heq : y-v = (y-z)+(z-v) := by abel
  rw [heq, inner_add_left, real_inner_self_eq_norm_sq] at h1
  have hzv : ‖z-v‖ = 0 := by nlinarith [norm_nonneg (z-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzv)

theorem coordinates_min {N : ℕ} {K : Set (EuclideanSpace ℝ (Fin N))}
    (hne : K.Nonempty) (hc : IsClosed K) (hv : Convex ℝ K) (y : Fin N → ℝ) :
    ∃! x : Fin N → ℝ, WithLp.toLp 2 x ∈ K ∧
      ∀ z : Fin N → ℝ, WithLp.toLp 2 z ∈ K →
        ∑ i, (x i-y i)^2 ≤ ∑ i, (z i-y i)^2 := by
  obtain ⟨v, hvm, hvuniq⟩ := hilbert_unique hne hc hv (WithLp.toLp 2 y)
  have hnorm (x : Fin N → ℝ) :
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 x‖^2 =
      ∑ i, (x i-y i)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [PiLp.sub_apply, PiLp.toLp_apply]
    ring
  refine ⟨v.ofLp, ⟨?_, ?_⟩, ?_⟩
  · simpa using hvm.1
  · intro z hz
    rw [← hnorm, ← hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvm.2 _ hz) 2
  · rintro z ⟨hzm,hzmin⟩
    have hz : WithLp.toLp 2 z = v := hvuniq _ ⟨hzm, by
      intro w hw
      have h := hzmin w.ofLp (by simpa using hw)
      rw [← hnorm, ← hnorm] at h
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h⟩
    exact congrArg WithLp.ofLp hz

end CondatProjection

open scoped BigOperators
namespace CondatProjection

abbrev simplex (N : ℕ) (a : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | (∑ i, x i) = a ∧ ∀ i, 0 ≤ x i}
abbrev ball (N : ℕ) (a : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | (∑ i, |x i|) ≤ a}

theorem simplex_closed (N : ℕ) (a : ℝ) : IsClosed (simplex N a) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin N) => ∑ i, x i) := by fun_prop
  have hd (i : Fin N) : IsClosed {x : EuclideanSpace ℝ (Fin N) | 0 ≤ x i} :=
    isClosed_le continuous_const (by fun_prop)
  have haC : Continuous (fun _ : EuclideanSpace ℝ (Fin N) => a) := continuous_const
  convert (isClosed_eq hc haC).inter (isClosed_iInter hd) using 1
  ext x
  simp [simplex]

theorem ball_closed (N : ℕ) (a : ℝ) : IsClosed (ball N a) := by
  apply isClosed_le _ continuous_const
  fun_prop

theorem simplex_convex (N : ℕ) (a : ℝ) : Convex ℝ (simplex N a) := by
  intro x hx y hy α β hα hβ hab
  constructor
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.1, hy.1]
    rw [← add_mul, hab, one_mul]
  · intro i
    exact add_nonneg (mul_nonneg hα (hx.2 i)) (mul_nonneg hβ (hy.2 i))

theorem ball_convex (N : ℕ) (a : ℝ) : Convex ℝ (ball N a) := by
  intro x hx y hy α β hα hβ hab
  change ∑ i, |α*x i+β*y i| ≤ a
  calc
    _ ≤ ∑ i, (α*|x i|+β*|y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ |α*x i|+|β*y i| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
    _ = α*(∑ i, |x i|)+β*(∑ i, |y i|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ α*a+β*a := add_le_add (mul_le_mul_of_nonneg_left hx hα)
      (mul_le_mul_of_nonneg_left hy hβ)
    _ = a := by rw [← add_mul, hab, one_mul]

theorem simplex_nonempty (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a) :
    (simplex N a).Nonempty := by
  let i : Fin N := ⟨0, by omega⟩
  refine ⟨WithLp.toLp 2 (Pi.single i a), ?_, ?_⟩
  · simp
  · intro j
    simp only [PiLp.toLp_apply]
    by_cases hj : j = i
    · subst j; simpa using ha
    · simp [Pi.single_apply, hj, Ne.symm hj]

theorem ball_nonempty (N : ℕ) (a : ℝ) (ha : 0 ≤ a) : (ball N a).Nonempty := by
  refine ⟨0, ?_⟩
  simpa [ball] using ha

end CondatProjection

open SimplexProj.Condat in
theorem solution (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a) (y : Fin N → ℝ) :
    (∃! x : Fin N → ℝ, IsSimplexProjection a y x) ∧
    (∃! x : Fin N → ℝ, IsL1Projection a y x) := by
  constructor
  · exact CondatProjection.coordinates_min (CondatProjection.simplex_nonempty N hN a ha.le)
      (CondatProjection.simplex_closed N a) (CondatProjection.simplex_convex N a) y
  · exact CondatProjection.coordinates_min (CondatProjection.ball_nonempty N a ha.le)
      (CondatProjection.ball_closed N a) (CondatProjection.ball_convex N a) y
