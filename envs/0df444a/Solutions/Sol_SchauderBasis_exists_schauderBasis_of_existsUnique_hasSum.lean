-- Prove2me | solution 1 for SchauderBasis.exists_schauderBasis_of_existsUnique_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:40:04.93344+00:00
-- url     : https://prove2.me/submissions/9ab9d174-d30a-472f-845a-0902f23749c2

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

open scoped BoundedContinuousFunction

namespace Sol_SchauderBasis_exists_schauderBasis_of_existsUnique_hasSum

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- `HasSum` along the conditional summation filter on `ℕ` is convergence of the partial sums. -/
lemma hasSum_cond_iff (f : ℕ → X) (x : X) :
    HasSum f x (SummationFilter.conditional ℕ) ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 x) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/-- The partial sums of the expansion with coefficients `a`. -/
def psum (e : ℕ → X) (a : ℕ → 𝕜) (N : ℕ) : X := ∑ n ∈ Finset.range N, a n • e n

section

variable (e : ℕ → X) (c : X → ℕ → 𝕜)
  (hc : ∀ x, Tendsto (fun N => psum e (c x) N) atTop (𝓝 x))
  (hu : ∀ x (a : ℕ → 𝕜), Tendsto (fun N => psum e a N) atTop (𝓝 x) → a = c x)

include hc hu

omit hc in
lemma e_ne_zero (n : ℕ) : e n ≠ 0 := by
  intro h
  classical
  have h1 : (fun m => if m = n then (1 : 𝕜) else 0) = c 0 := by
    apply hu
    have : ∀ N, psum e (fun m => if m = n then (1 : 𝕜) else 0) N = 0 := by
      intro N
      unfold psum
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : m = n
      · subst hm; simp [h]
      · simp [hm]
    simp only [this]
    exact tendsto_const_nhds
  have h2 : (fun _ : ℕ => (0 : 𝕜)) = c 0 := by
    apply hu
    simp only [psum, zero_smul, Finset.sum_const_zero]
    exact tendsto_const_nhds
  have := congrFun (h1.trans h2.symm) n
  simp at this

lemma c_add (x y : X) : c (x + y) = c x + c y := by
  symm
  apply hu
  have : ∀ N, psum e (c x + c y) N = psum e (c x) N + psum e (c y) N := by
    intro N
    simp only [psum, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  simp only [this]
  exact (hc x).add (hc y)

lemma c_smul (t : 𝕜) (x : X) : c (t • x) = t • c x := by
  symm
  apply hu
  have : ∀ N, psum e (t • c x) N = t • psum e (c x) N := by
    intro N
    simp only [psum, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  simp only [this]
  exact (hc x).const_smul t

omit hu in
lemma exists_bound (x : X) : ∃ C : ℝ, ∀ N, ‖psum e (c x) N‖ ≤ C := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun N => psum e (c x) N) (hc x))
  exact ⟨M, Set.forall_mem_range.mp hM⟩

/-- The map `x ↦ (S_N x)_N` into bounded sequences. -/
noncomputable def Phi : X →ₗ[𝕜] (ℕ →ᵇ X) where
  toFun x := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun N => psum e (c x) N)
    (exists_bound e c hc x).choose (exists_bound e c hc x).choose_spec
  map_add' x y := by
    ext N
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
      BoundedContinuousFunction.coe_add, Pi.add_apply, c_add e c hc hu, psum, Pi.add_apply,
      add_smul, Finset.sum_add_distrib]
  map_smul' t x := by
    ext N
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
      BoundedContinuousFunction.coe_smul, c_smul e c hc hu, psum, Pi.smul_apply, smul_eq_mul,
      mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma Phi_apply (x : X) (N : ℕ) : Phi e c hc hu x N = psum e (c x) N := rfl

lemma closed_graph [CompleteSpace X] (u : ℕ → X) (x : X) (y : ℕ →ᵇ X)
    (hux : Tendsto u atTop (𝓝 x))
    (huy : Tendsto (Phi e c hc hu ∘ u) atTop (𝓝 y)) : y = Phi e c hc hu x := by
  -- pointwise convergence of the partial sums
  have hev : ∀ N, Tendsto (fun k => psum e (c (u k)) N) atTop (𝓝 (y N)) := fun N =>
    ((BoundedContinuousFunction.lipschitz_eval_const N).continuous.tendsto y).comp huy
  -- the increments of `y` are multiples of the basis vectors
  have hcoef : ∀ N, ∃ a : 𝕜, y (N + 1) - y N = a • e N := by
    intro N
    obtain ⟨g, -, hg⟩ := exists_dual_vector'' 𝕜 (e N)
    have hne : (‖e N‖ : 𝕜) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (e_ne_zero e c hu N)
    have h1 : Tendsto (fun k => c (u k) N • e N) atTop (𝓝 (y (N + 1) - y N)) := by
      refine ((hev (N + 1)).sub (hev N)).congr fun k => ?_
      simp [psum, Finset.sum_range_succ]
    have h2 : Tendsto (fun k => c (u k) N) atTop (𝓝 (g (y (N + 1) - y N) / ‖e N‖)) := by
      refine (((g.continuous.tendsto _).comp h1).div_const (‖e N‖ : 𝕜)).congr fun k => ?_
      simp [hg, hne]
    exact ⟨g (y (N + 1) - y N) / ‖e N‖, tendsto_nhds_unique h1 (h2.smul_const (e N))⟩
  choose a ha using hcoef
  have hy0 : y 0 = 0 := by
    have := hev 0
    simp only [psum, Finset.range_zero, Finset.sum_empty] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hyN : ∀ N, y N = psum e a N := by
    intro N
    induction N with
    | zero => simp [hy0, psum]
    | succ N ih =>
      have := ha N
      rw [psum, Finset.sum_range_succ, ← psum, ← ih, ← this]
      abel
  have hyx : Tendsto (fun N => psum e a N) atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h1 := (Metric.tendsto_nhds.mp huy) (ε / 3) (by positivity)
    have h2 := (Metric.tendsto_nhds.mp hux) (ε / 3) (by positivity)
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hc (u k)) (ε / 3) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    have h3 : dist (y N) (psum e (c (u k)) N) < ε / 3 := by
      calc dist (y N) (psum e (c (u k)) N) = dist (Phi e c hc hu (u k) N) (y N) := by
            rw [dist_comm]; rfl
        _ ≤ dist (Phi e c hc hu (u k)) y := BoundedContinuousFunction.dist_coe_le_dist N
        _ < ε / 3 := hk1
    rw [← hyN]
    calc dist (y N) x ≤ dist (y N) (psum e (c (u k)) N) + dist (psum e (c (u k)) N) (u k)
          + dist (u k) x := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have := hN₀ N hN
          gcongr
      _ = ε := by ring
  have hax : a = c x := hu x a hyx
  ext N
  rw [hyN, hax]
  rfl

end

end Sol_SchauderBasis_exists_schauderBasis_of_existsUnique_hasSum

open Sol_SchauderBasis_exists_schauderBasis_of_existsUnique_hasSum

open SchauderBasis

theorem solution
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (e : ℕ → X)
    (he : ∀ x : X, ∃! c : ℕ → 𝕜,
      HasSum (fun n => c n • e n) x (SummationFilter.conditional ℕ)) :
    ∃ b : SchauderBasis 𝕜 X, b.basis = e := by
  have he1 : ∀ x : X, ∃ c : ℕ → 𝕜, Tendsto (fun N => psum e c N) atTop (𝓝 x) ∧
      ∀ a : ℕ → 𝕜, Tendsto (fun N => psum e a N) atTop (𝓝 x) → a = c := by
    intro x
    obtain ⟨c, hc, hu⟩ := he x
    exact ⟨c, (hasSum_cond_iff _ _).mp hc, fun a ha => hu a ((hasSum_cond_iff _ _).mpr ha)⟩
  choose c hc hu using he1
  have hu' : ∀ x (a : ℕ → 𝕜), Tendsto (fun N => psum e a N) atTop (𝓝 x) → a = c x :=
    fun x a ha => hu x a ha
  let Φ : X →L[𝕜] (ℕ →ᵇ X) := ContinuousLinearMap.ofSeqClosedGraph (g := Phi e c hc hu')
    (fun u x y hux huy => closed_graph e c hc hu' u x y hux huy)
  have hS : ∀ x N, ‖psum e (c x) N‖ ≤ ‖Φ‖ * ‖x‖ := fun x N =>
    (BoundedContinuousFunction.norm_coe_le_norm (Φ x) N).trans (Φ.le_opNorm x)
  have hcoef : ∀ n x, ‖c x n‖ ≤ (2 * ‖Φ‖ / ‖e n‖) * ‖x‖ := by
    intro n x
    have hpos : 0 < ‖e n‖ := norm_pos_iff.mpr (e_ne_zero e c hu' n)
    have h1 : c x n • e n = psum e (c x) (n + 1) - psum e (c x) n := by
      simp [psum, Finset.sum_range_succ]
    have h2 : ‖c x n‖ * ‖e n‖ ≤ 2 * ‖Φ‖ * ‖x‖ := by
      rw [← norm_smul, h1]
      calc ‖psum e (c x) (n + 1) - psum e (c x) n‖
          ≤ ‖psum e (c x) (n + 1)‖ + ‖psum e (c x) n‖ := norm_sub_le _ _
        _ ≤ ‖Φ‖ * ‖x‖ + ‖Φ‖ * ‖x‖ := add_le_add (hS x _) (hS x _)
        _ = 2 * ‖Φ‖ * ‖x‖ := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  let coord : ℕ → StrongDual 𝕜 X := fun n => LinearMap.mkContinuous
    { toFun := fun x => c x n
      map_add' := fun x y => by
        show c (x + y) n = c x n + c y n
        rw [c_add e c hc hu']; rfl
      map_smul' := fun t x => by
        show c (t • x) n = t • c x n
        rw [c_smul e c hc hu']; rfl }
    (2 * ‖Φ‖ / ‖e n‖) (fun x => hcoef n x)
  have hortho : ∀ j, c (e j) = Pi.single j (1 : 𝕜) := by
    intro j
    symm
    apply hu'
    apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
    intro N hN
    rw [psum, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      exact absurd (Finset.mem_range.mpr (by omega)) hj
  refine ⟨{ basis := e, coord := coord, ortho := ?_, expansion := ?_ }, rfl⟩
  · intro i j
    show c (e j) i = _
    rw [hortho j]
    congr
  · intro x
    rw [hasSum_cond_iff]
    exact hc x
