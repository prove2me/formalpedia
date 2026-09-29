-- Prove2me | solution 1 for Rudin.ch10_primitive_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T02:19:14.165343+00:00
-- url     : https://prove2.me/submissions/0c918fb7-309f-4628-91f3-090d39cc91a6

/-
Rudin, *Principles of Mathematical Analysis*, 3rd ed., Theorem 10.39 (Poincaré's lemma),
pointwise form: on a convex open set every closed `(m+1)`-form of class `C'` has a primitive.

The primitive is the classical cone (homotopy) operator based at a point `p` of the set.
-/
import Mathlib
import Definitions.Def_Rudin_ch10_forms

open MeasureTheory intervalIntegral

namespace Rudin

open scoped Nat

/-! ### The ray integral -/

section Ray

variable {n : ℕ}

/-- The ray integral `∫₀¹ tᶜ · g(p + t(x − p)) dt`, the building block of the cone operator. -/
noncomputable def rayInt (c : ℕ) (g : (Fin n → ℝ) → ℝ) (p x : Fin n → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ c * g (p + t • (x - p))

variable {E : Set (Fin n → ℝ)} {p x : Fin n → ℝ} {g : (Fin n → ℝ) → ℝ} {c : ℕ}

/-- Every point of the segment from `p` to `x` lies in the convex set `E`. -/
theorem segment_mem_of_convex (hconv : Convex ℝ E) (hp : p ∈ E) (hx : x ∈ E) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : p + t • (x - p) ∈ E := by
  have := hconv.add_smul_sub_mem hp hx ht
  simpa using this

/-- The ray from `p` to `x` maps `[0,1]` into `E`. -/
theorem mapsTo_ray (hconv : Convex ℝ E) (hp : p ∈ E) (hx : x ∈ E) :
    Set.MapsTo (fun t : ℝ => p + t • (x - p)) (Set.Icc 0 1) E := fun _ ht =>
  segment_mem_of_convex hconv hp hx ht

/-- A continuous function restricted to the ray from `p` to `x` is continuous. -/
theorem continuousOn_comp_ray (hconv : Convex ℝ E) (hp : p ∈ E) (hx : x ∈ E)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f E) :
    ContinuousOn (fun t : ℝ => f (p + t • (x - p))) (Set.Icc 0 1) :=
  hf.comp (by fun_prop) (mapsTo_ray hconv hp hx)

/-- The derivative of a `C¹` function restricted to the ray from `p` to `x` is continuous. -/
theorem continuousOn_fderiv_comp_ray (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E) (hx : x ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (v : Fin n → ℝ) :
    ContinuousOn (fun t : ℝ => fderiv ℝ g (p + t • (x - p)) v) (Set.Icc 0 1) :=
  (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hE le_rfl).comp (by fun_prop) (mapsTo_ray hconv hp hx))

/-- Expanding a continuous linear functional on `ℝⁿ` in the coordinate directions. -/
theorem sum_apply_single (L : (Fin n → ℝ) →L[ℝ] ℝ) (w : Fin n → ℝ) :
    ∑ q : Fin n, w q * L (Pi.single q 1) = L w := by
  have h : ∀ q : Fin n, w q * L (Pi.single q 1) = L (w q • (Pi.single q 1 : Fin n → ℝ)) := by
    intro q; rw [L.map_smul]; simp [smul_eq_mul]
  simp only [h]
  rw [← map_sum L]
  congr 1
  ext j
  simp [Pi.single_apply, Finset.sum_apply]

/-- The derivative of the ray integral: the integral of the derivatives along the ray. -/
noncomputable def rayDeriv (c : ℕ) (g : (Fin n → ℝ) → ℝ) (p x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∫ t in (0:ℝ)..1, (t ^ (c + 1) • fderiv ℝ g (p + t • (x - p)) : (Fin n → ℝ) →L[ℝ] ℝ)

/-- Around any point of `E` the derivative of `g` is bounded along all the rays from `p`. -/
theorem exists_local_ray_bound (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) :
    ∃ r > 0, ∃ C : ℝ, Metric.closedBall x r ⊆ E ∧
      ∀ y ∈ Metric.closedBall x r, ∀ t ∈ Set.Icc (0:ℝ) 1,
        p + t • (y - p) ∈ E ∧ ‖fderiv ℝ g (p + t • (y - p))‖ ≤ C := by
  have hfd : ContinuousOn (fun y => fderiv ℝ g y) E := hg.continuousOn_fderiv_of_isOpen hE le_rfl
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.closedBall x r ⊆ E := by
    obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hE x hx
    refine ⟨r / 2, by positivity, fun y hy => h ?_⟩
    simp only [Metric.mem_closedBall] at hy
    simp only [Metric.mem_ball]
    linarith
  set K := (fun z : ℝ × (Fin n → ℝ) => p + z.1 • (z.2 - p)) ''
    (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall x r) with hK
  have hKcomp : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall x r)).image (by fun_prop)
  have hKE : K ⊆ E := by
    rintro _ ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    exact segment_mem_of_convex hconv hp (hball hy) ht
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn (hfd.mono hKE)
  refine ⟨r, hr, C, hball, fun y hy t ht => ⟨hKE ⟨(t, y), ⟨ht, hy⟩, rfl⟩, hC _ ⟨(t, y), ⟨ht, hy⟩, rfl⟩⟩⟩

/-- Differentiation under the integral sign for the ray integral. -/
theorem rayInt_hasFDerivAt (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) :
    HasFDerivAt (rayInt c g p) (rayDeriv c g p x) x := by
  have hgc : ContinuousOn g E := hg.continuousOn
  have hfd : ContinuousOn (fun y => fderiv ℝ g y) E := hg.continuousOn_fderiv_of_isOpen hE le_rfl
  obtain ⟨r, hr, C, hball, hbnd⟩ := exists_local_ray_bound hE hconv hp hg hx
  set F : (Fin n → ℝ) → ℝ → ℝ := fun y t => t ^ c * g (p + t • (y - p)) with hF
  set F' : (Fin n → ℝ) → ℝ → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun y t => t ^ (c + 1) • fderiv ℝ g (p + t • (y - p)) with hF'
  have huIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have hcontF : ∀ y ∈ Metric.closedBall x r, ContinuousOn (F y) (Set.Icc 0 1) := fun y hy =>
    (continuous_pow c).continuousOn.mul (continuousOn_comp_ray hconv hp (hball hy) hgc)
  have hcontF' : ∀ y ∈ Metric.closedBall x r, ContinuousOn (F' y) (Set.Icc 0 1) := by
    intro y hy
    refine ContinuousOn.smul (continuous_pow (c + 1)).continuousOn ?_
    exact hfd.comp (by fun_prop) (mapsTo_ray hconv hp (hball hy))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := volume) (F := F) (F' := F') (s := Metric.ball x r) (bound := fun _ => C) (a := 0) (b := 1)
    (Metric.ball_mem_nhds x hr)
    (by
      filter_upwards [Metric.ball_mem_nhds x hr] with y hy
      rw [huIoc]
      exact ((hcontF y (Metric.ball_subset_closedBall hy)).mono
        Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    ((hcontF x (Metric.mem_closedBall_self hr.le)).intervalIntegrable_of_Icc zero_le_one)
    (by
      rw [huIoc]
      exact ((hcontF' x (Metric.mem_closedBall_self hr.le)).mono
        Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by
      rw [huIoc]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
      have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hb := (hbnd y (Metric.ball_subset_closedBall hy) t htI).2
      rw [hF']
      simp only [norm_smul, norm_pow, Real.norm_eq_abs]
      have h1 : |t| ^ (c + 1) ≤ 1 := by
        rw [abs_of_nonneg htI.1]
        exact pow_le_one₀ htI.1 htI.2
      calc |t| ^ (c + 1) * ‖fderiv ℝ g (p + t • (y - p))‖ ≤ 1 * C :=
            mul_le_mul h1 hb (norm_nonneg _) zero_le_one
        _ = C := one_mul C)
    (_root_.intervalIntegrable_const)
    (by
      rw [huIoc]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
      have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hmem : p + t • (y - p) ∈ E := (hbnd y (Metric.ball_subset_closedBall hy) t htI).1
      have hgd : DifferentiableAt ℝ g (p + t • (y - p)) :=
        (hg.contDiffAt (hE.mem_nhds hmem)).differentiableAt one_ne_zero
      have hbase : HasFDerivAt (fun z : Fin n → ℝ => t • (z - p))
          (t • ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
        ((hasFDerivAt_id y).sub_const p).const_smul t
      have h1 : HasFDerivAt (fun z : Fin n → ℝ => p + t • (z - p))
          (t • ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := hbase.const_add p
      have h2 := (hgd.hasFDerivAt.comp y h1).const_mul (t ^ c)
      refine h2.congr_fderiv ?_
      ext v
      simp [hF', pow_succ]
      ring)

/-- The ray integral of a `C¹` function is differentiable at every point of `E`. -/
theorem rayInt_differentiableAt (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) : DifferentiableAt ℝ (rayInt c g p) x :=
  (rayInt_hasFDerivAt hE hconv hp hg hx).differentiableAt

/-- The integrand of `rayDeriv` is interval integrable. -/
theorem rayDeriv_intervalIntegrable (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) :
    IntervalIntegrable
      (fun t : ℝ => (t ^ (c + 1) • fderiv ℝ g (p + t • (x - p)) : (Fin n → ℝ) →L[ℝ] ℝ))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.smul (continuous_pow (c + 1)).continuousOn ?_
  exact (hg.continuousOn_fderiv_of_isOpen hE le_rfl).comp (by fun_prop)
    (mapsTo_ray hconv hp hx)

/-- Differentiation under the integral sign for the ray integral, in applied form. -/
theorem rayInt_fderiv_apply (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) (v : Fin n → ℝ) :
    fderiv ℝ (rayInt c g p) x v
      = ∫ t in (0:ℝ)..1, t ^ (c + 1) * fderiv ℝ g (p + t • (x - p)) v := by
  rw [(rayInt_hasFDerivAt hE hconv hp hg hx).fderiv, rayDeriv]
  have hint := (rayDeriv_intervalIntegrable (c := c) hE hconv hp hg hx).1
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ContinuousLinearMap.integral_apply hint]
  rfl

/-- The derivative of the ray integral depends continuously on the base point. -/
theorem rayDeriv_continuousOn (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) : ContinuousOn (rayDeriv c g p) E := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hfd : ContinuousOn (fun y => fderiv ℝ g y) E := hg.continuousOn_fderiv_of_isOpen hE le_rfl
  obtain ⟨r, hr, C, hball, hbnd⟩ := exists_local_ray_bound hE hconv hp hg hx
  have huIoc : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have hcont' : ∀ y ∈ Metric.closedBall x r, ContinuousOn
      (fun t : ℝ => (t ^ (c + 1) • fderiv ℝ g (p + t • (y - p)) : (Fin n → ℝ) →L[ℝ] ℝ))
      (Set.Icc 0 1) := by
    intro y hy
    refine ContinuousOn.smul (continuous_pow (c + 1)).continuousOn ?_
    exact hfd.comp (by fun_prop) (mapsTo_ray hconv hp (hball hy))
  refine continuousAt_of_dominated_interval (μ := volume) (bound := fun _ => C) ?_ ?_
    _root_.intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rw [huIoc]
    exact ((hcont' y (Metric.ball_subset_closedBall hy)).mono
      Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    filter_upwards with t ht
    rw [huIoc] at ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hb := (hbnd y (Metric.ball_subset_closedBall hy) t htI).2
    simp only [norm_smul, norm_pow, Real.norm_eq_abs]
    have h1 : |t| ^ (c + 1) ≤ 1 := by
      rw [abs_of_nonneg htI.1]
      exact pow_le_one₀ htI.1 htI.2
    calc |t| ^ (c + 1) * ‖fderiv ℝ g (p + t • (y - p))‖ ≤ 1 * C :=
          mul_le_mul h1 hb (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · filter_upwards with t ht
    rw [huIoc] at ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hmem : p + t • (x - p) ∈ E :=
      (hbnd x (Metric.mem_closedBall_self hr.le) t htI).1
    have hmap : ContinuousAt (fun y : Fin n → ℝ => p + t • (y - p)) x := by fun_prop
    have hcomp : ContinuousAt (fun y : Fin n → ℝ => fderiv ℝ g (p + t • (y - p))) x :=
      ContinuousAt.comp (hfd.continuousAt (hE.mem_nhds hmem)) hmap
    exact hcomp.const_smul (t ^ (c + 1))

/-- The ray integral of a `C¹` function is `C¹`. -/
theorem rayInt_contDiffOn (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) : ContDiffOn ℝ 1 (rayInt c g p) E := by
  have hfderiv : ∀ y ∈ E, fderiv ℝ (rayInt c g p) y = rayDeriv c g p y :=
    fun y hy => (rayInt_hasFDerivAt hE hconv hp hg hy).fderiv
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  rw [h1, contDiffOn_succ_iff_fderiv_of_isOpen hE]
  refine ⟨fun y hy => (rayInt_differentiableAt hE hconv hp hg hy).differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (rayDeriv_continuousOn hE hconv hp hg).congr hfderiv

/-- The fundamental theorem of calculus along the ray from `p` to `x`, in the form used by the
cone operator: `∫₀¹ d/dt (t^{c+1} g(p + t(x−p))) dt = g x`. -/
theorem rayInt_ftc (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hg : ContDiffOn ℝ 1 g E) (hx : x ∈ E) :
    ((c : ℝ) + 1) * rayInt c g p x
        + ∫ t in (0:ℝ)..1, t ^ (c + 1) * fderiv ℝ g (p + t • (x - p)) (x - p)
      = g x := by
  have hgc : ContinuousOn g E := hg.continuousOn
  have hint1 : IntervalIntegrable
      (fun t : ℝ => ((c : ℝ) + 1) * (t ^ c * g (p + t • (x - p)))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      ((continuous_pow c).continuousOn.mul (continuousOn_comp_ray hconv hp hx hgc))
  have hint2 : IntervalIntegrable
      (fun t : ℝ => t ^ (c + 1) * fderiv ℝ g (p + t • (x - p)) (x - p)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuous_pow (c + 1)).continuousOn.mul
      (continuousOn_fderiv_comp_ray hE hconv hp hx hg (x - p))
  set F : ℝ → ℝ := fun t => t ^ (c + 1) * g (p + t • (x - p)) with hF
  set F' : ℝ → ℝ := fun t => ((c : ℝ) + 1) * (t ^ c * g (p + t • (x - p)))
      + t ^ (c + 1) * fderiv ℝ g (p + t • (x - p)) (x - p) with hF'
  have hcontF : ContinuousOn F (Set.Icc 0 1) :=
    (continuous_pow (c + 1)).continuousOn.mul (continuousOn_comp_ray hconv hp hx hgc)
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivWithinAt F (F' t) (Set.Ioi t) t := by
    intro t ht
    have hmem : p + t • (x - p) ∈ E :=
      segment_mem_of_convex hconv hp hx ⟨ht.1.le, ht.2.le⟩
    have hgd : DifferentiableAt ℝ g (p + t • (x - p)) :=
      (hg.contDiffAt (hE.mem_nhds hmem)).differentiableAt one_ne_zero
    have hray : HasDerivAt (fun s : ℝ => p + s • (x - p)) (x - p) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - p)).const_add p
    have h1 : HasDerivAt (fun s : ℝ => g (p + s • (x - p)))
        (fderiv ℝ g (p + t • (x - p)) (x - p)) t := hgd.hasFDerivAt.comp_hasDerivAt t hray
    have h2 : HasDerivAt (fun s : ℝ => s ^ (c + 1)) (((c : ℝ) + 1) * t ^ c) t := by
      simpa using hasDerivAt_pow (c + 1) t
    exact ((h2.mul h1).congr_deriv (by rw [hF']; ring)).hasDerivWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcontF hderiv
    (hint1.add hint2)
  have hF1 : F 1 = g x := by simp [hF]
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hF1, hF0, sub_zero] at hftc
  rw [← hftc, hF', intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_const_mul]
  rfl

/-- The ray integral is linear in the integrand: scaling. -/
theorem rayInt_const_smul (a : ℝ) :
    rayInt c (fun y => a * g y) p x = a * rayInt c g p x := by
  unfold rayInt
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by ring

end Ray

/-! ### Alternating sums of coefficients -/

/-- The alternation of the coefficients of a `k`-form: the value of the associated alternating
form on the basis vectors indexed by `i`. -/
noncomputable def altCoeff {k n : ℕ} (ω : KForm k n) (i : Fin k → Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω.coeff (fun r => i (σ r)) x

/-- The permutation of `Fin (k+1)` sending `0` to `r` and `j.succ` to `r.succAbove (σ j)`. -/
noncomputable def consPerm {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) :=
  (Fin.cycleRange r).symm * Equiv.Perm.decomposeFin.symm (0, σ)

@[simp] theorem consPerm_zero {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    consPerm r σ 0 = r := by
  simp [consPerm, Fin.cycleRange_symm_zero]

@[simp] theorem consPerm_succ {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    consPerm r σ j.succ = r.succAbove (σ j) := by
  simp [consPerm, Fin.cycleRange_symm_succ]

theorem consPerm_sign {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    (Equiv.Perm.sign (consPerm r σ) : ℝ) = (-1 : ℝ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℝ) := by
  simp [consPerm, Equiv.Perm.decomposeFin.symm_sign, Fin.sign_cycleRange]

theorem consPerm_bijective {k : ℕ} :
    Function.Bijective fun q : Fin (k + 1) × Equiv.Perm (Fin k) => consPerm q.1 q.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
  rintro ⟨r, σ⟩ ⟨r', σ'⟩ h
  simp only at h
  have hr : r = r' := by
    have := congrArg (fun e => e 0) h
    simpa using this
  subst hr
  have h2 : Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), σ)
      = Equiv.Perm.decomposeFin.symm (0, σ') := by
    have := congrArg (fun e => Fin.cycleRange r * e) h
    simpa [consPerm, ← mul_assoc] using this
  simpa using Equiv.Perm.decomposeFin.symm.injective h2

/-- Splitting a signed sum over `Perm (Fin (k+1))` according to the image of `0`. -/
theorem sum_perm_succ_split {k : ℕ} (f : Fin (k + 1) → (Fin k → Fin (k + 1)) → ℝ) :
    ∑ τ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign τ : ℝ) * f (τ 0) (fun j => τ j.succ)
      = ∑ r : Fin (k + 1), (-1 : ℝ) ^ (r : ℕ) *
          ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * f r (fun j => r.succAbove (σ j)) := by
  have key := Fintype.sum_bijective _ consPerm_bijective
    (fun q : Fin (k + 1) × Equiv.Perm (Fin k) =>
      (-1 : ℝ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℝ) * f q.1 fun j => q.1.succAbove (q.2 j)))
    (fun τ : Equiv.Perm (Fin (k + 1)) => (Equiv.Perm.sign τ : ℝ) * f (τ 0) fun j => τ j.succ)
    (by rintro ⟨r, σ⟩; simp only [consPerm_zero, consPerm_succ, consPerm_sign]; ring)
  rw [← key, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]

/-- Reindexing an alternating sum by a permutation multiplies it by the sign. -/
theorem altCoeff_comp_perm {k n : ℕ} (ω : KForm k n) (i : Fin k → Fin n)
    (ρ : Equiv.Perm (Fin k)) (x : Fin n → ℝ) :
    altCoeff ω (fun r => i (ρ r)) x = (Equiv.Perm.sign ρ : ℝ) * altCoeff ω i x := by
  unfold altCoeff
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun σ => ρ * σ) (Group.mulLeft_bijective ρ) _ _ ?_
  intro σ
  have h2 : ((Equiv.Perm.sign ρ : ℤ) : ℝ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> simp [h]
  simp only [Equiv.Perm.mul_apply, map_mul, Units.val_mul, Int.cast_mul]
  ring_nf
  rw [h2]
  ring

/-- Moving the `r`-th index to the front costs a sign `(-1)^r`. -/
theorem altCoeff_cons_succAbove {k n : ℕ} (ω : KForm (k + 1) n) (i : Fin (k + 1) → Fin n)
    (r : Fin (k + 1)) (x : Fin n → ℝ) :
    altCoeff ω (Fin.cons (i r) fun a => i (r.succAbove a)) x
      = (-1 : ℝ) ^ (r : ℕ) * altCoeff ω i x := by
  have hfun : (Fin.cons (i r) fun a => i (r.succAbove a))
      = fun b => i ((Fin.cycleRange r).symm b) := by
    funext b
    refine Fin.cases ?_ (fun a => ?_) b
    · simp [Fin.cycleRange_symm_zero]
    · simp [Fin.cycleRange_symm_succ]
  rw [hfun, altCoeff_comp_perm]
  congr 1
  simp [Fin.sign_cycleRange]

/-! ### The cone primitive -/

/-- The cone (homotopy) operator based at `p`: the `m`-form whose coefficients are obtained by
contracting the alternation of `ω` with `x − p` and integrating along the ray from `p` to `x`. -/
noncomputable def conePrimitive {m n : ℕ} (ω : KForm (m + 1) n) (p : Fin n → ℝ) : KForm m n where
  coeff := fun j x =>
    ((m ! : ℕ) : ℝ)⁻¹ * ∑ q : Fin n, (x q - p q) * rayInt m (altCoeff ω (Fin.cons q j)) p x

section Main

variable {m n : ℕ} {E : Set (Fin n → ℝ)} {ω : KForm (m + 1) n} {p : Fin n → ℝ}

/-- The alternation of a `C¹` form is `C¹`. -/
theorem altCoeff_contDiffOn (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E) (i : Fin (m + 1) → Fin n) :
    ContDiffOn ℝ 1 (altCoeff ω i) E :=
  ContDiffOn.sum fun _ _ => contDiffOn_const.mul (hω _)

/-- The derivative of an alternation is the alternation of the derivatives. -/
theorem fderiv_altCoeff_apply (hE : IsOpen E) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    {x : Fin n → ℝ} (hx : x ∈ E) (i : Fin (m + 1) → Fin n) (v : Fin n → ℝ) :
    fderiv ℝ (altCoeff ω i) x v
      = ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ : ℝ) *
          fderiv ℝ (ω.coeff fun r => i (σ r)) x v := by
  have hd : ∀ j : Fin (m + 1) → Fin n, DifferentiableAt ℝ (ω.coeff j) x := fun j =>
    ((hω j).contDiffAt (hE.mem_nhds hx)).differentiableAt one_ne_zero
  unfold altCoeff
  rw [fderiv_fun_sum (fun σ _ => (hd _).const_mul _)]
  simp [fderiv_const_mul (hd _)]

/-- The closedness hypothesis of Theorem 10.39, rewritten as the classical statement `dω = 0`
for the alternation of `ω`. -/
theorem closed_alt (hE : IsOpen E) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0) :
    ∀ x ∈ E, ∀ l : Fin (m + 1 + 1) → Fin n,
      ∑ s : Fin (m + 1 + 1), (-1 : ℝ) ^ (s : ℕ) *
        fderiv ℝ (altCoeff ω fun a => l (s.succAbove a)) x (Pi.single (l s) 1) = 0 := by
  intro x hx l
  have h := hclosed x hx l
  have hsplit := sum_perm_succ_split (k := m + 1)
    (fun a g => fderiv ℝ (ω.coeff fun r => l (g r)) x (Pi.single (l a) 1))
  simp only [extDeriv] at h
  rw [h] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [fderiv_altCoeff_apply hE hω hx]

/-- The cone primitive is alternating. -/
theorem conePrimitive_comp_perm (j : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) (x : Fin n → ℝ) :
    (conePrimitive ω p).coeff (fun r => j (σ r)) x
      = (Equiv.Perm.sign σ : ℝ) * (conePrimitive ω p).coeff j x := by
  have hfun : ∀ q : Fin n, (altCoeff ω (Fin.cons q fun r => j (σ r)))
      = fun y => (Equiv.Perm.sign σ : ℝ) * altCoeff ω (Fin.cons q j) y := by
    intro q
    funext y
    have hc : (Fin.cons q fun r => j (σ r))
        = fun b => (Fin.cons q j : Fin (m + 1) → Fin n) (consPerm 0 σ b) := by
      funext b
      refine Fin.cases ?_ (fun a => ?_) b
      · simp
      · simp
    rw [hc, altCoeff_comp_perm, consPerm_sign]
    simp
  simp only [conePrimitive, hfun, rayInt_const_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- The cone primitive is an alternating form: its own alternation is `m !` times itself. -/
theorem altCoeff_conePrimitive (j : Fin m → Fin n) (x : Fin n → ℝ) :
    altCoeff (conePrimitive ω p) j x = ((m ! : ℕ) : ℝ) * (conePrimitive ω p).coeff j x := by
  unfold altCoeff
  have : ∀ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℝ) *
      (conePrimitive ω p).coeff (fun r => j (σ r)) x = (conePrimitive ω p).coeff j x := by
    intro σ
    rw [conePrimitive_comp_perm, ← mul_assoc]
    have h2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [h2, one_mul]
  rw [Finset.sum_congr rfl fun σ _ => this σ]
  simp [Finset.sum_const, Fintype.card_perm]

/-- The coefficients of the cone primitive are of class `C¹`. -/
theorem conePrimitive_contDiffOn (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E) (j : Fin m → Fin n) :
    ContDiffOn ℝ 1 ((conePrimitive ω p).coeff j) E := by
  refine contDiffOn_const.mul (ContDiffOn.sum fun q _ => ContDiffOn.mul ?_ ?_)
  · exact ((contDiff_apply ℝ ℝ q).contDiffOn.sub contDiffOn_const)
  · exact rayInt_contDiffOn hE hconv hp (altCoeff_contDiffOn hω _)

/-- The directional derivative of a coefficient of the cone primitive. -/
theorem conePrimitive_fderiv_apply (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E) {x : Fin n → ℝ} (hx : x ∈ E)
    (j : Fin m → Fin n) (s : Fin n) :
    fderiv ℝ ((conePrimitive ω p).coeff j) x (Pi.single s 1)
      = ((m ! : ℕ) : ℝ)⁻¹ * (rayInt m (altCoeff ω (Fin.cons s j)) p x
          + ∑ q : Fin n, (x q - p q) *
              ∫ t in (0:ℝ)..1, t ^ (m + 1) *
                fderiv ℝ (altCoeff ω (Fin.cons q j)) (p + t • (x - p)) (Pi.single s 1)) := by
  have hR : ∀ q : Fin n, DifferentiableAt ℝ (rayInt m (altCoeff ω (Fin.cons q j)) p) x :=
    fun q => rayInt_differentiableAt hE hconv hp (altCoeff_contDiffOn hω _) hx
  have hL : ∀ q : Fin n, HasFDerivAt (fun y : Fin n → ℝ => y q - p q)
      (ContinuousLinearMap.proj q : (Fin n → ℝ) →L[ℝ] ℝ) x :=
    fun q => (hasFDerivAt_apply q x).sub_const _
  have hsum : DifferentiableAt ℝ (fun y : Fin n → ℝ =>
      ∑ q : Fin n, (y q - p q) * rayInt m (altCoeff ω (Fin.cons q j)) p y) x :=
    DifferentiableAt.fun_sum fun q _ => ((hL q).differentiableAt).mul (hR q)
  show fderiv ℝ (fun y : Fin n → ℝ => ((m ! : ℕ) : ℝ)⁻¹ *
      ∑ q : Fin n, (y q - p q) * rayInt m (altCoeff ω (Fin.cons q j)) p y) x (Pi.single s 1) = _
  rw [fderiv_const_mul hsum]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [fderiv_fun_sum (A := fun (q : Fin n) (y : Fin n → ℝ) =>
    (y q - p q) * rayInt m (altCoeff ω (Fin.cons q j)) p y)
    (fun q _ => ((hL q).differentiableAt).mul (hR q))]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  have hterm : ∀ q : Fin n,
      fderiv ℝ (fun y : Fin n → ℝ => (y q - p q) * rayInt m (altCoeff ω (Fin.cons q j)) p y) x
          (Pi.single s 1)
        = (if s = q then (1 : ℝ) else 0) * rayInt m (altCoeff ω (Fin.cons q j)) p x
          + (x q - p q) * ∫ t in (0:ℝ)..1, t ^ (m + 1) *
              fderiv ℝ (altCoeff ω (Fin.cons q j)) (p + t • (x - p)) (Pi.single s 1) := by
    intro q
    rw [fderiv_fun_mul ((hL q).differentiableAt) (hR q)]
    rw [(hL q).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    rw [rayInt_fderiv_apply hE hconv hp (altCoeff_contDiffOn hω _) hx]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      eq_comm (a := q) (b := s)]
    ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_add_distrib]
  congr 1
  simp

/-- The closedness relation in the form needed for the cone computation. -/
theorem closed_alt_cons (hE : IsOpen E) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0)
    {y : Fin n → ℝ} (hy : y ∈ E) (i : Fin (m + 1) → Fin n) (q : Fin n) :
    ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
        fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) y (Pi.single (i r) 1)
      = fderiv ℝ (altCoeff ω i) y (Pi.single q 1) := by
  have h := closed_alt hE hω hclosed y hy (Fin.cons q i)
  rw [Fin.sum_univ_succ] at h
  have h0 : (fun a => (Fin.cons q i : Fin (m + 1 + 1) → Fin n) ((0 : Fin (m + 1 + 1)).succAbove a))
      = i := by
    funext a; simp
  have hs : ∀ r : Fin (m + 1),
      (fun a => (Fin.cons q i : Fin (m + 1 + 1) → Fin n) (r.succ.succAbove a))
        = Fin.cons q fun a => i (r.succAbove a) := by
    intro r
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simp
    · simp [Fin.succ_succAbove_succ]
  simp only [h0, hs, Fin.cons_zero, Fin.cons_succ, Fin.val_succ, pow_succ, Fin.val_zero,
    pow_zero, one_mul] at h
  have key : ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) * (-1) *
      fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) y (Pi.single (i r) 1)
      = - ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
      fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) y (Pi.single (i r) 1) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [key] at h
  linarith

/-- The signed sum over permutations of the derivatives of the cone primitive. -/
theorem sum_sign_fderiv_conePrimitive (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E) {x : Fin n → ℝ} (hx : x ∈ E)
    (j : Fin m → Fin n) (v : Fin n → ℝ) :
    ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℝ) *
        fderiv ℝ ((conePrimitive ω p).coeff fun a => j (σ a)) x v
      = ((m ! : ℕ) : ℝ) * fderiv ℝ ((conePrimitive ω p).coeff j) x v := by
  have hd : DifferentiableAt ℝ ((conePrimitive ω p).coeff j) x :=
    ((conePrimitive_contDiffOn hE hconv hp hω j).contDiffAt
      (hE.mem_nhds hx)).differentiableAt one_ne_zero
  have hterm : ∀ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℝ) *
      fderiv ℝ ((conePrimitive ω p).coeff fun a => j (σ a)) x v
        = fderiv ℝ ((conePrimitive ω p).coeff j) x v := by
    intro σ
    have hfun : ((conePrimitive ω p).coeff fun a => j (σ a))
        = fun y => (Equiv.Perm.sign σ : ℝ) * (conePrimitive ω p).coeff j y := by
      funext y
      exact conePrimitive_comp_perm j σ y
    rw [hfun, fderiv_const_mul hd]
    have h2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ← mul_assoc, h2, one_mul]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ]
  simp [Finset.sum_const, Fintype.card_perm]

/-- The "free" part of the cone computation: the terms without a derivative of `ω`. -/
theorem cone_sum_free {x : Fin n → ℝ} (i : Fin (m + 1) → Fin n) :
    ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
        rayInt m (altCoeff ω (Fin.cons (i r) fun a => i (r.succAbove a))) p x
      = ((m : ℝ) + 1) * rayInt m (altCoeff ω i) p x := by
  have hterm : ∀ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
      rayInt m (altCoeff ω (Fin.cons (i r) fun a => i (r.succAbove a))) p x
        = rayInt m (altCoeff ω i) p x := by
    intro r
    have hfun : (altCoeff ω (Fin.cons (i r) fun a => i (r.succAbove a)))
        = fun y => (-1 : ℝ) ^ (r : ℕ) * altCoeff ω i y := by
      funext y
      exact altCoeff_cons_succAbove ω i r y
    rw [hfun, rayInt_const_smul, ← mul_assoc, ← pow_add]
    rw [show (r : ℕ) + (r : ℕ) = 2 * (r : ℕ) by ring, pow_mul]
    norm_num
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  simp [Finset.sum_const]

/-- The "derivative" part of the cone computation, where closedness of `ω` is used. -/
theorem cone_sum_deriv (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0)
    {x : Fin n → ℝ} (hx : x ∈ E) (i : Fin (m + 1) → Fin n) :
    ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
        (∑ q : Fin n, (x q - p q) *
          ∫ t in (0:ℝ)..1, t ^ (m + 1) *
            fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
              (Pi.single (i r) 1))
      = ∫ t in (0:ℝ)..1, t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (x - p) := by
  have hint : ∀ (j : Fin (m + 1) → Fin n) (v : Fin n → ℝ), IntervalIntegrable
      (fun t : ℝ => t ^ (m + 1) * fderiv ℝ (altCoeff ω j) (p + t • (x - p)) v) volume 0 1 := by
    intro j v
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuous_pow (m + 1)).continuousOn.mul
      (continuousOn_fderiv_comp_ray hE hconv hp hx (altCoeff_contDiffOn hω j) v)
  have inner : ∀ q : Fin n, ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
      (∫ t in (0:ℝ)..1, t ^ (m + 1) *
        fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
          (Pi.single (i r) 1))
      = ∫ t in (0:ℝ)..1, t ^ (m + 1) *
          fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1) := by
    intro q
    have h1 : ∀ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
        (∫ t in (0:ℝ)..1, t ^ (m + 1) *
          fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
            (Pi.single (i r) 1))
        = ∫ t in (0:ℝ)..1, (-1 : ℝ) ^ (r : ℕ) * (t ^ (m + 1) *
          fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
            (Pi.single (i r) 1)) := fun r => (intervalIntegral.integral_const_mul _ _).symm
    rw [Finset.sum_congr rfl fun r _ => h1 r,
      ← intervalIntegral.integral_finset_sum (fun r _ => ((hint _ _).const_mul _))]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hmem : p + t • (x - p) ∈ E := segment_mem_of_convex hconv hp hx ht
    have hkey := closed_alt_cons hE hω hclosed hmem i q
    calc ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) * (t ^ (m + 1) *
            fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
              (Pi.single (i r) 1))
        = t ^ (m + 1) * ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
            fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
              (Pi.single (i r) 1) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1) := by rw [hkey]
  have hswap : ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
      (∑ q : Fin n, (x q - p q) *
        ∫ t in (0:ℝ)..1, t ^ (m + 1) *
          fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
            (Pi.single (i r) 1))
      = ∑ q : Fin n, (x q - p q) * ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) *
          (∫ t in (0:ℝ)..1, t ^ (m + 1) *
            fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
              (Pi.single (i r) 1)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring
  rw [hswap, Finset.sum_congr rfl fun q _ => by rw [inner q]]
  have h2 : ∀ q : Fin n, (x q - p q) *
      (∫ t in (0:ℝ)..1, t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1))
      = ∫ t in (0:ℝ)..1, (x q - p q) *
        (t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1)) :=
    fun q => (intervalIntegral.integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun q _ => h2 q,
    ← intervalIntegral.integral_finset_sum (fun q _ => ((hint i _).const_mul _))]
  refine intervalIntegral.integral_congr fun t _ => ?_
  calc ∑ q : Fin n, (x q - p q) *
          (t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1))
      = t ^ (m + 1) * ∑ q : Fin n, (x q - p q) *
          fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (Pi.single q 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    _ = t ^ (m + 1) * fderiv ℝ (altCoeff ω i) (p + t • (x - p)) (x - p) := by
        rw [sum_apply_single]; rfl

/-- The key identity: the exterior derivative of the cone primitive has the same alternation
as `ω`. -/
theorem extDeriv_conePrimitive_altCoeff (hE : IsOpen E) (hconv : Convex ℝ E) (hp : p ∈ E)
    (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0)
    {x : Fin n → ℝ} (hx : x ∈ E) (i : Fin (m + 1) → Fin n) :
    altCoeff (extDeriv (conePrimitive ω p)) i x = altCoeff ω i x := by
  have hfac : ((m ! : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  -- Step 1: split the alternating sum according to the index sent to the front.
  have step1 : altCoeff (extDeriv (conePrimitive ω p)) i x
      = ∑ r : Fin (m + 1), (-1 : ℝ) ^ (r : ℕ) * (((m ! : ℕ) : ℝ) *
          fderiv ℝ ((conePrimitive ω p).coeff fun a => i (r.succAbove a)) x
            (Pi.single (i r) 1)) := by
    unfold altCoeff
    simp only [extDeriv]
    rw [sum_perm_succ_split (k := m)
      (fun a g => fderiv ℝ ((conePrimitive ω p).coeff fun r => i (g r)) x (Pi.single (i a) 1))]
    refine Finset.sum_congr rfl fun r _ => congrArg (fun z : ℝ => (-1 : ℝ) ^ (r : ℕ) * z) ?_
    exact sum_sign_fderiv_conePrimitive hE hconv hp hω hx (fun a => i (r.succAbove a))
      (Pi.single (i r) 1)
  -- Step 2: compute each derivative of the cone primitive.
  have step2 : ∀ r : Fin (m + 1),
      ((m ! : ℕ) : ℝ) * fderiv ℝ ((conePrimitive ω p).coeff fun a => i (r.succAbove a)) x
          (Pi.single (i r) 1)
        = rayInt m (altCoeff ω (Fin.cons (i r) fun a => i (r.succAbove a))) p x
          + ∑ q : Fin n, (x q - p q) *
              ∫ t in (0:ℝ)..1, t ^ (m + 1) *
                fderiv ℝ (altCoeff ω (Fin.cons q fun a => i (r.succAbove a))) (p + t • (x - p))
                  (Pi.single (i r) 1) := by
    intro r
    rw [conePrimitive_fderiv_apply hE hconv hp hω hx, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]
  rw [step1, Finset.sum_congr rfl fun r _ => by rw [step2 r]]
  -- Step 3: separate the two parts and use closedness and the fundamental theorem of calculus.
  simp only [mul_add]
  rw [Finset.sum_add_distrib, cone_sum_free i, cone_sum_deriv hE hconv hp hω hclosed hx i]
  exact rayInt_ftc hE hconv hp (altCoeff_contDiffOn hω i) hx

end Main

end Rudin

open Rudin

/-- Rudin, Theorem 10.39 (Poincaré's lemma), pointwise form. -/
theorem solution (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E)
    (hconv : Convex ℝ E) (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0) :
    ∃ η : KForm m n, (∀ i, ContDiffOn ℝ 1 (η.coeff i) E) ∧
      ∀ x ∈ E, ∀ i : Fin (m + 1) → Fin n,
        ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ : ℝ) *
            (extDeriv η).coeff (fun r => i (σ r)) x
          = ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ : ℝ) *
            ω.coeff (fun r => i (σ r)) x := by
  rcases Set.eq_empty_or_nonempty E with rfl | ⟨p, hp⟩
  · exact ⟨⟨fun _ _ => 0⟩, fun _ => contDiffOn_empty, by simp⟩
  · refine ⟨conePrimitive ω p, fun j => conePrimitive_contDiffOn hE hconv hp hω j, ?_⟩
    intro x hx i
    exact extDeriv_conePrimitive_altCoeff hE hconv hp hω hclosed hx i

