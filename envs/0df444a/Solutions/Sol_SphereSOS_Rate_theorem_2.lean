-- Prove2me | solution 1 for SphereSOS.Rate.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T15:36:00.083007+00:00
-- url     : https://prove2.me/submissions/0a4d7b27-3f8f-4452-b0e0-0b96b28b7e40

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

-- BEGIN SSProof/SharedBasics.lean
section

open scoped BigOperators
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

abbrev ESpace (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : ESpace d) 1

def sphereCoords {d : ℕ} (x : UnitSphere d) : Fin d → ℝ := fun i => x.val i

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SharedBasics.lean

-- BEGIN SSProof/MonicOrthogonal.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def momentPairing (L : Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) :
    Polynomial.degreeLT ℝ j →ₗ[ℝ] Module.Dual ℝ (Polynomial.degreeLT ℝ j) where
  toFun p :=
    { toFun := fun q => L (p.val*q.val)
      map_add' := by intro q r; simp [mul_add]
      map_smul' := by intro c q; simp }
  map_add' := by intro p q; ext r; simp [add_mul]
  map_smul' := by intro c p; ext q; simp

 theorem momentPairing_injective (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    Function.Injective (momentPairing L j) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  have he : L (p.val*p.val)=0 := congrArg (fun f => f p) hp
  apply Subtype.ext
  by_contra h
  exact (ne_of_gt (hpos p.val h)) he

 theorem exists_monic_orthogonal (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    ∃ G : Polynomial ℝ, G.Monic ∧ G.natDegree=j ∧
      ∀ q : Polynomial ℝ, q.degree < j → L (G*q)=0 := by
  let : FiniteDimensional ℝ (Polynomial.degreeLT ℝ j) :=
    Module.Finite.of_injective (Polynomial.degreeLTEquiv ℝ j).toLinearMap
      (Polynomial.degreeLTEquiv ℝ j).injective
  let b : Module.Dual ℝ (Polynomial.degreeLT ℝ j) :=
    { toFun := fun q => L (Polynomial.X^j*q.val)
      map_add' := by intro q r; simp [mul_add]
      map_smul' := by intro c q; simp }
  have hs : Function.Surjective (momentPairing L j) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp (momentPairing_injective L hpos j)
  obtain ⟨p,hp⟩ := hs b
  let G := (Polynomial.monicEquivDegreeLT (R := ℝ) j).symm (-p)
  refine ⟨G.val,G.property.1,G.property.2,?_⟩
  intro q hq
  have he := congrArg (fun f : Module.Dual ℝ (Polynomial.degreeLT ℝ j) =>
    f ⟨q,Polynomial.mem_degreeLT.mpr hq⟩) hp
  change L (p.val*q)=L (Polynomial.X^j*q) at he
  change L ((Polynomial.X^j + -p.val)*q)=0
  rw [add_mul,neg_mul,map_add,map_neg,he]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MonicOrthogonal.lean

-- BEGIN SSProof/OrthogonalSequence.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def orthogonalPolynomial (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) : Polynomial ℝ :=
  Classical.choose (exists_monic_orthogonal L hpos j)

theorem orthogonalPolynomial_spec (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    (orthogonalPolynomial L hpos j).Monic ∧
      (orthogonalPolynomial L hpos j).natDegree = j ∧
      ∀ q : Polynomial ℝ, q.degree < j → L (orthogonalPolynomial L hpos j*q)=0 :=
  Classical.choose_spec (exists_monic_orthogonal L hpos j)

theorem orthogonalPolynomial_pair (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) {i j : ℕ} (hij : i < j) :
    L (orthogonalPolynomial L hpos j * orthogonalPolynomial L hpos i) = 0 := by
  apply (orthogonalPolynomial_spec L hpos j).2.2
  rw [Polynomial.degree_eq_natDegree (orthogonalPolynomial_spec L hpos i).1.ne_zero,
    (orthogonalPolynomial_spec L hpos i).2.1]
  exact_mod_cast hij

end SphereSOS.Rate.SSFresh

end
-- END SSProof/OrthogonalSequence.lean

-- BEGIN SSProof/OrthogonalMultiple.lean
section

namespace SphereSOS.Rate.SSFresh

 theorem orthogonal_multiple (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ)
    (R : Polynomial ℝ) (hR : R.degree≤j)
    (horth : ∀ q : Polynomial ℝ, q.degree<j → L (R*q)=0) :
    R = Polynomial.C (R.coeff j)*orthogonalPolynomial L hpos j := by
  let G := orthogonalPolynomial L hpos j
  have hs := orthogonalPolynomial_spec L hpos j
  have hG : G.degree=j := by
    rw [Polynomial.degree_eq_natDegree hs.1.ne_zero,hs.2.1]
  have hc : G.coeff j=1 := by
    rw [← hs.2.1]
    exact hs.1.coeff_natDegree
  let D := R-Polynomial.C (R.coeff j)*G
  have hD : D.degree<j := by
    apply (Polynomial.degree_lt_iff_coeff_zero D j).mpr
    intro m hm
    change (R-Polynomial.C (R.coeff j)*G).coeff m=0
    rw [Polynomial.coeff_sub,Polynomial.coeff_C_mul]
    by_cases he : m=j
    · rw [he,hc]
      ring
    · have hlt : j < m := lt_of_le_of_ne hm (Ne.symm he)
      have hr : R.coeff m=0 := Polynomial.coeff_eq_zero_of_degree_lt
        (hR.trans_lt (by exact_mod_cast hlt))
      have hg : G.coeff m=0 := Polynomial.coeff_eq_zero_of_degree_lt
        (by rw [hG]; exact_mod_cast hlt)
      rw [hr,hg]
      ring
  have hz : L (D*D)=0 := by
    have hr := horth D hD
    have hg := hs.2.2 D hD
    change L ((R-Polynomial.C (R.coeff j)*G)*D)=0
    rw [sub_mul,mul_assoc,map_sub,Polynomial.C_mul',map_smul]
    change L (R*D)-R.coeff j*L (G*D)=0
    rw [hr,hg]
    ring
  have hd : D=0 := by
    by_contra hd
    exact (ne_of_gt (hpos D hd)) hz
  exact sub_eq_zero.mp hd

end SphereSOS.Rate.SSFresh

end
-- END SSProof/OrthogonalMultiple.lean

-- BEGIN SSProof/MonicDifference.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem monic_X_sub_degree (p q : Polynomial ℝ) (j : ℕ)
    (hp : p.Monic) (hq : q.Monic) (hpd : p.natDegree=j) (hqd : q.natDegree=j+1) :
    (X*p-q).degree < ((j+1 : ℕ) : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub]
  rcases eq_or_lt_of_le hm with rfl | hlt
  · rw [coeff_X_mul]
    have hp1 : p.coeff j=1 := by rw [← hpd]; exact hp.coeff_natDegree
    have hq1 : q.coeff (j+1)=1 := by rw [← hqd]; exact hq.coeff_natDegree
    rw [hp1, hq1]
    ring
  · have hm0 : q.coeff m=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hxp : (X*p).natDegree=j+1 := by
      rw [natDegree_X_mul hp.ne_zero, hpd]
    have hp0 : (X*p).coeff m=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hm0, hp0]
    ring

theorem monic_X_sub_degree_two (p q : Polynomial ℝ) (j : ℕ)
    (hp : p.Monic) (hq : q.Monic) (hpd : p.natDegree=j+1) (hqd : q.natDegree=j+2)
    (hpz : p.coeff j=0) (hqz : q.coeff (j+1)=0) :
    (X*p-q).degree ≤ (j : WithBot ℕ) := by
  rw [degree_le_iff_coeff_zero]
  intro m hm
  have hmm : j+1 ≤ m := by exact_mod_cast hm
  rcases eq_or_lt_of_le hmm with rfl | hlt
  · rw [coeff_sub, coeff_X_mul, hpz, hqz]
    ring
  · exact (degree_lt_iff_coeff_zero _ (j+2)).mp
      (monic_X_sub_degree p q (j+1) hp hq hpd (by omega)) m (by omega)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MonicDifference.lean

-- BEGIN SSProof/ThreeTerm.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem degree_X_mul_lt {p : Polynomial ℝ} {j : ℕ} (hp : p.degree<j) :
    (X*p).degree < ((j+1 : ℕ) : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro m hm
  cases m with
  | zero => omega
  | succ m => rw [coeff_X_mul]; exact hp m (by omega)

theorem orthogonal_three_term (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ)
    (h1 : (orthogonalPolynomial L hpos (j+1)).coeff j=0)
    (h2 : (orthogonalPolynomial L hpos (j+2)).coeff (j+1)=0) :
    X*orthogonalPolynomial L hpos (j+1)-orthogonalPolynomial L hpos (j+2) =
      C ((X*orthogonalPolynomial L hpos (j+1)-orthogonalPolynomial L hpos (j+2)).coeff j)*
        orthogonalPolynomial L hpos j := by
  have hsp := orthogonalPolynomial_spec L hpos (j+1)
  have hsq := orthogonalPolynomial_spec L hpos (j+2)
  apply orthogonal_multiple L hpos j
  · exact monic_X_sub_degree_two _ _ j hsp.1 hsq.1 hsp.2.1 hsq.2.1 h1 h2
  · intro q hq
    have hp0 := hsp.2.2 (X*q) (degree_X_mul_lt hq)
    have hq0 := hsq.2.2 q (hq.trans_le (by exact_mod_cast (show j ≤ j+2 by omega)))
    rw [sub_mul, map_sub]
    have he : X*orthogonalPolynomial L hpos (j+1)*q =
        orthogonalPolynomial L hpos (j+1)*(X*q) := by ring
    rw [he, hp0, hq0]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/ThreeTerm.lean

-- BEGIN SSProof/SphereLaw.lean
section

open scoped BigOperators
open MeasureTheory Set

namespace SphereSOS.Rate.SSFresh

noncomputable def sphereLaw (d : ℕ) : Measure (UnitSphere d) :=
  ((volume : Measure (ESpace d)).toSphere Set.univ)⁻¹ •
    (volume : Measure (ESpace d)).toSphere

theorem sphereLaw_probability {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (sphereLaw d) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let : NeZero ((volume : Measure (ESpace d)).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold sphereLaw
  infer_instance

theorem sphereLaw_openPos (d : ℕ) : (sphereLaw d).IsOpenPosMeasure := by
  unfold sphereLaw
  apply Measure.isOpenPosMeasure_smul
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

theorem sphereCoords_mem {d : ℕ} (x : UnitSphere d) :
    sphereCoords x ∈ SphereSOS.Rate.sphere d := by
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  change ∑ i, x.val i ^ 2 = 1
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

theorem sphereCoords_continuous {d : ℕ} :
    Continuous (sphereCoords : UnitSphere d → Fin d → ℝ) := by
  unfold sphereCoords
  fun_prop

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SphereLaw.lean

-- BEGIN SSProof/CircleGeometry.lean
section

open scoped RealInnerProductSpace

namespace SphereSOS.Rate.SSFresh

 theorem unit_circle_norm {d : ℕ} (x u : ESpace d) (hx : ‖x‖=1) (hu : ‖u‖=1)
    (hxu : ⟪x,u⟫=0) (t r : ℝ) (htr : t^2+r^2=1) :
    ‖t • x+r • u‖=1 := by
  have h := norm_add_sq_real (t • x) (r • u)
  simp only [norm_smul, Real.norm_eq_abs, hx, hu, mul_one, real_inner_smul_left,
    real_inner_smul_right, hxu, mul_zero, sq_abs] at h
  nlinarith [norm_nonneg (t • x+r • u)]

 theorem unit_circle_coords {d : ℕ} (x u : ESpace d) (hx : ‖x‖=1) (hu : ‖u‖=1)
    (hxu : ⟪x,u⟫=0) (t r : ℝ) (htr : t^2+r^2=1) :
    (fun i => t*x i+r*u i) ∈ sphere d := by
  have hn := unit_circle_norm x u hx hu hxu t r htr
  have he := EuclideanSpace.real_norm_sq_eq (t • x+r • u)
  change ∑ i, (t*x i+r*u i)^2=1
  simpa only [hn, one_pow, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using he.symm

 theorem perpendicular_remainder {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1) :
    ⟪x, y - ⟪x,y⟫ • x⟫=0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx]
  ring

 theorem remainder_norm_sq {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖y - ⟪x,y⟫ • x‖^2 = 1-⟪x,y⟫^2 := by
  rw [norm_sub_sq_real, hy, norm_smul, hx, Real.norm_eq_abs, mul_one,
    real_inner_smul_right, real_inner_comm y x, sq_abs]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/CircleGeometry.lean

-- BEGIN SSProof/CoordinateSupport.lean
section

open scoped BigOperators
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

theorem exists_sphere_coordinate {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (t : ℝ) (ht : |t| ≤ 1) : ∃ y : UnitSphere d, sphereCoords y i = t := by
  let x : ESpace d := EuclideanSpace.single i 1
  let u : ESpace d := EuclideanSpace.single j 1
  have hx : ‖x‖ = 1 := by simp [x]
  have hu : ‖u‖ = 1 := by simp [u]
  have hxu : inner ℝ x u = 0 := by
    simp [x, u, EuclideanSpace.inner_single_left, hij]
  have ht2 : 0 ≤ 1-t^2 := by
    have h := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0:ℝ)≤1)).mpr ht
    simpa only [sq_abs, one_pow] using sub_nonneg.mpr h
  have hn := unit_circle_norm x u hx hu hxu t (Real.sqrt (1-t^2))
    (by rw [Real.sq_sqrt ht2]; ring)
  refine ⟨⟨t • x + Real.sqrt (1-t^2) • u, ?_⟩, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hn
  · simp [sphereCoords, x, u, hij]

theorem polynomial_nonzero_on_interval (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ t : ℝ, -1 < t ∧ t < 1 ∧ p.eval t ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.Ioo_infinite (by norm_num : (-1:ℝ)<1)).mono
  intro t ht
  exact h t ht.1 ht.2

end SphereSOS.Rate.SSFresh

end
-- END SSProof/CoordinateSupport.lean

-- BEGIN SSProof/SphereAction.lean
section

open scoped BigOperators Pointwise
open MeasureTheory Set

namespace SphereSOS.Rate.SSFresh

noncomputable def sphereAction {d : ℕ} (e : ESpace d ≃ₗᵢ[ℝ] ESpace d) :
    UnitSphere d ≃ₜ UnitSphere d where
  toFun x := ⟨e x.val, by simpa only [Metric.mem_sphere, dist_zero_right, e.norm_map] using x.property⟩
  invFun x := ⟨e.symm x.val, by simpa only [Metric.mem_sphere, dist_zero_right,
    e.symm.norm_map] using x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem sphere_cone_preimage {d : ℕ} (e : ESpace d ≃ₗᵢ[ℝ] ESpace d)
    (s : Set (UnitSphere d)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereAction e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z.val, ⟨sphereAction e z, hz, rfl⟩, (e.map_smul r z.val).symm⟩
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, he⟩
    refine ⟨r, hr, e.symm z.val, ⟨sphereAction e.symm z, ?_, rfl⟩, ?_⟩
    · change sphereAction e (sphereAction e.symm z) ∈ s
      have heq : sphereAction e (sphereAction e.symm z) = z := by
        apply Subtype.ext
        exact e.apply_symm_apply z.val
      rw [heq]
      exact hz
    · apply e.injective
      simpa only [e.map_smul, e.apply_symm_apply] using he

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SphereAction.lean

-- BEGIN SSProof/SphereInvariance.lean
section

open scoped Pointwise
open MeasureTheory Set

namespace SphereSOS.Rate.SSFresh

theorem sphereAction_preserves_unnormalized {d : ℕ}
    (e : ESpace d ≃ₗᵢ[ℝ] ESpace d) :
    MeasurePreserving (sphereAction e)
      (volume : Measure (ESpace d)).toSphere
      (volume : Measure (ESpace d)).toSphere := by
  refine ⟨(sphereAction e).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereAction e).continuous.measurable hs,
    Measure.toSphere_apply' _ ((sphereAction e).continuous.measurable hs),
    Measure.toSphere_apply' _ hs, sphere_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphereAction_preserves {d : ℕ} (e : ESpace d ≃ₗᵢ[ℝ] ESpace d) :
    MeasurePreserving (sphereAction e) (sphereLaw d) (sphereLaw d) := by
  exact (sphereAction_preserves_unnormalized e).smul_measure _

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SphereInvariance.lean

-- BEGIN SSProof/SphereMoments.lean
section

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

noncomputable def linearMoment {d : ℕ} (r : ℕ) (x : ESpace d) : ℝ :=
  ∫ y : UnitSphere d, (inner ℝ x y.val) ^ r ∂sphereLaw d

theorem linearMoment_isometry {d : ℕ} (r : ℕ)
    (e : ESpace d ≃ₗᵢ[ℝ] ESpace d) (x : ESpace d) :
    linearMoment r (e x) = linearMoment r x := by
  unfold linearMoment
  have h := (sphereAction_preserves e).integral_comp
    (sphereAction e).measurableEmbedding
    (fun y : UnitSphere d => (inner ℝ (e x) y.val) ^ r)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with y
  change (inner ℝ (e x) (e y.val)) ^ r = _
  rw [e.inner_map_map]

theorem linearMoment_eq_of_norm_eq {d : ℕ} (r : ℕ) (x y : ESpace d)
    (h : ‖x‖ = ‖y‖) : linearMoment r x = linearMoment r y := by
  let e := (ℝ ∙ (x-y)).orthogonal.reflection
  have he : e x = y := Submodule.reflection_sub h
  rw [← he]
  exact (linearMoment_isometry r e x).symm

theorem linearMoment_smul {d : ℕ} (r : ℕ) (a : ℝ) (x : ESpace d) :
    linearMoment r (a • x) = a ^ r * linearMoment r x := by
  simp only [linearMoment, real_inner_smul_left, mul_pow, integral_const_mul]

theorem linearMoment_odd {d : ℕ} (r : ℕ) (hr : Odd r) (x : ESpace d) :
    linearMoment r x = 0 := by
  have h := linearMoment_eq_of_norm_eq r (-x) x (norm_neg x)
  have hn : linearMoment r (-x) = -linearMoment r x := by
    simpa only [neg_one_smul, hr.neg_one_pow, neg_one_mul] using
      linearMoment_smul r (-1) x
  linarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SphereMoments.lean

-- BEGIN SSProof/MomentPolynomial.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def tensorMoment {d r : ℕ} (f : Fin r → Fin d) : ℝ :=
  ∫ y : UnitSphere d, ∏ j, sphereCoords y (f j) ∂sphereLaw d

noncomputable def momentPolynomial (d r : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ f : Fin r → Fin d, C (tensorMoment f) * ∏ j, X (f j)

theorem sphere_continuous_integrable {d : ℕ} (hd : 0 < d)
    {f : UnitSphere d → ℝ} (hf : Continuous f) : Integrable f (sphereLaw d) := by
  let : IsProbabilityMeasure (sphereLaw d) := sphereLaw_probability hd
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem tensorIntegrable {d r : ℕ} (hd : 0 < d) (f : Fin r → Fin d) :
    Integrable (fun y : UnitSphere d => ∏ j, sphereCoords y (f j)) (sphereLaw d) := by
  apply sphere_continuous_integrable hd
  unfold sphereCoords
  fun_prop

theorem eval_momentPolynomial {d : ℕ} (hd : 0 < d) (r : ℕ) (x : ESpace d) :
    eval (fun i => x i) (momentPolynomial d r) = linearMoment r x := by
  classical
  simp only [momentPolynomial, map_sum, map_mul, eval_C, map_prod, eval_X]
  unfold linearMoment
  have hi (y : UnitSphere d) : inner ℝ x y.val = ∑ i, x i * sphereCoords y i := by
    simp [PiLp.inner_apply, sphereCoords, mul_comm]
  simp_rw [hi, Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro f _
    rw [integral_const_mul]
    simp only [tensorMoment]
    ring
  · intro f _
    exact (tensorIntegrable hd f).const_mul _

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MomentPolynomial.lean

-- BEGIN SSProof/CoordinateMean.lean
section

open MeasureTheory

namespace SphereSOS.Rate.SSFresh

theorem coordinate_eval_integrable {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p : Polynomial ℝ) :
    Integrable (fun y : UnitSphere d => p.eval (sphereCoords y i)) (sphereLaw d) := by
  apply sphere_continuous_integrable hd
  exact p.continuous.comp ((continuous_apply i).comp sphereCoords_continuous)

noncomputable def coordinateMean {d : ℕ} (hd : 0 < d) (i : Fin d) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ y : UnitSphere d, p.eval (sphereCoords y i) ∂sphereLaw d
  map_add' p q := by
    simp only [Polynomial.eval_add]
    exact integral_add (coordinate_eval_integrable hd i p) (coordinate_eval_integrable hd i q)
  map_smul' a p := by simp [Polynomial.eval_smul, integral_const_mul]

theorem coordinateMean_square_pos {d : ℕ} (hd : 0 < d) (i j : Fin d) (hij : i ≠ j)
    (p : Polynomial ℝ) (hp : p ≠ 0) : 0 < coordinateMean hd i (p*p) := by
  let : (sphereLaw d).IsOpenPosMeasure := sphereLaw_openPos d
  obtain ⟨t, ht0, ht1, hpt⟩ := polynomial_nonzero_on_interval p hp
  obtain ⟨y, hy⟩ := exists_sphere_coordinate i j hij t (abs_le.mpr ⟨ht0.le, ht1.le⟩)
  apply integral_pos_of_integrable_nonneg_nonzero
    (x := y) ((p*p).continuous.comp ((continuous_apply i).comp sphereCoords_continuous))
    (coordinate_eval_integrable hd i (p*p))
  · intro z
    simp only [Polynomial.eval_mul]
    exact mul_self_nonneg _
  · simp only [Function.comp_def, Polynomial.eval_mul, hy]
    exact mul_ne_zero hpt hpt

end SphereSOS.Rate.SSFresh

end
-- END SSProof/CoordinateMean.lean

-- BEGIN SSProof/PolynomialMean.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

theorem eval_integrable {d : ℕ} (hd : 0 < d) (p : MvPolynomial (Fin d) ℝ) :
    Integrable (fun y : UnitSphere d => eval (sphereCoords y) p) (sphereLaw d) := by
  apply sphere_continuous_integrable hd
  exact p.continuous_eval.comp sphereCoords_continuous

noncomputable def polynomialMean {d : ℕ} (hd : 0 < d) :
    MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ y : UnitSphere d, eval (sphereCoords y) p ∂sphereLaw d
  map_add' p q := by
    simp only [map_add]
    exact integral_add (eval_integrable hd p) (eval_integrable hd q)
  map_smul' a p := by
    simp only [smul_eval, integral_const_mul, RingHom.id_apply, smul_eq_mul]

noncomputable def coefficientMean {d : ℕ} (hd : 0 < d) :
    MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ) →ₗ[ℝ]
      MvPolynomial (Fin d) ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (polynomialMean hd) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem coefficientMean_coeff {d : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) (a : Fin d →₀ ℕ) :
    coeff a (coefficientMean hd p) = polynomialMean hd (coeff a p) := rfl

theorem polynomialMean_normSq_mul {d : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) ℝ) :
    polynomialMean hd (normSqPoly d * p) = polynomialMean hd p := by
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [map_mul, normSqPoly, map_sum, map_pow, eval_X]
  have h := sphereCoords_mem y
  change (∑ i, sphereCoords y i ^ 2) = 1 at h
  rw [h, one_mul]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/PolynomialMean.lean

-- BEGIN SSProof/MeanDerivatives.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

theorem coefficientMean_pderiv {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) :
    coefficientMean hd (pderiv i p) = pderiv i (coefficientMean hd p) := by
  ext a
  simp only [coefficientMean_coeff, coeff_pderiv]
  simpa [smul_eq_C_mul, smul_eq_mul, mul_comm] using
    (polynomialMean hd).map_smul ((a i + 1 : ℕ) : ℝ)
      (coeff (a + Finsupp.single i 1) p)

theorem coefficientMean_monomial {d : ℕ} (hd : 0 < d)
    (a : Fin d →₀ ℕ) (p : MvPolynomial (Fin d) ℝ) :
    coefficientMean hd (monomial a p) = monomial a (polynomialMean hd p) := by
  classical
  ext b
  by_cases h : a = b <;> simp [coefficientMean_coeff, coeff_monomial, h]

theorem polynomialMean_real_mul {d : ℕ} (hd : 0 < d)
    (a : ℝ) (p : MvPolynomial (Fin d) ℝ) :
    polynomialMean hd (C a * p) = a * polynomialMean hd p := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (polynomialMean hd).map_smul a p

theorem coefficientMean_eval {d : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) (x : Fin d → ℝ) :
    eval x (coefficientMean hd p) =
      polynomialMean hd (eval (fun i => C (x i)) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial a p =>
    rw [coefficientMean_monomial]
    simp only [eval_monomial]
    have he : a.prod (fun i n => (C (x i) : MvPolynomial (Fin d) ℝ)^n) =
        C (a.prod (fun i n => x i ^ n)) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [he, mul_comm p, polynomialMean_real_mul]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MeanDerivatives.lean

-- BEGIN SSProof/RadialMoments.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

theorem linearMoment_radial {d : ℕ} (r : ℕ) (u : ESpace d) (hu : ‖u‖ = 1)
    (x : ESpace d) : linearMoment r x = ‖x‖ ^ r * linearMoment r u := by
  have hn : ‖x‖ = ‖‖x‖ • u‖ := by simp [norm_smul, hu]
  rw [linearMoment_eq_of_norm_eq r x (‖x‖ • u) hn, linearMoment_smul]

theorem momentPolynomial_even {d : ℕ} (hd : 0 < d) (r : ℕ)
    (u : ESpace d) (hu : ‖u‖ = 1) :
    momentPolynomial d (2*r) = C (linearMoment (2*r) u) * normSqPoly d ^ r := by
  apply MvPolynomial.funext
  intro x
  let v : ESpace d := WithLp.toLp 2 x
  have h := linearMoment_radial (2*r) u hu v
  rw [← eval_momentPolynomial hd] at h
  change eval x (momentPolynomial d (2*r)) = _ at h
  rw [h]
  simp only [map_mul, eval_C, map_pow, normSqPoly, map_sum, eval_X]
  have hv : ‖v‖ ^ 2 = ∑ i, x i ^ 2 := EuclideanSpace.real_norm_sq_eq v
  rw [← hv, ← pow_mul]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/RadialMoments.lean

-- BEGIN SSProof/BilinearPolynomial.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def bilinearPolynomial (d : ℕ) :
    MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ) :=
  ∑ i, C (X i) * X i

theorem pderiv_bilinearPolynomial {d : ℕ} (i : Fin d) :
    pderiv i (bilinearPolynomial d) = C (X i) := by
  classical
  simp [bilinearPolynomial, map_sum, pderiv_X, Pi.single_apply]

theorem coefficientMean_bilinear_pow {d : ℕ} (hd : 0 < d) (r : ℕ) :
    coefficientMean hd (bilinearPolynomial d ^ r) = momentPolynomial d r := by
  apply MvPolynomial.funext
  intro x
  rw [coefficientMean_eval]
  let v : ESpace d := WithLp.toLp 2 x
  have he := eval_momentPolynomial hd r v
  change eval x (momentPolynomial d r) = linearMoment r v at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [bilinearPolynomial, map_pow, map_sum, map_mul, eval_C, eval_X]
  simp [PiLp.inner_apply, sphereCoords, v]


theorem coefficientMean_normSq_mul {d : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) :
    coefficientMean hd (C (normSqPoly d) * p) = coefficientMean hd p := by
  ext a
  simp only [coefficientMean_coeff, coeff_C_mul, polynomialMean_normSq_mul]

theorem pderiv_bilinear_pow_two {d : ℕ} (i : Fin d) (r : ℕ) :
    pderiv i (pderiv i (bilinearPolynomial d ^ (r+2))) =
      ((r+2)*(r+1) : ℕ) • (C (X i ^ 2) * bilinearPolynomial d ^ r) := by
  rw [pderiv_pow, pderiv_bilinearPolynomial]
  have h1 : r+2-1 = r+1 := by omega
  have h2 : r+1-1 = r := by omega
  simp only [pderiv_mul, pderiv_pow, pderiv_bilinearPolynomial, pderiv_C,
    Derivation.map_natCast, mul_zero, add_zero, zero_mul, zero_add, h1, h2]
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, map_pow]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/BilinearPolynomial.lean

-- BEGIN SSProof/NormSquareDerivative.lean
section

open scoped BigOperators
open MvPolynomial

namespace SphereSOS.Rate.SSFresh

theorem pderiv_two {d : ℕ} (i : Fin d) :
    pderiv i (2 : MvPolynomial (Fin d) ℝ) = 0 :=
  (pderiv i).map_natCast 2

theorem pderiv_normSqPoly {d : ℕ} (i : Fin d) :
    pderiv i (normSqPoly d) = 2 * X i := by
  classical
  simp [normSqPoly, map_sum, pderiv_X, Pi.single_apply]

theorem laplacian_normSqPoly (d : ℕ) :
    laplacian (normSqPoly d) = C (2 * (d : ℝ)) := by
  classical
  simp [laplacian, pderiv_normSqPoly, pderiv_two]
  rw [show C (2:ℝ) = (2 : MvPolynomial (Fin d) ℝ) from map_natCast C 2]
  ring

theorem laplacian_normSq_pow (d r : ℕ) :
    laplacian (normSqPoly d ^ (r+1)) =
      C (2 * ((r:ℝ)+1) * ((d:ℝ)+2*r)) * normSqPoly d ^ r := by
  classical
  cases r with
  | zero => simpa using laplacian_normSqPoly d
  | succ r =>
    have hi (i : Fin d) :
        pderiv i (pderiv i (normSqPoly d ^ (r+2))) =
          C (2*((r:ℝ)+2)) * normSqPoly d ^ (r+1) +
          C (4*((r:ℝ)+2)*((r:ℝ)+1)) * normSqPoly d ^ r * X i ^ 2 := by
      rw [pderiv_pow, pderiv_normSqPoly]
      have h1 : r+2-1 = r+1 := by omega
      have h2 : r+1-1 = r := by omega
      simp only [pderiv_mul, pderiv_pow, pderiv_normSqPoly,
        Derivation.map_natCast, pderiv_two, pderiv_X_self, zero_mul, zero_add,
        mul_one, h1, h2]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
        map_mul, map_add, map_ofNat, map_natCast, map_one]
      ring
    change (∑ i, pderiv i (pderiv i (normSqPoly d ^ (r+2)))) = _
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    change _ + _ * normSqPoly d = _
    simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_ofNat, map_natCast,
      map_one, pow_succ]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/NormSquareDerivative.lean

-- BEGIN SSProof/LaplacianMoments.lean
section

open scoped BigOperators
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

theorem laplacian_momentPolynomial {d : ℕ} (hd : 0 < d) (r : ℕ) :
    laplacian (momentPolynomial d (r+2)) =
      ((r+2)*(r+1) : ℕ) • momentPolynomial d r := by
  classical
  rw [← coefficientMean_bilinear_pow hd (r+2)]
  unfold laplacian
  simp_rw [← coefficientMean_pderiv, pderiv_bilinear_pow_two]
  rw [← map_sum]
  have he : (∑ i : Fin d, ((r+2)*(r+1) : ℕ) •
      (C (X i ^ 2) * bilinearPolynomial d ^ r)) =
      ((r+2)*(r+1) : ℕ) • (C (normSqPoly d) * bilinearPolynomial d ^ r) := by
    rw [← Finset.smul_sum, ← Finset.sum_mul, ← map_sum]
    rfl
  rw [he, map_nsmul, coefficientMean_normSq_mul, coefficientMean_bilinear_pow]

theorem linearMoment_even_recurrence {d : ℕ} (hd : 0 < d) (r : ℕ)
    (u : ESpace d) (hu : ‖u‖ = 1) :
    ((d : ℝ)+2*r) * linearMoment (2*(r+1)) u =
      (2*(r:ℝ)+1) * linearMoment (2*r) u := by
  have hm := laplacian_momentPolynomial hd (2*r)
  have he : 2*r+2 = 2*(r+1) := by omega
  rw [he, momentPolynomial_even hd (r+1) u hu,
    momentPolynomial_even hd r u hu] at hm
  have hl (a : ℝ) (p : MvPolynomial (Fin d) ℝ) :
      laplacian (C a * p) = C a * laplacian p := by
    simp only [laplacian, pderiv_C_mul, Finset.mul_sum]
  rw [hl, laplacian_normSq_pow] at hm
  have hv := congrArg (eval (fun i => u i)) hm
  have hs : eval (fun i => u i) (normSqPoly d) = 1 := by
    simp only [normSqPoly, map_sum, map_pow, eval_X]
    rw [← EuclideanSpace.real_norm_sq_eq, hu]
    norm_num
  simp only [map_mul, eval_C, map_pow, hs, one_pow, mul_one,
    nsmul_eq_mul] at hv
  push_cast at hv
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one] at hv
  have hr : (0:ℝ) < 2*((r:ℝ)+1) := by positivity
  nlinarith [hv]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/LaplacianMoments.lean

-- BEGIN SSProof/CoordinateMoments.lean
section

open MeasureTheory Polynomial

namespace SphereSOS.Rate.SSFresh

theorem coordinateMean_pow {d : ℕ} (hd : 0 < d) (i : Fin d) (r : ℕ) :
    coordinateMean hd i (X ^ r) = linearMoment r (EuclideanSpace.single i 1) := by
  apply integral_congr_ae
  filter_upwards [] with y
  simp [EuclideanSpace.inner_single_left, sphereCoords]

theorem coordinateMean_one {d : ℕ} (hd : 0 < d) (i : Fin d) :
    coordinateMean hd i 1 = 1 := by
  let : IsProbabilityMeasure (sphereLaw d) := sphereLaw_probability hd
  change (∫ y : UnitSphere d, (1 : Polynomial ℝ).eval (sphereCoords y i) ∂sphereLaw d) = 1
  simp

theorem coordinateMean_odd {d : ℕ} (hd : 0 < d) (i : Fin d) (r : ℕ) (hr : Odd r) :
    coordinateMean hd i (X^r) = 0 := by
  rw [coordinateMean_pow]
  exact linearMoment_odd r hr _

theorem coordinateMean_recurrence {d : ℕ} (hd : 0 < d) (i : Fin d) (r : ℕ) :
    ((d:ℝ)+r) * coordinateMean hd i (X^(r+2)) =
      ((r:ℝ)+1) * coordinateMean hd i (X^r) := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨k, hk⟩ := hr
    have he : r = 2*k := by omega
    subst r
    simp only [coordinateMean_pow]
    have h := linearMoment_even_recurrence hd k (EuclideanSpace.single i 1) (by simp)
    convert h using 1 <;> congr 1 <;> push_cast <;> ring
  · have hr2 : Odd (r+2) := by
      obtain ⟨k, hk⟩ := hr
      exact ⟨k+1, by omega⟩
    rw [coordinateMean_odd hd i (r+2) hr2, coordinateMean_odd hd i r hr]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/CoordinateMoments.lean

-- BEGIN SSProof/SteinIdentity.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def steinPolynomial (d : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  (1-X^2)*p.derivative-C (d-1)*X*p

theorem functional_C_mul (L : Polynomial ℝ →ₗ[ℝ] ℝ) (a : ℝ) (p : Polynomial ℝ) :
    L (C a * p) = a * L p := by
  simpa only [Polynomial.smul_eq_C_mul, smul_eq_mul] using L.map_smul a p

theorem stein_monomial_succ (d : ℝ) (n : ℕ) (a : ℝ) :
    steinPolynomial d (monomial (n+1) a) =
      C a * (C ((n:ℝ)+1)*X^n-C (d+n)*X^(n+2)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [steinPolynomial, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_pow, derivative_X, mul_one, Nat.add_sub_cancel]
  simp only [map_add, map_sub, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  ring

theorem coordinateMean_stein {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p : Polynomial ℝ) : coordinateMean hd i (steinPolynomial d p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he : steinPolynomial d (p+q) = steinPolynomial d p + steinPolynomial d q := by
      simp only [steinPolynomial, derivative_add]
      ring
    rw [he, map_add, hp, hq, add_zero]
  | monomial n a =>
    cases n with
    | zero =>
      have he : steinPolynomial d (monomial 0 a) = C (-(d-1)*a) * X := by
        simp only [monomial_zero_left, steinPolynomial, derivative_C, mul_zero,
          zero_sub, map_mul, map_neg, map_sub, map_one]
        ring
      rw [he, functional_C_mul]
      have hx := coordinateMean_odd hd i 1 (by decide)
      simpa only [pow_one, hx, mul_zero] using congrArg (fun z => (-(d-1)*a)*z) hx
    | succ n =>
      rw [stein_monomial_succ, functional_C_mul, map_sub, functional_C_mul,
        functional_C_mul]
      have h := coordinateMean_recurrence hd i n
      rw [← h, sub_self, mul_zero]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SteinIdentity.lean

-- BEGIN SSProof/SturmOperator.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def sturmPolynomial (d : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  (1-X^2)*p.derivative.derivative-C (d-1)*X*p.derivative

theorem sturm_integration_identity (d : ℝ) (p q : Polynomial ℝ) :
    sturmPolynomial d p * q + (1-X^2)*p.derivative*q.derivative =
      steinPolynomial d (p.derivative*q) := by
  simp only [sturmPolynomial, steinPolynomial, derivative_mul]
  ring

theorem coordinateMean_sturm {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p q : Polynomial ℝ) :
    coordinateMean hd i (sturmPolynomial d p*q) =
      -coordinateMean hd i ((1-X^2)*p.derivative*q.derivative) := by
  have h := coordinateMean_stein hd i (p.derivative*q)
  rw [← sturm_integration_identity, map_add] at h
  linarith

theorem coordinateMean_sturm_symm {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p q : Polynomial ℝ) :
    coordinateMean hd i (sturmPolynomial d p*q) =
      coordinateMean hd i (p*sturmPolynomial d q) := by
  rw [coordinateMean_sturm, mul_comm p, coordinateMean_sturm]
  congr 2
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SturmOperator.lean

-- BEGIN SSProof/SturmCoefficients.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem coeff_X_derivative (p : Polynomial ℝ) (j : ℕ) :
    (X*p.derivative).coeff j = (j:ℝ)*p.coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem coeff_X_sq_derivative (p : Polynomial ℝ) (j : ℕ) :
    (X^2*p.derivative.derivative).coeff j = (j:ℝ)*((j:ℝ)-1)*p.coeff j := by
  rcases j with _ | j
  · simp
  rcases j with _ | j
  · simp [coeff_X_pow_mul']
  · rw [show j+1+1 = j+2 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

theorem coeff_sturmPolynomial (d : ℝ) (p : Polynomial ℝ) (j : ℕ) :
    (sturmPolynomial d p).coeff j =
      ((j:ℝ)+2)*((j:ℝ)+1)*p.coeff (j+2) -
        (j:ℝ)*((j:ℝ)+d-2)*p.coeff j := by
  unfold sturmPolynomial
  rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_sub,
    coeff_C_mul, coeff_X_derivative, coeff_X_sq_derivative,
    coeff_derivative, coeff_derivative]
  push_cast
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SturmCoefficients.lean

-- BEGIN SSProof/SturmEigen.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem sturm_degree_lt (d : ℝ) (p : Polynomial ℝ) (j : ℕ) (hp : p.degree < j) :
    (sturmPolynomial d p).degree < j := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro m hm
  rw [coeff_sturmPolynomial, hp m hm, hp (m+2) (by omega)]
  ring

theorem sturm_residual_degree_lt (d : ℝ) (p : Polynomial ℝ) (j : ℕ)
    (hp : p.degree ≤ j) :
    (sturmPolynomial d p+C ((j:ℝ)*((j:ℝ)+d-2))*p).degree < j := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_add, coeff_C_mul, coeff_sturmPolynomial]
  have hz : p.coeff (m+2)=0 := coeff_eq_zero_of_degree_lt
    (hp.trans_lt (by exact_mod_cast (show j < m + 2 by omega)))
  rw [hz]
  rcases eq_or_lt_of_le hm with rfl | hlt
  · ring
  · have hm0 : p.coeff m=0 := coeff_eq_zero_of_degree_lt
      (hp.trans_lt (by exact_mod_cast hlt))
    rw [hm0]
    ring

theorem monic_sturm_eigen (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q))
    (j : ℕ) :
    sturmPolynomial d (orthogonalPolynomial L hpos j) +
      C ((j:ℝ)*((j:ℝ)+d-2))*orthogonalPolynomial L hpos j = 0 := by
  let p := orthogonalPolynomial L hpos j
  let R := sturmPolynomial d p+C ((j:ℝ)*((j:ℝ)+d-2))*p
  have hp : p.degree ≤ j := by
    rw [degree_eq_natDegree (orthogonalPolynomial_spec L hpos j).1.ne_zero,
      (orthogonalPolynomial_spec L hpos j).2.1]
  have hR : R.degree < j := sturm_residual_degree_lt d p j hp
  have hR0 := (orthogonalPolynomial_spec L hpos j).2.2 R hR
  have hD0 := (orthogonalPolynomial_spec L hpos j).2.2 (sturmPolynomial d R)
    (sturm_degree_lt d R j hR)
  have he : L (R*R)=0 := by
    change L ((sturmPolynomial d p+C ((j:ℝ)*((j:ℝ)+d-2))*p)*R)=0
    rw [add_mul, map_add, hsymm, mul_assoc, functional_C_mul]
    change L (p*sturmPolynomial d R)+((j:ℝ)*((j:ℝ)+d-2))*L (p*R)=0
    rw [hD0, hR0]
    ring
  by_contra h
  exact (ne_of_gt (hpos R h)) he

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SturmEigen.lean

-- BEGIN SSProof/EigenCoefficients.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem eigen_coefficient_equation (d : ℝ) (p : Polynomial ℝ) (j r : ℕ)
    (he : sturmPolynomial d p+C ((j:ℝ)*((j:ℝ)+d-2))*p=0) :
    ((r:ℝ)+2)*((r:ℝ)+1)*p.coeff (r+2) +
      ((j:ℝ)*((j:ℝ)+d-2)-(r:ℝ)*((r:ℝ)+d-2))*p.coeff r=0 := by
  have h := congrArg (fun q : Polynomial ℝ => q.coeff r) he
  rw [coeff_add, coeff_sturmPolynomial, coeff_C_mul, coeff_zero] at h
  linarith

theorem eigen_subleading_zero (d : ℝ) (hd : 2 ≤ d) (p : Polynomial ℝ) (j : ℕ)
    (hp : p.natDegree=j+1)
    (he : sturmPolynomial d p+C (((j+1:ℕ):ℝ)*(((j+1:ℕ):ℝ)+d-2))*p=0) :
    p.coeff j=0 := by
  have h := eigen_coefficient_equation d p (j+1) j he
  have hz : p.coeff (j+2)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hz] at h
  push_cast at h
  have hpos : 0 < 2*(j:ℝ)+d-1 := by
    have hj : (0:ℝ) ≤ j := by positivity
    linarith
  have heq : (2*(j:ℝ)+d-1)*p.coeff j=0 := by nlinarith
  exact (mul_eq_zero.mp heq).resolve_left hpos.ne'

theorem eigen_second_coefficient (d : ℝ) (hd : 2 ≤ d)
    (p : Polynomial ℝ) (j : ℕ) (hm : p.Monic) (hp : p.natDegree=j+2)
    (he : sturmPolynomial d p+C (((j+2:ℕ):ℝ)*(((j+2:ℕ):ℝ)+d-2))*p=0) :
    p.coeff j = -(((j:ℝ)+2)*((j:ℝ)+1))/(2*(2*(j:ℝ)+d)) := by
  have h := eigen_coefficient_equation d p (j+2) j he
  have hc : p.coeff (j+2)=1 := by rw [← hp]; exact hm.coeff_natDegree
  rw [hc] at h
  push_cast at h
  have hpos : 0 < 2*(2*(j:ℝ)+d) := by positivity
  apply (eq_div_iff hpos.ne').mpr
  nlinarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/EigenCoefficients.lean

-- BEGIN SSProof/JacobiAlgebra.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def jacobiSquare (d : ℝ) (j : ℕ) : ℝ :=
  if j=0 then 1/d else
    (((j:ℝ)+1)*((j:ℝ)+d-2))/((2*(j:ℝ)+d-2)*(2*(j:ℝ)+d))

theorem jacobiSquare_succ (d : ℝ) (j : ℕ) :
    jacobiSquare d (j+1) =
      (((j:ℝ)+2)*((j:ℝ)+d-1))/((2*(j:ℝ)+d)*(2*(j:ℝ)+d+2)) := by
  simp only [jacobiSquare, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.cast_add, Nat.cast_one]
  congr 1 <;> ring

theorem jacobiSquare_pos (d : ℝ) (hd : 2≤d) (j : ℕ) : 0<jacobiSquare d j := by
  cases j with
  | zero =>
    change 0 < 1/d
    exact div_pos zero_lt_one (by linarith)
  | succ j =>
    rw [jacobiSquare_succ]
    have hj : (0:ℝ)≤j := by positivity
    apply div_pos
    · apply mul_pos <;> linarith
    · apply mul_pos <;> linarith

theorem jacobi_coefficient_difference (d : ℝ) (hd : 2≤d) (j : ℕ) :
    -(((j:ℝ)+2)*((j:ℝ)+1))/(2*(2*(j:ℝ)+d)) +
      (((j:ℝ)+3)*((j:ℝ)+2))/(2*(2*(j:ℝ)+d+2)) = jacobiSquare d (j+1) := by
  rw [jacobiSquare_succ]
  have hj : (0:ℝ)≤j := by positivity
  have h1 : 2*(j:ℝ)+d ≠ 0 := by linarith
  have h2 : 2*(j:ℝ)+d+2 ≠ 0 := by linarith
  field_simp
  ring

theorem jacobiSquare_identity (d : ℝ) (hd : 2≤d) (j : ℕ) (hj : 1≤j) :
    jacobiSquare d j = 1/4-(d-2)*(d-4)/(4*(2*(j:ℝ)+d-2)*(2*(j:ℝ)+d)) := by
  rw [jacobiSquare, if_neg (by omega)]
  have hjr : (1:ℝ)≤j := by exact_mod_cast hj
  have h1 : 2*(j:ℝ)+d-2 ≠ 0 := by linarith
  have h2 : 2*(j:ℝ)+d ≠ 0 := by linarith
  have h3 : -2+(j:ℝ)*2+d ≠ 0 := by linarith
  field_simp [h1, h2]
  ring_nf
  have hi := mul_inv_cancel₀ h3
  linear_combination (2*(j:ℝ)+d)*hi

end SphereSOS.Rate.SSFresh

end
-- END SSProof/JacobiAlgebra.lean

-- BEGIN SSProof/JacobiRecurrence.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem orthogonal_subleading_zero (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    (orthogonalPolynomial L hpos (j+1)).coeff j=0 :=
  eigen_subleading_zero d hd _ j (orthogonalPolynomial_spec L hpos (j+1)).2.1
    (monic_sturm_eigen L hpos d hsymm (j+1))

theorem orthogonal_second_coefficient (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    (orthogonalPolynomial L hpos (j+2)).coeff j =
      -(((j:ℝ)+2)*((j:ℝ)+1))/(2*(2*(j:ℝ)+d)) :=
  eigen_second_coefficient d hd _ j (orthogonalPolynomial_spec L hpos (j+2)).1
    (orthogonalPolynomial_spec L hpos (j+2)).2.1
    (monic_sturm_eigen L hpos d hsymm (j+2))

theorem orthogonal_jacobi_recurrence (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    X*orthogonalPolynomial L hpos (j+1)-orthogonalPolynomial L hpos (j+2) =
      C (jacobiSquare d j)*orthogonalPolynomial L hpos j := by
  rw [orthogonal_three_term L hpos j
    (orthogonal_subleading_zero L hpos d hd hsymm j)
    (orthogonal_subleading_zero L hpos d hd hsymm (j+1))]
  congr 2
  rw [coeff_sub]
  cases j with
  | zero =>
    rw [coeff_X_mul_zero, orthogonal_second_coefficient L hpos d hd hsymm 0]
    simp only [jacobiSquare, if_true, Nat.cast_zero]
    field_simp
    ring
  | succ j =>
    rw [coeff_X_mul]
    rw [orthogonal_second_coefficient L hpos d hd hsymm j,
      orthogonal_second_coefficient L hpos d hd hsymm (j+1)]
    push_cast
    convert jacobi_coefficient_difference d hd j using 1
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/JacobiRecurrence.lean

-- BEGIN SSProof/OrthogonalNorm.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def orthogonalNorm (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) : ℝ :=
  L (orthogonalPolynomial L hpos j * orthogonalPolynomial L hpos j)

theorem orthogonalNorm_pos (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    0 < orthogonalNorm L hpos j :=
  hpos _ (orthogonalPolynomial_spec L hpos j).1.ne_zero

theorem orthogonal_adjacent_pair (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    L (orthogonalPolynomial L hpos (j+1)*(X*orthogonalPolynomial L hpos j)) =
      orthogonalNorm L hpos (j+1) := by
  have hp := orthogonalPolynomial_spec L hpos j
  have hq := orthogonalPolynomial_spec L hpos (j+1)
  have h := hq.2.2 (X*orthogonalPolynomial L hpos j-orthogonalPolynomial L hpos (j+1))
    (monic_X_sub_degree _ _ j hp.1 hq.1 hp.2.1 hq.2.1)
  rw [mul_sub, map_sub] at h
  exact sub_eq_zero.mp h

theorem orthogonalNorm_succ (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    orthogonalNorm L hpos (j+1) = jacobiSquare d j*orthogonalNorm L hpos j := by
  have h := congrArg (fun p : Polynomial ℝ => L (p*orthogonalPolynomial L hpos j))
    (orthogonal_jacobi_recurrence L hpos d hd hsymm j)
  rw [sub_mul, map_sub] at h
  rw [mul_assoc (C (jacobiSquare d j)), functional_C_mul] at h
  have hz := orthogonalPolynomial_pair L hpos (show j < j+2 by omega)
  have he : X*orthogonalPolynomial L hpos (j+1)*orthogonalPolynomial L hpos j =
    orthogonalPolynomial L hpos (j+1)*(X*orthogonalPolynomial L hpos j) := by ring
  rw [he, orthogonal_adjacent_pair, hz, sub_zero] at h
  exact h

end SphereSOS.Rate.SSFresh

end
-- END SSProof/OrthogonalNorm.lean

-- BEGIN SSProof/NormalizedOrthogonal.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def normalizedOrthogonal (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) : Polynomial ℝ :=
  C ((Real.sqrt (orthogonalNorm L hpos j))⁻¹) * orthogonalPolynomial L hpos j

theorem functional_two_C (L : Polynomial ℝ →ₗ[ℝ] ℝ) (a b : ℝ) (p q : Polynomial ℝ) :
    L ((C a*p)*(C b*q))=a*b*L (p*q) := by
  have he : (C a*p)*(C b*q)=C (a*b)*(p*q) := by rw [map_mul]; ring
  rw [he, functional_C_mul]

theorem normalizedOrthogonal_natDegree (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    (normalizedOrthogonal L hpos j).natDegree=j := by
  have hs := Real.sqrt_pos.2 (orthogonalNorm_pos L hpos j)
  simp only [normalizedOrthogonal]
  rw [natDegree_C_mul (inv_ne_zero hs.ne')]
  exact (orthogonalPolynomial_spec L hpos j).2.1

theorem normalizedOrthogonal_self (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) (j : ℕ) :
    L (normalizedOrthogonal L hpos j * normalizedOrthogonal L hpos j)=1 := by
  have hn := orthogonalNorm_pos L hpos j
  have hs := Real.sqrt_pos.2 hn
  have he := Real.sq_sqrt hn.le
  simp only [normalizedOrthogonal]
  rw [functional_two_C]
  change (Real.sqrt (orthogonalNorm L hpos j))⁻¹ *
    (Real.sqrt (orthogonalNorm L hpos j))⁻¹ * orthogonalNorm L hpos j=1
  field_simp
  nlinarith

theorem normalizedOrthogonal_pair (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) {i j : ℕ} (hij : i < j) :
    L (normalizedOrthogonal L hpos j * normalizedOrthogonal L hpos i)=0 := by
  simp only [normalizedOrthogonal]
  rw [functional_two_C, orthogonalPolynomial_pair L hpos hij, mul_zero]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/NormalizedOrthogonal.lean

-- BEGIN SSProof/NormalizedJacobi.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem normalized_jacobi_adjacent (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    L (normalizedOrthogonal L hpos (j+1)*(X*normalizedOrthogonal L hpos j)) =
      Real.sqrt (jacobiSquare d j) := by
  have hn := orthogonalNorm_pos L hpos j
  have hb := jacobiSquare_pos d hd j
  have hs := Real.sqrt_pos.2 hn
  have ht := Real.sqrt_pos.2 hb
  have he : normalizedOrthogonal L hpos (j+1)*(X*normalizedOrthogonal L hpos j) =
      (C ((Real.sqrt (orthogonalNorm L hpos (j+1)))⁻¹)*orthogonalPolynomial L hpos (j+1))*
      (C ((Real.sqrt (orthogonalNorm L hpos j))⁻¹)*(X*orthogonalPolynomial L hpos j)) := by
    simp only [normalizedOrthogonal]
    ring
  rw [he, functional_two_C, orthogonal_adjacent_pair,
    orthogonalNorm_succ L hpos d hd hsymm, Real.sqrt_mul hb.le]
  have he1 := Real.sq_sqrt hn.le
  have he2 := Real.sq_sqrt hb.le
  field_simp
  nlinarith

theorem normalized_jacobi_far (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) {i j : ℕ} (hij : i+1 < j) :
    L (normalizedOrthogonal L hpos j*(X*normalizedOrthogonal L hpos i))=0 := by
  have hp := orthogonalPolynomial_spec L hpos j
  have hi := orthogonalPolynomial_spec L hpos i
  have hdeg : (X*orthogonalPolynomial L hpos i).degree < (j : WithBot ℕ) := by
    rw [degree_eq_natDegree (mul_ne_zero X_ne_zero hi.1.ne_zero), natDegree_X_mul hi.1.ne_zero, hi.2.1]
    exact_mod_cast hij
  have hz := hp.2.2 _ hdeg
  have he : normalizedOrthogonal L hpos j*(X*normalizedOrthogonal L hpos i) =
      (C ((Real.sqrt (orthogonalNorm L hpos j))⁻¹)*orthogonalPolynomial L hpos j)*
      (C ((Real.sqrt (orthogonalNorm L hpos i))⁻¹)*(X*orthogonalPolynomial L hpos i)) := by
    simp only [normalizedOrthogonal]
    ring
  rw [he, functional_two_C, hz, mul_zero]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/NormalizedJacobi.lean

-- BEGIN SSProof/JacobiDiagonal.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem orthogonal_first (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) :
    X*orthogonalPolynomial L hpos 0=orthogonalPolynomial L hpos 1 := by
  apply sub_eq_zero.mp
  have hp := orthogonalPolynomial_spec L hpos 0
  have hq := orthogonalPolynomial_spec L hpos 1
  have hdeg := monic_X_sub_degree _ _ 0 hp.1 hq.1 hp.2.1 hq.2.1
  ext m
  rw [coeff_zero]
  cases m with
  | zero =>
    rw [coeff_sub, coeff_X_mul_zero, orthogonal_subleading_zero L hpos d hd hsymm 0]
    ring
  | succ m => exact (degree_lt_iff_coeff_zero _ 1).mp hdeg _ (by omega)

theorem orthogonal_jacobi_diagonal (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    L ((X*orthogonalPolynomial L hpos j)*orthogonalPolynomial L hpos j)=0 := by
  cases j with
  | zero =>
    rw [orthogonal_first L hpos d hd hsymm]
    exact orthogonalPolynomial_pair L hpos (by omega)
  | succ j =>
    have he := orthogonal_jacobi_recurrence L hpos d hd hsymm j
    have he' := sub_eq_iff_eq_add.mp he
    rw [he', add_mul, map_add]
    rw [mul_assoc (C _), functional_C_mul]
    rw [orthogonalPolynomial_pair L hpos (show j+1 < j+2 by omega)]
    rw [mul_comm (orthogonalPolynomial L hpos j),
      orthogonalPolynomial_pair L hpos (show j < j+1 by omega)]
    ring

theorem normalized_jacobi_diagonal (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (j : ℕ) :
    L ((X*normalizedOrthogonal L hpos j)*normalizedOrthogonal L hpos j)=0 := by
  have he : (X*normalizedOrthogonal L hpos j)*normalizedOrthogonal L hpos j =
      (C ((Real.sqrt (orthogonalNorm L hpos j))⁻¹)*(X*orthogonalPolynomial L hpos j))*
      (C ((Real.sqrt (orthogonalNorm L hpos j))⁻¹)*orthogonalPolynomial L hpos j) := by
    simp only [normalizedOrthogonal]
    ring
  rw [he, functional_two_C, orthogonal_jacobi_diagonal L hpos d hd hsymm, mul_zero]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/JacobiDiagonal.lean

-- BEGIN SSProof/OrthogonalCombination.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem normalized_pair_ne (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p)) {i j : ℕ} (hij : i ≠ j) :
    L (normalizedOrthogonal L hpos i*normalizedOrthogonal L hpos j)=0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [mul_comm]
    exact normalizedOrthogonal_pair L hpos h
  · exact normalizedOrthogonal_pair L hpos h

noncomputable def orthogonalCombination (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (a : ℕ) (v : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range N, C (v r)*normalizedOrthogonal L hpos (a+r)

theorem combination_pair (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (a : ℕ) (v : ℕ → ℝ) (N r : ℕ) (hr : r < N) :
    L (orthogonalCombination L hpos a v N*normalizedOrthogonal L hpos (a+r))=v r := by
  simp only [orthogonalCombination, Finset.sum_mul, map_sum, mul_assoc, functional_C_mul]
  rw [Finset.sum_eq_single r]
  · rw [normalizedOrthogonal_self, mul_one]
  · intro b hb hbr
    rw [normalized_pair_ne L hpos (by omega), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hr))

theorem combination_norm (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (a : ℕ) (v : ℕ → ℝ) (N : ℕ) :
    L (orthogonalCombination L hpos a v N*orthogonalCombination L hpos a v N)=
      ∑ r ∈ Finset.range N, v r^2 := by
  conv_lhs => rhs; unfold orthogonalCombination
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have he : orthogonalCombination L hpos a v N*(C (v r)*normalizedOrthogonal L hpos (a+r)) =
      C (v r)*(orthogonalCombination L hpos a v N*normalizedOrthogonal L hpos (a+r)) := by ring
  change L (orthogonalCombination L hpos a v N*(C (v r)*normalizedOrthogonal L hpos (a+r)))=v r^2
  rw [he, functional_C_mul, combination_pair L hpos a v N r (Finset.mem_range.mp hr)]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/OrthogonalCombination.lean

-- BEGIN SSProof/JacobiPair.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem normalized_jacobi_pair (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q)) (i j : ℕ) :
    L ((X*normalizedOrthogonal L hpos i)*normalizedOrthogonal L hpos j) =
      (if i+1=j then Real.sqrt (jacobiSquare d i) else 0) +
      (if j+1=i then Real.sqrt (jacobiSquare d j) else 0) := by
  by_cases h1 : i+1=j
  · subst j
    rw [if_pos rfl, if_neg (by omega), add_zero, mul_comm]
    exact normalized_jacobi_adjacent L hpos d hd hsymm i
  by_cases h2 : j+1=i
  · subst i
    rw [if_neg (by omega), if_pos rfl, zero_add]
    have he : (X*normalizedOrthogonal L hpos (j+1))*normalizedOrthogonal L hpos j =
        normalizedOrthogonal L hpos (j+1)*(X*normalizedOrthogonal L hpos j) := by ring
    rw [he]
    exact normalized_jacobi_adjacent L hpos d hd hsymm j
  rw [if_neg h1, if_neg h2, add_zero]
  by_cases he : i=j
  · subst j
    exact normalized_jacobi_diagonal L hpos d hd hsymm i
  rcases lt_or_gt_of_ne he with hij | hji
  · rw [mul_comm]
    exact normalized_jacobi_far L hpos (by omega)
  · have heq : (X*normalizedOrthogonal L hpos i)*normalizedOrthogonal L hpos j =
        normalizedOrthogonal L hpos i*(X*normalizedOrthogonal L hpos j) := by ring
    rw [heq]
    exact normalized_jacobi_far L hpos (by omega)

theorem shifted_pair_expansion (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q))
    (a : ℕ) (v : ℕ → ℝ) (N : ℕ) :
    L ((X*orthogonalCombination L hpos a v N)*orthogonalCombination L hpos a v N)=
      ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        v r*v s*((if r+1=s then Real.sqrt (jacobiSquare d (a+r)) else 0)+
          (if s+1=r then Real.sqrt (jacobiSquare d (a+s)) else 0)) := by
  simp only [orthogonalCombination, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have he : (X*(C (v s)*normalizedOrthogonal L hpos (a+s)))*
      (C (v r)*normalizedOrthogonal L hpos (a+r)) =
      (C (v r)*(X*normalizedOrthogonal L hpos (a+r)))*
      (C (v s)*normalizedOrthogonal L hpos (a+s)) := by ring
  rw [he, functional_two_C, normalized_jacobi_pair L hpos d hd hsymm]
  have h1 : a+r+1=a+s ↔ r+1=s := by omega
  have h2 : a+s+1=a+r ↔ s+1=r := by omega
  simp only [h1, h2]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/JacobiPair.lean

-- BEGIN SSProof/AdjacentSum.lean
section

namespace SphereSOS.Rate.SSFresh

theorem adjacent_upper_sum (v w : ℕ → ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range (N+1), ∑ s ∈ Finset.range (N+1),
      v r*v s*(if r+1=s then w r else 0)) =
      ∑ r ∈ Finset.range N, v r*v (r+1)*w r := by
  rw [Finset.sum_range_succ]
  have hz : (∑ s ∈ Finset.range (N+1), v N*v s*(if N+1=s then w N else 0))=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [if_neg (by have := Finset.mem_range.mp hs; omega), mul_zero]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single (r+1)]
  · rw [if_pos rfl]
  · intro s hs hsr
    rw [if_neg (Ne.symm hsr), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega)))

theorem adjacent_symmetric_sum (v w : ℕ → ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range (N+1), ∑ s ∈ Finset.range (N+1),
      v r*v s*((if r+1=s then w r else 0)+(if s+1=r then w s else 0))) =
      2*∑ r ∈ Finset.range N, v r*v (r+1)*w r := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [adjacent_upper_sum]
  have he : (∑ r ∈ Finset.range (N+1), ∑ s ∈ Finset.range (N+1),
      v r*v s*(if s+1=r then w s else 0)) =
      ∑ r ∈ Finset.range N, v r*v (r+1)*w r := by
    rw [Finset.sum_comm]
    have he' : (∑ s ∈ Finset.range (N+1), ∑ r ∈ Finset.range (N+1),
      v r*v s*(if s+1=r then w s else 0)) =
      ∑ s ∈ Finset.range (N+1), ∑ r ∈ Finset.range (N+1),
      v s*v r*(if s+1=r then w s else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [he', adjacent_upper_sum]
  rw [he]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/AdjacentSum.lean

-- BEGIN SSProof/TentSums.lean
section

namespace SphereSOS.Rate.SSFresh

def tentWeight (m r : ℕ) : ℝ :=
  if r ≤ m then (r:ℝ)+1 else (2*m+1:ℕ)-r

theorem sum_successor_sq (m : ℕ) :
    (∑ r ∈ Finset.range m, ((r:ℝ)+1)^2) = (m:ℝ)*(m+1)*(2*m+1)/6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_successor_mul (m : ℕ) :
    (∑ r ∈ Finset.range m, ((r:ℝ)+1)*((r:ℝ)+2)) = (m:ℝ)*(m+1)*(m+2)/3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem tent_square_sum (m : ℕ) :
    (∑ r ∈ Finset.range (2*m+1), tentWeight m r^2) =
      2*((m:ℝ)*(m+1)*(2*m+1)/6)+((m:ℝ)+1)^2 := by
  have hsplit : 2*m+1=(m+1)+m := by omega
  rw [hsplit, Finset.sum_range_add]
  have hleft : (∑ r ∈ Finset.range (m+1), tentWeight m r^2)=
      (m:ℝ)*(m+1)*(2*m+1)/6+((m:ℝ)+1)^2 := by
    rw [Finset.sum_range_succ]
    have hs : (∑ r ∈ Finset.range m, tentWeight m r^2)=
        ∑ r ∈ Finset.range m, ((r:ℝ)+1)^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [tentWeight, if_pos (by have := Finset.mem_range.mp hr; omega)]
    rw [hs, sum_successor_sq]
    simp [tentWeight]
  rw [hleft]
  have hright : (∑ r ∈ Finset.range m, tentWeight m (m+1+r)^2)=
      (m:ℝ)*(m+1)*(2*m+1)/6 := by
    rw [← sum_successor_sq]
    rw [← Finset.sum_range_reflect (fun r => ((r:ℝ)+1)^2)]
    apply Finset.sum_congr rfl
    intro r hr
    have hrm := Finset.mem_range.mp hr
    rw [tentWeight, if_neg (by omega)]
    congr 1
    rw [Nat.cast_sub (by omega : r ≤ m-1), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  rw [hright]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/TentSums.lean

-- BEGIN SSProof/TentAdjacent.lean
section

namespace SphereSOS.Rate.SSFresh

theorem tentWeight_upper (m r : ℕ) (hr : m ≤ r) :
    tentWeight m r=2*(m:ℝ)+1-r := by
  rw [tentWeight]
  split_ifs with h
  · have he : r=m := by omega
    subst r
    ring
  · push_cast
    ring

theorem tent_adjacent_sum (m : ℕ) :
    (∑ r ∈ Finset.range (2*m), tentWeight m r*tentWeight m (r+1)) =
      2*((m:ℝ)*(m+1)*(m+2)/3) := by
  rw [show 2*m=m+m by omega, Finset.sum_range_add]
  have hl : (∑ r ∈ Finset.range m, tentWeight m r*tentWeight m (r+1)) =
      (m:ℝ)*(m+1)*(m+2)/3 := by
    rw [← sum_successor_mul]
    apply Finset.sum_congr rfl
    intro r hr
    have hrm := Finset.mem_range.mp hr
    simp only [tentWeight, if_pos (show r ≤ m by omega), if_pos (show r+1 ≤ m by omega)]
    push_cast
    ring
  have hr : (∑ r ∈ Finset.range m, tentWeight m (m+r)*tentWeight m (m+r+1)) =
      (m:ℝ)*(m+1)*(m+2)/3 := by
    rw [← sum_successor_mul, ← Finset.sum_range_reflect (fun r => ((r:ℝ)+1)*((r:ℝ)+2))]
    apply Finset.sum_congr rfl
    intro r hr
    have hrm := Finset.mem_range.mp hr
    rw [tentWeight_upper m (m+r) (by omega), tentWeight_upper m (m+r+1) (by omega)]
    rw [Nat.cast_sub (by omega : r ≤ m-1), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  rw [hl, hr]
  ring

theorem tent_energy_identity (m : ℕ) :
    (∑ r ∈ Finset.range (2*m+1), tentWeight m r^2) -
      (∑ r ∈ Finset.range (2*m), tentWeight m r*tentWeight m (r+1)) = (m:ℝ)+1 := by
  rw [tent_square_sum, tent_adjacent_sum]
  ring

theorem tent_energy_lower (m : ℕ) :
    ((m:ℝ)+1)^3/2 ≤ ∑ r ∈ Finset.range (2*m+1), tentWeight m r^2 := by
  rw [tent_square_sum]
  have hm : (0:ℝ) ≤ m := by positivity
  nlinarith [sq_nonneg (m:ℝ), pow_nonneg hm 3]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/TentAdjacent.lean

-- BEGIN SSProof/JacobiLower.lean
section

namespace SphereSOS.Rate.SSFresh

theorem jacobiSquare_lower (d : ℝ) (hd : 2 ≤ d) (j : ℕ) (ell : ℝ)
    (hell : 0 < ell) (hj : ell ≤ 2*(j:ℝ)) (hj1 : 1 ≤ j) :
    1/4-d^2/(4*ell^2) ≤ jacobiSquare d j := by
  rw [jacobiSquare_identity d hd j hj1]
  have ha : ell ≤ 2*(j:ℝ)+d-2 := by linarith
  have hb : ell ≤ 2*(j:ℝ)+d := by linarith
  have hden : 4*ell^2 ≤ 4*(2*(j:ℝ)+d-2)*(2*(j:ℝ)+d) := by
    nlinarith [mul_le_mul ha hb hell.le (by linarith : 0 ≤ 2*(j:ℝ)+d-2)]
  have hn : (d-2)*(d-4) ≤ d^2 := by nlinarith
  have hdp : 0 < 4*(2*(j:ℝ)+d-2)*(2*(j:ℝ)+d) := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hq : (d-2)*(d-4)/(4*(2*(j:ℝ)+d-2)*(2*(j:ℝ)+d)) ≤ d^2/(4*ell^2) := by
    calc
      _ ≤ d^2/(4*(2*(j:ℝ)+d-2)*(2*(j:ℝ)+d)) := div_le_div_of_nonneg_right hn hdp.le
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) hden
  linarith

theorem jacobi_sqrt_lower (d : ℝ) (hd : 2 ≤ d) (j : ℕ) (ell : ℝ)
    (hell : 8*d ≤ ell) (hj : ell ≤ 2*(j:ℝ)) :
    1/2-(d/ell)^2 ≤ Real.sqrt (jacobiSquare d j) := by
  have he : 0 < ell := by linarith
  have hj1 : 1 ≤ j := by
    by_contra h
    have hz : j=0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hj
    linarith
  have hlow := jacobiSquare_lower d hd j ell he hj hj1
  have hp := jacobiSquare_pos d hd j
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg (jacobiSquare d j)
  have hr0 : 0 ≤ d/ell := div_nonneg (by linarith) he.le
  have hr : d/ell ≤ 1/8 := (div_le_iff₀ he).2 (by linarith)
  have heq : d^2/(4*ell^2)=(d/ell)^2/4 := by field_simp
  rw [heq] at hlow
  nlinarith [sq_nonneg (d/ell), sq_nonneg ((d/ell)^2)]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/JacobiLower.lean

-- BEGIN SSProof/TentPolynomial.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem tentWeight_nonneg (m r : ℕ) (hr : r ≤ 2*m+1) : 0 ≤ tentWeight m r := by
  rw [tentWeight]
  split_ifs
  · positivity
  · exact sub_nonneg.mpr (by exact_mod_cast hr)

theorem combination_x_moment (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q))
    (a : ℕ) (v : ℕ → ℝ) (N : ℕ) :
    L ((X*orthogonalCombination L hpos a v (N+1))*orthogonalCombination L hpos a v (N+1))=
      2*∑ r ∈ Finset.range N, v r*v (r+1)*Real.sqrt (jacobiSquare d (a+r)) := by
  rw [shifted_pair_expansion L hpos d hd hsymm, adjacent_symmetric_sum]

theorem tent_raw_deficit (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q))
    (a m : ℕ) (ell : ℝ) (hell : 8*d ≤ ell) (ha : ell ≤ 2*(a:ℝ)) :
    let p := orthogonalCombination L hpos a (tentWeight m) (2*m+1)
    L (p*p)-L ((X*p)*p) ≤ (m:ℝ)+1+2*(d/ell)^2*L (p*p) := by
  dsimp only
  rw [combination_norm, combination_x_moment L hpos d hd hsymm]
  let S := ∑ r ∈ Finset.range (2*m+1), tentWeight m r^2
  let A := ∑ r ∈ Finset.range (2*m), tentWeight m r*tentWeight m (r+1)
  have he : S-A=(m:ℝ)+1 := tent_energy_identity m
  have hAS : A ≤ S := by linarith
  have hsum : (1/2-(d/ell)^2)*A ≤
      ∑ r ∈ Finset.range (2*m), tentWeight m r*tentWeight m (r+1)*
        Real.sqrt (jacobiSquare d (a+r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrm := Finset.mem_range.mp hr
    have hv := mul_nonneg (tentWeight_nonneg m r (by omega))
      (tentWeight_nonneg m (r+1) (by omega))
    have hj : ell ≤ 2*((a+r:ℕ):ℝ) := by
      push_cast
      have hr0 : (0:ℝ) ≤ r := by positivity
      linarith
    have hh := mul_le_mul_of_nonneg_left (jacobi_sqrt_lower d hd (a+r) ell hell hj) hv
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hAS (sq_nonneg (d/ell))
  change S-2*(∑ r ∈ Finset.range (2*m), tentWeight m r*tentWeight m (r+1)*
    Real.sqrt (jacobiSquare d (a+r))) ≤ (m:ℝ)+1+2*(d/ell)^2*S
  nlinarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/TentPolynomial.lean

-- BEGIN SSProof/TentParameters.lean
section

namespace SphereSOS.Rate.SSFresh

theorem tent_indices (ell : ℕ) :
    let m := ell/4
    let a := ell-2*m
    a+2*m=ell ∧ (ell:ℝ) ≤ 2*(a:ℝ) ∧ (ell:ℝ) ≤ 4*((m:ℝ)+1) := by
  dsimp only
  have hm : 4*(ell/4) ≤ ell := Nat.mul_div_le ell 4
  constructor
  · omega
  constructor
  · exact_mod_cast (show ell ≤ 2*(ell-2*(ell/4)) by omega)
  · exact_mod_cast (show ell ≤ 4*(ell/4+1) by omega)

theorem tent_normalized_error (d ell : ℝ) (hd : 2 ≤ d) (hell : 0 < ell)
    (m : ℕ) (hm : ell ≤ 4*((m:ℝ)+1)) :
    (m:ℝ)+1 ≤ 8*(d/ell)^2*(∑ r ∈ Finset.range (2*m+1), tentWeight m r^2) := by
  let z : ℝ := (m:ℝ)+1
  let S : ℝ := ∑ r ∈ Finset.range (2*m+1), tentWeight m r^2
  have hz : 0 < z := by dsimp [z]; positivity
  have hS : z^3/2 ≤ S := tent_energy_lower m
  have hr : 0 ≤ d/ell := div_nonneg (by linarith) hell.le
  have h1 : 1 ≤ 2*(d/ell)*z := by
    have hdz : ell ≤ 2*d*z := by change ell ≤ 4*z at hm; nlinarith
    have hh : 1 ≤ (2*d*z)/ell := (le_div_iff₀ hell).2 (by simpa using hdz)
    convert hh using 1
    field_simp
  have h2 : 1 ≤ 4*(d/ell)^2*z^2 := by nlinarith [sq_nonneg (2*(d/ell)*z-1)]
  have h3 := mul_le_mul_of_nonneg_right h2 hz.le
  have h4 := mul_le_mul_of_nonneg_left hS (show 0 ≤ 8*(d/ell)^2 by positivity)
  change z ≤ 8*(d/ell)^2*S
  nlinarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/TentParameters.lean

-- BEGIN SSProof/NormalizePolynomial.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def normalizePolynomial (p : Polynomial ℝ) (S : ℝ) : Polynomial ℝ :=
  C ((Real.sqrt S)⁻¹)*p

theorem normalizePolynomial_degree (p : Polynomial ℝ) (S : ℝ) :
    (normalizePolynomial p S).natDegree ≤ p.natDegree := natDegree_C_mul_le _ _

theorem normalizePolynomial_square (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (p : Polynomial ℝ) (S : ℝ) (hS : 0 < S) (hp : L (p*p)=S) :
    L (normalizePolynomial p S*normalizePolynomial p S)=1 := by
  rw [normalizePolynomial, functional_two_C, hp]
  have hs := Real.sqrt_pos.2 hS
  have he := Real.sq_sqrt hS.le
  field_simp
  nlinarith

theorem normalizePolynomial_deficit (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (p : Polynomial ℝ) (S B : ℝ) (hS : 0 < S) (hp : L (p*p)=S)
    (h : L (p*p)-L ((X*p)*p) ≤ B*S) :
    L ((1-X)*(normalizePolynomial p S*normalizePolynomial p S)) ≤ B := by
  have he : (1-X)*(normalizePolynomial p S*normalizePolynomial p S) =
      C ((Real.sqrt S)⁻¹*(Real.sqrt S)⁻¹)*(p*p-(X*p)*p) := by
    simp only [normalizePolynomial, map_mul]
    ring
  rw [he, functional_C_mul, map_sub]
  have hs := Real.sqrt_pos.2 hS
  have heq : (Real.sqrt S)⁻¹*(Real.sqrt S)⁻¹=1/S := by
    have ht := Real.sq_sqrt hS.le
    field_simp
    nlinarith
  rw [heq, one_div, ← div_eq_inv_mul, hp]
  exact (div_le_iff₀ hS).2 (by simpa only [hp] using h)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/NormalizePolynomial.lean

-- BEGIN SSProof/PolynomialLocalizer.lean
section

open Polynomial

namespace SphereSOS.Rate.SSFresh

theorem combination_degree (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (a N ell : ℕ) (v : ℕ → ℝ) (hN : a+N ≤ ell+1) :
    (orthogonalCombination L hpos a v N).natDegree ≤ ell := by
  apply natDegree_sum_le_of_forall_le
  intro r hr
  apply (natDegree_C_mul_le _ _).trans
  rw [normalizedOrthogonal_natDegree]
  have := Finset.mem_range.mp hr
  omega

theorem exists_polynomial_localizer (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p))
    (d : ℝ) (hd : 2 ≤ d)
    (hsymm : ∀ p q, L (sturmPolynomial d p*q)=L (p*sturmPolynomial d q))
    (ell : ℕ) (hell : 8*d ≤ (ell:ℝ)) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ ell ∧ L (q*q)=1 ∧
      L ((1-X)*(q*q)) ≤ 10*(d/(ell:ℝ))^2 := by
  let m := ell/4
  let a := ell-2*m
  let p := orthogonalCombination L hpos a (tentWeight m) (2*m+1)
  let S := ∑ r ∈ Finset.range (2*m+1), tentWeight m r^2
  have hi := tent_indices ell
  change a+2*m=ell ∧ (ell:ℝ) ≤ 2*(a:ℝ) ∧ (ell:ℝ) ≤ 4*((m:ℝ)+1) at hi
  have hS : 0 < S := by
    have hb := tent_energy_lower m
    have hp : 0 < ((m:ℝ)+1)^3/2 := by positivity
    exact hp.trans_le hb
  have hp : L (p*p)=S := combination_norm L hpos a (tentWeight m) (2*m+1)
  refine ⟨normalizePolynomial p S, ?_, normalizePolynomial_square L p S hS hp, ?_⟩
  · apply (normalizePolynomial_degree p S).trans
    exact combination_degree L hpos a (2*m+1) ell (tentWeight m) (by omega)
  · apply normalizePolynomial_deficit L p S _ hS hp
    have hraw := tent_raw_deficit L hpos d hd hsymm a m ell hell hi.2.1
    change L (p*p)-L ((X*p)*p) ≤ (m:ℝ)+1+2*(d/(ell:ℝ))^2*L (p*p) at hraw
    have he := tent_normalized_error d ell hd (by linarith) m hi.2.2
    change (m:ℝ)+1 ≤ 8*(d/(ell:ℝ))^2*S at he
    rw [hp] at hraw ⊢
    linarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/PolynomialLocalizer.lean

-- BEGIN SSProof/AxisReflection.lean
section

open scoped RealInnerProductSpace

namespace SphereSOS.Rate.SSFresh

noncomputable def axisReflection {d : ℕ} (x : ESpace d) : ESpace d ≃ₗᵢ[ℝ] ESpace d :=
  (Submodule.span ℝ {x}).reflection

 theorem axisReflection_apply {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1) :
    axisReflection x y = (2*⟪x,y⟫) • x - y := by
  rw [axisReflection, Submodule.reflection_singleton_apply, hx]
  norm_num [smul_smul]
  module

 theorem axisReflection_inner {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1) :
    ⟪x,axisReflection x y⟫ = ⟪x,y⟫ := by
  rw [axisReflection_apply x y hx, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx]
  ring

 theorem normalized_remainder {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1)
    (hr : 0 < ‖y-⟪x,y⟫ • x‖) :
    let u := ‖y-⟪x,y⟫ • x‖⁻¹ • (y-⟪x,y⟫ • x)
    ‖u‖=1 ∧ ⟪x,u⟫=0 ∧ y=⟪x,y⟫ • x+‖y-⟪x,y⟫ • x‖ • u := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']
  · rw [real_inner_smul_right, perpendicular_remainder x y hx, mul_zero]
  · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel

end SphereSOS.Rate.SSFresh

end
-- END SSProof/AxisReflection.lean

-- BEGIN SSProof/PolynomialRestrictions.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def sphereEval (d : ℕ) :
    MvPolynomial (Fin d) ℝ →ₗ[ℝ] C(UnitSphere d, ℝ) where
  toFun p := ⟨fun x => MvPolynomial.eval (sphereCoords x) p,
    p.continuous_eval.comp (by unfold sphereCoords; fun_prop)⟩
  map_add' p q := by ext x; simp
  map_smul' c p := by ext x; simp

noncomputable def degreeSphereEval (d s : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ s →ₗ[ℝ] C(UnitSphere d, ℝ) :=
  (sphereEval d).comp (MvPolynomial.restrictTotalDegree (Fin d) ℝ s).subtype

noncomputable def restrictionSpace (d s : ℕ) : Submodule ℝ C(UnitSphere d, ℝ) :=
  LinearMap.range (degreeSphereEval d s)

instance restrictionSpace_finite (d s : ℕ) :
    FiniteDimensional ℝ (restrictionSpace d s) := by
  unfold restrictionSpace
  infer_instance

 theorem mem_restrictionSpace_iff (d s : ℕ) (f : C(UnitSphere d, ℝ)) :
    f ∈ restrictionSpace d s ↔ ∃ p : MvPolynomial (Fin d) ℝ,
      p.totalDegree ≤ s ∧ ∀ x, f x = MvPolynomial.eval (sphereCoords x) p := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.val, (MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property, ?_⟩
    intro x
    rw [← hp]
    rfl
  · rintro ⟨p, hp, hf⟩
    refine ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp⟩, ?_⟩
    ext x
    exact (hf x).symm

end SphereSOS.Rate.SSFresh

end
-- END SSProof/PolynomialRestrictions.lean

-- BEGIN SSProof/KernelBasics.lean
section

open scoped RealInnerProductSpace
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

noncomputable def kernelWeight {d : ℕ} (q : Polynomial ℝ) (x y : UnitSphere d) : ℝ :=
  (q.eval ⟪x.val,y.val⟫)^2

noncomputable def kernelValue {d : ℕ} (q : Polynomial ℝ)
    (f : C(UnitSphere d, ℝ)) (x : UnitSphere d) : ℝ :=
  ∫ y, kernelWeight q x y * f y ∂sphereLaw d

 theorem kernelWeight_nonneg {d : ℕ} (q : Polynomial ℝ) (x y : UnitSphere d) :
    0 ≤ kernelWeight q x y := sq_nonneg _

 theorem kernelWeight_continuous {d : ℕ} (q : Polynomial ℝ) (x : UnitSphere d) :
    Continuous (kernelWeight q x) := by
  unfold kernelWeight
  fun_prop

 theorem kernelWeight_reflection {d : ℕ} (q : Polynomial ℝ) (x y : UnitSphere d) :
    kernelWeight q x (sphereAction (axisReflection x.val) y) = kernelWeight q x y := by
  unfold kernelWeight
  congr 2
  exact axisReflection_inner x.val y.val
    (by simpa only [Metric.mem_sphere, dist_zero_right] using x.property)

 theorem kernelValue_reflection {d : ℕ} (q : Polynomial ℝ)
    (f : C(UnitSphere d, ℝ)) (x : UnitSphere d) :
    (∫ y, kernelWeight q x y * f (sphereAction (axisReflection x.val) y) ∂sphereLaw d) =
      kernelValue q f x := by
  have h := (sphereAction_preserves (axisReflection x.val)).integral_comp
    (sphereAction (axisReflection x.val)).measurableEmbedding
    (fun y => kernelWeight q x y * f y)
  simpa only [kernelWeight_reflection, kernelValue] using h

 theorem kernelValue_add {d : ℕ} (hd : 0 < d) (q : Polynomial ℝ)
    (f g : C(UnitSphere d, ℝ)) (x : UnitSphere d) :
    kernelValue q (f+g) x = kernelValue q f x + kernelValue q g x := by
  let := sphereLaw_probability hd
  unfold kernelValue
  simp only [ContinuousMap.add_apply, mul_add]
  apply integral_add
  · exact ((kernelWeight_continuous q x).mul f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((kernelWeight_continuous q x).mul g.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

 theorem kernelValue_smul {d : ℕ} (q : Polynomial ℝ)
    (f : C(UnitSphere d, ℝ)) (x : UnitSphere d) (c : ℝ) :
    kernelValue q (c • f) x = c * kernelValue q f x := by
  unfold kernelValue
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (kernelWeight q x _) c]
  rw [integral_const_mul]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelBasics.lean

-- BEGIN SSProof/PolynomialRotation.lean
section

open MeasureTheory

namespace SphereSOS.Rate.SSFresh

theorem polynomial_inner_isometry {d : ℕ} (p : Polynomial ℝ)
    (e : ESpace d ≃ₗᵢ[ℝ] ESpace d) (x : ESpace d) :
    (∫ y : UnitSphere d, p.eval (inner ℝ (e x) y.val) ∂sphereLaw d)=
      ∫ y : UnitSphere d, p.eval (inner ℝ x y.val) ∂sphereLaw d := by
  have h := (sphereAction_preserves e).integral_comp
    (sphereAction e).measurableEmbedding
    (fun y : UnitSphere d => p.eval (inner ℝ (e x) y.val))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with y
  change p.eval (inner ℝ (e x) (e y.val))= _
  rw [e.inner_map_map]

theorem polynomial_inner_norm_eq {d : ℕ} (p : Polynomial ℝ) (x y : ESpace d)
    (h : ‖x‖=‖y‖) :
    (∫ z : UnitSphere d, p.eval (inner ℝ x z.val) ∂sphereLaw d)=
      ∫ z : UnitSphere d, p.eval (inner ℝ y z.val) ∂sphereLaw d := by
  let e := (ℝ ∙ (x-y)).orthogonal.reflection
  have he : e x=y := Submodule.reflection_sub h
  rw [← he]
  exact (polynomial_inner_isometry p e x).symm

theorem coordinateMean_inner {d : ℕ} (hd : 0 < d) (i : Fin d)
    (p : Polynomial ℝ) (x : UnitSphere d) :
    (∫ y : UnitSphere d, p.eval (inner ℝ x.val y.val) ∂sphereLaw d)=coordinateMean hd i p := by
  let e : ESpace d := EuclideanSpace.single i 1
  have he : ‖e‖=1 := by simp [e]
  have hx : ‖x.val‖=1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [polynomial_inner_norm_eq p x.val e (hx.trans he.symm)]
  change (∫ y : UnitSphere d, p.eval (inner ℝ e y.val) ∂sphereLaw d)=
    ∫ y : UnitSphere d, p.eval (sphereCoords y i) ∂sphereLaw d
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  simp [e, EuclideanSpace.inner_single_left, sphereCoords]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/PolynomialRotation.lean

-- BEGIN SSProof/LocalizingKernel.lean
section

open Polynomial MeasureTheory

namespace SphereSOS.Rate.SSFresh

theorem exists_localizing_kernel (d ell : ℕ) (hd : 2 ≤ d) (hell : 8*d ≤ ell) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ ell ∧
      (∀ x : UnitSphere d, (∫ y, kernelWeight q x y ∂sphereLaw d)=1) ∧
      (∀ x : UnitSphere d,
        (∫ y, kernelWeight q x y*(1-inner ℝ x.val y.val) ∂sphereLaw d) ≤
          1000*((d:ℝ)/(ell:ℝ))^2) := by
  have hd0 : 0 < d := by omega
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  let L := coordinateMean hd0 i
  have hpos : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < L (p*p) :=
    coordinateMean_square_pos hd0 i j hij
  obtain ⟨q,hq,hn,he⟩ := exists_polynomial_localizer L hpos d (by exact_mod_cast hd)
    (coordinateMean_sturm_symm hd0 i) ell (by exact_mod_cast hell)
  refine ⟨q,hq,?_,?_⟩
  · intro x
    have h := coordinateMean_inner hd0 i (q*q) x
    simpa only [kernelWeight, pow_two, Polynomial.eval_mul] using h.trans hn
  · intro x
    have h := coordinateMean_inner hd0 i ((1-X)*(q*q)) x
    have heq : (∫ y : UnitSphere d, kernelWeight q x y*(1-inner ℝ x.val y.val) ∂sphereLaw d)=
        L ((1-X)*(q*q)) := by
      rw [← h]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [kernelWeight, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X]
      ring
    rw [heq]
    exact he.trans (by nlinarith [sq_nonneg ((d:ℝ)/(ell:ℝ))])

end SphereSOS.Rate.SSFresh

end
-- END SSProof/LocalizingKernel.lean

-- BEGIN SSProof/DerivativeDegree.lean
section

open MvPolynomial

namespace SphereSOS.Rate.SSFresh

 theorem totalDegree_pderiv_le {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℝ) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro z hz
  have hz' : coeff z (pderiv i p)≠0 := mem_support_iff.mp hz
  have hp : z+Finsupp.single i 1 ∈ p.support := by
    apply mem_support_iff.mpr
    intro he
    rw [coeff_pderiv,he,zero_mul] at hz'
    exact hz' rfl
  have h := le_totalDegree hp
  have he : (z+Finsupp.single i 1).sum (fun _ e => e)=z.sum (fun _ e => e)+1 := by
    simp [Finsupp.sum_add_index',Finsupp.sum_single_index]
  rw [he] at h
  exact (Nat.le_add_right _ 1).trans h

end SphereSOS.Rate.SSFresh

end
-- END SSProof/DerivativeDegree.lean

-- BEGIN SSProof/RadialSpan.lean
section

open scoped BigOperators
open MvPolynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def radialSpan (d s : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  Submodule.span ℝ {f | ∃ r : ℕ, ∃ p : MvPolynomial (Fin d) ℝ,
    p.totalDegree ≤ s ∧ f=normSqPoly d^r*p}

 theorem radialSpan_generator {d s : ℕ} (r : ℕ) (p : MvPolynomial (Fin d) ℝ)
    (hp : p.totalDegree ≤ s) : normSqPoly d^r*p ∈ radialSpan d s :=
  Submodule.subset_span ⟨r,p,hp,rfl⟩

 theorem radialSpan_representative {d s : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (hf : f ∈ radialSpan d s) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ s ∧
      ∀ x ∈ sphere d, eval x f=eval x p := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨r,p,hp,rfl⟩ := hf
    refine ⟨p,hp,?_⟩
    intro x hx
    have he : eval x (normSqPoly d)=1 := by simpa [normSqPoly,sphere] using hx
    simp only [map_mul,map_pow,he,one_pow,one_mul]
  | zero => exact ⟨0,by simp,by simp⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨p,hp,he⟩ := ihf
    obtain ⟨q,hq,he'⟩ := ihg
    refine ⟨p+q,(totalDegree_add _ _).trans (max_le hp hq),?_⟩
    intro x hx
    simp only [map_add,he x hx,he' x hx]
  | smul c f hf ih =>
    obtain ⟨p,hp,he⟩ := ih
    refine ⟨c • p,(totalDegree_smul_le _ _).trans hp,?_⟩
    intro x hx
    simp only [smul_eval,he x hx]

 theorem radialSpan_pderiv {d s : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (hf : f ∈ radialSpan d s) (i : Fin d) : pderiv i f ∈ radialSpan d (s+1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨r,p,hp,rfl⟩ := hf
    have h1 := radialSpan_generator (s := s+1) (r-1) (C (2*(r:ℝ))*X i*p) (by
      apply (totalDegree_mul _ _).trans
      have h := totalDegree_mul (C (2*(r:ℝ))) (X i : MvPolynomial (Fin d) ℝ)
      simp only [totalDegree_C,totalDegree_X,zero_add] at h
      omega)
    have h2 := radialSpan_generator (s := s+1) r (pderiv i p)
      ((totalDegree_pderiv_le i p).trans (hp.trans (Nat.le_succ s)))
    have he : pderiv i (normSqPoly d^r*p)=
        normSqPoly d^(r-1)*(C (2*(r:ℝ))*X i*p)+normSqPoly d^r*pderiv i p := by
      rw [pderiv_mul,pderiv_pow,pderiv_normSqPoly]
      simp only [map_mul,map_natCast,map_ofNat]
      ring
    rw [he]
    exact (radialSpan d (s+1)).add_mem h1 h2
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (radialSpan d (s+1)).add_mem ihf ihg
  | smul c f hf ih =>
    rw [(pderiv i).map_smul]
    exact (radialSpan d (s+1)).smul_mem c ih

end SphereSOS.Rate.SSFresh

end
-- END SSProof/RadialSpan.lean

-- BEGIN SSProof/DerivativeList.lean
section

open MvPolynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def derivativeList {σ R : Type*} [CommSemiring R] :
    List σ → MvPolynomial σ R → MvPolynomial σ R
  | [],p => p
  | i::l,p => pderiv i (derivativeList l p)

 theorem coefficientMean_derivativeList {d : ℕ} (hd : 0 < d) (l : List (Fin d))
    (p : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) :
    coefficientMean hd (derivativeList l p)=derivativeList l (coefficientMean hd p) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [derivativeList,coefficientMean_pderiv,ih]

 theorem radialSpan_derivativeList {d s : ℕ} (l : List (Fin d))
    (p : MvPolynomial (Fin d) ℝ) (hp : p ∈ radialSpan d s) :
    derivativeList l p ∈ radialSpan d (s+l.length) := by
  induction l with
  | nil => simpa only [derivativeList,List.length_nil,Nat.add_zero] using hp
  | cons i l ih =>
    have h := radialSpan_pderiv (derivativeList l p) ih i
    simpa only [derivativeList,List.length_cons,Nat.add_assoc] using h

def derivativeFactor : ℕ → ℕ → ℕ
  | _j,0 => 1
  | j,a+1 => derivativeFactor (j+1) a*(j+1)

 theorem derivativeFactor_pos (j a : ℕ) : 0 < derivativeFactor j a := by
  induction a generalizing j with
  | zero => simp [derivativeFactor]
  | succ a ih => exact Nat.mul_pos (ih (j+1)) (Nat.succ_pos j)

 theorem derivativeList_bilinear_pow {d : ℕ} (l : List (Fin d)) (j : ℕ) :
    derivativeList l (bilinearPolynomial d^(j+l.length)) =
      (derivativeFactor j l.length : ℕ) •
        (C ((l.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod)*bilinearPolynomial d^j) := by
  induction l generalizing j with
  | nil => simp [derivativeList,derivativeFactor]
  | cons i l ih =>
    have he : j+(i::l).length=(j+1)+l.length := by simp; omega
    rw [he,derivativeList,ih (j+1)]
    simp only [pderiv_mul,pderiv_C,zero_mul,zero_add,pderiv_pow,
      pderiv_bilinearPolynomial,Nat.add_sub_cancel,List.length_cons,List.map_cons,List.prod_cons,
      derivativeFactor,map_mul,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one,(pderiv i).map_natCast]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/DerivativeList.lean

-- BEGIN SSProof/RadialMomentSpan.lean
section

open MvPolynomial

namespace SphereSOS.Rate.SSFresh

 theorem momentPolynomial_odd {d : ℕ} (hd : 0 < d) (r : ℕ) (hr : Odd r) :
    momentPolynomial d r=0 := by
  apply MvPolynomial.funext
  intro x
  have h := eval_momentPolynomial hd r (WithLp.toLp 2 x)
  change eval x (momentPolynomial d r)=_ at h
  rw [h,linearMoment_odd r hr]
  simp

 theorem momentPolynomial_radialSpan {d : ℕ} (hd : 0 < d) (r : ℕ) :
    momentPolynomial d r ∈ radialSpan d 0 := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨a,ha⟩ := hr
    have he : r=2*a := by omega
    rw [he,momentPolynomial_even hd a (EuclideanSpace.single ⟨0,hd⟩ 1) (by simp)]
    have h := radialSpan_generator (d := d) (s := 0) a
      (C (linearMoment (2*a) (EuclideanSpace.single ⟨0,hd⟩ 1))) (by simp)
    simpa only [mul_comm] using h
  · rw [momentPolynomial_odd hd r hr]
    exact (radialSpan d 0).zero_mem

 theorem coefficientMean_bilinear_list_radial {d : ℕ} (hd : 0 < d)
    (l : List (Fin d)) (j : ℕ) :
    coefficientMean hd
      (C ((l.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod)*bilinearPolynomial d^j)
      ∈ radialSpan d l.length := by
  have h := radialSpan_derivativeList l (momentPolynomial d (j+l.length))
    (momentPolynomial_radialSpan hd (j+l.length))
  simp only [Nat.zero_add] at h
  rw [← coefficientMean_bilinear_pow hd (j+l.length),← coefficientMean_derivativeList,
    derivativeList_bilinear_pow,map_nsmul] at h
  have hf : (derivativeFactor j l.length : ℝ)  ≠  0 := by
    exact_mod_cast (Nat.ne_of_gt (derivativeFactor_pos j l.length))
  have hs := (radialSpan d l.length).smul_mem (derivativeFactor j l.length : ℝ)⁻¹ h
  simpa only [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hf,one_smul] using hs

end SphereSOS.Rate.SSFresh

end
-- END SSProof/RadialMomentSpan.lean

-- BEGIN SSProof/MonomialList.lean
section

open MvPolynomial

namespace SphereSOS.Rate.SSFresh

 theorem monomial_list {d : ℕ} (z : Fin d →₀ ℕ) :
    ∃ l : List (Fin d), l.length=z.sum (fun _ e => e) ∧
      (l.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod=monomial z 1 := by
  classical
  refine ⟨z.toMultiset.toList,?_,?_⟩
  · rw [Multiset.length_toList,Finsupp.card_toMultiset]
    rfl
  · have he : ((z.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod) =
        z.prod (fun i e => (X i : MvPolynomial (Fin d) ℝ)^e) := by
      rw [Finsupp.toMultiset_map,Finsupp.prod_toMultiset]
      exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    calc
      (z.toMultiset.toList.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod =
          ((z.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℝ))).prod) := by
        exact Multiset.prod_map_toList _ _
      _ = z.prod (fun i e => (X i : MvPolynomial (Fin d) ℝ)^e) := he
      _ = monomial z 1 := by simp only [monomial_eq,C_1,one_mul]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MonomialList.lean

-- BEGIN SSProof/RadialInput.lean
section

open scoped BigOperators
open MvPolynomial

namespace SphereSOS.Rate.SSFresh

 theorem radialSpan_mono {d s t : ℕ} (hst : s ≤ t) : radialSpan d s  ≤  radialSpan d t := by
  apply Submodule.span_mono
  rintro f ⟨r,p,hp,he⟩
  exact ⟨r,p,hp.trans hst,he⟩

 theorem coefficientMean_outer_scalar {d : ℕ} (hd : 0 < d) (c : ℝ)
    (P : MvPolynomial (Fin d) (MvPolynomial (Fin d) ℝ)) :
    coefficientMean hd (C (C c)*P)=c • coefficientMean hd P := by
  ext z
  simp only [coefficientMean_coeff,coeff_C_mul,coeff_smul,smul_eq_mul,
    polynomialMean_real_mul]

 theorem coefficientMean_input_radial {d s : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ s) (j : ℕ) :
    coefficientMean hd (C p*bilinearPolynomial d^j) ∈ radialSpan d s := by
  classical
  rw [p.as_sum]
  simp only [map_sum,Finset.sum_mul]
  apply (radialSpan d s).sum_mem
  intro z hz
  obtain ⟨l,hlen,hprod⟩ := monomial_list z
  have h := coefficientMean_bilinear_list_radial hd l j
  rw [hprod] at h
  have hsize : l.length ≤ s := by rw [hlen]; exact (le_totalDegree hz).trans hp
  have hmem := radialSpan_mono (d := d) hsize h
  have hscalar := (radialSpan d s).smul_mem (p.coeff z) hmem
  have he : C (monomial z (p.coeff z))*bilinearPolynomial d^j =
      C (C (p.coeff z))*(C (monomial z 1)*bilinearPolynomial d^j) := by
    simp only [monomial_eq,map_mul,map_one,one_mul]
    ring
  rw [he,coefficientMean_outer_scalar]
  exact hscalar

end SphereSOS.Rate.SSFresh

end
-- END SSProof/RadialInput.lean

-- BEGIN SSProof/EvenCircle.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def circleMonomial (a b : ℕ) : Polynomial ℝ :=
  if Even b then Polynomial.X ^ a * (1 - Polynomial.X ^ 2) ^ (b / 2) else 0

 theorem circleMonomial_eval (a b : ℕ) (t r : ℝ) (hr : r ^ 2 = 1 - t ^ 2) :
    (circleMonomial a b).eval t = (t ^ a * r ^ b + t ^ a * (-r) ^ b) / 2 := by
  unfold circleMonomial
  split_ifs with hb
  · have hm : b % 2 = 0 := Nat.mod_eq_zero_of_dvd hb.two_dvd
    have he : b = 2 * (b / 2) := by omega
    have hn : (-r) ^ b = r ^ b := hb.neg_pow r
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one]
    have hp : r ^ b = (1-t^2) ^ (b/2) := by
      calc
        r ^ b = r ^ (2*(b/2)) := congrArg (fun j : ℕ => r^j) he
        _ = (1-t^2) ^ (b/2) := by rw [pow_mul, hr]
    rw [hn, hp]
    ring
  · have ho : Odd b := Nat.not_even_iff_odd.mp hb
    simp only [Polynomial.eval_zero]
    rw [ho.neg_pow]
    ring

 theorem circleMonomial_degree (a b : ℕ) :
    (circleMonomial a b).natDegree ≤ a + b := by
  unfold circleMonomial
  split_ifs with hb
  · calc
      (Polynomial.X ^ a * (1 - Polynomial.X ^ 2) ^ (b / 2) : Polynomial ℝ).natDegree
          ≤ (Polynomial.X ^ a : Polynomial ℝ).natDegree +
              ((1 - Polynomial.X ^ 2) ^ (b / 2) : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ a + 2 * (b / 2) := by
        gcongr
        · simp
        · apply (Polynomial.natDegree_pow_le).trans
          have h : (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
            exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (b / 2) h
      _ ≤ a + b := by omega
  · simp

end SphereSOS.Rate.SSFresh

end
-- END SSProof/EvenCircle.lean

-- BEGIN SSProof/BivariateCircle.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

noncomputable def bivariateCircle (P : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  ∑ z ∈ P.support, Polynomial.C (P.coeff z) * circleMonomial (z 0) (z 1)

 theorem bivariate_eval_expansion (P : MvPolynomial (Fin 2) ℝ) (t r : ℝ) :
    MvPolynomial.eval ![t,r] P =
      ∑ z ∈ P.support, P.coeff z * (t ^ z 0 * r ^ z 1) := by
  conv_lhs => rw [P.as_sum]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · simp

 theorem bivariateCircle_eval (P : MvPolynomial (Fin 2) ℝ) (t r : ℝ)
    (hr : r ^ 2 = 1-t^2) :
    (bivariateCircle P).eval t =
      (MvPolynomial.eval ![t,r] P + MvPolynomial.eval ![t,-r] P) / 2 := by
  rw [bivariate_eval_expansion, bivariate_eval_expansion]
  simp only [bivariateCircle, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, circleMonomial_eval _ _ _ _ hr]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  ring

 theorem bivariateCircle_degree (P : MvPolynomial (Fin 2) ℝ) :
    (bivariateCircle P).natDegree ≤ P.totalDegree := by
  unfold bivariateCircle
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have h := MvPolynomial.le_totalDegree hz
  have he : z.sum (fun _ e => e) = z 0 + z 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_two]
    · simp
  rw [he] at h
  exact (Polynomial.natDegree_C_mul_le _ _).trans ((circleMonomial_degree _ _).trans h)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/BivariateCircle.lean

-- BEGIN SSProof/LinearSubstitution.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

 theorem totalDegree_linear_substitution {σ τ : Type*}
    (p : MvPolynomial σ ℝ) (v : σ → MvPolynomial τ ℝ)
    (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (MvPolynomial.eval₂ (MvPolynomial.C) v p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro z hz
  rw [MvPolynomial.eval₂_monomial]
  have hprod : (z.prod (fun i e => v i ^ e)).totalDegree ≤ z.sum (fun _ e => e) := by
    unfold Finsupp.prod Finsupp.sum
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (z i) (hv i))
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa using hprod.trans (MvPolynomial.le_totalDegree hz))

noncomputable def circleSubstitution {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (x i) * MvPolynomial.X 0 +
      MvPolynomial.C (u i) * MvPolynomial.X 1) p

 theorem circleSubstitution_degree {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) :
    (circleSubstitution x u p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_linear_substitution
  intro i
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

 theorem circleSubstitution_eval {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (t r : ℝ) :
    MvPolynomial.eval ![t,r] (circleSubstitution x u p) =
      MvPolynomial.eval (fun i => t*x i+r*u i) p := by
  unfold circleSubstitution
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [MvPolynomial.eval₂_add, MvPolynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
      MvPolynomial.eval_add, MvPolynomial.eval_C, MvPolynomial.eval_X, hp,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/LinearSubstitution.lean

-- BEGIN SSProof/IntervalPolynomial.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

noncomputable def coefficientLip (p : Polynomial ℝ) : ℝ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j| * j

 theorem coefficientLip_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientLip p := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

 theorem interval_polynomial_lipschitz (p : Polynomial ℝ) (x y : ℝ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |p.eval x - p.eval y| ≤ coefficientLip p * |x - y| := by
  have hp (j : ℕ) : |x ^ j - y ^ j| ≤ |x - y| * j := by
    have h := abs_pow_sub_pow_le x y j
    have hm : max |x| |y| ≤ (1 : ℝ) := max_le hx hy
    have hn : max |x| |y| ^ (j - 1) ≤ (1 : ℝ) := by
      simpa using pow_le_pow_left₀ (le_trans (abs_nonneg x) (le_max_left _ _)) hm (j - 1)
    exact h.trans (by nlinarith [mul_nonneg (abs_nonneg (x-y)) (Nat.cast_nonneg j)])
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j * x ^ j - p.coeff j * y ^ j)|
        ≤ ∑ j ∈ Finset.range (p.natDegree + 1),
            |p.coeff j * x ^ j - p.coeff j * y ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (p.natDegree + 1), |p.coeff j| * (|x-y| * j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)
    _ = coefficientLip p * |x-y| := by
      unfold coefficientLip
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/IntervalPolynomial.lean

-- BEGIN SSProof/InterpolationBound.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

noncomputable def interpolationLip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) : ℝ :=
  ∑ i, coefficientLip (Lagrange.basis Finset.univ v i)

 theorem interpolationLip_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) : 0 ≤ interpolationLip v := by
  exact Finset.sum_nonneg fun i _ => coefficientLip_nonneg _

 theorem interpolated_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : Function.Injective v) (p : Polynomial ℝ)
    (hp : p.natDegree < Fintype.card ι) (M : ℝ)
    (hM : ∀ i, |p.eval (v i)| ≤ M) (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |p.eval x - p.eval y| ≤ M * interpolationLip v * |x-y| := by
  have he : p = Lagrange.interpolate Finset.univ v (fun i => p.eval (v i)) := by
    apply Lagrange.eq_interpolate hv.injOn
    apply lt_of_le_of_lt (Polynomial.degree_le_natDegree)
    exact_mod_cast hp
  have hx' : p.eval x = ∑ i, p.eval (v i) * (Lagrange.basis Finset.univ v i).eval x := by
    conv_lhs => rw [he]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hy' : p.eval y = ∑ i, p.eval (v i) * (Lagrange.basis Finset.univ v i).eval y := by
    conv_lhs => rw [he]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
  rw [hx', hy', ← Finset.sum_sub_distrib]
  calc
    |∑ i, (p.eval (v i) * (Lagrange.basis Finset.univ v i).eval x -
        p.eval (v i) * (Lagrange.basis Finset.univ v i).eval y)|
        ≤ ∑ i, |p.eval (v i) * (Lagrange.basis Finset.univ v i).eval x -
          p.eval (v i) * (Lagrange.basis Finset.univ v i).eval y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, M * (coefficientLip (Lagrange.basis Finset.univ v i) * |x-y|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hM i)
        (interval_polynomial_lipschitz _ x y hx hy) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hM i))
    _ = M * interpolationLip v * |x-y| := by
      unfold interpolationLip
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/InterpolationBound.lean

-- BEGIN SSProof/FixedNodes.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def intervalNode (s : ℕ) (i : Fin (s+1)) : ℝ :=
  (i.val : ℝ) / (s+1)

 theorem intervalNode_injective (s : ℕ) : Function.Injective (intervalNode s) := by
  intro i j h
  have hd : (s : ℝ)+1 ≠ 0 := by positivity
  have he : (i.val : ℝ) = j.val := (div_left_inj' hd).mp h
  exact Fin.ext (by exact_mod_cast he)

 theorem intervalNode_abs (s : ℕ) (i : Fin (s+1)) : |intervalNode s i| ≤ 1 := by
  unfold intervalNode
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity : 0 < (s : ℝ)+1)).mpr
  exact_mod_cast (Nat.le_of_lt i.isLt)

noncomputable def reflectionConstant (s : ℕ) : ℝ :=
  1 + interpolationLip (intervalNode s)

 theorem reflectionConstant_pos (s : ℕ) : 0 < reflectionConstant s := by
  have := interpolationLip_nonneg (intervalNode s)
  unfold reflectionConstant
  linarith

 theorem fixed_degree_lipschitz (s : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ s) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |t| ≤ 1 → |p.eval t| ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) :
    |p.eval t - p.eval 1| ≤ reflectionConstant s * M * (1-t) := by
  have h := interpolated_lipschitz (intervalNode s) (intervalNode_injective s) p
    (by simpa using Nat.lt_succ_of_le hp) M
    (fun i => hb _ (intervalNode_abs s i)) t 1 ht (by norm_num)
  have hdist : |t - 1| = 1-t := by
    rw [abs_of_nonpos (by have := le_trans (le_abs_self t) ht; linarith)]
    ring
  rw [hdist] at h
  have ht' : 0 ≤ 1-t := by have := le_trans (le_abs_self t) ht; linarith
  have hm : 0 ≤ M * (1-t) := mul_nonneg hM ht'
  unfold reflectionConstant
  nlinarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/FixedNodes.lean

-- BEGIN SSProof/ReflectedPolynomial.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def reflectedPolynomial {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) : Polynomial ℝ :=
  bivariateCircle (circleSubstitution x u p)

 theorem reflectedPolynomial_degree {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) :
    (reflectedPolynomial x u p).natDegree ≤ p.totalDegree :=
  (bivariateCircle_degree _).trans (circleSubstitution_degree _ _ _)

 theorem reflectedPolynomial_eval {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (t r : ℝ) (hr : r^2 = 1-t^2) :
    (reflectedPolynomial x u p).eval t =
      (MvPolynomial.eval (fun i => t*x i+r*u i) p +
       MvPolynomial.eval (fun i => t*x i-r*u i) p) / 2 := by
  rw [reflectedPolynomial, bivariateCircle_eval _ _ _ hr,
    circleSubstitution_eval, circleSubstitution_eval]
  have he : (fun i => t*x i + -r*u i) = (fun i => t*x i-r*u i) := by
    funext i
    ring
  rw [he]

 theorem reflectedPolynomial_one {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) :
    (reflectedPolynomial x u p).eval 1 = MvPolynomial.eval x p := by
  rw [reflectedPolynomial_eval x u p 1 0 (by norm_num)]
  simp

 theorem reflectedPolynomial_bound {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (M : ℝ)
    (hb : ∀ t r : ℝ, t^2+r^2=1 →
      |MvPolynomial.eval (fun i => t*x i+r*u i) p| ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) : |(reflectedPolynomial x u p).eval t| ≤ M := by
  have ht2 : 0 ≤ 1-t^2 := by
    have ha := abs_nonneg t
    nlinarith [sq_abs t]
  have hr : (Real.sqrt (1-t^2))^2 = 1-t^2 := Real.sq_sqrt ht2
  rw [reflectedPolynomial_eval _ _ _ _ _ hr, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hp := hb t (Real.sqrt (1-t^2)) (by linarith)
  have hm := hb t (-Real.sqrt (1-t^2)) (by nlinarith)
  have he : (fun i => t*x i+ -Real.sqrt (1-t^2)*u i) =
      (fun i => t*x i-Real.sqrt (1-t^2)*u i) := by funext i; ring
  rw [he] at hm
  have hh := abs_add_le (MvPolynomial.eval (fun i => t*x i+Real.sqrt (1-t^2)*u i) p)
    (MvPolynomial.eval (fun i => t*x i-Real.sqrt (1-t^2)*u i) p)
  linarith

 theorem reflection_polynomial_error {d : ℕ} (x u : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (s : ℕ) (hp : p.totalDegree ≤ s)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t r : ℝ, t^2+r^2=1 →
      |MvPolynomial.eval (fun i => t*x i+r*u i) p| ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) :
    |(reflectedPolynomial x u p).eval t - MvPolynomial.eval x p| ≤
      reflectionConstant s * M * (1-t) := by
  rw [← reflectedPolynomial_one x u p]
  exact fixed_degree_lipschitz s _ ((reflectedPolynomial_degree _ _ _).trans hp)
    M hM (reflectedPolynomial_bound x u p M hb) t ht

end SphereSOS.Rate.SSFresh

end
-- END SSProof/ReflectedPolynomial.lean

-- BEGIN SSProof/ReflectionError.lean
section

open scoped RealInnerProductSpace

namespace SphereSOS.Rate.SSFresh

 theorem coords_mem_of_norm {d : ℕ} (x : ESpace d) (hx : ‖x‖=1) :
    (fun i => x i) ∈ sphere d :=
  sphereCoords_mem ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩

 theorem reflection_error {d : ℕ} (x y : ESpace d) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (p : MvPolynomial (Fin d) ℝ) (s : ℕ) (hp : p.totalDegree ≤ s)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere d, |MvPolynomial.eval z p| ≤ M) :
    |(MvPolynomial.eval (fun i => y i) p +
       MvPolynomial.eval (fun i => axisReflection x y i) p) / 2 -
       MvPolynomial.eval (fun i => x i) p| ≤
      reflectionConstant s * M * (1-⟪x,y⟫) := by
  let t : ℝ := ⟪x,y⟫
  let r : ℝ := ‖y-t • x‖
  have ht : |t| ≤ 1 := by
    simpa only [hx, hy, one_mul] using abs_real_inner_le_norm x y
  have hr2 : r^2=1-t^2 := remainder_norm_sq x y hx hy
  have hL : 1 ≤ reflectionConstant s := by
    unfold reflectionConstant
    linarith [interpolationLip_nonneg (intervalNode s)]
  by_cases hr : r=0
  · have he : y=t • x := by
      have hh : y-t • x=0 := norm_eq_zero.mp hr
      exact sub_eq_zero.mp hh
    have ht2 : t=1 ∨ t= -1 := by
      apply eq_or_eq_neg_of_sq_eq_sq t 1
      rw [hr] at hr2
      nlinarith
    rcases ht2 with ht1 | htm
    · have hyx : y=x := by simpa only [ht1, one_smul] using he
      rw [hyx]
      have href : axisReflection x x=x := by
        rw [axisReflection_apply _ _ hx, real_inner_self_eq_norm_sq, hx]
        module
      rw [href]
      have hi : ⟪x,x⟫=(1:ℝ) := by rw [real_inner_self_eq_norm_sq,hx]; norm_num
      rw [hi]
      ring_nf
      simp
    · have ha := hb (fun i => y i) (coords_mem_of_norm y hy)
      have hb' := hb (fun i => axisReflection x y i)
        (coords_mem_of_norm _ (by rw [(axisReflection x).norm_map,hy]))
      have hc := hb (fun i => x i) (coords_mem_of_norm x hx)
      have hsum := abs_add_le (MvPolynomial.eval (fun i => y i) p)
        (MvPolynomial.eval (fun i => axisReflection x y i) p)
      have hdiff := abs_sub ( (MvPolynomial.eval (fun i => y i) p +
        MvPolynomial.eval (fun i => axisReflection x y i) p)/2)
        (MvPolynomial.eval (fun i => x i) p)
      rw [abs_div] at hdiff
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at hdiff
      change _ ≤ reflectionConstant s*M*(1-t)
      rw [htm]
      nlinarith
  · have hrpos : 0<r := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
    obtain ⟨hu, hxu, he⟩ := normalized_remainder x y hx hrpos
    let u := r⁻¹ • (y-t • x)
    change ‖u‖=1 at hu
    change ⟪x,u⟫=0 at hxu
    change y=t • x+r • u at he
    have href : axisReflection x y=t • x-r • u := by
      rw [axisReflection_apply _ _ hx]
      change (2*t) • x-y=t • x-r • u
      rw [he]
      module
    have hb' : ∀ a b : ℝ, a^2+b^2=1 →
        |MvPolynomial.eval (fun i => a*x i+b*u i) p| ≤ M := by
      intro a b hab
      exact hb _ (unit_circle_coords x u hx hu hxu a b hab)
    have h := reflection_polynomial_error (fun i => x i) (fun i => u i) p s hp M hM hb' t ht
    rw [reflectedPolynomial_eval _ _ _ _ _ hr2] at h
    change _ ≤ reflectionConstant s*M*(1-t)
    rw [href,he]
    simpa only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using h

end SphereSOS.Rate.SSFresh

end
-- END SSProof/ReflectionError.lean

-- BEGIN SSProof/SphereTransport.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

noncomputable def nativeSpherePoint {d : ℕ} (z : Fin d → ℝ) (hz : z ∈ sphere d) :
    UnitSphere d :=
  ⟨WithLp.toLp 2 z, by
    have h : ‖(WithLp.toLp 2 z : ESpace d)‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hz
    have hn := norm_nonneg (WithLp.toLp 2 z : ESpace d)
    have he : ‖(WithLp.toLp 2 z : ESpace d)‖=1 := by nlinarith
    simpa only [Metric.mem_sphere, dist_zero_right] using he⟩

 theorem sphereCoords_nativeSpherePoint {d : ℕ} (z : Fin d → ℝ) (hz : z ∈ sphere d) :
    sphereCoords (nativeSpherePoint z hz) = z := rfl

 theorem nativeSpherePoint_coords {d : ℕ} (x : UnitSphere d) :
    nativeSpherePoint (sphereCoords x) (sphereCoords_mem x) = x := by
  apply Subtype.ext
  rfl

 theorem restriction_representative_bound {d : ℕ} (f : C(UnitSphere d, ℝ))
    (p : MvPolynomial (Fin d) ℝ)
    (hp : ∀ x, f x = MvPolynomial.eval (sphereCoords x) p) :
    ∀ z ∈ sphere d, |MvPolynomial.eval z p| ≤ ‖f‖ := by
  intro z hz
  have h := f.norm_coe_le_norm (nativeSpherePoint z hz)
  rw [hp, sphereCoords_nativeSpherePoint] at h
  exact h

end SphereSOS.Rate.SSFresh

end
-- END SSProof/SphereTransport.lean

-- BEGIN SSProof/WeightedIntegral.lean
section

open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem weighted_reflection_integral {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (w f g h : C(X, ℝ)) (f0 C : ℝ) (_hC : 0 ≤ C)
    (hw : ∀ x, 0 ≤ w x) (hn : ∫ x, w x ∂μ = 1)
    (hs : ∫ x, w x*g x ∂μ = ∫ x, w x*f x ∂μ)
    (hb : ∀ x, |(f x+g x)/2-f0| ≤ C*h x) :
    |(∫ x, w x*f x ∂μ)-f0| ≤ C*(∫ x, w x*h x ∂μ) := by
  have hf : Integrable (fun x => w x*f x) μ :=
    (w.continuous.mul f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun x => w x*g x) μ :=
    (w.continuous.mul g.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwc : Integrable (fun x => w x*f0) μ :=
    (w.continuous.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, w x*((f x+g x)/2-f0) ∂μ) = (∫ x, w x*f x ∂μ)-f0 := by
    have ht : (fun x => w x*((f x+g x)/2-f0)) =
        (fun x => (w x*f x+w x*g x)/2-w x*f0) := by funext x; ring
    rw [ht, integral_sub (f := fun x => (w x*f x+w x*g x)/2)
      (g := fun x => w x*f0) ((hf.add hg).div_const 2) hwc, integral_div,
      integral_add hf hg, integral_mul_const, hn, hs]
    ring
  rw [← he]
  calc
    |∫ x, w x*((f x+g x)/2-f0) ∂μ| ≤
        ∫ x, |w x*((f x+g x)/2-f0)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C*(w x*h x) ∂μ := by
      apply integral_mono
      · exact (by fun_prop : Continuous (fun x => |w x*((f x+g x)/2-f0)|)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous (fun x => C*(w x*h x))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro x
        dsimp only
        rw [abs_mul, abs_of_nonneg (hw x)]
        have hh := mul_le_mul_of_nonneg_left (hb x) (hw x)
        nlinarith
    _ = C*(∫ x, w x*h x ∂μ) := integral_const_mul _ _

end SphereSOS.Rate.SSFresh

end
-- END SSProof/WeightedIntegral.lean

-- BEGIN SSProof/KernelError.lean
section

open scoped RealInnerProductSpace
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem kernel_error {d : ℕ} (hd : 0 < d) (s : ℕ) (q : Polynomial ℝ)
    (f : C(UnitSphere d, ℝ)) (hf : f ∈ restrictionSpace d s) (x : UnitSphere d)
    (hn : ∫ y, kernelWeight q x y ∂sphereLaw d = 1) :
    |kernelValue q f x-f x| ≤ reflectionConstant s * ‖f‖ *
      (∫ y, kernelWeight q x y*(1-⟪x.val,y.val⟫) ∂sphereLaw d) := by
  let := sphereLaw_probability hd
  obtain ⟨p,hp,hf⟩ := (mem_restrictionSpace_iff d s f).mp hf
  let w : C(UnitSphere d,ℝ) := ⟨kernelWeight q x,kernelWeight_continuous q x⟩
  let g : C(UnitSphere d,ℝ) := f.comp ⟨sphereAction (axisReflection x.val), (sphereAction (axisReflection x.val)).continuous⟩
  let h : C(UnitSphere d,ℝ) := ⟨fun y => 1-⟪x.val,y.val⟫,by fun_prop⟩
  apply weighted_reflection_integral (sphereLaw d) w f g h (f x)
    (reflectionConstant s*‖f‖) (mul_nonneg (reflectionConstant_pos s).le (norm_nonneg f))
    (kernelWeight_nonneg q x) hn (kernelValue_reflection q f x)
  intro y
  have hx : ‖x.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
  have hy : ‖y.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using y.property
  have he := reflection_error x.val y.val hx hy p s hp ‖f‖ (norm_nonneg f)
    (restriction_representative_bound f p hf)
  change |(f y+f (sphereAction (axisReflection x.val) y))/2-f x| ≤ _
  rw [hf y,hf (sphereAction (axisReflection x.val) y),hf x]
  exact he

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelError.lean

-- BEGIN SSProof/FiniteInverse.lean
section

namespace SphereSOS.Rate.SSFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

 theorem near_identity_injective (K : V →ₗ[ℝ] V) (δ : ℝ) (hδ : δ < 1)
    (hK : ∀ x, ‖K x - x‖ ≤ δ * ‖x‖) : Function.Injective K := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h := hK x
  rw [hx, zero_sub, norm_neg] at h
  have hz : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hz

 theorem near_identity_preimage [FiniteDimensional ℝ V]
    (K : V →ₗ[ℝ] V) (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2)
    (hK : ∀ x, ‖K x - x‖ ≤ δ * ‖x‖) (f : V) :
    ∃ g, K g = f ∧ ‖g - f‖ ≤ 2 * δ * ‖f‖ := by
  obtain ⟨g, hg⟩ := LinearMap.surjective_of_injective
    (near_identity_injective K δ (by linarith) hK) f
  refine ⟨g, hg, ?_⟩
  have he := hK g
  rw [hg, norm_sub_rev] at he
  have ht : ‖g‖ ≤ ‖g - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (g - f) f
  have hnorm : ‖g‖ ≤ 2 * ‖f‖ := by nlinarith [norm_nonneg g]
  calc
    ‖g - f‖ ≤ δ * ‖g‖ := he
    _ ≤ δ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hnorm hδ
    _ = 2 * δ * ‖f‖ := by ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/FiniteInverse.lean

-- BEGIN SSProof/KernelOperator.lean
section

namespace SphereSOS.Rate.SSFresh

 def KernelPreserves {d : ℕ} (s : ℕ) (q : Polynomial ℝ) : Prop :=
  ∀ f : restrictionSpace d s, ∃ g : restrictionSpace d s,
    ∀ x, g.val x=kernelValue q f.val x

noncomputable def kernelRestriction {d : ℕ} (hd : 0<d) (s : ℕ) (q : Polynomial ℝ)
    (hP : KernelPreserves (d := d) s q) : restrictionSpace d s →ₗ[ℝ] restrictionSpace d s where
  toFun f := Classical.choose (hP f)
  map_add' f g := by
    apply Subtype.ext
    ext x
    change (Classical.choose (hP (f+g))).val x =
      (Classical.choose (hP f)).val x + (Classical.choose (hP g)).val x
    rw [Classical.choose_spec (hP (f+g)),
      Classical.choose_spec (hP f),Classical.choose_spec (hP g)]
    exact kernelValue_add hd q f.val g.val x
  map_smul' c f := by
    apply Subtype.ext
    ext x
    change (Classical.choose (hP (c • f))).val x = c*(Classical.choose (hP f)).val x
    rw [Classical.choose_spec (hP (c • f)),
      Classical.choose_spec (hP f)]
    exact kernelValue_smul q f.val x c

 theorem kernelRestriction_apply {d : ℕ} (hd : 0<d) (s : ℕ) (q : Polynomial ℝ)
    (hP : KernelPreserves (d := d) s q) (f : restrictionSpace d s) (x : UnitSphere d) :
    (kernelRestriction hd s q hP f).val x = kernelValue q f.val x :=
  Classical.choose_spec (hP f) x

 theorem kernelRestriction_error {d : ℕ} (hd : 0<d) (s : ℕ) (q : Polynomial ℝ)
    (hP : KernelPreserves (d := d) s q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hE : ∀ f : restrictionSpace d s, ∀ x,
      |kernelValue q f.val x-f.val x| ≤ δ*‖f‖) (f : restrictionSpace d s) :
    ‖kernelRestriction hd s q hP f-f‖ ≤ δ*‖f‖ := by
  change ‖(kernelRestriction hd s q hP f).val-f.val‖ ≤ δ*‖f‖
  apply (ContinuousMap.norm_le _ (mul_nonneg hδ (norm_nonneg f))).mpr
  intro x
  change |(kernelRestriction hd s q hP f).val x-f.val x| ≤ _
  rw [kernelRestriction_apply]
  exact hE f x

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelOperator.lean

-- BEGIN SSProof/KernelPreservation.lean
section

open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem kernelPreserves_of_polynomial {d : ℕ} (s : ℕ) (q : Polynomial ℝ)
    (hpoly : ∀ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ s →
      ∃ r : MvPolynomial (Fin d) ℝ, r.totalDegree ≤ s ∧ ∀ x : UnitSphere d,
        MvPolynomial.eval (sphereCoords x) r =
          ∫ y, kernelWeight q x y*MvPolynomial.eval (sphereCoords y) p ∂sphereLaw d) :
    KernelPreserves (d := d) s q := by
  intro f
  obtain ⟨p,hp,hf⟩ := (mem_restrictionSpace_iff d s f.val).mp f.property
  obtain ⟨r,hr,he⟩ := hpoly p hp
  let g : C(UnitSphere d,ℝ) := sphereEval d r
  have hg : g ∈ restrictionSpace d s :=
    (mem_restrictionSpace_iff d s g).mpr ⟨r,hr,fun _ => rfl⟩
  refine ⟨⟨g,hg⟩,?_⟩
  intro x
  change MvPolynomial.eval (sphereCoords x) r = kernelValue q f.val x
  rw [he]
  unfold kernelValue
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hf y]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelPreservation.lean

-- BEGIN SSProof/KernelPolynomial.lean
section

open scoped BigOperators RealInnerProductSpace
open MeasureTheory MvPolynomial

namespace SphereSOS.Rate.SSFresh

noncomputable def kernelIntegralPolynomial {d : ℕ} (hd : 0 < d)
    (q : Polynomial ℝ) (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ j ∈ Finset.range ((q*q).natDegree+1), (q*q).coeff j •
    coefficientMean hd (C p*bilinearPolynomial d^j)

 theorem eval_bilinear_input {d : ℕ} (hd : 0 < d) (p : MvPolynomial (Fin d) ℝ)
    (j : ℕ) (x : UnitSphere d) :
    eval (sphereCoords x) (coefficientMean hd (C p*bilinearPolynomial d^j)) =
      ∫ y, eval (sphereCoords y) p*⟪x.val,y.val⟫^j ∂sphereLaw d := by
  rw [coefficientMean_eval]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [bilinearPolynomial,map_mul,map_pow,map_sum,eval_C,eval_X]
  congr 2

 theorem kernelIntegralPolynomial_radial {d s : ℕ} (hd : 0 < d)
    (q : Polynomial ℝ) (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ s) :
    kernelIntegralPolynomial hd q p ∈ radialSpan d s := by
  apply (radialSpan d s).sum_mem
  intro j hj
  exact (radialSpan d s).smul_mem _ (coefficientMean_input_radial hd p hp j)

 theorem eval_kernelIntegralPolynomial {d : ℕ} (hd : 0 < d)
    (q : Polynomial ℝ) (p : MvPolynomial (Fin d) ℝ) (x : UnitSphere d) :
    eval (sphereCoords x) (kernelIntegralPolynomial hd q p) =
      ∫ y, kernelWeight q x y*eval (sphereCoords y) p ∂sphereLaw d := by
  simp only [kernelIntegralPolynomial,map_sum,smul_eval,eval_bilinear_input]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with y
    unfold kernelWeight
    have h := Polynomial.eval_eq_sum_range (p := q*q) ⟪x.val,y.val⟫
    rw [Polynomial.eval_mul] at h
    rw [pow_two,h,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    apply sphere_continuous_integrable hd
    exact continuous_const.mul
      ((p.continuous_eval.comp sphereCoords_continuous).mul (by fun_prop))

 theorem kernel_polynomial_representative {d : ℕ} (hd : 0 < d) (s : ℕ)
    (q : Polynomial ℝ) (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ s) :
    ∃ r : MvPolynomial (Fin d) ℝ, r.totalDegree ≤ s ∧ ∀ x : UnitSphere d,
      eval (sphereCoords x) r =
        ∫ y, kernelWeight q x y*eval (sphereCoords y) p ∂sphereLaw d := by
  obtain ⟨r,hr,he⟩ := radialSpan_representative (kernelIntegralPolynomial hd q p)
    (kernelIntegralPolynomial_radial hd q p hp)
  refine ⟨r,hr,?_⟩
  intro x
  rw [← he (sphereCoords x) (sphereCoords_mem x),eval_kernelIntegralPolynomial]

 theorem actual_kernel_preserves {d : ℕ} (hd : 0 < d) (s : ℕ) (q : Polynomial ℝ) :
    KernelPreserves (d := d) s q :=
  kernelPreserves_of_polynomial s q (kernel_polynomial_representative hd s q)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelPolynomial.lean

-- BEGIN SSProof/InverseOperator.lean
section

namespace SphereSOS.Rate.SSFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable def nearIdentityEquiv (K : V →ₗ[ℝ] V) (δ : ℝ) (hδ : δ<1)
    (hK : ∀ f, ‖K f-f‖ ≤ δ*‖f‖) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective K ⟨near_identity_injective K δ hδ hK,
    LinearMap.surjective_of_injective (near_identity_injective K δ hδ hK)⟩

 theorem nearIdentityEquiv_inverse_error (K : V →ₗ[ℝ] V) (δ : ℝ)
    (hδ : 0≤δ) (hh : δ≤1/2) (hK : ∀ f, ‖K f-f‖ ≤ δ*‖f‖) (f : V) :
    ‖(nearIdentityEquiv K δ (by linarith) hK).symm f-f‖ ≤ 2*δ*‖f‖ := by
  obtain ⟨g,hg,he⟩ := near_identity_preimage K δ hδ hh hK f
  have heq : (nearIdentityEquiv K δ (by linarith) hK).symm f=g := by
    apply near_identity_injective K δ (by linarith) hK
    exact (nearIdentityEquiv K δ (by linarith) hK).apply_symm_apply f |>.trans hg.symm
  rw [heq]
  exact he

end SphereSOS.Rate.SSFresh

end
-- END SSProof/InverseOperator.lean

-- BEGIN SSProof/KernelInverse.lean
section

namespace SphereSOS.Rate.SSFresh

theorem exists_controlled_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (K : V →ₗ[ℝ] V)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : δ ≤ 1/2)
    (hK : ∀ f, ‖K f-f‖ ≤ δ*‖f‖) :
    ∃ T : V →ₗ[ℝ] V, (∀ f, K (T f)=f) ∧
      ∀ f, ‖T f-f‖ ≤ (2*δ)*‖f‖ := by
  let e := nearIdentityEquiv K δ (by linarith) hK
  refine ⟨e.symm.toLinearMap,?_,?_⟩
  · intro f
    exact e.apply_symm_apply f
  · exact nearIdentityEquiv_inverse_error K δ hδ hh hK

theorem exists_submodule_inverse {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (V : Submodule ℝ C(X,ℝ)) [FiniteDimensional ℝ V]
    (K : V →ₗ[ℝ] V) (δ : ℝ) (hδ : 0 ≤ δ) (hh : δ ≤ 1/2)
    (hK : ∀ f : V, ‖K f-f‖ ≤ δ*‖f‖) :
    ∃ T : V →ₗ[ℝ] V, (∀ f, K (T f)=f) ∧
      ∀ f, ‖T f-f‖ ≤ (2*δ)*‖f‖ := by
  have hinj : Function.Injective K := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have h := hK f
    rw [hf] at h
    change ‖(0 : C(X,ℝ))-f.val‖ ≤ δ*‖f.val‖ at h
    rw [zero_sub,norm_neg] at h
    have hz : ‖f.val‖=0 := by nlinarith [norm_nonneg f.val]
    apply Subtype.ext
    exact norm_eq_zero.mp hz
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective K
    ⟨hinj,LinearMap.surjective_of_injective hinj⟩
  refine ⟨e.symm.toLinearMap,?_,?_⟩
  · intro f
    exact e.apply_symm_apply f
  · intro f
    let g := e.symm f
    have hg : K g=f := e.apply_symm_apply f
    have he := hK g
    rw [hg] at he
    change ‖f.val-g.val‖ ≤ δ*‖g.val‖ at he
    rw [norm_sub_rev] at he
    have ht : ‖g.val‖ ≤ ‖g.val-f.val‖+‖f.val‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g.val-f.val) f.val
    have hnorm : ‖g.val‖ ≤ 2*‖f.val‖ := by nlinarith [norm_nonneg g.val]
    change ‖g.val-f.val‖ ≤ (2*δ)*‖f.val‖
    calc
      ‖g.val-f.val‖ ≤ δ*‖g.val‖ := he
      _ ≤ δ*(2*‖f.val‖) := mul_le_mul_of_nonneg_left hnorm hδ
      _ = (2*δ)*‖f.val‖ := by ring

theorem exists_restriction_inverse {d : ℕ} (s : ℕ) (q : Polynomial ℝ)
    (K : restrictionSpace d s →ₗ[ℝ] restrictionSpace d s)
    (happly : ∀ f x, (K f).val x=kernelValue q f.val x)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : δ ≤ 1/2)
    (hK : ∀ f, ‖K f-f‖ ≤ δ*‖f‖) :
    ∃ T : restrictionSpace d s →ₗ[ℝ] restrictionSpace d s,
      (∀ f x, kernelValue q (T f).val x=f.val x) ∧
      ∀ f, ‖T f-f‖ ≤ (2*δ)*‖f‖ := by
  obtain ⟨T,hT,hbound⟩ := exists_submodule_inverse (restrictionSpace d s) K δ hδ hh hK
  refine ⟨T,?_,hbound⟩
  intro f x
  rw [← happly]
  exact congrArg (fun g : restrictionSpace d s => g.val x) (hT f)

theorem exists_kernel_inverse {d : ℕ} (hd : 0 < d) (s : ℕ) (q : Polynomial ℝ)
    (hP : KernelPreserves (d := d) s q) (δ : ℝ) (hδ : 0 ≤ δ) (hh : δ ≤ 1/2)
    (hE : ∀ f : restrictionSpace d s, ∀ x,
      |kernelValue q f.val x-f.val x| ≤ δ*‖f‖) :
    ∃ T : restrictionSpace d s →ₗ[ℝ] restrictionSpace d s,
      (∀ f x, kernelValue q (T f).val x=f.val x) ∧
      ∀ f, ‖T f-f‖ ≤ (2*δ)*‖f‖ :=
  exists_restriction_inverse s q (kernelRestriction hd s q hP)
    (kernelRestriction_apply hd s q hP) δ hδ hh
    (kernelRestriction_error hd s q hP δ hδ hE)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelInverse.lean

-- BEGIN SSProof/MatrixInverseBound.lean
section

open scoped BigOperators Matrix

namespace SphereSOS.Rate.SSFresh

noncomputable def quadraticRestriction {X I : Type*} [TopologicalSpace X] [Fintype I]
    (V : Submodule ℝ C(X,ℝ)) (F : I → I → V) (v : I → ℝ) : V :=
  ∑ a, ∑ b, (v a*v b) • F a b

 theorem quadraticRestriction_apply {X I : Type*} [TopologicalSpace X] [Fintype I]
    (V : Submodule ℝ C(X,ℝ)) (F : I → I → V) (v : I → ℝ) (x : X) :
    (quadraticRestriction V F v).val x = ∑ a, ∑ b, v a*(F a b).val x*v b := by
  simp only [quadraticRestriction,Submodule.coe_sum,ContinuousMap.sum_apply,
    SetLike.val_smul,ContinuousMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

 theorem inverse_matrix_psd {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    [Fintype I] [DecidableEq I] (V : Submodule ℝ C(X,ℝ)) (T : V →ₗ[ℝ] V)
    (ε : ℝ) (hε : 0≤ε) (hT : ∀ f, ‖T f-f‖≤ε*‖f‖)
    (F : I → I → V) (hsym : ∀ a b, F a b=F b a)
    (hb : ∀ v : I → ℝ, ∀ x : X,
      0≤(quadraticRestriction V F v).val x ∧
      (quadraticRestriction V F v).val x≤∑ i, v i^2) (x : X) :
    (Matrix.of (fun a b : I => (T (F a b)).val x) + ε • (1 : Matrix I I ℝ)).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext a b
    simp only [Matrix.conjTranspose_apply,star_trivial,Matrix.add_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Matrix.of_apply]
    rw [hsym b a]
    congr 1
    simp only [eq_comm]
  · intro v
    let f := quadraticRestriction V F v
    let S : ℝ := ∑ i, v i^2
    have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hnorm : ‖f‖≤S := by
      change ‖f.val‖≤S
      apply (ContinuousMap.norm_le _ hS).mpr
      intro y
      change |f.val y|≤S
      rw [abs_of_nonneg (hb v y).1]
      exact (hb v y).2
    have herr : |(T f).val x-f.val x|≤ε*S := by
      have he := ContinuousMap.norm_coe_le_norm ((T f).val-f.val) x
      change |(T f).val x-f.val x|≤‖T f-f‖ at he
      exact he.trans ((hT f).trans (mul_le_mul_of_nonneg_left hnorm hε))
    have hlow : 0≤(T f).val x+ε*S := by
      have he := (abs_le.mp herr).1
      have hf := (hb v x).1
      change 0≤f.val x at hf
      linarith
    have ht : (T f).val x=∑ a, ∑ b, v a*(T (F a b)).val x*v b := by
      change (T (quadraticRestriction V F v)).val x = _
      have he : T (quadraticRestriction V F v)=quadraticRestriction V (fun a b => T (F a b)) v := by
        simp only [quadraticRestriction,map_sum,map_smul]
      rw [he,quadraticRestriction_apply]
    rw [ht] at hlow
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,dotProduct_smul]
    simpa only [dotProduct,Matrix.mulVec,Matrix.of_apply,Pi.star_apply,star_trivial,
      Finset.mul_sum,smul_eq_mul,S,pow_two,mul_assoc] using hlow

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MatrixInverseBound.lean

-- BEGIN SSProof/MatrixQuadraticBounds.lean
section

open scoped BigOperators Matrix

namespace SphereSOS.Rate.SSFresh

 theorem psd_subunit_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.PosSemidef) (hB : (1-A).PosSemidef) (v : I → ℝ) :
    0  ≤  ∑ i, ∑ j, v i*A i j*v j ∧
      (∑ i, ∑ j, v i*A i j*v j)  ≤  ∑ i, v i^2 := by
  have ha := hA.dotProduct_mulVec_nonneg v
  have hb := hB.dotProduct_mulVec_nonneg v
  have he : star v ⬝ᵥ ((1-A) *ᵥ v) =
      (∑ i, v i^2)-(∑ i, ∑ j, v i*A i j*v j) := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub]
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc,pow_two]
  rw [he] at hb
  constructor
  · simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc] using ha
  · linarith

 theorem restriction_matrix_bounds {X I : Type*} [TopologicalSpace X] [Fintype I]
    [DecidableEq I] (V : Submodule ℝ C(X,ℝ)) (F : I → I → V)
    (hF : ∀ x : X, Matrix.PosSemidef (Matrix.of (fun a b => (F a b).val x)) ∧
      ((1 : Matrix I I ℝ)-Matrix.of (fun a b => (F a b).val x)).PosSemidef) :
    ∀ v : I → ℝ, ∀ x : X, 0  ≤  (quadraticRestriction V F v).val x ∧
      (quadraticRestriction V F v).val x  ≤  ∑ i, v i^2 := by
  intro v x
  rw [quadraticRestriction_apply]
  exact psd_subunit_quadratic _ (hF x).1 (hF x).2 v

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MatrixQuadraticBounds.lean

-- BEGIN SSProof/KernelExpansion.lean
section

open scoped BigOperators RealInnerProductSpace

namespace SphereSOS.Rate.SSFresh

abbrev KernelIndex (d : ℕ) (q : Polynomial ℝ) :=
  (r : Fin (q.natDegree+1)) × (Fin r.val → Fin d)

noncomputable def kernelMonomial {d : ℕ} {q : Polynomial ℝ} (z : KernelIndex d q) :
    MvPolynomial (Fin d) ℝ := ∏ j, MvPolynomial.X (z.2 j)

noncomputable def kernelCoefficient {d : ℕ} (q : Polynomial ℝ)
    (z : KernelIndex d q) (y : UnitSphere d) : ℝ :=
  q.coeff z.1.val * ∏ j, sphereCoords y (z.2 j)

 theorem kernelMonomial_degree {d : ℕ} {q : Polynomial ℝ} (z : KernelIndex d q) :
    (kernelMonomial z).totalDegree ≤ q.natDegree := by
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  simp only [MvPolynomial.totalDegree_X,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one]
  exact Nat.le_of_lt_succ z.1.isLt

 theorem kernelCoefficient_continuous {d : ℕ} (q : Polynomial ℝ) (z : KernelIndex d q) :
    Continuous (kernelCoefficient q z) := by
  unfold kernelCoefficient sphereCoords
  fun_prop

 theorem kernel_expansion {d : ℕ} (q : Polynomial ℝ) (x y : UnitSphere d) :
    q.eval ⟪x.val,y.val⟫ = ∑ z : KernelIndex d q,
      kernelCoefficient q z y * MvPolynomial.eval (sphereCoords x) (kernelMonomial z) := by
  classical
  have hi : ⟪x.val,y.val⟫ = ∑ i, sphereCoords x i*sphereCoords y i := by
    simp [PiLp.inner_apply,sphereCoords,mul_comm]
  rw [Polynomial.eval_eq_sum_range,hi]
  simp_rw [Fintype.sum_pow,Finset.prod_mul_distrib,Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro f hf
  simp only [kernelCoefficient,kernelMonomial,map_prod,MvPolynomial.eval_X]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelExpansion.lean

-- BEGIN SSProof/GramSquare.lean
section

open scoped MatrixOrder

namespace SphereSOS.Rate.SSFresh

 theorem real_psd_factor {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, G = B * B.transpose := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  refine ⟨B.transpose, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose] using hB

 theorem constant_matrix_sos {d k : ℕ} (ℓ : ℕ) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosSemidef) :
    IsSosOnSphere (d := d) ℓ (A.map MvPolynomial.C) := by
  obtain ⟨B, hB⟩ := real_psd_factor A hA
  refine ⟨1, fun _ => B.map MvPolynomial.C, ?_, ?_⟩
  · intro j a b
    simp only [Matrix.map_apply, MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  · intro x hx
    simpa [evalM, Matrix.map_map, Function.comp_def, MvPolynomial.eval_C,
      Fin.sum_univ_one] using hB

 theorem empty_dimension_sos {k : ℕ} (ℓ : ℕ)
    (G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin 0) ℝ)) : IsSosOnSphere ℓ G := by
  refine ⟨0, Fin.elim0, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro x hx
    have : (0 : ℝ) = 1 := by simpa only [sphere, Set.mem_ofPred_eq, Fin.sum_univ_zero] using hx
    norm_num at this

end SphereSOS.Rate.SSFresh

end
-- END SSProof/GramSquare.lean

-- BEGIN SSProof/VectorSquares.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

 theorem zero_matrix_size_sos {d : ℕ} (ℓ : ℕ)
    (G : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin d) ℝ)) : IsSosOnSphere ℓ G := by
  refine ⟨0,Fin.elim0,?_,?_⟩
  · intro j
    exact Fin.elim0 j
  · intro x hx
    ext i
    exact Fin.elim0 i

 theorem vector_squares_sos {d k : ℕ} {J : Type*} [Fintype J]
    (ℓ : ℕ) (G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (V : J → Fin k → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ j a, (V j a).totalDegree ≤ ℓ)
    (he : ∀ x ∈ sphere d, ∀ a b,
      evalM x G a b = ∑ j, MvPolynomial.eval x (V j a)*MvPolynomial.eval x (V j b)) :
    IsSosOnSphere ℓ G := by
  classical
  by_cases hk : k=0
  · subst k
    exact zero_matrix_size_sos ℓ G
  let : NeZero k := ⟨hk⟩
  let e := (Fintype.equivFin J).symm
  let U : Fin (Fintype.card J) → Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ) :=
    fun j a b => if b=0 then V (e j) a else 0
  refine ⟨Fintype.card J,U,?_,?_⟩
  · intro j a b
    dsimp only [U]
    split_ifs
    · exact hdeg _ _
    · simp
  · intro x hx
    ext a b
    rw [he x hx]
    simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.transpose_apply,evalM,Matrix.map_apply]
    have hu (j : Fin (Fintype.card J)) :
        (∑ z : Fin k, MvPolynomial.eval x (U j a z)*MvPolynomial.eval x (U j b z)) =
          MvPolynomial.eval x (V (e j) a)*MvPolynomial.eval x (V (e j) b) := by
      simp [U,apply_ite]
    simp_rw [hu]
    exact (Fintype.sum_equiv e
      (fun j => MvPolynomial.eval x (V (e j) a)*MvPolynomial.eval x (V (e j) b))
      (fun j => MvPolynomial.eval x (V j a)*MvPolynomial.eval x (V j b))
      (fun _ => rfl)).symm

end SphereSOS.Rate.SSFresh

end
-- END SSProof/VectorSquares.lean

-- BEGIN SSProof/PolynomialGram.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

 theorem polynomial_gram_sos {d k : ℕ} {I : Type*} [Fintype I]
    (ℓ : ℕ) (G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (m : I → MvPolynomial (Fin d) ℝ) (hm : ∀ i, (m i).totalDegree ≤ ℓ)
    (A : Matrix (Fin k × I) (Fin k × I) ℝ) (hA : A.PosSemidef)
    (he : ∀ x ∈ sphere d, ∀ a b, evalM x G a b =
      ∑ i, ∑ j, A (a,i) (b,j)*MvPolynomial.eval x (m i)*MvPolynomial.eval x (m j)) :
    IsSosOnSphere ℓ G := by
  classical
  obtain ⟨B,hB⟩ := real_psd_factor A hA
  let V : (Fin k × I) → Fin k → MvPolynomial (Fin d) ℝ :=
    fun z a => ∑ i, MvPolynomial.C (B (a,i) z)*m i
  apply vector_squares_sos ℓ G V
  · intro z a
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hm i)
  · intro x hx a b
    rw [he x hx]
    simp only [V,MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_C,
      hB,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro z hz
    ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/PolynomialGram.lean

-- BEGIN SSProof/IntegralPsd.lean
section

open scoped BigOperators
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem integral_matrix_psd {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (H : X → Matrix I I ℝ)
    (hI : ∀ i j, Integrable (fun x => H x i j) μ)
    (hH : ∀ x, (H x).PosSemidef) :
    Matrix.PosSemidef (fun i j => ∫ x, H x i j ∂μ) := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    change (∫ x, H x j i ∂μ) = ∫ x, H x i j ∂μ
    apply integral_congr_ae
    filter_upwards [] with x
    have h := (hH x).isHermitian.apply i j
    simpa using h
  · intro v
    have hi (i j : I) : Integrable (fun x => v i*H x i j*v j) μ :=
      ((hI i j).const_mul (v i)).mul_const (v j)
    have he : (∫ x, ∑ i, ∑ j, v i*H x i j*v j ∂μ) =
        ∑ i, ∑ j, v i*(∫ x, H x i j ∂μ)*v j := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i hi'
      rw [integral_finsetSum _ (fun j _ => hi i j)]
      simp only [integral_mul_const,integral_const_mul]
    have hp : 0 ≤ ∫ x, ∑ i, ∑ j, v i*H x i j*v j ∂μ := by
      apply integral_nonneg
      intro x
      change (0 : ℝ) ≤ ∑ i, ∑ j, v i*H x i j*v j
      simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
        Finset.mul_sum,mul_assoc] using (hH x).dotProduct_mulVec_nonneg v
    rw [he] at hp
    simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc] using hp

 theorem weighted_block_psd {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I I ℝ) (hH : H.PosSemidef) (c : J → ℝ) :
    Matrix.PosSemidef (fun a b : I × J => H a.1 b.1*c a.2*c b.2) := by
  classical
  have h := (hH.submatrix Prod.fst).mul_mul_conjTranspose_same
    (Matrix.diagonal (fun a : I×J => c a.2))
  have he : (fun a b : I×J => H a.1 b.1*c a.2*c b.2) =
      Matrix.diagonal (fun a : I×J => c a.2) * H.submatrix Prod.fst Prod.fst *
        (Matrix.diagonal (fun a : I×J => c a.2)).conjTranspose := by
    ext a b
    simp only [Matrix.diagonal_conjTranspose,star_trivial]
    change H a.1 b.1*c a.2*c b.2 =
      (Matrix.diagonal (fun a : I×J => c a.2) * H.submatrix Prod.fst Prod.fst *
        Matrix.diagonal (fun a : I×J => c a.2) : Matrix (I×J) (I×J) ℝ) a b
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    change H a.1 b.1*c a.2*c b.2 = c a.2*H a.1 b.1*c b.2
    ring
  rw [he]
  exact h

end SphereSOS.Rate.SSFresh

end
-- END SSProof/IntegralPsd.lean

-- BEGIN SSProof/IntegralExpansion.lean
section

open scoped BigOperators
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem integral_square_expansion {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (H : X → ℝ) (c : I → X → ℝ) (m : I → ℝ)
    (hi : ∀ i j, Integrable (fun x => H x*c i x*c j x) μ) :
    (∫ x, H x*(∑ i, c i x*m i)^2 ∂μ) =
      ∑ i, ∑ j, (∫ x, H x*c i x*c j x ∂μ)*m i*m j := by
  classical
  have he (x : X) : H x*(∑ i, c i x*m i)^2 =
      ∑ i, ∑ j, (H x*c i x*c j x)*m i*m j := by
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi'
    rw [integral_finsetSum]
    · simp only [integral_mul_const]
    · intro j hj
      exact ((hi i j).mul_const (m i)).mul_const (m j)
  · intro i hi'
    exact integrable_finsetSum _ (fun j _ => ((hi i j).mul_const (m i)).mul_const (m j))

end SphereSOS.Rate.SSFresh

end
-- END SSProof/IntegralExpansion.lean

-- BEGIN SSProof/KernelSos.lean
section

open scoped BigOperators
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem kernel_psd_sos {d k : ℕ} (hd : 0<d) (ℓ : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree≤ℓ) (H : UnitSphere d → Matrix (Fin k) (Fin k) ℝ)
    (hH : ∀ y, (H y).PosSemidef) (hcont : ∀ a b, Continuous (fun y => H y a b))
    (G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (he : ∀ x : UnitSphere d, ∀ a b, evalM (sphereCoords x) G a b =
      ∫ y, kernelWeight q x y*H y a b ∂sphereLaw d) : IsSosOnSphere ℓ G := by
  classical
  let : IsProbabilityMeasure (sphereLaw d) := sphereLaw_probability hd
  let A : Matrix (Fin k × KernelIndex d q) (Fin k × KernelIndex d q) ℝ :=
    fun a b => ∫ y, H y a.1 b.1*kernelCoefficient q a.2 y*kernelCoefficient q b.2 y ∂sphereLaw d
  have hi (a b : Fin k) (i j : KernelIndex d q) :
      Integrable (fun y => H y a b*kernelCoefficient q i y*kernelCoefficient q j y) (sphereLaw d) :=
    (((hcont a b).mul (kernelCoefficient_continuous q i)).mul
      (kernelCoefficient_continuous q j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hA : A.PosSemidef := integral_matrix_psd (I := Fin k × KernelIndex d q) (sphereLaw d)
    (fun y a b => H y a.1 b.1*kernelCoefficient q a.2 y*kernelCoefficient q b.2 y)
    (fun a b => hi a.1 b.1 a.2 b.2)
    (fun y => weighted_block_psd (H y) (hH y) (fun i => kernelCoefficient q i y))
  apply polynomial_gram_sos ℓ G kernelMonomial
    (fun i => (kernelMonomial_degree i).trans hq) A hA
  intro z hz a b
  let x := nativeSpherePoint z hz
  have hx : sphereCoords x=z := rfl
  rw [← hx,he]
  have hh := integral_square_expansion (sphereLaw d) (fun y => H y a b)
    (fun i => kernelCoefficient q i) (fun i => MvPolynomial.eval (sphereCoords x) (kernelMonomial i))
    (hi a b)
  change _ = ∑ i, ∑ j, (∫ y, H y a b*kernelCoefficient q i y*kernelCoefficient q j y ∂sphereLaw d)*
    MvPolynomial.eval (sphereCoords x) (kernelMonomial i)*
    MvPolynomial.eval (sphereCoords x) (kernelMonomial j)
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold kernelWeight
  rw [kernel_expansion]
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelSos.lean

-- BEGIN SSProof/MatrixKernelSos.lean
section

open scoped BigOperators Matrix
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

noncomputable def polynomialRestriction {d : ℕ} (s : ℕ) (p : MvPolynomial (Fin d) ℝ)
    (hp : p.totalDegree ≤ s) : restrictionSpace d s :=
  ⟨sphereEval d p, ⟨⟨p,(MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp⟩,rfl⟩⟩

 theorem matrix_kernel_sos {d k : ℕ} (hd : 0 < d) (s ℓ : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ ℓ) (hP : KernelPreserves (d := d) s q)
    (hn : ∀ x, ∫ y, kernelWeight q x y ∂sphereLaw d=1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hh : δ ≤ 1/2)
    (hE : ∀ f : restrictionSpace d s, ∀ x,
      |kernelValue q f.val x-f.val x| ≤ δ*‖f‖)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (hdeg : ∀ a b, (F a b).totalDegree ≤ s)
    (hF : ∀ x ∈ sphere d, (evalM x F).PosSemidef ∧ (1-evalM x F).PosSemidef) :
    IsSosOnSphere ℓ (F+(2*δ) • (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) := by
  classical
  let : IsProbabilityMeasure (sphereLaw d) := sphereLaw_probability hd
  let V := restrictionSpace d s
  obtain ⟨T,hpreimage,hT⟩ := exists_kernel_inverse hd s q hP δ hδ hh hE
  let A : Fin k → Fin k → V := fun a b => polynomialRestriction s (F a b) (hdeg a b)
  have hA : ∀ x : UnitSphere d,
      Matrix.PosSemidef (Matrix.of (fun a b => (A a b).val x)) ∧
        ((1 : Matrix (Fin k) (Fin k) ℝ)-Matrix.of (fun a b => (A a b).val x)).PosSemidef := by
    intro x
    exact hF (sphereCoords x) (sphereCoords_mem x)
  have hsym : ∀ a b, A a b=A b a := by
    intro a b
    apply Subtype.ext
    ext x
    have he := (hA x).1.isHermitian.apply b a
    simpa using he
  let H : UnitSphere d → Matrix (Fin k) (Fin k) ℝ :=
    fun x => Matrix.of (fun a b => (T (A a b)).val x)+(2*δ) • 1
  apply kernel_psd_sos hd ℓ q hq H
  · intro x
    exact inverse_matrix_psd V T (2*δ) (by positivity) hT A hsym
      (restriction_matrix_bounds V A hA) x
  · intro a b
    change Continuous (fun x => (T (A a b)).val x+(2*δ)*(1 : Matrix (Fin k) (Fin k) ℝ) a b)
    exact (T (A a b)).val.continuous.add continuous_const
  · intro x a b
    have hpre : kernelValue q (T (A a b)).val x=(A a b).val x := hpreimage (A a b) x
    change _ = ∫ y, kernelWeight q x y*((T (A a b)).val y+
      (2*δ)*(1 : Matrix (Fin k) (Fin k) ℝ) a b) ∂sphereLaw d
    simp_rw [mul_add]
    rw [integral_add]
    · rw [integral_mul_const,hn,one_mul]
      rw [show (∫ y, kernelWeight q x y*(T (A a b)).val y ∂sphereLaw d)=
        (A a b).val x from hpre]
      by_cases hab : a=b
      · simp [evalM,A,polynomialRestriction,sphereEval,Matrix.one_apply,hab]
      · simp [evalM,A,polynomialRestriction,sphereEval,hab]
    · exact Continuous.integrable_of_hasCompactSupport
        ((kernelWeight_continuous q x).mul (T (A a b)).val.continuous)
        (HasCompactSupport.of_compactSpace _)
    · exact Continuous.integrable_of_hasCompactSupport
        ((kernelWeight_continuous q x).mul continuous_const)
        (HasCompactSupport.of_compactSpace _)

end SphereSOS.Rate.SSFresh

end
-- END SSProof/MatrixKernelSos.lean

-- BEGIN SSProof/KernelDeficit.lean
section

open scoped RealInnerProductSpace
open MeasureTheory

namespace SphereSOS.Rate.SSFresh

 theorem kernel_deficit_error {d : ℕ} (hd : 0 < d) (s : ℕ) (q : Polynomial ℝ)
    (hn : ∀ x, ∫ y, kernelWeight q x y ∂sphereLaw d=1) (η : ℝ)
    (hη : ∀ x, ∫ y, kernelWeight q x y*(1-⟪x.val,y.val⟫) ∂sphereLaw d ≤ η)
    (f : restrictionSpace d s) (x : UnitSphere d) :
    |kernelValue q f.val x-f.val x| ≤ (reflectionConstant s*η)*‖f‖ := by
  have h := kernel_error hd s q f.val f.property x (hn x)
  calc
    |kernelValue q f.val x-f.val x|  ≤  reflectionConstant s*‖f.val‖*
      (∫ y, kernelWeight q x y*(1-⟪x.val,y.val⟫) ∂sphereLaw d) := h
    _  ≤  reflectionConstant s*‖f.val‖*η :=
      mul_le_mul_of_nonneg_left (hη x)
        (mul_nonneg (reflectionConstant_pos s).le (norm_nonneg _))
    _ = (reflectionConstant s*η)*‖f‖ := by change reflectionConstant s*‖f‖*η=(reflectionConstant s*η)*‖f‖; ring

 theorem kernel_deficit_sos {d k : ℕ} (hd : 0 < d) (s ℓ : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ ℓ) (hP : KernelPreserves (d := d) s q)
    (hn : ∀ x, ∫ y, kernelWeight q x y ∂sphereLaw d=1)
    (η : ℝ) (hη0 : 0 ≤ η) (hh : reflectionConstant s*η ≤ 1/2)
    (hη : ∀ x, ∫ y, kernelWeight q x y*(1-⟪x.val,y.val⟫) ∂sphereLaw d ≤ η)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (hdeg : ∀ a b, (F a b).totalDegree ≤ s)
    (hF : ∀ x ∈ sphere d, (evalM x F).PosSemidef ∧ (1-evalM x F).PosSemidef) :
    IsSosOnSphere ℓ (F+(2*(reflectionConstant s*η)) •
      (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) :=
  matrix_kernel_sos hd s ℓ q hq hP hn (reflectionConstant s*η)
    (mul_nonneg (reflectionConstant_pos s).le hη0) hh
    (kernel_deficit_error hd s q hn η hη) F hdeg hF

end SphereSOS.Rate.SSFresh

end
-- END SSProof/KernelDeficit.lean

-- BEGIN SSProof/ScalarConstants.lean
section

namespace SphereSOS.Rate.SSFresh

noncomputable def sphereApproxConstant (n : ℕ) : ℝ := 1000*reflectionConstant (2*n)
noncomputable def sphereDegreeConstant (n : ℕ) : ℝ := 8+2*sphereApproxConstant n
noncomputable def sphereShiftConstant (n : ℕ) : ℝ := 2*sphereApproxConstant n

 theorem sphereApproxConstant_pos (n : ℕ) : 0 < sphereApproxConstant n :=
  mul_pos (by norm_num) (reflectionConstant_pos _)

 theorem sphereDegreeConstant_ge_eight (n : ℕ) : 8 ≤ sphereDegreeConstant n := by
  unfold sphereDegreeConstant
  linarith [sphereApproxConstant_pos n]

 theorem degree_threshold_guards (n d ℓ : ℕ) (hd : 0 < d)
    (h : sphereDegreeConstant n*(d:ℝ) ≤ (ℓ:ℝ)) :
    8*d ≤ ℓ ∧ 0 < ℓ ∧ sphereApproxConstant n*((d:ℝ)/(ℓ:ℝ))^2 ≤ 1/2 := by
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hC := sphereDegreeConstant_ge_eight n
  have hCpos : 0 < sphereDegreeConstant n := by linarith
  have hA := sphereApproxConstant_pos n
  have h8 : (8:ℝ)*d ≤ ℓ := (mul_le_mul_of_nonneg_right hC hd'.le).trans h
  have hell : 0<(ℓ:ℝ) := lt_of_lt_of_le (by positivity : 0<(8:ℝ)*d) h8
  refine ⟨by exact_mod_cast h8,by exact_mod_cast hell,?_⟩
  have hCsq : 2*sphereApproxConstant n ≤ (sphereDegreeConstant n)^2 := by
    unfold sphereDegreeConstant
    nlinarith
  have hsq : (sphereDegreeConstant n*(d:ℝ))^2 ≤ (ℓ:ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have hmul := mul_le_mul_of_nonneg_right hCsq (sq_nonneg (d:ℝ))
  have hnum : 2*sphereApproxConstant n*(d:ℝ)^2 ≤ (ℓ:ℝ)^2 := by
    nlinarith
  have he : 2*(sphereApproxConstant n*((d:ℝ)/(ℓ:ℝ))^2) ≤ 1 := by
    rw [div_pow,← mul_div_assoc,← mul_div_assoc]
    rw [← mul_assoc]
    apply (div_le_one (sq_pos_of_pos hell)).mpr
    exact hnum
  linarith

end SphereSOS.Rate.SSFresh

end
-- END SSProof/ScalarConstants.lean

-- BEGIN SSProof/OneDimension.lean
section

open scoped BigOperators

namespace SphereSOS.Rate.SSFresh

 theorem one_dimensional_even_eval (n : ℕ) (p : MvPolynomial (Fin 1) ℝ)
    (hp : p.IsHomogeneous (2*n)) (x : Fin 1 → ℝ) (hx : x ∈ sphere 1) :
    MvPolynomial.eval x p=MvPolynomial.eval (fun _ => 1) p := by
  classical
  have hx2 : x 0^2=1 := by simpa [sphere] using hx
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hd := hp.degree_eq_sum_deg_support hz
  have hz0 : z 0=2*n := by
    have he : z.sum (fun _ e => e)=z 0 := by
      rw [Finsupp.sum_fintype]
      · simp
      · simp
    change 2*n=z.sum (fun _ e => e) at hd
    rw [he] at hd
    exact hd.symm
  rw [MvPolynomial.eval_monomial,MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_one,hz0,pow_mul,hx2,one_pow]
  · simp
  · simp

 theorem one_dimensional_sos {k : ℕ} (n ℓ : ℕ)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin 1) ℝ))
    (hdeg : ∀ a b, (F a b).IsHomogeneous (2*n))
    (hF : ∀ x ∈ sphere 1, (evalM x F).PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    IsSosOnSphere ℓ (F+c • (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin 1) ℝ))) := by
  let A := evalM (fun _ : Fin 1 => 1) F+c • (1 : Matrix (Fin k) (Fin k) ℝ)
  have hA : A.PosSemidef := (hF _ (by simp [sphere])).add
    (Matrix.PosSemidef.one.smul hc)
  obtain ⟨m,U,hU,he⟩ := constant_matrix_sos (d := 1) ℓ A hA
  refine ⟨m,U,hU,?_⟩
  intro x hx
  rw [← he x hx]
  ext a b
  have hp := one_dimensional_even_eval n (F a b) (hdeg a b) x hx
  by_cases hab : a=b
  · subst b
    simp [evalM,A,hp]
  · simp [evalM,A,hp,hab]

end SphereSOS.Rate.SSFresh

end
-- END SSProof/OneDimension.lean

-- BEGIN SSProof/NativeConclusion.lean
section

namespace SphereSOS.Rate.SSFresh

theorem native_theorem_2 :
    ∀ n : ℕ, ∃ C C' : ℝ, ∀ (d k ℓ : ℕ)
      (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)),
      n ≤ d →
      (∀ a b, (F a b).IsHomogeneous (2 * n)) →
      (∀ x, (evalM x F).IsSymm) →
      (∀ x ∈ sphere d,
        (evalM x F).PosSemidef ∧ (1 - evalM x F).PosSemidef) →
      C * (d : ℝ) ≤ (ℓ : ℝ) →
      IsSosOnSphere ℓ
        (F + (C' * ((d : ℝ) / (ℓ : ℝ)) ^ 2) •
          (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) := by
  intro n
  refine ⟨sphereDegreeConstant n,sphereShiftConstant n,?_⟩
  intro d k ℓ F _hnd hdeg _hsym hF hell
  rcases d with _ | d
  · exact empty_dimension_sos ℓ _
  rcases d with _ | d
  · exact one_dimensional_sos n ℓ F hdeg (fun x hx => (hF x hx).1) _
      (mul_nonneg (mul_nonneg (by norm_num) (sphereApproxConstant_pos n).le) (sq_nonneg _))
  have hd : 0 < d+2 := by omega
  obtain ⟨h8,_hℓ,hsmall⟩ := degree_threshold_guards n (d+2) ℓ hd hell
  obtain ⟨q,hq,hn,hdef⟩ := exists_localizing_kernel (d+2) ℓ (by omega) h8
  have hsmall' : reflectionConstant (2*n)*(1000*((((d+2:ℕ):ℝ)/(ℓ:ℝ))^2)) ≤ 1/2 := by
    change (1000*reflectionConstant (2*n))*((((d+2:ℕ):ℝ)/(ℓ:ℝ))^2) ≤ 1/2 at hsmall
    nlinarith
  have h := kernel_deficit_sos hd (2*n) ℓ q hq
    (actual_kernel_preserves hd (2*n) q) hn
    (1000*((((d+2:ℕ):ℝ)/(ℓ:ℝ))^2)) (by positivity) hsmall' hdef F
    (fun a b => (hdeg a b).totalDegree_le) hF
  convert h using 1
  congr 2
  unfold sphereShiftConstant sphereApproxConstant
  ring

end SphereSOS.Rate.SSFresh

end
-- END SSProof/NativeConclusion.lean

-- BEGIN Canonical.lean
section

namespace SphereSOS.Rate

theorem theorem_2 :
    ∀ n : ℕ, ∃ C C' : ℝ, ∀ (d k ℓ : ℕ)
      (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)),
      n ≤ d →
      (∀ a b, (F a b).IsHomogeneous (2 * n)) →
      (∀ x, (evalM x F).IsSymm) →
      (∀ x ∈ sphere d,
        (evalM x F).PosSemidef ∧ (1 - evalM x F).PosSemidef) →
      C * (d : ℝ) ≤ (ℓ : ℝ) →
      IsSosOnSphere ℓ
        (F + (C' * ((d : ℝ) / (ℓ : ℝ)) ^ 2) •
          (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)))  := SSFresh.native_theorem_2

end SphereSOS.Rate

end
-- END Canonical.lean

open SphereSOS.Rate

theorem solution :
    ∀ n : ℕ, ∃ C C' : ℝ, ∀ (d k ℓ : ℕ)
      (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ)),
      n ≤ d →
      (∀ a b, (F a b).IsHomogeneous (2 * n)) →
      (∀ x, (evalM x F).IsSymm) →
      (∀ x ∈ sphere d,
        (evalM x F).PosSemidef ∧ (1 - evalM x F).PosSemidef) →
      C * (d : ℝ) ≤ (ℓ : ℝ) →
      IsSosOnSphere ℓ
        (F + (C' * ((d : ℝ) / (ℓ : ℝ)) ^ 2) •
          (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) := by
  exact SphereSOS.Rate.theorem_2
