-- Prove2me | solution 1 for PolyhedralSOC.LowerBound.polyhedral_approx_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T05:50:22.608337+00:00
-- url     : https://prove2.me/submissions/17fef109-e16c-45b0-91e4-3264d18cd229

-- Complete checked reconstruction of the full native polyhedral SOC approximation lower-bound theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Mathlib


-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin NativeEuclidean
section ModuleScope_NativeEuclidean

namespace PolyhedralSOC.LowerBound.Proof

noncomputable def euclideanEquiv (k : ℕ) : (Fin k → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm

 theorem norm_euclideanEquiv {k : ℕ} (y : Fin k → ℝ) :
    ‖euclideanEquiv k y‖ = Shared.eucNorm y := by
  simp [euclideanEquiv, EuclideanSpace.norm_eq, Shared.eucNorm, Real.norm_eq_abs, sq_abs]

 theorem euclidean_hull {k N : ℕ} (v : Fin N → (Fin k → ℝ))
    (h : ∀ y, Shared.eucNorm y ≤ 1 → y ∈ convexHull ℝ (Set.range v)) :
    ∀ y : EuclideanSpace ℝ (Fin k), ‖y‖ ≤ 1 →
      y ∈ convexHull ℝ (Set.range (fun i => euclideanEquiv k (v i))) := by
  intro y hy
  have hn : Shared.eucNorm ((euclideanEquiv k).symm y) ≤ 1 := by
    simpa only [← norm_euclideanEquiv, LinearEquiv.apply_symm_apply] using hy
  have hh := Set.mem_image_of_mem (euclideanEquiv k) (h _ hn)
  change (euclideanEquiv k).toLinearMap ((euclideanEquiv k).symm y) ∈ (euclideanEquiv k).toLinearMap '' convexHull ℝ (Set.range v) at hh
  rw [(euclideanEquiv k).toLinearMap.image_convexHull] at hh
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← Set.range_comp,Function.comp_def] using hh

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_NativeEuclidean
-- End NativeEuclidean

-- Begin SphereCover
section ModuleScope_SphereCover

open scoped RealInnerProductSpace
namespace PolyhedralSOC.LowerBound.Proof

 theorem sphere_cover {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (v : Fin N → E) {eps : ℝ} (heps : 0 < eps)
    (hinner : ∀ x : E, ‖x‖ ≤ 1 → x ∈ convexHull ℝ (Set.range v))
    (houter : ∀ i, ‖v i‖ ≤ 1+eps) (y : E) (hy : ‖y‖ = 1+eps) :
    ∃ i, ‖y-v i‖ ≤ Real.sqrt (2*eps*(1+eps)) := by
  have hR : 0 < 1+eps := by linarith
  have hunit : ‖((1+eps)⁻¹:ℝ) • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),hy,inv_mul_cancel₀ hR.ne']
  have hx := hinner _ hunit
  have hex : ∃ i, 1+eps ≤ ⟪y,v i⟫ := by
    by_contra hn
    push Not at hn
    have hc : Convex ℝ {x : E | ⟪y,x⟫ < 1+eps} :=
      convex_halfSpace_lt (innerSL ℝ y).toLinearMap.isLinear _
    have hs : Set.range v ⊆ {x : E | ⟪y,x⟫ < 1+eps} := by
      rintro _ ⟨i,rfl⟩
      exact hn i
    have hh := convexHull_min hs hc hx
    simp only [Set.mem_ofPred_eq,inner_smul_right,real_inner_self_eq_norm_sq,hy] at hh
    have hid : (1+eps)⁻¹*(1+eps)^2 = 1+eps := by field_simp
    rw [hid] at hh
    exact lt_irrefl _ hh
  obtain ⟨i,hi⟩ := hex
  refine ⟨i,?_⟩
  have hv0 := norm_nonneg (v i)
  have hv := houter i
  have hs : ‖y-v i‖^2 ≤ 2*eps*(1+eps) := by
    rw [norm_sub_sq_real,hy]
    nlinarith
  have hr : 0 ≤ 2*eps*(1+eps) := by positivity
  nlinarith [Real.sq_sqrt hr,Real.sqrt_nonneg (2*eps*(1+eps)),norm_nonneg (y-v i)]

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_SphereCover
-- End SphereCover

-- Begin SphereProjection
section ModuleScope_SphereProjection

open scoped BigOperators
namespace PolyhedralSOC.LowerBound.Proof

noncomputable def tailProjection {d : ℕ} (x : EuclideanSpace ℝ (Fin (d+1))) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => x i.succ)

 theorem tailProjection_norm_le {d : ℕ} (x : EuclideanSpace ℝ (Fin (d+1))) :
    ‖tailProjection x‖ ≤ ‖x‖ := by
  have he : ‖x‖^2 = (x 0)^2+‖tailProjection x‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,tailProjection]
  nlinarith [sq_nonneg (x 0),norm_nonneg x,norm_nonneg (tailProjection x)]

 theorem tailProjection_sub {d : ℕ} (x y : EuclideanSpace ℝ (Fin (d+1))) :
    tailProjection (x-y)=tailProjection x-tailProjection y := by
  ext i
  rfl

 theorem exists_sphere_lift {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {R : ℝ}
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    ∃ y : EuclideanSpace ℝ (Fin (d+1)), ‖y‖=R ∧ tailProjection y=x := by
  let a := Real.sqrt (R^2-‖x‖^2)
  let y : EuclideanSpace ℝ (Fin (d+1)) := WithLp.toLp 2 (Fin.cons a (fun i => x i))
  have hp : 0 ≤ R^2-‖x‖^2 := by nlinarith [norm_nonneg x]
  have he : ‖y‖^2=R^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, y,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [← EuclideanSpace.real_norm_sq_eq,Real.sq_sqrt hp]
    ring
  refine ⟨y,?_,?_⟩
  · nlinarith [norm_nonneg y]
  · ext i
    rfl

 theorem projected_ball_cover {d N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin (d+1)))
    {R r : ℝ} (hR : 0 ≤ R)
    (hcover : ∀ y, ‖y‖=R → ∃ i, ‖y-v i‖≤r) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ⊆
      ⋃ i, Metric.closedBall (tailProjection (v i)) r := by
  intro x hx
  have hn : ‖x‖≤R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  obtain ⟨y,hy,ht⟩ := exists_sphere_lift x hR hn
  obtain ⟨i,hi⟩ := hcover y hy
  apply Set.mem_iUnion.2
  refine ⟨i,?_⟩
  rw [Metric.mem_closedBall,dist_eq_norm,← ht,← tailProjection_sub]
  exact (tailProjection_norm_le (y-v i)).trans hi

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_SphereProjection
-- End SphereProjection

-- Begin BallVolume
section ModuleScope_BallVolume

open MeasureTheory MeasureTheory.Measure Metric
open scoped BigOperators
namespace PolyhedralSOC.LowerBound.Proof

 theorem ball_cover_volume {d N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin d))
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hc : closedBall (0 : EuclideanSpace ℝ (Fin d)) R ⊆ ⋃ i, closedBall (v i) r) :
    R^d ≤ (N:ℝ)*r^d := by
  let E := EuclideanSpace ℝ (Fin d)
  have hfin : volume (⋃ i, closedBall (v i) r) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_iUnion_le _)
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 (fun i _ => measure_closedBall_lt_top)
  have hm := (measureReal_mono hc hfin).trans (measureReal_iUnion_fintype_le (μ:=volume) (fun i => closedBall (v i) r))
  simp only [Measure.addHaar_real_closedBall' volume _ hR,Measure.addHaar_real_closedBall' volume _ hr,finrank_euclideanSpace, Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hm
  have hu : 0 < volume.real (closedBall (0:E) 1) := by
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne' measure_closedBall_lt_top.ne
  nlinarith

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_BallVolume
-- End BallVolume

-- Begin LogarithmicBound
section ModuleScope_LogarithmicBound

namespace PolyhedralSOC.LowerBound.Proof

 theorem radius_log_bound {eps : ℝ} (heps : 0 < eps) :
    Real.log (1/eps)/4 ≤ Real.log (1+eps)-Real.log (Real.sqrt (2*eps*(1+eps))) := by
  have hR : 0 < 1+eps := by linarith
  have hp : 0 < 2*eps*(1+eps) := by positivity
  have hbase : 4*eps ≤ (1+eps)^2 := by nlinarith [sq_nonneg (1-eps)]
  have hlog := Real.log_le_log (by positivity : 0 < 4*eps) hbase
  rw [Real.log_mul (by norm_num) heps.ne',Real.log_pow] at hlog
  have h4 : Real.log 4=2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  rw [h4] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  rw [Real.log_sqrt hp.le,Real.log_mul (mul_ne_zero (by norm_num) heps.ne') hR.ne',Real.log_mul (by norm_num) heps.ne',Real.log_div one_ne_zero heps.ne',Real.log_one]
  linarith

 theorem logarithmic_size_bound {d N q : ℕ} (hd : 1 ≤ d) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1/2)
    (hN : N ≤ 2^q)
    (hv : (1+eps)^d ≤ (N:ℝ)*(Real.sqrt (2*eps*(1+eps)))^d) :
    (1/8:ℝ)*(d+1)*Real.log (1/eps) ≤ q := by
  have hR : 0 < 1+eps := by linarith
  have hr : 0 < Real.sqrt (2*eps*(1+eps)) := Real.sqrt_pos.2 (by positivity)
  have hNp : 0 < (N:ℝ) := by
    by_contra h
    have hz : (N:ℝ)=0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz,zero_mul] at hv
    exact (not_le_of_gt (pow_pos hR d)) hv
  have hl := Real.log_le_log (pow_pos hR d) hv
  rw [Real.log_mul hNp.ne' (pow_ne_zero _ hr.ne'),Real.log_pow,Real.log_pow] at hl
  have hncast : (N:ℝ) ≤ (2:ℝ)^q := by exact_mod_cast hN
  have hnlog := Real.log_le_log hNp hncast
  rw [Real.log_pow] at hnlog
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    linarith
  have hq := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg q : (0:ℝ)≤q)
  have hrad := mul_le_mul_of_nonneg_left (radius_log_bound heps) (Nat.cast_nonneg d : (0:ℝ)≤d)
  have hL : 0 ≤ Real.log (1/eps) := Real.log_nonneg ((one_le_div heps).2 (by linarith))
  have hdreal : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdim := mul_nonneg (by linarith : (0:ℝ)≤(d:ℝ)-1) hL
  nlinarith

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_LogarithmicBound
-- End LogarithmicBound

-- Begin FiniteHullBound
section ModuleScope_FiniteHullBound

namespace PolyhedralSOC.LowerBound.Proof

 theorem finite_hull_size_lower_bound {k N q : ℕ} (hk : 2 ≤ k) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1/2)
    (v : Fin N → (Fin k → ℝ)) (hN : N ≤ 2^q)
    (hinner : ∀ y, Shared.eucNorm y ≤ 1 → y ∈ convexHull ℝ (Set.range v))
    (houter : ∀ i, Shared.eucNorm (v i) ≤ 1+eps) :
    (1/8:ℝ)*k*Real.log (1/eps) ≤ q := by
  obtain ⟨d,rfl⟩ : ∃ d, k=d+1 := ⟨k-1,by omega⟩
  let w : Fin N → EuclideanSpace ℝ (Fin (d+1)) := fun i => euclideanEquiv (d+1) (v i)
  have hi : ∀ y : EuclideanSpace ℝ (Fin (d+1)), ‖y‖≤1 → y∈convexHull ℝ (Set.range w) :=
    euclidean_hull v hinner
  have ho : ∀ i, ‖w i‖≤1+eps := by
    intro i
    simpa only [w,norm_euclideanEquiv] using houter i
  have hc := projected_ball_cover w (by linarith : 0≤1+eps)
    (fun y hy => sphere_cover w heps hi ho y hy)
  have hv := ball_cover_volume (fun i => tailProjection (w i))
    (by linarith : 0≤1+eps) (Real.sqrt_nonneg _) hc
  have hh := logarithmic_size_bound (by omega : 1≤d) heps heps1 hN hv
  simpa only [Nat.cast_add,Nat.cast_one] using hh

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_FiniteHullBound
-- End FiniteHullBound

-- Begin SlackSection
section ModuleScope_SlackSection

open Finset
namespace PolyhedralSOC.LowerBound.Proof

 def slackSection {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) : Set (Fin q → ℝ) :=
  (L : Set (Fin q → ℝ)) ∩ stdSimplex ℝ (Fin q)

 theorem slack_mem {q : ℕ} {L : Submodule ℝ (Fin q → ℝ)} {a : Fin q → ℝ} :
    a ∈ slackSection L ↔ a ∈ L ∧ (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 := by
  rfl

 theorem slack_compact {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    IsCompact (slackSection L) := by
  exact (isCompact_stdSimplex ℝ (Fin q)).inter_left L.closed_of_finiteDimensional

 theorem slack_convex {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    Convex ℝ (slackSection L) := L.convex.inter (convex_stdSimplex ℝ (Fin q))

 theorem slack_support_eq {q : ℕ} {L : Submodule ℝ (Fin q → ℝ)}
    {a b : Fin q → ℝ} (ha : a ∈ (slackSection L).extremePoints ℝ)
    (hb : b ∈ slackSection L) (hs : ∀ i, a i = 0 ↔ b i = 0) : b = a := by
  classical
  obtain ⟨haL, ha0, ha1⟩ := ha.1
  obtain ⟨hbL, hb0, hb1⟩ := hb
  let C : ℝ := ∑ i, b i / a i
  have hC : 0 ≤ C := sum_nonneg fun i _ => div_nonneg (hb0 i) (ha0 i)
  let d : ℝ := 1 / (2 + C)
  have hd : 0 < d := one_div_pos.mpr (by linarith)
  have hd1 : d < 1 := (div_lt_one (by linarith : 0 < 2 + C)).mpr (by linarith)
  have hda : ∀ i, d * b i ≤ a i := by
    intro i
    by_cases hi : a i = 0
    · simp [hi, (hs i).mp hi]
    · have hai : 0 < a i := lt_of_le_of_ne (ha0 i) (Ne.symm hi)
      have hr : b i / a i ≤ C := single_le_sum (fun j _ => div_nonneg (hb0 j) (ha0 j)) (mem_univ i)
      have hbi : b i ≤ C * a i := (div_le_iff₀ hai).mp hr
      have hdC : d * C ≤ 1 := by
        dsimp [d]
        rw [one_div_mul_eq_div]
        exact (div_le_one (by linarith : 0 < 2 + C)).mpr (by linarith)
      nlinarith
  let c : Fin q → ℝ := (1 - d)⁻¹ • (a - d • b)
  have hc : c ∈ slackSection L := by
    refine ⟨L.smul_mem _ (L.sub_mem haL (L.smul_mem _ hbL)), ?_, ?_⟩
    · intro i
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (sub_nonneg.mpr (hda i))
    · change ∑ i, (1 - d)⁻¹ * (a i - d * b i) = 1
      rw [← mul_sum, sum_sub_distrib, ← mul_sum, ha1, hb1, mul_one]
      exact inv_mul_cancel₀ (by linarith)
  apply ha.2 ⟨hbL, hb0, hb1⟩ hc
  rw [openSegment_eq_image]
  refine ⟨1 - d, ⟨by linarith, by linarith⟩, ?_⟩
  ext i
  simp only [c, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [show 1 - d ≠ 0 by linarith]
  ring

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_SlackSection
-- End SlackSection

-- Begin SlackHull
section ModuleScope_SlackHull

open Finset
namespace PolyhedralSOC.LowerBound.Proof

noncomputable def slackSupport {q : ℕ} (a : Fin q → ℝ) : Finset (Fin q) :=
  univ.filter fun i => a i ≠ 0

 theorem extreme_support_injective {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    Function.Injective (fun a : (slackSection L).extremePoints ℝ => slackSupport a.val) := by
  intro a b h
  apply Subtype.ext
  apply (slack_support_eq a.property b.property.1 _).symm
  intro i
  have hi := congrArg (fun s : Finset (Fin q) => i ∈ s) h
  simpa only [slackSupport, mem_filter, mem_univ, true_and, not_iff_not] using (iff_of_eq hi)

 theorem slack_extreme_finite {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    ((slackSection L).extremePoints ℝ).Finite := by
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (extreme_support_injective L))

 theorem slack_hull {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    convexHull ℝ ((slackSection L).extremePoints ℝ) = slackSection L := by
  have hc := closure_convexHull_extremePoints (slack_compact L) (slack_convex L)
  have hf : IsClosed (convexHull ℝ ((slackSection L).extremePoints ℝ)) :=
    (slack_extreme_finite L).isCompact_convexHull (𝕜 := ℝ) |>.isClosed
  rwa [hf.closure_eq] at hc

 theorem slack_generators {q : ℕ} (L : Submodule ℝ (Fin q → ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → (Fin q → ℝ), N ≤ 2^q ∧
      (∀ i, v i ∈ slackSection L) ∧ slackSection L = convexHull ℝ (Set.range v) := by
  classical
  let T := (slackSection L).extremePoints ℝ
  let : Fintype T := (slack_extreme_finite L).fintype
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun i => (e i).val, ?_, fun i => (e i).property.1, ?_⟩
  · have h := Fintype.card_le_of_injective _ (extreme_support_injective L)
    simpa only [Fintype.card_finset, Fintype.card_fin] using h
  · have hr : Set.range (fun i => (e i).val) = T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    rw [hr]
    exact (slack_hull L).symm

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_SlackHull
-- End SlackHull

-- Begin KernelProjection
section ModuleScope_KernelProjection

namespace PolyhedralSOC.LowerBound.Proof

 theorem native_norm_nonneg {k : ℕ} (y : Fin k → ℝ) : 0 ≤ Shared.eucNorm y :=
  Real.sqrt_nonneg _

 theorem native_norm_zero {k : ℕ} {y : Fin k → ℝ} (h : Shared.eucNorm y = 0) : y = 0 := by
  apply (euclideanEquiv k).injective
  simpa only [map_zero] using norm_eq_zero.mp (by simpa only [norm_euclideanEquiv] using h)

 theorem native_norm_smul {k : ℕ} (a : ℝ) (y : Fin k → ℝ) :
    Shared.eucNorm (a • y) = |a| * Shared.eucNorm y := by
  rw [← norm_euclideanEquiv, map_smul, norm_smul, Real.norm_eq_abs, norm_euclideanEquiv]

 theorem kernel_projection {k p q : ℕ} {eps : ℝ} (heps : 0 < eps)
    {P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)}
    (hP : Shared.IsPolyhedralApprox k p q eps P)
    {z : (Fin k → ℝ) × ℝ × (Fin p → ℝ)} (hz : P z = 0) :
    z.1 = 0 ∧ z.2.1 = 0 := by
  have h1 := hP.2 z.1 z.2.1 z.2.2 (by simpa only [Prod.mk.eta, hz] using (le_refl (0 : Fin q → ℝ)))
  have h2 := hP.2 (-z.1) (-z.2.1) (-z.2.2) (by
    change 0 ≤ P (-z)
    rw [map_neg, hz, neg_zero])
  have hn := native_norm_nonneg z.1
  have hn' := native_norm_nonneg (-z.1)
  have ht : z.2.1 = 0 := by nlinarith
  refine ⟨native_norm_zero (by nlinarith), ht⟩

 theorem equal_slack_projection {k p q : ℕ} {eps : ℝ} (heps : 0 < eps)
    {P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)}
    (hP : Shared.IsPolyhedralApprox k p q eps P)
    {z w : (Fin k → ℝ) × ℝ × (Fin p → ℝ)} (h : P z = P w) :
    z.1 = w.1 ∧ z.2.1 = w.2.1 := by
  have hh := kernel_projection heps hP (z := z - w) (by rw [map_sub, h, sub_self])
  exact ⟨sub_eq_zero.mp hh.1, sub_eq_zero.mp hh.2⟩

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_KernelProjection
-- End KernelProjection

-- Begin SliceGenerators
section ModuleScope_SliceGenerators

open Finset
namespace PolyhedralSOC.LowerBound.Proof

 theorem exists_slice_generators {k p q : ℕ} {eps : ℝ}
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (heps : 0 < eps) (hP : Shared.IsPolyhedralApprox k p q eps P) :
    ∃ N : ℕ, ∃ v : Fin N → (Fin k → ℝ), N ≤ 2^q ∧
      (∀ y, Shared.eucNorm y ≤ 1 → y ∈ convexHull ℝ (Set.range v)) ∧
      (∀ i, Shared.eucNorm (v i) ≤ 1 + eps) := by
  classical
  obtain ⟨N, s, hN, hs, hHull⟩ := slack_generators P.range
  have hsP : ∀ i, ∃ z, P z = s i := fun i => (hs i).1
  choose z hz using hsP
  have hpos : ∀ i, 0 ≤ P (z i) := fun i => by rw [hz]; exact (hs i).2.1
  have hnorm : ∀ i, Shared.eucNorm (z i).1 ≤ (1 + eps) * (z i).2.1 :=
    fun i => hP.2 _ _ _ (hpos i)
  have ht : ∀ i, 0 ≤ (z i).2.1 := fun i => by
    have := hnorm i
    have := native_norm_nonneg (z i).1
    nlinarith
  have ht0 : ∀ i, (z i).2.1 = 0 → (z i).1 = 0 := by
    intro i hi
    apply native_norm_zero
    have hh := hnorm i
    rw [hi, mul_zero] at hh
    exact le_antisymm hh (native_norm_nonneg _)
  let v : Fin N → (Fin k → ℝ) := fun i => ((z i).2.1)⁻¹ • (z i).1
  have hv : ∀ i, Shared.eucNorm (v i) ≤ 1 + eps := by
    intro i
    by_cases hi : (z i).2.1 = 0
    · simp only [v, hi, inv_zero, zero_smul, Shared.eucNorm, Pi.zero_apply, sq, zero_mul,
        sum_const_zero, Real.sqrt_zero]
      linarith
    · have hi' : 0 < (z i).2.1 := lt_of_le_of_ne (ht i) (Ne.symm hi)
      change Shared.eucNorm (((z i).2.1)⁻¹ • (z i).1) ≤ 1 + eps
      rw [native_norm_smul, abs_of_pos (inv_pos.mpr hi')]
      calc
        (z i).2.1⁻¹ * Shared.eucNorm (z i).1 ≤
          (z i).2.1⁻¹ * ((1 + eps) * (z i).2.1) := mul_le_mul_of_nonneg_left (hnorm i) (inv_nonneg.mpr (ht i))
        _ = 1 + eps := by field_simp
  have htv : ∀ i, (z i).2.1 • v i = (z i).1 := by
    intro i
    by_cases hi : (z i).2.1 = 0
    · simp [hi, ht0 i hi]
    · simp [v, smul_smul, hi]
  refine ⟨N, v, hN, ?_, hv⟩
  intro y hy
  obtain ⟨u, hu⟩ := hP.1 y 1 hy
  let a : ℝ := ∑ i, P (y, 1, u) i
  have ha0 : 0 ≤ a := sum_nonneg fun i _ => hu i
  have ha : 0 < a := by
    by_contra hn
    have ha' : a = 0 := le_antisymm (not_lt.mp hn) ha0
    have hz0 : P (y, 1, u) = 0 := by
      ext i
      exact (sum_eq_zero_iff_of_nonneg (fun j _ => hu j)).mp ha' i (mem_univ i)
    have hh := (kernel_projection heps hP hz0).2
    norm_num at hh
  have hb : a⁻¹ • P (y, 1, u) ∈ slackSection P.range := by
    refine ⟨P.range.smul_mem _ ⟨(y, 1, u), rfl⟩, ?_, ?_⟩
    · intro i
      exact mul_nonneg (inv_nonneg.mpr ha.le) (hu i)
    · change ∑ i, a⁻¹ * P (y, 1, u) i = 1
      rw [← mul_sum]
      exact inv_mul_cancel₀ ha.ne'
  rw [hHull] at hb
  obtain ⟨I, hI, w, b, hw, hw1, hbmem, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hb
  have hbidx : ∀ i, ∃ j, s j = b i := hbmem
  choose j hj using hbidx
  let Z := ∑ i, (a * w i) • z (j i)
  have hZ : P Z = P (y, 1, u) := by
    rw [show Z = ∑ i, (a * w i) • z (j i) from rfl, map_sum]
    simp_rw [map_smul, hz, hj, mul_smul]
    rw [← smul_sum, hsum, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hproj := equal_slack_projection heps hP hZ
  have htime : ∑ i, a * w i * (z (j i)).2.1 = 1 := by
    simpa only [Z, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, smul_eq_mul] using hproj.2
  have hyrep : ∑ i, (a * w i * (z (j i)).2.1) • v (j i) = y := by
    simp_rw [mul_smul, htv]
    simpa only [Z, Prod.fst_sum, Prod.smul_fst, mul_smul] using hproj.1
  exact mem_convexHull_of_exists_fintype (fun i => a * w i * (z (j i)).2.1)
    (fun i => v (j i)) (fun i => mul_nonneg (mul_nonneg ha.le (hw i)) (ht _))
    htime (fun i => Set.mem_range_self _) hyrep

end PolyhedralSOC.LowerBound.Proof
end ModuleScope_SliceGenerators
-- End SliceGenerators

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, Eq. (13), p. 202 (PDF p. 10):
there is a positive absolute constant `c` such that, for every `k ≥ 2`, every `ε ∈ (0, 0.5]` and
every polyhedral `ε`-approximation `Π(y, t, u) : ℝ^k × ℝ × ℝ^p → ℝ^q` of the Lorentz cone `L^k`,
`q ≥ c k ln(1/ε)`.
**Correction:** the paper states this for every positive integer `k`; for `k = 1` it is false,
because `L^1 = {(y, t) | |y| ≤ t}` is polyhedral and `Π(y, t) = (t − y, t + y)` (`p = 0`, `q = 2`)
is a polyhedral `ε`-approximation for every `ε > 0`. The result is stated for `k ≥ 2`. -/
theorem polyhedral_approx_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (p q : ℕ) (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
        Shared.IsPolyhedralApprox k p q ε P → c * k * Real.log (1 / ε) ≤ q := by
  refine ⟨1/8,by norm_num,?_⟩
  intro k hk eps heps heps1 p q P hP
  obtain ⟨N,v,hN,hi,ho⟩ := Proof.exists_slice_generators P heps hP
  exact Proof.finite_hull_size_lower_bound hk heps heps1 v hN hi ho

end PolyhedralSOC.LowerBound
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (p q : ℕ) (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
        PolyhedralSOC.Shared.IsPolyhedralApprox k p q ε P → c * k * Real.log (1 / ε) ≤ q := PolyhedralSOC.LowerBound.polyhedral_approx_lower_bound
end ModuleScope_Solution
-- End Solution
