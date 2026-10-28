-- Prove2me | solution 1 for SAGFiniteSum.Rate.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T06:46:43.227705+00:00
-- url     : https://prove2.me/submissions/f91459af-f7a0-4982-b090-064c9051084a

/- SPDX-License-Identifier: Apache-2.0 -/
import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGFiniteSum_Rate_Model


-- Complete module: SAGProof.ScalarCoefficients

namespace SAGFiniteSum.Rate.SAGFresh

noncomputable def sa1 (t : ℝ) : ℝ := t * (1 - t / 2) / 32
noncomputable def sa2 (t : ℝ) : ℝ := t * (1 - t / 2) / 16
noncomputable def sb (t : ℝ) : ℝ := -t * (1 - t) / 4
noncomputable def sc (t : ℝ) : ℝ := 4 * t
noncomputable def sd (t : ℝ) : ℝ := t / 16
noncomputable def sh (t : ℝ) : ℝ := 1 / 2 - t
noncomputable def coefA (t : ℝ) : ℝ := sa1 t - 2 * sd t * sb t + (sd t) ^ 2 * sc t
noncomputable def coefB0 (t μ : ℝ) : ℝ := 2 * (μ / 16) * sh t
noncomputable def coefB1 (t : ℝ) : ℝ := 2 * (sb t - sd t * sc t)
noncomputable def coefB2 (_t : ℝ) : ℝ := 0
noncomputable def coefB3 (t μ : ℝ) : ℝ := -((μ / 16 - t) * sa2 t + t * coefA t)
/-- Smaller than the coefficient retaining the favorable strong-convexity term. -/
noncomputable def coefB4 (t μ : ℝ) : ℝ :=
  coefB3 t μ - ((1 - 2 * t) * coefA t - (1 - μ / 16) * sa1 t) / t
noncomputable def coefB5 (t μ : ℝ) : ℝ :=
  2 * ((μ / 16 - t) * sb t - sd t * (1 - t) * sc t)
noncomputable def coefB6 (t : ℝ) : ℝ := -2 * t * coefA t
noncomputable def coefB7 (t μ : ℝ) : ℝ := 2 * coefA t - 2 * sh t * (1 - μ / 16) * sd t
noncomputable def coefB8 (t : ℝ) : ℝ := t * (coefA t + sa2 t)
noncomputable def coefB9 (t μ : ℝ) : ℝ := sc t * (μ / 16)
noncomputable def coefC0 (t μ : ℝ) : ℝ :=
  -coefB0 t μ * μ / 2 + coefB9 t μ + (coefB5 t μ) ^ 2 / (4 * t * coefB4 t μ)
noncomputable def coefC1 (t μ : ℝ) : ℝ :=
  coefB0 t μ + coefB1 t + (coefB6 t) ^ 2 / (4 * t * coefB3 t μ) +
    coefB5 t μ * (coefB6 t + coefB7 t μ) / (2 * t * coefB4 t μ) + coefB8 t / t
noncomputable def coefC2 (t μ : ℝ) : ℝ :=
  -(coefB6 t) ^ 2 / (4 * t * coefB3 t μ) +
    (coefB6 t + coefB7 t μ) ^ 2 / (4 * t * coefB4 t μ)

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.TableAlgebra
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [InnerProductSpace ℝ E] in
lemma sum_refresh (u : ι → E) (i : ι) (v : E) :
    (∑ j, Function.update u i v j) = (∑ j, u j)-u i+v := by
  have he : Function.update u i v = fun j => u j + if j=i then v-u i else 0 := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]
  rw [he, Finset.sum_add_distrib]
  simp
  abel

omit [InnerProductSpace ℝ E] in
lemma sum_refresh_sq (u : ι → E) (i : ι) (v : E) :
    (∑ j, ‖Function.update u i v j‖^2) = (∑ j, ‖u j‖^2)-‖u i‖^2+‖v‖^2 := by
  have he : (fun j => ‖Function.update u i v j‖^2) = Function.update (fun j => ‖u j‖^2) i (‖v‖^2) := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  rw [he]
  exact sum_refresh (fun j => ‖u j‖^2) i (‖v‖^2)

lemma refresh_sum_square (S u v : E) :
    ‖S-u+v‖^2 = ‖S‖^2+‖u‖^2+‖v‖^2-2*⟪S,u⟫+2*⟪S,v⟫-2*⟪u,v⟫ := by
  rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_left]
  ring

omit [DecidableEq ι] in
lemma sum_refresh_sum_square (u v : ι → E) :
    (∑ i, ‖(∑ j, u j)-u i+v i‖^2) =
      ((Fintype.card ι:ℝ)-2)*‖∑ j,u j‖^2 + (∑ i,‖u i‖^2)+
        (∑ i,‖v i‖^2)+2*⟪∑ j,u j,∑ i,v i⟫-2*(∑ i,⟪u i,v i⟫) := by
  simp_rw [refresh_sum_square]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,← inner_sum]
  rw [real_inner_self_eq_norm_sq]
  ring
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.Potential
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def potential {n : ℕ} (t : ℝ) (G : E → ℝ) (xstar : E)
    (u : Fin n → E) (x : E) : ℝ :=
  2*sh t*(G (x+sd t • ∑ i,u i)-G xstar) +
    sa1 t*‖∑ i,u i‖^2+sa2 t*(∑ i,‖u i‖^2)+
    2*sb t*⟪∑ i,u i,x-xstar⟫+sc t*‖x-xstar‖^2

lemma shifted_refresh {n : ℕ} (d : ℝ) (u v : Fin n → E) (x : E) (i : Fin n) :
    (x-d • ∑ j, Function.update u i (v i) j)+
      d • ∑ j, Function.update u i (v i) j = x := by abel

lemma potential_refresh {n : ℕ} (t : ℝ) (G : E → ℝ) (xstar x : E)
    (u v : Fin n → E) (i : Fin n) :
    potential t G xstar (Function.update u i (v i))
      (x-sd t • ∑ j,Function.update u i (v i) j) =
    2*sh t*(G x-G xstar)+
      coefA t*‖(∑ j,u j)-u i+v i‖^2+
      sa2 t*((∑ j,‖u j‖^2)-‖u i‖^2+‖v i‖^2)+
      2*(sb t-sd t*sc t)*⟪(∑ j,u j)-u i+v i,x-xstar⟫+
      sc t*‖x-xstar‖^2 := by
  unfold potential
  rw [shifted_refresh, sum_refresh, sum_refresh_sq]
  have he : x-sd t • ((∑ j,u j)-u i+v i)-xstar =
      (x-xstar)-sd t • ((∑ j,u j)-u i+v i) := by module
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_smul_right, real_inner_comm (x-xstar)]
  unfold coefA
  ring
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.SmoothFirstOrder

namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_line_deriv {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪g (x+t • v),v⟫ t := by
  have hp : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hg _).hasFDerivAt.comp_hasDerivAt t hp

omit [CompleteSpace E] in
lemma convex_line {f : E → ℝ} (hf : ConvexOn ℝ univ f) (x v : E) :
    ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
  refine ⟨convex_univ,?_⟩
  intro s _ t _ a b ha hb hab
  have he : x+(a*s+b*t) • v = a • (x+s • v)+b • (x+t • v) := by
    calc
      _ = (a+b) • x + (a*s+b*t) • v := by rw [hab,one_smul]
      _ = _ := by module
  change f (x+(a*s+b*t) • v) ≤ a * f (x+s • v) + b * f (x+t • v)
  rw [he]
  exact hf.2 (mem_univ _) (mem_univ _) ha hb hab

lemma convex_gradient_lower {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    f x + ⟪g x,y-x⟫ ≤ f y := by
  have hd := gradient_line_deriv hg x (y-x) 0
  have hc := (convex_line hf x (y-x)).le_slope_of_hasDerivAt
    (mem_univ 0) (mem_univ 1) (by norm_num : (0:ℝ)<1) hd
  simp only [zero_smul,add_zero,one_smul,add_sub_cancel,slope_def_field,sub_zero,
    div_one] at hc
  linarith

lemma minimum_of_gradient_zero {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (x : E) (hx : g x = 0) (y : E) : f x ≤ f y := by
  have h := convex_gradient_lower hf hg x y
  simpa [hx] using h

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.SmoothDescent
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_descent {f : E → ℝ} {g : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x v : E) :
    f (x+v) ≤ f x + ⟪g x,v⟫ + L/2*‖v‖^2 := by
  let F : ℝ → ℝ := fun t => f (x+t • v)-f x-t*⟪g x,v⟫-(L/2)*t^2*‖v‖^2
  let D : ℝ → ℝ := fun t => ⟪g (x+t • v),v⟫-⟪g x,v⟫-L*t*‖v‖^2
  have hd (t : ℝ) : HasDerivAt F (D t) t := by
    have h := ((gradient_line_deriv hg x v t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪g x,v⟫)
    have hq := (((hasDerivAt_id t).pow 2).const_mul (L/2)).mul_const (‖v‖^2)
    exact (h.sub hq).congr_deriv (by dsimp [D]; ring)
  have hn (t : ℝ) (ht : t ∈ interior (Icc (0:ℝ) 1)) : D t ≤ 0 := by
    have ht0 := (interior_subset ht).1
    have hc := real_inner_le_norm (g (x+t • v)-g x) v
    have hl := mul_le_mul_of_nonneg_right (hlip (x+t • v) x) (norm_nonneg v)
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hl
    rw [inner_sub_left] at hc
    dsimp [D]
    nlinarith
  have hm : AntitoneOn F (Icc (0:ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) hn
  have h := hm (by simp : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1) (by norm_num : (0:ℝ) ≤ 1)
  simp [F] at h
  linarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.Bregman
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_sub_linear {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (a x : E) :
    HasGradientAt (fun z => f z-⟪a,z⟫) (g x-a) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sub]
  exact (hg x).hasFDerivAt.sub (InnerProductSpace.toDual ℝ E a).hasFDerivAt

lemma bregman_gradient_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hf : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x y : E) :
    ‖g x-g y‖^2 ≤ 2*L*(f x-f y-⟪g y,x-y⟫) := by
  let v := g x-g y
  have hh : ∀ z, HasGradientAt (fun z => f z-⟪g y,z⟫) (g z-g y) z :=
    fun z => gradient_sub_linear hg (g y) z
  have hl : ∀ z w, ‖(g z-g y)-(g w-g y)‖ ≤ L*‖z-w‖ := by
    intro z w
    simpa only [sub_sub_sub_cancel_right] using hlip z w
  have hd := smooth_descent hh hl x (-(1/L) • v)
  have hm := convex_gradient_lower hf hg y (x+(-(1/L) • v))
  have hn : ‖-(1/L) • v‖^2 = (1/L)^2*‖v‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  rw [hn, inner_smul_right] at hd
  have hv : ⟪g x-g y,v⟫ = ‖v‖^2 := by exact real_inner_self_eq_norm_sq v
  rw [hv] at hd
  simp only [inner_sub_right, inner_add_right, inner_smul_right] at hm hd
  have he : -(1/L)*‖v‖^2 + L/2*((1/L)^2*‖v‖^2) = -‖v‖^2/(2*L) := by
    field_simp
    ring
  rw [neg_div] at he
  have hb : ‖v‖^2/(2*L) ≤ f x-f y-⟪g y,x-y⟫ := by
    rw [inner_sub_right]
    linarith
  have hb' := (div_le_iff₀ (show 0 < 2*L by positivity)).mp hb
  dsimp [v] at hb'
  nlinarith

lemma gradient_cocoercive {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hf : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x y : E) :
    ‖g x-g y‖^2 ≤ L*⟪g x-g y,x-y⟫ := by
  have hxy := bregman_gradient_bound hL hf hg hlip x y
  have hyx := bregman_gradient_bound hL hf hg hlip y x
  rw [norm_sub_rev] at hyx
  have he : ⟪g x,y-x⟫ = -⟪g x,x-y⟫ := by rw [← inner_neg_right]; congr 1; module
  rw [he] at hyx
  rw [inner_sub_left]
  nlinarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.AverageSmooth
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
variable {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
variable {f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}

lemma avg_hasGradient (h : SAGAssumptions f f' L xstar) (x : EuclideanSpace ℝ (Fin p)) :
    HasGradientAt (SAGA.Convex.fAvg f) (SAGA.Convex.gradAvg f' x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold SAGA.Convex.fAvg SAGA.Convex.gradAvg
  rw [map_smul, map_sum]
  exact (HasFDerivAt.fun_sum (fun i _ => (h.hasGradient i x).hasFDerivAt)).const_smul (1/(n:ℝ))

lemma avg_convex (h : SAGAssumptions f f' L xstar) :
    ConvexOn ℝ univ (SAGA.Convex.fAvg f) := by
  unfold SAGA.Convex.fAvg
  refine ConvexOn.smul (by positivity) ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h.convex i).2 (mem_univ x) (mem_univ y) ha hb hab))

lemma avg_lipschitz (h : SAGAssumptions f f' L xstar)
    (x y : EuclideanSpace ℝ (Fin p)) :
    ‖SAGA.Convex.gradAvg f' x-SAGA.Convex.gradAvg f' y‖ ≤ L*‖x-y‖ := by
  have hn : (0:ℝ)<n := by exact_mod_cast h.n_pos
  unfold SAGA.Convex.gradAvg
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/n)]
  calc
    _ ≤ (1/(n:ℝ)) * ∑ i, ‖f' i x-f' i y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1/(n:ℝ)) * ∑ _i : Fin n, L*‖x-y‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h.lipschitz i x y)) (by positivity)
    _ = _ := by simp; field_simp

lemma avg_min_gradient_zero (h : SAGAssumptions f f' L xstar) :
    SAGA.Convex.gradAvg f' xstar = 0 := by
  have hm : IsLocalMin (SAGA.Convex.fAvg f) xstar := Filter.Eventually.of_forall h.minimizer
  have he := hm.fderiv_eq_zero
  rw [(avg_hasGradient h xstar).hasFDerivAt.fderiv] at he
  exact (InnerProductSpace.toDual ℝ _).injective (by simpa using he)
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.Normalization
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
noncomputable def normalizedF (f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ) (L : ℝ) :=
  fun i x => f i x/L
noncomputable def normalizedGrad
    (f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p)) (L : ℝ) :=
  fun i x => (1/L) • f' i x
lemma normalized_avg (f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ) (L : ℝ) (x) :
    SAGA.Convex.fAvg (normalizedF f L) x = SAGA.Convex.fAvg f x/L := by
  unfold SAGA.Convex.fAvg normalizedF
  rw [← Finset.sum_div]
  ring
lemma normalized_grad_avg (f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p))
    (L : ℝ) (x) :
    SAGA.Convex.gradAvg (normalizedGrad f' L) x = (1/L) • SAGA.Convex.gradAvg f' x := by
  unfold SAGA.Convex.gradAvg normalizedGrad
  rw [← Finset.smul_sum]
  module
lemma normalized_assumptions {f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ}
    {f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p)}
    {L : ℝ} {xstar} (h : SAGAssumptions f f' L xstar) :
    SAGAssumptions (normalizedF f L) (normalizedGrad f' L) 1 xstar := by
  have hL := h.L_pos
  refine ⟨h.n_pos,by norm_num,?_,?_,?_,?_⟩
  · intro i x
    rw [hasGradientAt_iff_hasFDerivAt]
    unfold normalizedF normalizedGrad
    rw [map_smul]
    have hd := (h.hasGradient i x).hasFDerivAt.const_smul (1/L)
    have he : (1/L) • f i = (fun x => f i x/L) := by
      funext z
      simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
      ring
    rw [he] at hd
    exact hd
  · intro i
    have hc := ConvexOn.smul (show 0≤1/L by positivity) (h.convex i)
    have he : (fun x => (1/L) • f i x) = normalizedF f L i := by
      funext z
      simp only [normalizedF,smul_eq_mul,div_eq_mul_inv]
      ring
    rw [he] at hc
    exact hc
  · intro i x y
    unfold normalizedGrad
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hL)]
    have hl := mul_le_mul_of_nonneg_left (h.lipschitz i x y) (show 0≤1/L by positivity)
    have he : (1/L)*(L*‖x-y‖)=‖x-y‖ := by field_simp
    simpa only [he,one_mul] using hl
  · intro x
    rw [normalized_avg,normalized_avg]
    exact div_le_div_of_nonneg_right (h.minimizer x) hL.le
lemma normalized_strong {f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ} {L μ : ℝ}
    (hL : 0<L)
    (h : ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg f x-μ/2*‖x‖^2)) :
    ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg (normalizedF f L) x-(μ/L)/2*‖x‖^2) := by
  have hc := ConvexOn.smul (show 0≤1/L by positivity) h
  have he : (fun x => SAGA.Convex.fAvg (normalizedF f L) x-(μ/L)/2*‖x‖^2) =
      (fun x => (1/L) • (SAGA.Convex.fAvg f x-μ/2*‖x‖^2)) := by
    funext x
    rw [normalized_avg]
    simp only [smul_eq_mul]
    ring
  rw [he]
  exact hc
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativePotential
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
noncomputable def centeredError
    (f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p))
    (L : ℝ) (xstar : EuclideanSpace ℝ (Fin p)) (y : Fin n→EuclideanSpace ℝ (Fin p)) :=
  fun i => (1/L) • (y i-f' i xstar)
noncomputable def nativePotential (f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ)
    (f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p))
    (L : ℝ) (xstar : EuclideanSpace ℝ (Fin p))
    (θ : (Fin n→EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  L*potential (1/(n:ℝ)) (SAGA.Convex.fAvg (normalizedF f L)) xstar
    (centeredError f' L xstar θ.1) θ.2
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeBridge
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
variable {f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ}
variable {f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}
lemma gradient_sum_zero (h : SAGAssumptions f f' L xstar) : ∑i,f' i xstar=0 := by
  have hz := avg_min_gradient_zero h
  unfold SAGA.Convex.gradAvg at hz
  exact (smul_eq_zero.mp hz).resolve_left (one_div_ne_zero (by exact_mod_cast h.n_pos.ne'))
lemma centeredError_sum (h : SAGAssumptions f f' L xstar)
    (y : Fin n→EuclideanSpace ℝ (Fin p)) :
    (∑i,centeredError f' L xstar y i) = (1/L) • ∑i,y i := by
  unfold centeredError
  rw [← Finset.smul_sum,Finset.sum_sub_distrib,gradient_sum_zero h,sub_zero]
lemma centeredError_update (y : Fin n→EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) (i : Fin n) :
    centeredError f' L xstar (Function.update y i (f' i x)) =
      Function.update (centeredError f' L xstar y) i
        (normalizedGrad f' L i x-normalizedGrad f' L i xstar) := by
  funext j
  by_cases hj : j=i
  · subst j; simp [centeredError,normalizedGrad,smul_sub]
  · simp [centeredError,Function.update_of_ne hj]
lemma native_step_centered (h : SAGAssumptions f f' L xstar)
    (θ : (Fin n→EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (i : Fin n) :
    (sagStep f' (1/(16*L)) i θ).2 = θ.2-sd (1/(n:ℝ)) •
      ∑j,centeredError f' L xstar (sagStep f' (1/(16*L)) i θ).1 j := by
  rw [centeredError_sum h]
  unfold sagStep sd
  simp only [smul_smul]
  congr 2
  ring
lemma normalized_component_mean (h : SAGAssumptions f f' L xstar)
    (x : EuclideanSpace ℝ (Fin p)) :
    (1/(n:ℝ)) • (∑i,(normalizedGrad f' L i x-normalizedGrad f' L i xstar)) =
      SAGA.Convex.gradAvg (normalizedGrad f' L) x := by
  rw [Finset.sum_sub_distrib,smul_sub]
  change SAGA.Convex.gradAvg (normalizedGrad f' L) x-
    SAGA.Convex.gradAvg (normalizedGrad f' L) xstar = _
  rw [avg_min_gradient_zero (normalized_assumptions h),sub_zero]
lemma normalized_component_variance (h : SAGAssumptions f f' L xstar)
    (x : EuclideanSpace ℝ (Fin p)) :
    (1/(n:ℝ))*(∑i,‖normalizedGrad f' L i x-normalizedGrad f' L i xstar‖^2) ≤
      ⟪SAGA.Convex.gradAvg (normalizedGrad f' L) x,x-xstar⟫ := by
  let hn := normalized_assumptions h
  have hi (i : Fin n) := gradient_cocoercive (by norm_num : (0:ℝ)<1)
    (hn.convex i) (hn.hasGradient i) (hn.lipschitz i) x xstar
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i))
    (show 0≤1/(n:ℝ) by positivity)
  simp only [one_mul,← sum_inner,← real_inner_smul_left] at hs
  rw [normalized_component_mean h x] at hs
  exact hs
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.PotentialCoefficients
namespace SAGFiniteSum.Rate.SAGFresh
lemma potential_coefficients {t : ℝ} (ht : 0<t) (ht1 : t≤1/2) :
    0 ≤ sh t ∧ 0 ≤ sa2 t ∧ 0 < sa1 t+t*sa2 t ∧
    sb t ≤ 0 ∧ 0 ≤ sh t*sd t ∧ sh t*sd t+2*sb t ≤ 0 ∧
    (sb t)^2 ≤ 3*t*(sa1 t+t*sa2 t) := by
  have ht2 : 0 ≤ t*(1/2-t) := mul_nonneg ht.le (sub_nonneg.mpr ht1)
  have hpos : 0 < 1-t/2 := by linarith
  have hh : 0 ≤ 1/2-t := by linarith
  have hq : 0 < sa1 t+t*sa2 t := by
    unfold sa1 sa2
    positivity
  have he : 3*t*(sa1 t+t*sa2 t)-(sb t)^2 = t^2*(2+17*t-10*t^2)/64 := by
    unfold sa1 sa2 sb
    ring
  have hb : 0 ≤ 2+17*t-10*t^2 := by nlinarith
  refine ⟨?_,?_,hq,?_,?_,?_,?_⟩
  · unfold sh; linarith
  · unfold sa2; positivity
  · unfold sb
    have hp := mul_nonneg ht.le (show 0≤1-t by linarith)
    nlinarith
  · unfold sh sd; positivity
  · unfold sh sd sb; nlinarith
  · nlinarith [mul_nonneg (sq_nonneg t) hb]
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.QuadraticCompletion
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadratic_completion (u z : E) {q : ℝ} (hq : 0 < q) :
    -q*‖u‖^2+⟪u,z⟫ ≤ ‖z‖^2/(4*q) := by
  have h := mul_nonneg hq.le (sq_nonneg ‖u-(1/(2*q)) • z‖)
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] at h
  have he : q*(‖u‖^2-2*((1/(2*q))*⟪u,z⟫)+(1/(2*q))^2*‖z‖^2) =
      q*‖u‖^2-⟪u,z⟫+‖z‖^2/(4*q) := by
    field_simp
    ring
  rw [he] at h
  linarith

lemma mean_residual_square {n : ℕ} (u : Fin n → E) (t : ℝ)
    (ht : t*(n:ℝ)=1) :
    (∑ i, ‖u i-t • ∑ j,u j‖^2) =
      (∑ i, ‖u i‖^2)-t*‖∑ j,u j‖^2 := by
  simp only [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← Finset.mul_sum,← sum_inner,real_inner_self_eq_norm_sq]
  linear_combination (t*‖∑ j,u j‖^2)*ht

lemma mean_residual_inner {n : ℕ} (u v : Fin n → E) (t : ℝ)
    (ht : t*(n:ℝ)=1) :
    (∑ i, ⟪u i-t • ∑ j,u j,v i-t • ∑ j,v j⟫) =
      (∑ i, ⟪u i,v i⟫)-t*⟪∑ j,u j,∑ j,v j⟫ := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,
    ← sum_inner,← inner_sum]
  linear_combination (t*⟪∑ j,u j,∑ j,v j⟫)*ht
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.PotentialDomination
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma mixed_gradient_norm_bound (g w : E) {a b : ℝ}
    (ha : 0≤a) (hb : b≤0) (hab : a+2*b≤0) (hgw : ‖g‖^2≤⟪g,w⟫) :
    ‖a • g+b • w‖^2 ≤ b^2*‖w‖^2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
  have h1 := mul_le_mul_of_nonpos_left hgw (show 2*a*b≤0 by nlinarith)
  have h2 := mul_nonpos_of_nonpos_of_nonneg (show a*(a+2*b)≤0 by nlinarith) (sq_nonneg ‖g‖)
  nlinarith

lemma potential_dominates {n : ℕ} {t : ℝ} (ht : 0<t) (ht1 : t≤1/2)
    (htn : t*(n:ℝ)=1) {G : E→ℝ} {g : E→E}
    (hconv : ConvexOn ℝ univ G) (hg : ∀x,HasGradientAt G (g x) x)
    (hlip : ∀x y,‖g x-g y‖≤1*‖x-y‖) (xstar : E) (hstar : g xstar=0)
    (u : Fin n→E) (x : E) : G x-G xstar ≤ potential t G xstar u x := by
  rcases potential_coefficients ht ht1 with ⟨hh,ha2,hq,hb,had,hab,hbq⟩
  let S := ∑i,u i
  let w := x-xstar
  let q := sa1 t+t*sa2 t
  have hv := mean_residual_square u t htn
  have hv0 := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg ‖u i-t • ∑j,u j‖)
  have hvb : t*‖S‖^2 ≤ ∑i,‖u i‖^2 := by dsimp [S]; linarith
  have hshift := convex_gradient_lower hconv hg x (x+sd t • S)
  simp only [add_sub_cancel_left,real_inner_smul_right] at hshift
  have hshift' := mul_le_mul_of_nonneg_left hshift (show 0≤2*sh t by positivity)
  have hc := gradient_cocoercive (by norm_num : (0:ℝ)<1) hconv hg hlip x xstar
  simp only [hstar,sub_zero,one_mul] at hc
  have hn := mixed_gradient_norm_bound (g x) w had hb hab hc
  have hcomplete := quadratic_completion (-S) ((2:ℝ) • ((sh t*sd t) • g x+sb t • w)) hq
  norm_num only [norm_neg,inner_neg_left,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2),mul_pow] at hcomplete
  have hnorm : ‖(sh t*sd t) • g x+sb t • w‖^2 / q ≤ 3*t*‖w‖^2 := by
    apply (div_le_iff₀ hq).mpr
    have hmul := mul_le_mul_of_nonneg_right hbq (sq_nonneg ‖w‖)
    nlinarith
  have hdes := smooth_descent hg hlip xstar (x-xstar)
  simp only [hstar,inner_zero_left,add_sub_cancel] at hdes
  have hvar := mul_le_mul_of_nonneg_left hvb ha2
  have he : 4*‖(sh t*sd t) • g x+sb t • w‖^2/(4*q) =
      ‖(sh t*sd t) • g x+sb t • w‖^2/q := by field_simp
  rw [he] at hcomplete
  simp only [inner_add_right,real_inner_smul_right] at hcomplete
  have he1 : ⟪S,g x⟫ = ⟪g x,S⟫ := real_inner_comm _ _
  unfold potential
  dsimp [S,w,q] at *
  unfold sh sc at *
  nlinarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.TableMoments
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma refresh_square_mean {n : ℕ} (u v : Fin n → E) (t : ℝ)
    (ht : t*(n:ℝ)=1) :
    t*(∑ i, ‖(∑ j,u j)-u i+v i‖^2) =
      (1-2*t)*‖∑ j,u j‖^2+t*(∑ i,‖u i‖^2)+
      2*⟪∑ j,u j,t • ∑ i,v i⟫-2*t*(∑ i,⟪u i,v i⟫)+t*(∑ i,‖v i‖^2) := by
  rw [sum_refresh_sum_square, Fintype.card_fin, real_inner_smul_right]
  nlinarith [mul_assoc t (n:ℝ) (‖∑ j,u j‖^2)]

omit [InnerProductSpace ℝ E] in
lemma refresh_table_square_mean {n : ℕ} (u v : Fin n → E) (t : ℝ)
    (ht : t*(n:ℝ)=1) :
    t*(∑ i, ∑ j, ‖Function.update u i (v i) j‖^2) =
      (1-t)*(∑ i,‖u i‖^2)+t*(∑ i,‖v i‖^2) := by
  simp_rw [sum_refresh_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  linear_combination (∑ i,‖u i‖^2)*ht

lemma refresh_inner_mean {n : ℕ} (u v : Fin n → E) (t : ℝ)
    (ht : t*(n:ℝ)=1) (w : E) :
    t*(∑ i, ⟪(∑ j,u j)-u i+v i,w⟫) =
      (1-t)*⟪∑ j,u j,w⟫+⟪t • ∑ i,v i,w⟫ := by
  simp only [inner_add_left,inner_sub_left,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← sum_inner,real_inner_smul_left]
  linear_combination ⟪∑ j,u j,w⟫*ht
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.PotentialMean
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma potential_refresh_mean {n : ℕ} (t : ℝ) (ht : t*(n:ℝ)=1)
    (G : E→ℝ) (xstar x : E) (u v : Fin n→E) :
    t*(∑i,potential t G xstar (Function.update u i (v i))
      (x-sd t • ∑j,Function.update u i (v i) j)) =
    2*sh t*(G x-G xstar)+coefA t*((1-2*t)*‖∑j,u j‖^2+
      t*(∑i,‖u i‖^2)+2*⟪∑j,u j,t • ∑i,v i⟫-
      2*t*(∑i,⟪u i,v i⟫)+t*(∑i,‖v i‖^2))+
    sa2 t*((1-t)*(∑i,‖u i‖^2)+t*(∑i,‖v i‖^2))+
    2*(sb t-sd t*sc t)*((1-t)*⟪∑j,u j,x-xstar⟫+⟪t • ∑i,v i,x-xstar⟫)+
    sc t*‖x-xstar‖^2 := by
  have hp (i : Fin n) := potential_refresh t G xstar x u v i
  have hsq := refresh_square_mean u v t ht
  have htab := refresh_table_square_mean u v t ht
  have hin := refresh_inner_mean u v t ht (x-xstar)
  simp_rw [sum_refresh_sq] at htab
  rw [Finset.sum_add_distrib] at htab
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  linear_combination (coefA t)*hsq + (sa2 t)*htab +
    (2*(sb t-sd t*sc t))*hin +
    (2*sh t*(G x-G xstar)+sc t*‖x-xstar‖^2)*ht
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.RawDrift
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def rawDrift {n : ℕ} (t μ : ℝ) (u v : Fin n→E) (w : E) (gap : ℝ) : ℝ :=
  coefB0 t μ*gap+coefB1 t*⟪t • ∑i,v i,w⟫+coefB9 t μ*‖w‖^2-
  coefB3 t μ*(∑i,‖u i‖^2)-(coefB4 t μ-coefB3 t μ)*t*‖∑i,u i‖^2+
  coefB5 t μ*⟪∑i,u i,w⟫+coefB6 t*(∑i,⟪u i,v i⟫)+
  coefB7 t μ*⟪∑i,u i,t • ∑i,v i⟫+coefB8 t*(∑i,‖v i‖^2)

lemma potential_raw_identity {n : ℕ} {t : ℝ} (ht : t≠0) (htn : t*(n:ℝ)=1)
    (μ : ℝ) (G : E→ℝ) (xstar x : E) (u v : Fin n→E) :
    t*(∑i,potential t G xstar (Function.update u i (v i))
      (x-sd t • ∑j,Function.update u i (v i) j)) -
      (1-μ/16)*potential t G xstar u x =
    rawDrift t μ u v (x-xstar) (G x-G xstar)-
      2*sh t*(1-μ/16)*(G (x+sd t • ∑i,u i)-G x-
        sd t*⟪t • ∑i,v i,∑i,u i⟫) := by
  rw [potential_refresh_mean t htn]
  unfold potential rawDrift coefB0 coefB1 coefB4 coefB3 coefB5 coefB6 coefB7 coefB8 coefB9
  rw [real_inner_comm (t • ∑i,v i) (∑i,u i)]
  field_simp
  ring

variable [CompleteSpace E]
lemma potential_raw_bound {n : ℕ} {t μ : ℝ} (ht : 0<t) (ht1 : t≤1/2)
    (htn : t*(n:ℝ)=1) (hμ : μ≤16) {G : E→ℝ} {g : E→E}
    (hconv : ConvexOn ℝ univ G) (hg : ∀x,HasGradientAt G (g x) x)
    (xstar x : E) (u v : Fin n→E) (hv : t • ∑i,v i=g x) :
    t*(∑i,potential t G xstar (Function.update u i (v i))
      (x-sd t • ∑j,Function.update u i (v i) j)) ≤
      (1-μ/16)*potential t G xstar u x+rawDrift t μ u v (x-xstar) (G x-G xstar) := by
  have hh : 0 ≤ sh t := by unfold sh; linarith
  have hl := convex_gradient_lower hconv hg x (x+sd t • ∑i,u i)
  simp only [add_sub_cancel_left,real_inner_smul_right] at hl
  have hδ : 0 ≤ 1-μ/16 := by linarith
  have hprod := mul_nonneg (show 0≤2*sh t*(1-μ/16) by positivity)
    (show 0≤G (x+sd t • ∑i,u i)-G x-sd t*⟪g x,∑i,u i⟫ by linarith)
  have he := potential_raw_identity ht.ne' htn μ G xstar x u v
  rw [hv] at he
  linarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.TableCompletion
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma table_completion {n : ℕ} (u v : Fin n→E) (w : E) {t b3 b4 : ℝ}
    (ht : 0<t) (htn : t*(n:ℝ)=1) (h3 : 0<b3) (h4 : 0<b4) (b5 b6 b7 : ℝ) :
    -b3*(∑i,‖u i‖^2)-(b4-b3)*t*‖∑i,u i‖^2+
      b5*⟪∑i,u i,w⟫+b6*(∑i,⟪u i,v i⟫)+b7*⟪∑i,u i,t • ∑i,v i⟫ ≤
    b6^2/(4*b3)*((∑i,‖v i‖^2)-‖t • ∑i,v i‖^2/t)+
      ‖b5 • w+(b6+b7) • (t • ∑i,v i)‖^2/(4*t*b4) := by
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    quadratic_completion (u i-t • ∑j,u j) (b6 • (v i-t • ∑j,v j)) h3)
  simp only [real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    Finset.sum_add_distrib,← Finset.mul_sum] at hc
  rw [mean_residual_square u t htn,mean_residual_inner u v t htn] at hc
  have hr : (∑i,b6^2*‖v i-t • ∑j,v j‖^2) =
      b6^2*((∑i,‖v i‖^2)-t*‖∑j,v j‖^2) := by
    rw [← Finset.mul_sum,mean_residual_square v t htn]
  rw [← Finset.sum_div,hr] at hc
  have hs := quadratic_completion (∑i,u i)
    (b5 • w+(b6+b7) • (t • ∑i,v i)) (mul_pos ht h4)
  simp only [inner_add_right,real_inner_smul_right] at hs
  have he : ‖t • ∑i,v i‖^2/t = t*‖∑i,v i‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    field_simp
  rw [he]
  rw [real_inner_smul_right]
  have hd : 4*(t*b4)=4*t*b4 := by ring
  rw [hd] at hs
  linear_combination hc+hs
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.RawCompletion
namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma b8_nonneg {t : ℝ} (ht : 0<t) (ht1 : t≤1/2) : 0 ≤ coefB8 t := by
  rcases potential_coefficients ht ht1 with ⟨hh,ha2,hq,hb,had,hab,hbq⟩
  have ha1 : 0 ≤ sa1 t := by
    unfold sa1
    have : 0≤1-t/2 := by linarith
    positivity
  have hd : 0 ≤ sd t := by unfold sd; positivity
  have hc : 0 ≤ sc t := by unfold sc; positivity
  unfold coefB8 coefA
  have hp := mul_nonneg hd (neg_nonneg.mpr hb)
  have hA : 0 ≤ sa1 t-2*sd t*sb t+(sd t)^2*sc t+sa2 t := by nlinarith [mul_nonneg (sq_nonneg (sd t)) hc]
  exact mul_nonneg ht.le hA

lemma completed_scalar_identity (t μ b0 b1 b3 b4 b5 b6 b7 b8 b9 W H V : ℝ)
    (ht : t≠0) (h3 : b3≠0) (h4 : b4≠0) :
    b0*(H-μ/2*W)+b1*H+b9*W+
      b6^2/(4*b3)*(H/t-V/t)+
      (b5^2*W+2*b5*(b6+b7)*H+(b6+b7)^2*V)/(4*t*b4)+b8*(H/t) =
    (-b0*μ/2+b9+b5^2/(4*t*b4))*W+
    (b0+b1+b6^2/(4*t*b3)+b5*(b6+b7)/(2*t*b4)+b8/t)*H+
    (-b6^2/(4*t*b3)+(b6+b7)^2/(4*t*b4))*V := by
  field_simp
  ring

lemma raw_completed_bound {n : ℕ} (u v : Fin n→E) (w : E) (gap : ℝ)
    {t μ : ℝ} (ht : 0<t) (ht1 : t≤1/2) (htn : t*(n:ℝ)=1)
    (hμ : 0≤μ) (h3 : 0<coefB3 t μ) (h4 : 0<coefB4 t μ)
    (hgap : gap ≤ ⟪t • ∑i,v i,w⟫-μ/2*‖w‖^2)
    (hv : t*(∑i,‖v i‖^2) ≤ ⟪t • ∑i,v i,w⟫) :
    rawDrift t μ u v w gap ≤ coefC0 t μ*‖w‖^2+
      coefC1 t μ*⟪t • ∑i,v i,w⟫+coefC2 t μ*‖t • ∑i,v i‖^2 := by
  have hc := table_completion u v w ht htn h3 h4 (coefB5 t μ) (coefB6 t) (coefB7 t μ)
  have hb0 : 0 ≤ coefB0 t μ := by
    unfold coefB0 sh
    have : 0≤1/2-t := by linarith
    positivity
  have hg := mul_le_mul_of_nonneg_left hgap hb0
  have hsum : (∑i,‖v i‖^2) ≤ ⟪t • ∑i,v i,w⟫/t :=
    (le_div_iff₀ ht).mpr (by simpa [mul_comm] using hv)
  have hcoef : 0 ≤ coefB8 t+(coefB6 t)^2/(4*coefB3 t μ) :=
    add_nonneg (b8_nonneg ht ht1) (by positivity)
  have hs := mul_le_mul_of_nonneg_left hsum hcoef
  have he := completed_scalar_identity t μ (coefB0 t μ) (coefB1 t) (coefB3 t μ)
    (coefB4 t μ) (coefB5 t μ) (coefB6 t) (coefB7 t μ) (coefB8 t) (coefB9 t μ)
    (‖w‖^2) ⟪t • ∑i,v i,w⟫ (‖t • ∑i,v i‖^2) ht.ne' h3.ne' h4.ne'
  have hn (a b : ℝ) (x y : E) : ‖a • x+b • y‖^2 =
      a^2*‖x‖^2+2*a*b*⟪x,y⟫+b^2*‖y‖^2 := by
    simp only [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      real_inner_smul_left,real_inner_smul_right]
    ring
  rw [hn] at hc
  rw [real_inner_comm (t • ∑i,v i) w] at hc
  unfold rawDrift coefC0 coefC1 coefC2
  linear_combination hc+hg+hs+he
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.BernsteinCertificates

namespace SAGFiniteSum.Rate.SAGFresh

noncomputable def poly_b3 (t y : ℝ) : ℝ :=
  4 * t ^ 2 + 1 * t ^ 1 * y ^ 1 - 12 * t ^ 1 - 2 * y ^ 1 + 8

theorem poly_b3_bernstein (t y : ℝ) :
    poly_b3 t y - (3 / 2) =
    (13 / 2) * (2 * t) ^ 0 * (1 - 2 * t) ^ 2 * y ^ 0 * (1 - y) ^ 1 +
    (9 / 2) * (2 * t) ^ 0 * (1 - 2 * t) ^ 2 * y ^ 1 * (1 - y) ^ 0 +
    7 * (2 * t) ^ 1 * (1 - 2 * t) ^ 1 * y ^ 0 * (1 - y) ^ 1 +
    (7 / 2) * (2 * t) ^ 1 * (1 - 2 * t) ^ 1 * y ^ 1 * (1 - y) ^ 0 +
    (3 / 2) * (2 * t) ^ 2 * (1 - 2 * t) ^ 0 * y ^ 0 * (1 - y) ^ 1 := by
  unfold poly_b3
  ring

theorem poly_b3_lower {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : (3 / 2) ≤ poly_b3 t y := by
  have htx : 0 ≤ 1 - 2 * t := by linarith
  have hyx : 0 ≤ 1 - y := by linarith
  have hp : 0 ≤ poly_b3 t y - (3 / 2) := by
    rw [poly_b3_bernstein]
    positivity
  linarith

noncomputable def poly_b4 (t y : ℝ) : ℝ :=
  8 * t ^ 3 + 2 * t ^ 2 * y ^ 1 - 40 * t ^ 2 - 3 * t ^ 1 * y ^ 1 + 40 * t ^ 1 - 2 * y ^ 1 + 16

theorem poly_b4_bernstein (t y : ℝ) :
    poly_b4 t y - 14 =
    2 * (2 * t) ^ 0 * (1 - 2 * t) ^ 3 * y ^ 0 * (1 - y) ^ 1 +
    26 * (2 * t) ^ 1 * (1 - 2 * t) ^ 2 * y ^ 0 * (1 - y) ^ 1 +
    (37 / 2) * (2 * t) ^ 1 * (1 - 2 * t) ^ 2 * y ^ 1 * (1 - y) ^ 0 +
    36 * (2 * t) ^ 2 * (1 - 2 * t) ^ 1 * y ^ 0 * (1 - y) ^ 1 +
    (55 / 2) * (2 * t) ^ 2 * (1 - 2 * t) ^ 1 * y ^ 1 * (1 - y) ^ 0 +
    13 * (2 * t) ^ 3 * (1 - 2 * t) ^ 0 * y ^ 0 * (1 - y) ^ 1 +
    10 * (2 * t) ^ 3 * (1 - 2 * t) ^ 0 * y ^ 1 * (1 - y) ^ 0 := by
  unfold poly_b4
  ring

theorem poly_b4_lower {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 14 ≤ poly_b4 t y := by
  have htx : 0 ≤ 1 - 2 * t := by linarith
  have hyx : 0 ≤ 1 - y := by linarith
  have hp : 0 ≤ poly_b4 t y - 14 := by
    rw [poly_b4_bernstein]
    positivity
  linarith

noncomputable def poly_c2 (t y : ℝ) : ℝ :=
  64 * t ^ 6 * y ^ 1 - 312 * t ^ 5 * y ^ 1 - 768 * t ^ 5 - 4 * t ^ 4 * y ^ 3 - 8 * t ^ 4 * y ^ 2 + 560 * t ^ 4 * y ^ 1 + 3904 * t ^ 4 + 12 * t ^ 3 * y ^ 3 + 60 * t ^ 3 * y ^ 2 - 504 * t ^ 3 * y ^ 1 - 6400 * t ^ 3 - 9 * t ^ 2 * y ^ 3 - 108 * t ^ 2 * y ^ 2 + 288 * t ^ 2 * y ^ 1 + 2880 * t ^ 2 + 2 * t ^ 1 * y ^ 3 + 40 * t ^ 1 * y ^ 2 - 64 * t ^ 1 * y ^ 1 + 640 * t ^ 1 - 64 * y ^ 1 + 512

theorem poly_c2_bernstein (t y : ℝ) :
    poly_c2 t y - 448 =
    64 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 0 * (1 - y) ^ 3 +
    128 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 1 * (1 - y) ^ 2 +
    64 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 2 * (1 - y) ^ 1 +
    704 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 0 * (1 - y) ^ 3 +
    1696 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 1 * (1 - y) ^ 2 +
    1300 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 2 * (1 - y) ^ 1 +
    309 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 3 * (1 - y) ^ 0 +
    3280 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 0 * (1 - y) ^ 3 +
    8792 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 1 * (1 - y) ^ 2 +
    7817 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 2 * (1 - y) ^ 1 +
    (9231 / 4) * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 3 * (1 - y) ^ 0 +
    6560 * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 0 * (1 - y) ^ 3 +
    18305 * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 1 * (1 - y) ^ 2 +
    (34059 / 2) * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 2 * (1 - y) ^ 1 +
    5287 * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 3 * (1 - y) ^ 0 +
    6324 * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 0 * (1 - y) ^ 3 +
    17970 * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 1 * (1 - y) ^ 2 +
    17028 * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 2 * (1 - y) ^ 1 +
    (21531 / 4) * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 3 * (1 - y) ^ 0 +
    2928 * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 0 * (1 - y) ^ 3 +
    (33597 / 4) * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 1 * (1 - y) ^ 2 +
    8028 * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 2 * (1 - y) ^ 1 +
    (10227 / 4) * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 3 * (1 - y) ^ 0 +
    524 * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 0 * (1 - y) ^ 3 +
    (6045 / 4) * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 1 * (1 - y) ^ 2 +
    (2901 / 2) * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 2 * (1 - y) ^ 1 +
    (1853 / 4) * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 3 * (1 - y) ^ 0 := by
  unfold poly_c2
  ring

theorem poly_c2_lower {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 448 ≤ poly_c2 t y := by
  have htx : 0 ≤ 1 - 2 * t := by linarith
  have hyx : 0 ≤ 1 - y := by linarith
  have hp : 0 ≤ poly_c2 t y - 448 := by
    rw [poly_c2_bernstein]
    positivity
  linarith

noncomputable def poly_c1 (t y : ℝ) : ℝ :=
  392 * t ^ 6 * y ^ 1 + 290 * t ^ 5 * y ^ 2 - 3632 * t ^ 5 * y ^ 1 + 832 * t ^ 5 + 48 * t ^ 4 * y ^ 3 - 1733 * t ^ 4 * y ^ 2 + 11728 * t ^ 4 * y ^ 1 - 6528 * t ^ 4 - 184 * t ^ 3 * y ^ 3 + 3501 * t ^ 3 * y ^ 2 - 16528 * t ^ 3 * y ^ 1 + 17408 * t ^ 3 + 176 * t ^ 2 * y ^ 3 - 2368 * t ^ 2 * y ^ 2 + 9320 * t ^ 2 * y ^ 1 - 17216 * t ^ 2 + 16 * t ^ 1 * y ^ 3 - 284 * t ^ 1 * y ^ 2 + 288 * t ^ 1 * y ^ 1 + 2304 * t ^ 1 - 32 * y ^ 3 + 480 * y ^ 2 - 2144 * y ^ 1 + 2816

theorem poly_c1_bernstein (t y : ℝ) :
    poly_c1 t y - 432 =
    2384 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 0 * (1 - y) ^ 3 +
    5008 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 1 * (1 - y) ^ 2 +
    3344 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 2 * (1 - y) ^ 1 +
    688 * (2 * t) ^ 0 * (1 - 2 * t) ^ 6 * y ^ 3 * (1 - y) ^ 0 +
    15456 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 0 * (1 - y) ^ 3 +
    33648 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 1 * (1 - y) ^ 2 +
    23666 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 2 * (1 - y) ^ 1 +
    5290 * (2 * t) ^ 1 * (1 - 2 * t) ^ 5 * y ^ 3 * (1 - y) ^ 0 +
    37216 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 0 * (1 - y) ^ 3 +
    82538 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 1 * (1 - y) ^ 2 +
    59326 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 2 * (1 - y) ^ 1 +
    13608 * (2 * t) ^ 2 * (1 - 2 * t) ^ 4 * y ^ 3 * (1 - y) ^ 0 +
    44160 * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 0 * (1 - y) ^ 3 +
    98294 * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 1 * (1 - y) ^ 2 +
    (562861 / 8) * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 2 * (1 - y) ^ 1 +
    (126533 / 8) * (2 * t) ^ 3 * (1 - 2 * t) ^ 3 * y ^ 3 * (1 - y) ^ 0 +
    27576 * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 0 * (1 - y) ^ 3 +
    60523 * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 1 * (1 - y) ^ 2 +
    (668009 / 16) * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 2 * (1 - y) ^ 1 +
    (137625 / 16) * (2 * t) ^ 4 * (1 - 2 * t) ^ 2 * y ^ 3 * (1 - y) ^ 0 +
    8586 * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 0 * (1 - y) ^ 3 +
    (36177 / 2) * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 1 * (1 - y) ^ 2 +
    (181221 / 16) * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 2 * (1 - y) ^ 1 +
    (28557 / 16) * (2 * t) ^ 5 * (1 - 2 * t) ^ 1 * y ^ 3 * (1 - y) ^ 0 +
    1026 * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 0 * (1 - y) ^ 3 +
    (15741 / 8) * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 1 * (1 - y) ^ 2 +
    (7533 / 8) * (2 * t) ^ 6 * (1 - 2 * t) ^ 0 * y ^ 2 * (1 - y) ^ 1 := by
  unfold poly_c1
  ring

theorem poly_c1_lower {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 432 ≤ poly_c1 t y := by
  have htx : 0 ≤ 1 - 2 * t := by linarith
  have hyx : 0 ≤ 1 - y := by linarith
  have hp : 0 ≤ poly_c1 t y - 432 := by
    rw [poly_c1_bernstein]
    positivity
  linarith

noncomputable def poly_main (t y : ℝ) : ℝ :=
  64 * t ^ 7 * y ^ 2 - 312 * t ^ 6 * y ^ 2 - 632 * t ^ 6 * y ^ 1 - 4 * t ^ 5 * y ^ 4 - 8 * t ^ 5 * y ^ 3 + 722 * t ^ 5 * y ^ 2 + 2448 * t ^ 5 * y ^ 1 + 320 * t ^ 5 + 12 * t ^ 4 * y ^ 4 + 92 * t ^ 4 * y ^ 3 - 1437 * t ^ 4 * y ^ 2 - 1648 * t ^ 4 * y ^ 1 - 2432 * t ^ 4 - 9 * t ^ 3 * y ^ 4 - 228 * t ^ 3 * y ^ 3 + 2061 * t ^ 3 * y ^ 2 - 3152 * t ^ 3 * y ^ 1 + 6144 * t ^ 3 + 2 * t ^ 2 * y ^ 4 + 156 * t ^ 2 * y ^ 3 - 1088 * t ^ 2 * y ^ 2 + 2792 * t ^ 2 * y ^ 1 - 5440 * t ^ 2 - 364 * t ^ 1 * y ^ 2 + 1760 * t ^ 1 * y ^ 1 + 256 * t ^ 1 - 16 * y ^ 3 + 256 * y ^ 2 - 992 * y ^ 1 + 768

theorem poly_main_bernstein (t y : ℝ) :
    poly_main t y - 16 =
    752 * (2 * t) ^ 0 * (1 - 2 * t) ^ 7 * y ^ 0 * (1 - y) ^ 4 +
    2016 * (2 * t) ^ 0 * (1 - 2 * t) ^ 7 * y ^ 1 * (1 - y) ^ 3 +
    1792 * (2 * t) ^ 0 * (1 - 2 * t) ^ 7 * y ^ 2 * (1 - y) ^ 2 +
    528 * (2 * t) ^ 0 * (1 - 2 * t) ^ 7 * y ^ 3 * (1 - y) ^ 1 +
    5392 * (2 * t) ^ 1 * (1 - 2 * t) ^ 6 * y ^ 0 * (1 - y) ^ 4 +
    15504 * (2 * t) ^ 1 * (1 - 2 * t) ^ 6 * y ^ 1 * (1 - y) ^ 3 +
    15770 * (2 * t) ^ 1 * (1 - 2 * t) ^ 6 * y ^ 2 * (1 - y) ^ 2 +
    6484 * (2 * t) ^ 1 * (1 - 2 * t) ^ 6 * y ^ 3 * (1 - y) ^ 1 +
    826 * (2 * t) ^ 1 * (1 - 2 * t) ^ 6 * y ^ 4 * (1 - y) ^ 0 +
    15200 * (2 * t) ^ 2 * (1 - 2 * t) ^ 5 * y ^ 0 * (1 - y) ^ 4 +
    45946 * (2 * t) ^ 2 * (1 - 2 * t) ^ 5 * y ^ 1 * (1 - y) ^ 3 +
    50650 * (2 * t) ^ 2 * (1 - 2 * t) ^ 5 * y ^ 2 * (1 - y) ^ 2 +
    23965 * (2 * t) ^ 2 * (1 - 2 * t) ^ 5 * y ^ 3 * (1 - y) ^ 1 +
    (8123 / 2) * (2 * t) ^ 2 * (1 - 2 * t) ^ 5 * y ^ 4 * (1 - y) ^ 0 +
    22208 * (2 * t) ^ 3 * (1 - 2 * t) ^ 4 * y ^ 0 * (1 - y) ^ 4 +
    70408 * (2 * t) ^ 3 * (1 - 2 * t) ^ 4 * y ^ 1 * (1 - y) ^ 3 +
    (664829 / 8) * (2 * t) ^ 3 * (1 - 2 * t) ^ 4 * y ^ 2 * (1 - y) ^ 2 +
    (173687 / 4) * (2 * t) ^ 3 * (1 - 2 * t) ^ 4 * y ^ 3 * (1 - y) ^ 1 +
    (17039 / 2) * (2 * t) ^ 3 * (1 - 2 * t) ^ 4 * y ^ 4 * (1 - y) ^ 0 +
    18200 * (2 * t) ^ 4 * (1 - 2 * t) ^ 3 * y ^ 0 * (1 - y) ^ 4 +
    60981 * (2 * t) ^ 4 * (1 - 2 * t) ^ 3 * y ^ 1 * (1 - y) ^ 3 +
    (1236539 / 16) * (2 * t) ^ 4 * (1 - 2 * t) ^ 3 * y ^ 2 * (1 - y) ^ 2 +
    (353169 / 8) * (2 * t) ^ 4 * (1 - 2 * t) ^ 3 * y ^ 3 * (1 - y) ^ 1 +
    (154315 / 16) * (2 * t) ^ 4 * (1 - 2 * t) ^ 3 * y ^ 4 * (1 - y) ^ 0 +
    8274 * (2 * t) ^ 5 * (1 - 2 * t) ^ 2 * y ^ 0 * (1 - y) ^ 4 +
    (59695 / 2) * (2 * t) ^ 5 * (1 - 2 * t) ^ 2 * y ^ 1 * (1 - y) ^ 3 +
    (328987 / 8) * (2 * t) ^ 5 * (1 - 2 * t) ^ 2 * y ^ 2 * (1 - y) ^ 2 +
    (102801 / 4) * (2 * t) ^ 5 * (1 - 2 * t) ^ 2 * y ^ 3 * (1 - y) ^ 1 +
    (24603 / 4) * (2 * t) ^ 5 * (1 - 2 * t) ^ 2 * y ^ 4 * (1 - y) ^ 0 +
    1868 * (2 * t) ^ 6 * (1 - 2 * t) ^ 1 * y ^ 0 * (1 - y) ^ 4 +
    (60449 / 8) * (2 * t) ^ 6 * (1 - 2 * t) ^ 1 * y ^ 1 * (1 - y) ^ 3 +
    (185627 / 16) * (2 * t) ^ 6 * (1 - 2 * t) ^ 1 * y ^ 2 * (1 - y) ^ 2 +
    (31971 / 4) * (2 * t) ^ 6 * (1 - 2 * t) ^ 1 * y ^ 3 * (1 - y) ^ 1 +
    (33267 / 16) * (2 * t) ^ 6 * (1 - 2 * t) ^ 1 * y ^ 4 * (1 - y) ^ 0 +
    146 * (2 * t) ^ 7 * (1 - 2 * t) ^ 0 * y ^ 0 * (1 - y) ^ 4 +
    (5917 / 8) * (2 * t) ^ 7 * (1 - 2 * t) ^ 0 * y ^ 1 * (1 - y) ^ 3 +
    (10647 / 8) * (2 * t) ^ 7 * (1 - 2 * t) ^ 0 * y ^ 2 * (1 - y) ^ 2 +
    (8215 / 8) * (2 * t) ^ 7 * (1 - 2 * t) ^ 0 * y ^ 3 * (1 - y) ^ 1 +
    (2317 / 8) * (2 * t) ^ 7 * (1 - 2 * t) ^ 0 * y ^ 4 * (1 - y) ^ 0 := by
  unfold poly_main
  ring

theorem poly_main_lower {t y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 16 ≤ poly_main t y := by
  have htx : 0 ≤ 1 - 2 * t := by linarith
  have hyx : 0 ≤ 1 - y := by linarith
  have hp : 0 ≤ poly_main t y - 16 := by
    rw [poly_main_bernstein]
    positivity
  linarith

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.ScalarCertificateAlgebra

namespace SAGFiniteSum.Rate.SAGFresh

theorem coefB3_polynomial (t y : ℝ) :
    coefB3 t (2 * t * y) = t ^ 2 * poly_b3 t y / 256 := by
  unfold coefB3 coefA sa1 sa2 sb sc sd poly_b3
  ring

theorem coefB4_polynomial {t : ℝ} (ht : 0 < t) (y : ℝ) :
    coefB4 t (2 * t * y) = t * poly_b4 t y / 512 := by
  unfold coefB4 coefB3 coefA sa1 sa2 sb sc sd poly_b4
  field_simp [ne_of_gt ht]
  ring

theorem coefB3_pos {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < coefB3 t (2 * t * y) := by
  rw [coefB3_polynomial]
  have hp := poly_b3_lower ht.le ht1 hy0 hy1
  positivity

theorem coefB4_pos {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < coefB4 t (2 * t * y) := by
  rw [coefB4_polynomial ht]
  have hp := poly_b4_lower ht.le ht1 hy0 hy1
  positivity

theorem coefC2_certificate {t y : ℝ} (ht : 0 < t)
    (hb3 : 0 < coefB3 t (2 * t * y)) (hb4 : 0 < coefB4 t (2 * t * y)) :
    -coefC2 t (2 * t * y) * coefB3 t (2 * t * y) * coefB4 t (2 * t * y) =
      t ^ 4 * poly_c2 t y / 16777216 := by
  unfold coefC2
  generalize h3 : coefB3 t (2 * t * y) = b3 at hb3 ⊢
  generalize h4 : coefB4 t (2 * t * y) = b4 at hb4 ⊢
  field_simp [ne_of_gt ht, ne_of_gt hb3, ne_of_gt hb4]
  rw [← h3, ← h4]
  unfold coefB4 coefB3 coefB6 coefB7 coefA sa1 sa2 sb sc sd sh poly_c2
  field_simp [ne_of_gt ht]
  ring

theorem coefC1_certificate {t y : ℝ} (ht : 0 < t)
    (hb3 : 0 < coefB3 t (2 * t * y)) (hb4 : 0 < coefB4 t (2 * t * y)) :
    -(coefC1 t (2 * t * y) + t / 32) * coefB3 t (2 * t * y) * coefB4 t (2 * t * y) =
      t ^ 4 * poly_c1 t y / 8388608 := by
  unfold coefC1
  generalize h3 : coefB3 t (2 * t * y) = b3 at hb3 ⊢
  generalize h4 : coefB4 t (2 * t * y) = b4 at hb4 ⊢
  field_simp [ne_of_gt ht, ne_of_gt hb3, ne_of_gt hb4]
  rw [← h3, ← h4]
  unfold coefB0 coefB1 coefB4 coefB3 coefB5 coefB6 coefB7 coefB8 coefA sa1 sa2 sb sc sd sh poly_c1
  field_simp [ne_of_gt ht]
  ring

theorem coef_main_certificate {t y : ℝ} (ht : 0 < t)
    (hb3 : 0 < coefB3 t (2 * t * y)) (hb4 : 0 < coefB4 t (2 * t * y)) :
    -(coefC0 t (2 * t * y) + (2 * t * y) * (coefC1 t (2 * t * y) + t / 32) +
      (2 * t * y) ^ 2 * coefC2 t (2 * t * y)) *
      coefB3 t (2 * t * y) * coefB4 t (2 * t * y) =
      t ^ 5 * y * poly_main t y / 4194304 := by
  unfold coefC0 coefC1 coefC2
  generalize h3 : coefB3 t (2 * t * y) = b3 at hb3 ⊢
  generalize h4 : coefB4 t (2 * t * y) = b4 at hb4 ⊢
  field_simp [ne_of_gt ht, ne_of_gt hb3, ne_of_gt hb4]
  rw [← h3, ← h4]
  unfold coefB0 coefB1 coefB4 coefB3 coefB5 coefB6 coefB7 coefB8 coefB9 coefA sa1 sa2 sb sc sd sh poly_main
  field_simp [ne_of_gt ht]
  ring

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.ScalarSigns

namespace SAGFiniteSum.Rate.SAGFresh

theorem nonpos_of_neg_mul_mul_nonneg {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h : 0 ≤ -a * b * c) : a ≤ 0 := by
  have h1 := (mul_nonneg_iff_of_pos_right hc).mp h
  have h2 := (mul_nonneg_iff_of_pos_right hb).mp h1
  exact neg_nonneg.mp h2

theorem scalar_signs_y {t y : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < coefB3 t (2 * t * y) ∧ 0 < coefB4 t (2 * t * y) ∧
    coefC2 t (2 * t * y) ≤ 0 ∧ coefC1 t (2 * t * y) + t / 32 ≤ 0 ∧
    coefC0 t (2 * t * y) + (2 * t * y) * (coefC1 t (2 * t * y) + t / 32) +
      (2 * t * y) ^ 2 * coefC2 t (2 * t * y) ≤ 0 := by
  have hb3 := coefB3_pos ht ht1 hy0 hy1
  have hb4 := coefB4_pos ht ht1 hy0 hy1
  refine ⟨hb3, hb4, ?_, ?_, ?_⟩
  · apply nonpos_of_neg_mul_mul_nonneg hb3 hb4
    rw [coefC2_certificate ht hb3 hb4]
    have hp := poly_c2_lower ht.le ht1 hy0 hy1
    positivity
  · apply nonpos_of_neg_mul_mul_nonneg hb3 hb4
    rw [coefC1_certificate ht hb3 hb4]
    have hp := poly_c1_lower ht.le ht1 hy0 hy1
    positivity
  · apply nonpos_of_neg_mul_mul_nonneg hb3 hb4
    rw [coef_main_certificate ht hb3 hb4]
    have hp := poly_main_lower ht.le ht1 hy0 hy1
    positivity

theorem scalar_signs {t μ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 2 * t) :
    0 < coefB3 t μ ∧ 0 < coefB4 t μ ∧
    coefC2 t μ ≤ 0 ∧ coefC1 t μ + t / 32 ≤ 0 ∧
    coefC0 t μ + μ * (coefC1 t μ + t / 32) + μ ^ 2 * coefC2 t μ ≤ 0 := by
  have h2t : 0 < 2 * t := by positivity
  have hy0 : 0 ≤ μ / (2 * t) := div_nonneg hμ0 h2t.le
  have hy1 : μ / (2 * t) ≤ 1 := (div_le_one h2t).mpr hμ1
  have he : 2 * t * (μ / (2 * t)) = μ := by
    simpa only [mul_comm] using div_mul_cancel₀ μ (ne_of_gt h2t)
  simpa only [he] using scalar_signs_y ht ht1 hy0 hy1

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.StrongConvex
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_sub_norm_sq {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (μ : ℝ) (x : E) :
    HasGradientAt (fun z => f z-μ/2*‖z‖^2) (g x-μ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (hg x).hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ/2))
  have he : (InnerProductSpace.toDual ℝ E) (g x-μ • x) =
      (InnerProductSpace.toDual ℝ E) (g x) - (μ/2) • (2 • innerSL ℝ x) := by
    ext v
    simp
    ring
  rw [he]
  exact hh

lemma strong_gradient_lower {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hc : ConvexOn ℝ univ (fun z => f z-μ/2*‖z‖^2)) (x y : E) :
    f x + ⟪g x,y-x⟫ + μ/2*‖y-x‖^2 ≤ f y := by
  have h := convex_gradient_lower hc (gradient_sub_norm_sq hg μ) x y
  rw [inner_sub_left, real_inner_smul_left, inner_sub_right] at h
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h ⊢
  rw [real_inner_comm x y]
  nlinarith

lemma strong_gradient_monotone {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hc : ConvexOn ℝ univ (fun z => f z-μ/2*‖z‖^2)) (x y : E) :
    μ*‖x-y‖^2 ≤ ⟪g x-g y,x-y⟫ := by
  have hxy := strong_gradient_lower hg hc x y
  have hyx := strong_gradient_lower hg hc y x
  have he : ⟪g x,y-x⟫ = -⟪g x,x-y⟫ := by rw [← inner_neg_right]; congr 1; module
  rw [he, norm_sub_rev] at hxy
  rw [inner_sub_left]
  linarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.PotentialDrift
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
lemma strong_gradient_norm {G : E→ℝ} {g : E→E} {μ : ℝ} (hμ : 0≤μ)
    (hg : ∀x,HasGradientAt G (g x) x)
    (hc : ConvexOn ℝ univ (fun z => G z-μ/2*‖z‖^2))
    (xstar x : E) (hstar : g xstar=0) : μ^2*‖x-xstar‖^2 ≤ ‖g x‖^2 := by
  have hm := strong_gradient_monotone hg hc x xstar
  simp only [hstar,sub_zero] at hm
  have hi := real_inner_le_norm (g x) (x-xstar)
  have hw := norm_nonneg (x-xstar)
  have hg0 := norm_nonneg (g x)
  by_cases hz : ‖x-xstar‖=0
  · simp [hz]
  have hp : 0<‖x-xstar‖ := lt_of_le_of_ne hw (Ne.symm hz)
  have hlin : μ*‖x-xstar‖ ≤ ‖g x‖ := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hlin) (show 0≤‖g x‖+μ*‖x-xstar‖ by positivity)]

lemma potential_drift {n : ℕ} {t μ : ℝ} (ht : 0<t) (ht1 : t≤1/2)
    (htn : t*(n:ℝ)=1) (hμ0 : 0≤μ) (hμ1 : μ≤2*t)
    {G : E→ℝ} {g : E→E} (hconv : ConvexOn ℝ univ G)
    (hg : ∀x,HasGradientAt G (g x) x)
    (hstrong : ConvexOn ℝ univ (fun z => G z-μ/2*‖z‖^2))
    (xstar x : E) (hstar : g xstar=0) (u v : Fin n→E)
    (hv : t • ∑i,v i=g x) (hvar : t*(∑i,‖v i‖^2)≤⟪g x,x-xstar⟫) :
    t*(∑i,potential t G xstar (Function.update u i (v i))
      (x-sd t • ∑j,Function.update u i (v i) j)) ≤
      (1-μ/16)*potential t G xstar u x-t/32*⟪g x,x-xstar⟫ := by
  rcases scalar_signs ht ht1 hμ0 hμ1 with ⟨h3,h4,hc2,hc1,hmain⟩
  have hr := potential_raw_bound ht ht1 htn (show μ≤16 by linarith) hconv hg xstar x u v hv
  have hsg := strong_gradient_lower hg hstrong x xstar
  rw [norm_sub_rev] at hsg
  have hinner : ⟪g x,xstar-x⟫ = -⟪g x,x-xstar⟫ := by
    rw [← inner_neg_right]; congr 1; module
  rw [hinner] at hsg
  have hgap : G x-G xstar ≤ ⟪g x,x-xstar⟫-μ/2*‖x-xstar‖^2 := by linarith
  have hrc := raw_completed_bound u v (x-xstar) (G x-G xstar) ht ht1 htn hμ0 h3 h4
    (by simpa only [hv] using hgap) (by simpa only [hv] using hvar)
  rw [hv] at hrc
  have hmon := strong_gradient_monotone hg hstrong x xstar
  simp only [hstar,sub_zero] at hmon
  have hnorm := strong_gradient_norm hμ0 hg hstrong xstar x hstar
  have h1 := mul_le_mul_of_nonpos_left hmon hc1
  have h2 := mul_le_mul_of_nonpos_left hnorm hc2
  have h3' := mul_nonpos_of_nonpos_of_nonneg hmain (sq_nonneg ‖x-xstar‖)
  nlinarith
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeDrift
namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
variable {f : Fin n→EuclideanSpace ℝ (Fin p)→ℝ}
variable {f' : Fin n→EuclideanSpace ℝ (Fin p)→EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}
lemma native_t_bounds (hn : 2≤n) : 0<1/(n:ℝ) ∧ 1/(n:ℝ)≤1/2 ∧ (1/(n:ℝ))*(n:ℝ)=1 := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  refine ⟨by positivity,?_,?_⟩
  · exact one_div_le_one_div_of_le (by norm_num) hnR
  · field_simp
lemma normalized_gap_scale (hL : L≠0) (x : EuclideanSpace ℝ (Fin p)) :
    L*(SAGA.Convex.fAvg (normalizedF f L) x-SAGA.Convex.fAvg (normalizedF f L) xstar) =
      SAGA.Convex.fAvg f x-SAGA.Convex.fAvg f xstar := by
  rw [normalized_avg,normalized_avg]
  field_simp
lemma native_potential_dominates (h : SAGAssumptions f f' L xstar) (hn : 2≤n)
    (θ : (Fin n→EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    SAGA.Convex.fAvg f θ.2-SAGA.Convex.fAvg f xstar ≤ nativePotential f f' L xstar θ := by
  let hA := normalized_assumptions h
  rcases native_t_bounds hn with ⟨ht,ht1,htn⟩
  have hp := potential_dominates ht ht1 htn (avg_convex hA) (avg_hasGradient hA)
    (avg_lipschitz hA) xstar (avg_min_gradient_zero hA) (centeredError f' L xstar θ.1) θ.2
  have hb := mul_le_mul_of_nonneg_left hp h.L_pos.le
  rw [normalized_gap_scale h.L_pos.ne'] at hb
  exact hb
lemma native_potential_nonneg (h : SAGAssumptions f f' L xstar) (hn : 2≤n)
    (θ : (Fin n→EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    0 ≤ nativePotential f f' L xstar θ := by
  have hp := native_potential_dominates h hn θ
  have hm := h.minimizer θ.2
  linarith
lemma native_potential_drift (h : SAGAssumptions f f' L xstar) (hn : 2≤n)
    {μ : ℝ} (hμ0 : 0≤μ) (hμ1 : μ≤2*L/(n:ℝ))
    (hc : ConvexOn ℝ univ (fun x => SAGA.Convex.fAvg f x-μ/2*‖x‖^2))
    (θ : (Fin n→EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1/(n:ℝ))*(∑i,nativePotential f f' L xstar (sagStep f' (1/(16*L)) i θ)) ≤
      (1-μ/(16*L))*nativePotential f f' L xstar θ-
        (1/(n:ℝ))/32*(SAGA.Convex.fAvg f θ.2-SAGA.Convex.fAvg f xstar) := by
  let hA := normalized_assumptions h
  rcases native_t_bounds hn with ⟨ht,ht1,htn⟩
  have hL := h.L_pos
  have hm0 : 0≤μ/L := div_nonneg hμ0 hL.le
  have hm1 : μ/L≤2*(1/(n:ℝ)) := by
    apply (div_le_iff₀ hL).mpr
    have he : 2*(1/(n:ℝ))*L = 2*L/(n:ℝ) := by ring
    rw [he]
    exact hμ1
  let u := centeredError f' L xstar θ.1
  let v := fun i => normalizedGrad f' L i θ.2-normalizedGrad f' L i xstar
  have hp := potential_drift ht ht1 htn hm0 hm1 (avg_convex hA) (avg_hasGradient hA)
    (normalized_strong hL hc) xstar θ.2 (avg_min_gradient_zero hA) u v
    (normalized_component_mean h θ.2) (normalized_component_variance h θ.2)
  have hs (i : Fin n) : nativePotential f f' L xstar (sagStep f' (1/(16*L)) i θ) =
      L*potential (1/(n:ℝ)) (SAGA.Convex.fAvg (normalizedF f L)) xstar
        (Function.update u i (v i)) (θ.2-sd (1/(n:ℝ)) • ∑j,Function.update u i (v i) j) := by
    unfold nativePotential
    rw [native_step_centered h]
    change L*potential _ _ _ (centeredError f' L xstar (Function.update θ.1 i (f' i θ.2)))
      (θ.2-sd _ • ∑j,centeredError f' L xstar (Function.update θ.1 i (f' i θ.2)) j) = _
    rw [centeredError_update]
  have hg := convex_gradient_lower (avg_convex hA) (avg_hasGradient hA) θ.2 xstar
  have hi : ⟪SAGA.Convex.gradAvg (normalizedGrad f' L) θ.2,xstar-θ.2⟫ =
      -⟪SAGA.Convex.gradAvg (normalizedGrad f' L) θ.2,θ.2-xstar⟫ := by
    rw [← inner_neg_right]; congr 1; module
  rw [hi] at hg
  have hpL := mul_le_mul_of_nonneg_left hp hL.le
  have hgL := mul_le_mul_of_nonneg_left hg (show 0≤L*((1/(n:ℝ))/32) by positivity)
  have hgap := normalized_gap_scale (f:=f) (xstar:=xstar) hL.ne' θ.2
  simp_rw [hs]
  rw [← Finset.mul_sum]
  unfold nativePotential
  dsimp [u] at hpL
  have he : (μ/L)/16=μ/(16*L) := by ring
  rw [he] at hpL
  linear_combination hpL+hgL-((1/(n:ℝ))/32)*hgap
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.PotentialInitial

namespace SAGFiniteSum.Rate.SAGFresh
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem potential_sum_zero {n : ℕ} (t : ℝ) (G : E → ℝ) (xstar x : E)
    (u : Fin n → E) (hu : ∑ i, u i = 0) :
    potential t G xstar u x = 2 * sh t * (G x - G xstar) +
      sa2 t * (∑ i, ‖u i‖ ^ 2) + sc t * ‖x - xstar‖ ^ 2 := by
  simp [potential, hu]

theorem initial_zero_bound {n : ℕ} {t σ : ℝ} (ht : 0 ≤ t) (_ht1 : t ≤ 1 / 2)
    (G : E → ℝ) (xstar x : E) (u : Fin n → E)
    (hu : ∑ i, u i = 0) (hg : 0 ≤ G x - G xstar)
    (henergy : t * (∑ i, ‖u i‖ ^ 2) ≤ σ) :
    potential t G xstar u x ≤ G x - G xstar +
      4 * t * ‖x - xstar‖ ^ 2 + σ / 16 := by
  rw [potential_sum_zero t G xstar x u hu]
  have he : 0 ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsmall : sa2 t ≤ t / 16 := by unfold sa2; nlinarith
  have htable := mul_le_mul_of_nonneg_right hsmall he
  unfold sh sc
  nlinarith [mul_nonneg ht hg]

theorem initial_centered_bound {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (G : E → ℝ) (xstar x : E) (u : Fin n → E)
    (hu : ∑ i, u i = 0) (hg : 0 ≤ G x - G xstar)
    (henergy : t * (∑ i, ‖u i‖ ^ 2) ≤ 2 * (G x - G xstar)) :
    potential t G xstar u x ≤ (3 / 2 : ℝ) * (G x - G xstar) +
      4 * t * ‖x - xstar‖ ^ 2 := by
  have h := initial_zero_bound ht ht1 G xstar x u hu hg henergy
  linarith

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeInitial

namespace SAGFiniteSum.Rate.SAGFresh
open SAGA.Convex
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
variable {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
variable {f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
variable {xstar : EuclideanSpace ℝ (Fin p)}

lemma sum_gradient_min_zero {L : ℝ} (h : SAGAssumptions f f' L xstar) :
    (∑ i, f' i xstar) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.n_pos)
  have hh := avg_min_gradient_zero h
  unfold gradAvg at hh
  exact (smul_eq_zero.mp hh).resolve_left (one_div_ne_zero hn)

lemma sum_centered_zero {L : ℝ} (h : SAGAssumptions f f' L xstar)
    (x : EuclideanSpace ℝ (Fin p)) : (∑ i, centeredTable f' x i) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.n_pos)
  simp only [centeredTable, gradAvg, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn]

lemma centered_energy_le {L : ℝ} (h : SAGAssumptions f f' L xstar)
    (x : EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * (∑ i, ‖centeredTable f' x i - f' i xstar‖ ^ 2) ≤
      2 * L * (fAvg f x - fAvg f xstar) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.n_pos)
  have ht : (1 / (n : ℝ)) * n = 1 := by field_simp
  let v := fun i => f' i x - f' i xstar
  have hv : (∑ i, v i) = ∑ i, f' i x := by
    simp only [v, Finset.sum_sub_distrib, sum_gradient_min_zero h, sub_zero]
  have he (i : Fin n) : centeredTable f' x i - f' i xstar =
      v i - (1 / (n : ℝ)) • ∑ j, v j := by
    rw [hv]
    unfold centeredTable gradAvg v
    abel
  simp_rw [he]
  rw [mean_residual_square v (1 / (n : ℝ)) ht]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    bregman_gradient_bound h.L_pos (h.convex i) (h.hasGradient i) (h.lipschitz i) x xstar)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, ← sum_inner,
    sum_gradient_min_zero h, inner_zero_left, sub_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 1 / n by positivity)
  unfold fAvg
  dsimp [v]
  have hs : 0 ≤ (1 / (n : ℝ)) * ‖∑ j, (f' j x - f' j xstar)‖ ^ 2 := by positivity
  have ht0 : 0 ≤ (1 / (n : ℝ)) := by positivity
  nlinarith [mul_nonneg ht0 hs]

lemma native_zero_potential (h : SAGAssumptions f f' 1 xstar) (hn2 : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin p)) :
    potential (1 / (n : ℝ)) (fAvg f) xstar (fun i => zeroTable i - f' i xstar) x ≤
      C0zero f f' 1 xstar x := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have ht : (1 / (n : ℝ)) ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hu : (∑ i, (zeroTable i - f' i xstar)) = 0 := by
    simp [zeroTable, sum_gradient_min_zero h]
  have he : (1 / (n : ℝ)) * (∑ i, ‖zeroTable i - f' i xstar‖ ^ 2) ≤ sigmaSq f' xstar := by
    simp [zeroTable, sigmaSq]
  have hh := initial_zero_bound (by positivity : 0 ≤ 1 / (n : ℝ)) ht
    (fAvg f) xstar x (fun i => zeroTable i - f' i xstar) hu
    (sub_nonneg.mpr (h.minimizer x)) he
  simpa [C0zero, div_eq_mul_inv] using hh

lemma native_centered_potential (h : SAGAssumptions f f' 1 xstar) (hn2 : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin p)) :
    potential (1 / (n : ℝ)) (fAvg f) xstar (fun i => centeredTable f' x i - f' i xstar) x ≤
      C0centered f 1 xstar x := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have ht : (1 / (n : ℝ)) ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hu : (∑ i, (centeredTable f' x i - f' i xstar)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_centered_zero h, sum_gradient_min_zero h, sub_self]
  have he := centered_energy_le h x
  simp only [mul_one] at he
  have hh := initial_centered_bound (by positivity : 0 ≤ 1 / (n : ℝ)) ht
    (fAvg f) xstar x (fun i => centeredTable f' x i - f' i xstar) hu
    (sub_nonneg.mpr (h.minimizer x)) he
  simpa [C0centered, div_eq_mul_inv] using hh

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeInitialization

namespace SAGFiniteSum.Rate.SAGFresh
open SAGA.Convex
open scoped BigOperators RealInnerProductSpace
variable {p n : ℕ}
variable {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
variable {f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}

lemma normalized_sigma (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (L : ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    sigmaSq (normalizedGrad f' L) x = sigmaSq f' x / L ^ 2 := by
  simp only [sigmaSq, normalizedGrad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.mul_sum]
  ring

lemma normalized_C0zero (hL : 0 < L) (x : EuclideanSpace ℝ (Fin p)) :
    L * C0zero (normalizedF f L) (normalizedGrad f' L) 1 xstar x =
      C0zero f f' L xstar x := by
  simp only [C0zero, normalized_avg, normalized_sigma]
  field_simp [ne_of_gt hL]

lemma normalized_C0centered (hL : 0 < L) (x : EuclideanSpace ℝ (Fin p)) :
    L * C0centered (normalizedF f L) 1 xstar x = C0centered f L xstar x := by
  simp only [C0centered, normalized_avg]
  field_simp [ne_of_gt hL]

lemma native_initial_zero (h : SAGAssumptions f f' L xstar) (hn2 : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin p)) :
    nativePotential f f' L xstar (zeroTable, x) ≤ C0zero f f' L xstar x := by
  have hi := native_zero_potential (normalized_assumptions h) hn2 x
  have he : centeredError f' L xstar zeroTable =
      fun i => zeroTable i - normalizedGrad f' L i xstar := by
    funext i
    simp [centeredError, zeroTable, normalizedGrad]
  have hm := mul_le_mul_of_nonneg_left hi h.L_pos.le
  rw [normalized_C0zero h.L_pos] at hm
  simpa only [nativePotential, he] using hm

lemma native_initial_centered (h : SAGAssumptions f f' L xstar) (hn2 : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin p)) :
    nativePotential f f' L xstar (centeredTable f' x, x) ≤ C0centered f L xstar x := by
  have hi := native_centered_potential (normalized_assumptions h) hn2 x
  have he : centeredError f' L xstar (centeredTable f' x) =
      fun i => centeredTable (normalizedGrad f' L) x i - normalizedGrad f' L i xstar := by
    funext i
    unfold centeredError centeredTable
    rw [normalized_grad_avg]
    unfold normalizedGrad
    module
  have hm := mul_le_mul_of_nonneg_left hi h.L_pos.le
  rw [normalized_C0centered h.L_pos] at hm
  simpa only [nativePotential, he] using hm

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.FiniteExpectation

namespace SAGFiniteSum.Rate.SAGFresh

open Finset
open SAGA.Convex

theorem expectIdx_mono {n k : ℕ} {f g : (Fin k → Fin n) → ℝ}
    (h : ∀ js, f js ≤ g js) : expectIdx n k f ≤ expectIdx n k g := by
  unfold expectIdx
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun js _ => h js)) (by positivity)

theorem expectIdx_add {n k : ℕ} (f g : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => f js + g js) = expectIdx n k f + expectIdx n k g := by
  simp only [expectIdx, sum_add_distrib, mul_add]

theorem expectIdx_sub {n k : ℕ} (f g : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => f js - g js) = expectIdx n k f - expectIdx n k g := by
  simp only [expectIdx, sum_sub_distrib, mul_sub]

theorem expectIdx_mul {n k : ℕ} (a : ℝ) (f : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => a * f js) = a * expectIdx n k f := by
  simp only [expectIdx, ← mul_sum]
  ring

theorem expectIdx_const {n k : ℕ} (hn : 0 < n) (a : ℝ) :
    expectIdx n k (fun _ => a) = a := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [expectIdx, Nat.cast_pow, hn']

theorem expectIdx_zero {n : ℕ} (f : (Fin 0 → Fin n) → ℝ) :
    expectIdx n 0 f = f Fin.elim0 := by
  simp only [expectIdx, pow_zero, div_one, Fintype.sum_unique, one_mul]
  congr 1

theorem sum_fin_cons {n k : ℕ} (f : (Fin (k + 1) → Fin n) → ℝ) :
    (∑ js, f js) = ∑ i : Fin n, ∑ js : Fin k → Fin n, f (Fin.cons i js) := by
  have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type] at he
  exact he.symm

theorem expectIdx_succ {n k : ℕ} (f : (Fin (k + 1) → Fin n) → ℝ) :
    expectIdx n (k + 1) f =
      (1 / (n : ℝ)) * ∑ i : Fin n, expectIdx n k (fun js => f (Fin.cons i js)) := by
  unfold expectIdx
  rw [sum_fin_cons]
  simp only [← mul_sum, pow_succ, one_div, mul_inv_rev]
  ring

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.FiniteDriftRates

namespace SAGFiniteSum.Rate.SAGFresh

open Finset SAGA.Convex

noncomputable def pathCost {ι X : Type*} (step : ι → X → X) (cost : X → ℝ)
    (x : X) : List ι → ℝ
  | [] => 0
  | i :: is => cost x + pathCost step cost (step i x) is

theorem fold_mean_geometric {X : Type*} {n : ℕ} (step : Fin n → X → X)
    (potential : X → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ x, (1 / (n : ℝ)) * ∑ i, potential (step i x) ≤ q * potential x)
    (k : ℕ) (x : X) :
    expectIdx n k (fun js => potential ((List.ofFn js).foldl (fun x i => step i x) x)) ≤
      q ^ k * potential x := by
  induction k generalizing x with
  | zero => simp [expectIdx]
  | succ k ih =>
    rw [expectIdx_succ]
    simp only [List.ofFn_cons, List.foldl_cons]
    calc
      _ ≤ (1 / (n : ℝ)) * ∑ i, q ^ k * potential (step i x) :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => ih (step i x))) (by positivity)
      _ = q ^ k * ((1 / (n : ℝ)) * ∑ i, potential (step i x)) := by
        rw [← mul_sum]
        ring
      _ ≤ q ^ k * (q * potential x) := mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg hq k)
      _ = q ^ (k + 1) * potential x := by rw [pow_succ]; ring

theorem fold_mean_budget {X : Type*} {n : ℕ} (hn : 0 < n) (step : Fin n → X → X)
    (potential cost : X → ℝ) (η : ℝ)
    (hstep : ∀ x, (1 / (n : ℝ)) * ∑ i, potential (step i x) ≤ potential x - η * cost x)
    (k : ℕ) (x : X) :
    expectIdx n k (fun js => η * pathCost step cost x (List.ofFn js) +
      potential ((List.ofFn js).foldl (fun x i => step i x) x)) ≤ potential x := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  induction k generalizing x with
  | zero => simp [expectIdx, pathCost]
  | succ k ih =>
    rw [expectIdx_succ]
    have hinner (i : Fin n) :
        expectIdx n k (fun js => η * pathCost step cost x (List.ofFn (Fin.cons i js)) +
          potential ((List.ofFn (Fin.cons i js)).foldl (fun x i => step i x) x)) ≤
          η * cost x + potential (step i x) := by
      simp only [List.ofFn_cons, pathCost, List.foldl_cons, mul_add, add_assoc]
      rw [expectIdx_add, expectIdx_const hn]
      exact add_le_add le_rfl (ih (step i x))
    have hm := mul_le_mul_of_nonneg_left (sum_le_sum (s := Finset.univ) (fun i _ => hinner i))
      (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity)
    have he : (1 / (n : ℝ)) * ∑ i, (η * cost x + potential (step i x)) =
        η * cost x + (1 / (n : ℝ)) * ∑ i, potential (step i x) := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
      field_simp [hn']
    apply hm.trans
    rw [he]
    linarith [hstep x]

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeRunAlgebra

namespace SAGFiniteSum.Rate.SAGFresh

open Finset SAGA.Convex

theorem pathCost_eq_sum {ι X : Type*} (step : ι → X → X) (cost : X → ℝ)
    (l : List ι) (x : X) :
    pathCost step cost x l = ∑ t ∈ range l.length,
      cost ((l.take t).foldl (fun x i => step i x) x) := by
  induction l generalizing x with
  | nil => simp [pathCost]
  | cons i l ih =>
    simp only [pathCost, List.length_cons, sum_range_succ', List.take_zero, List.foldl_nil,
      List.take_succ_cons, List.foldl_cons]
    rw [← ih]
    ring

theorem sagIter_final {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (js : Fin k → Fin n) :
    sagIter f' α θ js k = (List.ofFn js).foldl (fun θ i => sagStep f' α i θ) θ := by
  unfold sagIter
  rw [(List.take_eq_self_iff (List.ofFn js)).mpr (by simp)]

theorem sag_pathCost {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (cost : ((Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) → ℝ)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (js : Fin k → Fin n) :
    pathCost (sagStep f' α) cost θ (List.ofFn js) =
      ∑ t ∈ range k, cost (sagIter f' α θ js t) := by
  rw [pathCost_eq_sum]
  simp only [List.length_ofFn, sagIter]

theorem convex_avg_gap_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {g : E → ℝ} (hg : ConvexOn ℝ Set.univ g) (gstar : ℝ)
    {k : ℕ} (hk : 0 < k) (x : ℕ → E) :
    g ((1 / (k : ℝ)) • ∑ t ∈ range k, x t) - gstar ≤
      (1 / (k : ℝ)) * ∑ t ∈ range k, (g (x t) - gstar) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hw : ∑ _t ∈ range k, (1 / (k : ℝ)) = 1 := by simp [hk']
  have hj := hg.map_sum_le (t := range k) (w := fun _ => 1 / (k : ℝ))
    (p := x) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  have hj' : g ((1 / (k : ℝ)) • ∑ t ∈ range k, x t) ≤
      (1 / (k : ℝ)) * ∑ t ∈ range k, g (x t) := by
    simpa only [← smul_sum, smul_eq_mul, ← mul_sum] using hj
  have he : (1 / (k : ℝ)) * ∑ t ∈ range k, (g (x t) - gstar) =
      (1 / (k : ℝ)) * ∑ t ∈ range k, g (x t) - gstar := by
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub]
    field_simp [hk']
  rw [he]
  linarith

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.OperationalRates

namespace SAGFiniteSum.Rate.SAGFresh
open Finset SAGA.Convex

theorem sag_geometric_rate {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (α : ℝ) (G : EuclideanSpace ℝ (Fin p) → ℝ) (gstar : ℝ)
    (V : ((Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (hdom : ∀ θ, G θ.2 - gstar ≤ V θ)
    (hstep : ∀ θ, (1 / (n : ℝ)) * ∑ i, V (sagStep f' α i θ) ≤ q * V θ)
    (k : ℕ) (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx n k (fun js => G (sagIter f' α θ js k).2 - gstar) ≤ q ^ k * V θ := by
  have hb := fold_mean_geometric (sagStep f' α) V q hq hstep k θ
  refine (expectIdx_mono (k := k) (fun js => hdom (sagIter f' α θ js k))).trans ?_
  simpa only [sagIter_final] using hb

theorem sag_convex_rate {p n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (α : ℝ) (G : EuclideanSpace ℝ (Fin p) → ℝ) (gstar : ℝ)
    (hG : ConvexOn ℝ Set.univ G)
    (V : ((Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) → ℝ)
    (η : ℝ) (hη : 0 < η) (hV : ∀ θ, 0 ≤ V θ)
    (hstep : ∀ θ, (1 / (n : ℝ)) * ∑ i, V (sagStep f' α i θ) ≤
      V θ - η * (G θ.2 - gstar))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx n k (fun js => G (avgIter f' α θ js) - gstar) ≤ V θ / (η * k) := by
  let cost := fun θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) =>
    G θ.2 - gstar
  have hb := fold_mean_budget hn (sagStep f' α) V cost η hstep k θ
  have hm := expectIdx_mono (k := k) (fun js =>
    le_add_of_nonneg_right (a := η * pathCost (sagStep f' α) cost θ (List.ofFn js))
      (hV ((List.ofFn js).foldl (fun θ i => sagStep f' α i θ) θ)))
  have hs : η * expectIdx n k (fun js => ∑ t ∈ range k,
      (G (sagIter f' α θ js t).2 - gstar)) ≤ V θ := by
    have hh := hm.trans hb
    rw [expectIdx_mul] at hh
    simpa only [sag_pathCost, cost] using hh
  have hj := expectIdx_mono (k := k) (fun js =>
    convex_avg_gap_le hG gstar hk (fun t => (sagIter f' α θ js t).2))
  rw [expectIdx_mul] at hj
  change expectIdx n k (fun js => G (avgIter f' α θ js) - gstar) ≤ _ at hj
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply hj.trans
  apply (le_div_iff₀ (mul_pos hη hkR)).mpr
  have he (a : ℝ) : (1 / (k : ℝ) * a) * (η * k) = η * a := by
    field_simp [ne_of_gt hkR]
  rw [he]
  exact hs

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.StrongParameter
namespace SAGFiniteSum.Rate.SAGFresh
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma strong_parameter_mono {G : E→ℝ} {μ ν : ℝ} (hν : ν≤μ)
    (h : ConvexOn ℝ univ (fun x => G x-μ/2*‖x‖^2)) :
    ConvexOn ℝ univ (fun x => G x-ν/2*‖x‖^2) := by
  have hn : ConvexOn ℝ univ (fun x : E => ‖x‖^2) :=
    (convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 2)
  have ha := h.add (ConvexOn.smul (show 0≤(μ-ν)/2 by positivity) hn)
  change ConvexOn ℝ univ (fun x => (G x-μ/2*‖x‖^2)+((μ-ν)/2)*‖x‖^2) at ha
  have he : (fun x => G x-ν/2*‖x‖^2) =
      (fun x => (G x-μ/2*‖x‖^2)+((μ-ν)/2)*‖x‖^2) := by funext x; ring
  rw [he]
  exact ha
end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeManyComponent

namespace SAGFiniteSum.Rate.SAGFresh
open SAGA.Convex
open scoped BigOperators
variable {p n : ℕ}
variable {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
variable {f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}

theorem many_convex_rate (h : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    {k : ℕ} (hk : 0 < k)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx n k (fun js => fAvg f (avgIter f' (1 / (16 * L)) θ js)) - fAvg f xstar ≤
      32 * (n : ℝ) / k * nativePotential f f' L xstar θ := by
  have hL := h.L_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs (θ) := native_potential_drift h hn (μ := 0) (by norm_num)
    (by positivity) (by simpa using avg_convex h) θ
  simp only [zero_div, sub_zero, one_mul] at hs
  have hr := sag_convex_rate h.n_pos hk f' (1 / (16 * L)) (fAvg f) (fAvg f xstar)
    (avg_convex h) (nativePotential f f' L xstar) ((1 / (n : ℝ)) / 32)
    (by positivity) (native_potential_nonneg h hn) hs θ
  rw [expectIdx_sub, expectIdx_const h.n_pos] at hr
  convert hr using 1
  field_simp

theorem many_geometric_rate (h : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (μ : ℝ) (hμ : 0 < μ)
    (hc : ConvexOn ℝ Set.univ (fun x => fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (k : ℕ) (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx n k (fun js => fAvg f (sagIter f' (1 / (16 * L)) θ js k).2) - fAvg f xstar ≤
      (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * nativePotential f f' L xstar θ := by
  have hL := h.L_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.n_pos
  let μb := min μ (2 * L / (n : ℝ))
  have hμb : 0 ≤ μb := le_min hμ.le (by positivity)
  have hb1 : μb ≤ 2 * L / (n : ℝ) := min_le_right _ _
  have hcb := strong_parameter_mono (min_le_left μ (2 * L / (n : ℝ))) hc
  have hrate : μb / (16 * L) = min (μ / (16 * L)) (1 / (8 * (n : ℝ))) := by
    dsimp [μb]
    rw [← min_div_div_right (show 0 ≤ 16 * L by positivity)]
    congr 1
    field_simp
    ring
  have hq : 0 ≤ 1 - μb / (16 * L) := by
    rw [hrate]
    have hm := min_le_right (μ / (16 * L)) (1 / (8 * (n : ℝ)))
    have hb : 1 / (8 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hs (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
      (1 / (n : ℝ)) * ∑ i, nativePotential f f' L xstar (sagStep f' (1 / (16 * L)) i θ) ≤
        (1 - μb / (16 * L)) * nativePotential f f' L xstar θ := by
    have hd := native_potential_drift h hn hμb hb1 hcb θ
    have hgap : 0 ≤ fAvg f θ.2 - fAvg f xstar := sub_nonneg.mpr (h.minimizer θ.2)
    have hcost : 0 ≤ ((1 / (n : ℝ)) / 32) * (fAvg f θ.2 - fAvg f xstar) := by positivity
    linarith
  have hr := sag_geometric_rate f' (1 / (16 * L)) (fAvg f) (fAvg f xstar)
    (nativePotential f f' L xstar) (1 - μb / (16 * L)) hq
    (native_potential_dominates h hn) hs k θ
  rw [expectIdx_sub, expectIdx_const h.n_pos, hrate] at hr
  exact hr

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.GradientRates

namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def gdStep (g : E → E) (L : ℝ) (x : E) : E :=
  x - (1 / (16 * L)) • g x

theorem gradient_norm_gap {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (f x - f xstar) := by
  have hd := smooth_descent hg hlip x (-(1 / L) • g x)
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hd
  have hm := hmin (x + -(1 / L) • g x)
  have he : -(1 / L) + L / 2 * (-(1 / L)) ^ 2 = -(1 / (2 * L)) := by
    field_simp [ne_of_gt hL]
    ring
  have hh : f (x + -(1 / L) • g x) ≤ f x - ‖g x‖ ^ 2 / (2 * L) := by
    calc
      _ ≤ f x + (-(1 / L) + L / 2 * (-(1 / L)) ^ 2) * ‖g x‖ ^ 2 := by nlinarith [hd]
      _ = _ := by rw [he]; ring
  have hp := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp
    (show ‖g x‖ ^ 2 / (2 * L) ≤ f x - f xstar by linarith)
  nlinarith

theorem gd_decrease {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E) :
    f (gdStep g L x) ≤ f x - ‖g x‖ ^ 2 / (32 * L) := by
  have hd := smooth_descent hg hlip x (-(1 / (16 * L)) • g x)
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hd
  have he : -(1 / (16 * L)) + L / 2 * (-(1 / (16 * L))) ^ 2 =
      -(31 / (512 * L)) := by field_simp [ne_of_gt hL]; ring
  have hcoef : 1 / (32 * L) ≤ 31 / (512 * L) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖g x‖)
  have hx : x + -(1 / (16 * L)) • g x = gdStep g L x := by
    simp [gdStep, sub_eq_add_neg]
  rw [hx] at hd
  calc
    _ ≤ f x + (-(1 / (16 * L)) + L / 2 * (-(1 / (16 * L))) ^ 2) * ‖g x‖ ^ 2 := by nlinarith [hd]
    _ ≤ _ := by
      rw [he]
      have he2 : ‖g x‖ ^ 2 / (32 * L) = (1 / (32 * L)) * ‖g x‖ ^ 2 := by ring
      rw [he2]
      nlinarith

theorem gradient_pl {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hc : ConvexOn ℝ univ (fun z => f z - μ / 2 * ‖z‖ ^ 2))
    (xstar x : E) : 2 * μ * (f x - f xstar) ≤ ‖g x‖ ^ 2 := by
  have h := strong_gradient_lower hg hc x xstar
  have he : ⟪g x, xstar - x⟫ = -⟪g x, x - xstar⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [he, norm_sub_rev] at h
  have hn := sq_nonneg ‖g x - μ • (x - xstar)‖
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] at hn
  nlinarith

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.GradientDrift

namespace SAGFiniteSum.Rate.SAGFresh
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gd_gap_contraction {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hc : ConvexOn ℝ univ (fun z => f z - μ / 2 * ‖z‖ ^ 2))
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    f (gdStep g L x) - f xstar ≤
      (1 - min (μ / (16 * L)) (1 / 8)) * (f x - f xstar) := by
  have hd := gd_decrease hL hg hlip x
  have hp := gradient_pl hμ hg hc xstar x
  have hdiv := (div_le_div_iff_of_pos_right (by positivity : 0 < 32 * L)).mpr hp
  have he : 2 * μ * (f x - f xstar) / (32 * L) =
      μ / (16 * L) * (f x - f xstar) := by ring
  rw [he] at hdiv
  have hm := mul_le_mul_of_nonneg_right
    (min_le_left (μ / (16 * L)) (1 / 8)) (sub_nonneg.mpr (hmin x))
  nlinarith

theorem gd_distance_drift {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hc : ConvexOn ℝ univ f) (xstar : E) (hmin : ∀ x, f xstar ≤ f x)
    (x : E) :
    4 * L * ‖gdStep g L x - xstar‖ ^ 2 ≤
      4 * L * ‖x - xstar‖ ^ 2 - (f x - f xstar) / 32 := by
  have hg2 := gradient_norm_gap hL hg hlip xstar hmin x
  have hc1 := convex_gradient_lower hc hg x xstar
  have he : ⟪g x, xstar - x⟫ = -⟪g x, x - xstar⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [he] at hc1
  have hgap : 0 ≤ f x - f xstar := sub_nonneg.mpr (hmin x)
  have hx : gdStep g L x - xstar =
      (x - xstar) - (1 / (16 * L)) • g x := by unfold gdStep; module
  rw [hx, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  have hi : ⟪x - xstar, g x⟫ = ⟪g x, x - xstar⟫ := real_inner_comm _ _
  rw [hi]
  have halg : 4 * L *
      (‖x - xstar‖ ^ 2 - 2 * ((1 / (16 * L)) * ⟪g x, x - xstar⟫) +
        (1 / (16 * L)) ^ 2 * ‖g x‖ ^ 2) =
      4 * L * ‖x - xstar‖ ^ 2 - ⟪g x, x - xstar⟫ / 2 +
        ‖g x‖ ^ 2 / (64 * L) := by
    field_simp [ne_of_gt hL]
    ring
  have hbound : ‖g x‖ ^ 2 / (64 * L) ≤ (f x - f xstar) / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * L)).mpr
    nlinarith
  nlinarith [halg]

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.SingleComponent

namespace SAGFiniteSum.Rate.SAGFresh
open SAGA.Convex
open scoped BigOperators

lemma sagStep_single {p : ℕ}
    (f' : Fin 1 → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (L : ℝ) (i : Fin 1)
    (θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (sagStep f' (1 / (16 * L)) i θ).2 = gdStep (gradAvg f') L θ.2 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [sagStep, gdStep, gradAvg]

theorem single_convex_rate {p k : ℕ}
    (f : Fin 1 → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin 1 → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (L : ℝ) (xstar : EuclideanSpace ℝ (Fin p)) (h : SAGAssumptions f f' L xstar)
    (hk : 0 < k) (θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx 1 k (fun js => fAvg f (avgIter f' (1 / (16 * L)) θ js)) - fAvg f xstar ≤
      32 / (k : ℝ) * (4 * L * ‖θ.2 - xstar‖ ^ 2) := by
  have hL := h.L_pos
  let V := fun θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) =>
    4 * L * ‖θ.2 - xstar‖ ^ 2
  have hs (θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
      (1 / ((1 : ℕ) : ℝ)) * ∑ i : Fin 1, V (sagStep f' (1 / (16 * L)) i θ) ≤
        V θ - (1 / 32 : ℝ) * (fAvg f θ.2 - fAvg f xstar) := by
    dsimp only [V]
    simp only [Fin.sum_univ_one, Nat.cast_one, div_one, one_mul]
    rw [sagStep_single]
    convert gd_distance_drift h.L_pos (avg_hasGradient h) (avg_lipschitz h)
      (avg_convex h) xstar h.minimizer θ.2 using 1
    ring
  have hr := sag_convex_rate (by decide : 0 < 1) hk f' (1 / (16 * L))
    (fAvg f) (fAvg f xstar) (avg_convex h) V (1 / 32) (by norm_num)
    (fun θ => by dsimp [V]; positivity) hs θ
  rw [expectIdx_sub, expectIdx_const (by decide : 0 < 1)] at hr
  convert hr using 1
  dsimp [V]
  ring

theorem single_geometric_rate {p k : ℕ}
    (f : Fin 1 → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin 1 → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (L : ℝ) (xstar : EuclideanSpace ℝ (Fin p)) (h : SAGAssumptions f f' L xstar)
    (μ : ℝ) (hμ : 0 < μ)
    (hc : ConvexOn ℝ Set.univ (fun x => fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    expectIdx 1 k (fun js => fAvg f (sagIter f' (1 / (16 * L)) θ js k).2) - fAvg f xstar ≤
      (1 - min (μ / (16 * L)) (1 / 8)) ^ k * (fAvg f θ.2 - fAvg f xstar) := by
  let V := fun θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) =>
    fAvg f θ.2 - fAvg f xstar
  have hq : 0 ≤ 1 - min (μ / (16 * L)) (1 / 8) := by
    have hm := min_le_right (μ / (16 * L)) (1 / 8 : ℝ)
    linarith
  have hs (θ : (Fin 1 → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
      (1 / ((1 : ℕ) : ℝ)) * ∑ i : Fin 1, V (sagStep f' (1 / (16 * L)) i θ) ≤
        (1 - min (μ / (16 * L)) (1 / 8)) * V θ := by
    dsimp only [V]
    simp only [Fin.sum_univ_one, Nat.cast_one, div_one, one_mul]
    rw [sagStep_single]
    exact gd_gap_contraction h.L_pos hμ
      (avg_hasGradient h) (avg_lipschitz h) hc xstar h.minimizer θ.2
  have hr := sag_geometric_rate f' (1 / (16 * L)) (fAvg f) (fAvg f xstar) V
    (1 - min (μ / (16 * L)) (1 / 8)) hq (fun _ => le_rfl) hs k θ
  rw [expectIdx_sub, expectIdx_const (by decide : 0 < 1)] at hr
  exact hr

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.InitialConstants

namespace SAGFiniteSum.Rate.SAGFresh
open SAGA.Convex
open scoped BigOperators
variable {p n : ℕ}
variable {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
variable {f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
variable {L : ℝ} {xstar : EuclideanSpace ℝ (Fin p)}

lemma sigmaSq_nonneg (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) : 0 ≤ sigmaSq f' x := by
  unfold sigmaSq
  positivity

lemma gap_le_C0zero (h : SAGAssumptions f f' L xstar) (x : EuclideanSpace ℝ (Fin p)) :
    fAvg f x - fAvg f xstar ≤ C0zero f f' L xstar x := by
  have hL := h.L_pos
  have hs := sigmaSq_nonneg f' xstar
  unfold C0zero
  have hdist : 0 ≤ 4 * L / (n : ℝ) * ‖x - xstar‖ ^ 2 := by positivity
  have hnoise : 0 ≤ sigmaSq f' xstar / (16 * L) := by positivity
  linarith

lemma distance_le_C0zero (h : SAGAssumptions f f' L xstar) (x : EuclideanSpace ℝ (Fin p)) :
    4 * L / (n : ℝ) * ‖x - xstar‖ ^ 2 ≤ C0zero f f' L xstar x := by
  have hL := h.L_pos
  have hs := sigmaSq_nonneg f' xstar
  have hg := h.minimizer x
  unfold C0zero
  have hnoise : 0 ≤ sigmaSq f' xstar / (16 * L) := by positivity
  linarith

lemma gap_le_C0centered (h : SAGAssumptions f f' L xstar) (x : EuclideanSpace ℝ (Fin p)) :
    fAvg f x - fAvg f xstar ≤ C0centered f L xstar x := by
  have hL := h.L_pos
  have hg := h.minimizer x
  unfold C0centered
  have hdist : 0 ≤ 4 * L / (n : ℝ) * ‖x - xstar‖ ^ 2 := by positivity
  linarith

lemma distance_le_C0centered (h : SAGAssumptions f f' L xstar) (x : EuclideanSpace ℝ (Fin p)) :
    4 * L / (n : ℝ) * ‖x - xstar‖ ^ 2 ≤ C0centered f L xstar x := by
  have hg := h.minimizer x
  unfold C0centered
  linarith

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeSingleComponent
namespace SAGFiniteSum.Rate.SAGFresh
theorem single_component_theorem {p : ℕ} (f : Fin 1 → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin 1 → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    (SAGA.Convex.expectIdx 1 k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (1 : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx 1 k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (1 : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx 1 k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (1 : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx 1 k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (1 : ℝ)))) ^ k * C0centered f L xstar x0)) := by
  have hk0 : 0 < k := hk
  constructor
  · have hr := single_convex_rate f f' L xstar hA hk0 (zeroTable, x0)
    have hc := distance_le_C0zero hA x0
    simp only [Nat.cast_one, div_one] at hc
    simpa only [one_mul, mul_one] using hr.trans
      (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 32 / (k : ℝ)))
  constructor
  · have hr := single_convex_rate f f' L xstar hA hk0 (centeredTable f' x0, x0)
    have hc := distance_le_C0centered hA x0
    simp only [Nat.cast_one, div_one] at hc
    simpa only [one_mul, mul_one] using hr.trans
      (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 32 / (k : ℝ)))
  intro μ hμ hstrong
  have hq : 0 ≤ 1 - min (μ / (16 * L)) (1 / 8) := by
    have hm := min_le_right (μ / (16 * L)) (1 / 8 : ℝ)
    linarith
  constructor
  · have hr := single_geometric_rate f f' L xstar hA μ hμ hstrong (zeroTable, x0) (k := k)
    simpa only [mul_one] using hr.trans
      (mul_le_mul_of_nonneg_left (gap_le_C0zero hA x0) (pow_nonneg hq k))
  · have hr := single_geometric_rate f f' L xstar hA μ hμ hstrong (centeredTable f' x0, x0) (k := k)
    simpa only [mul_one] using hr.trans
      (mul_le_mul_of_nonneg_left (gap_le_C0centered hA x0) (pow_nonneg hq k))

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.NativeConclusion
namespace SAGFiniteSum.Rate.SAGFresh
theorem many_component_theorem {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) (hn2 : 2 ≤ n) :
    (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0centered f L xstar x0)) := by
  have hk0 : 0 < k := hk
  constructor
  · exact (many_convex_rate hA hn2 hk0 (zeroTable, x0)).trans
      (mul_le_mul_of_nonneg_left (native_initial_zero hA hn2 x0) (by positivity))
  constructor
  · exact (many_convex_rate hA hn2 hk0 (centeredTable f' x0, x0)).trans
      (mul_le_mul_of_nonneg_left (native_initial_centered hA hn2 x0) (by positivity))
  intro μ hμ hstrong
  have hnR : (0 : ℝ) < n := by exact_mod_cast hA.n_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hA.n_pos
  have hq : 0 ≤ 1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ))) := by
    have hm := min_le_right (μ / (16 * L)) (1 / (8 * (n : ℝ)))
    have hb : 1 / (8 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  constructor
  · exact (many_geometric_rate hA hn2 μ hμ hstrong k (zeroTable, x0)).trans
      (mul_le_mul_of_nonneg_left (native_initial_zero hA hn2 x0) (pow_nonneg hq k))
  · exact (many_geometric_rate hA hn2 μ hμ hstrong k (centeredTable f' x0, x0)).trans
      (mul_le_mul_of_nonneg_left (native_initial_centered hA hn2 x0) (pow_nonneg hq k))

theorem native_theorem_1 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0centered f L xstar x0)) := by
  by_cases hn : n = 1
  · subst n
    simpa only [Nat.cast_one] using single_component_theorem f f' L xstar hA x0 k hk
  · have hn2 : 2 ≤ n := by have hp := hA.n_pos; omega
    exact many_component_theorem f f' L xstar hA x0 k hk hn2

end SAGFiniteSum.Rate.SAGFresh

-- Complete module: SAGProof.FinalRoot
open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- Theorem 1 (Schmidt, Le Roux & Bach, arXiv:1309.2388v2, p. 7). SAG with the constant step
size `α = 1/(16L)`, for `k ≥ 1`, from `(y⁰, x⁰)` with `y⁰ = 0` or `y⁰ᵢ = f'ᵢ(x⁰) − g'(x⁰)`:
`E[g(x̄ᵏ)] − g(x*) ≤ (32n/k) C₀`, and if `g` is `μ`-strongly convex,
`E[g(xᵏ)] − g(x*) ≤ (1 − min{μ/(16L), 1/(8n)})ᵏ C₀`, with the `C₀` of each initialization. -/
theorem theorem_1 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0centered f L xstar x0)) := by
  exact SAGFresh.native_theorem_1 f f' L xstar hA x0 k hk

end SAGFiniteSum.Rate


open SAGFiniteSum.Rate

theorem solution {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (zeroTable, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0zero f f' L xstar x0)
    ∧ (SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * C0centered f L xstar x0)
    ∧ (∀ μ : ℝ, 0 < μ →
        ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2) →
        (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) (zeroTable, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0zero f f' L xstar x0)
        ∧ (SAGA.Convex.expectIdx n k
            (fun js => SAGA.Convex.fAvg f
              (sagIter f' (1 / (16 * L)) (centeredTable f' x0, x0) js k).2)
            - SAGA.Convex.fAvg f xstar
          ≤ (1 - min (μ / (16 * L)) (1 / (8 * (n : ℝ)))) ^ k * C0centered f L xstar x0)) := by
  exact theorem_1 f f' L xstar hA x0 k hk
