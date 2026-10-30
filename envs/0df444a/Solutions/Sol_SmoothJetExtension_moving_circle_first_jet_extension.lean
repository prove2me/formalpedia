-- Prove2me | solution 1 for SmoothJetExtension.moving_circle_first_jet_extension
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:53:01.880076+00:00
-- url     : https://prove2.me/submissions/68bbbc8a-adfa-4afa-9e48-bb0e1455aacd

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_SmoothJetExtension_compact_first_jet_extension



namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

def circleNormalize (u : Plane) : Plane := (Real.sqrt (planeNormSq u))⁻¹ • u

def circleCutoff (u : Plane) : ℝ :=
  Real.smoothTransition (4 * planeNormSq u - 1) *
    Real.smoothTransition (4 - 2 * planeNormSq u)

lemma planeNormSq_pos {u : Plane} (hu : u ≠ 0) : 0 < planeNormSq u := by
  by_contra hn
  have h0 : u 0 = 0 := by dsimp [planeNormSq] at hn; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by dsimp [planeNormSq] at hn; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  apply hu
  ext i; fin_cases i <;> assumption

lemma planeNormSq_contDiff : ContDiff ℝ ∞ planeNormSq := by unfold planeNormSq; fun_prop

lemma circleNormalize_mem {u : Plane} (hu : u ≠ 0) : circleNormalize u ∈ unitCircle := by
  have hr := planeNormSq_pos hu
  have he : planeNormSq (circleNormalize u) = (Real.sqrt (planeNormSq u))⁻¹ ^ 2 * planeNormSq u := by
    simp [circleNormalize, planeNormSq]
    ring
  change planeNormSq (circleNormalize u) = 1
  rw [he, inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']

lemma circleNormalize_eq {u : Plane} (hu : u ∈ unitCircle) : circleNormalize u = u := by
  have he : planeNormSq u = 1 := hu
  simp [circleNormalize, he]

lemma circleNormalize_contDiffAt {u : Plane} (hu : u ≠ 0) : ContDiffAt ℝ ∞ circleNormalize u := by
  have hr := planeNormSq_pos hu
  exact ((planeNormSq_contDiff.contDiffAt.sqrt hr.ne').inv (Real.sqrt_pos.mpr hr).ne').smul contDiffAt_id

lemma circleCutoff_contDiff : ContDiff ℝ ∞ circleCutoff := by
  unfold circleCutoff
  have hsq := planeNormSq_contDiff
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  fun_prop

lemma circleCutoff_one {u : Plane} (hu : u ∈ unitCircle) : circleCutoff u = 1 := by
  have he : planeNormSq u = 1 := hu
  simp only [circleCutoff, he]
  rw [Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.one_of_one_le (by norm_num), one_mul]

lemma circleCutoff_zero_of_small {u : Plane} (hu : planeNormSq u ≤ 1 / 4) : circleCutoff u = 0 := by
  unfold circleCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma circleCutoff_zero_of_large {u : Plane} (hu : 2 ≤ planeNormSq u) : circleCutoff u = 0 := by
  unfold circleCutoff
  rw [Real.smoothTransition.zero_of_nonpos (x := 4 - 2 * planeNormSq u) (by linarith), mul_zero]

lemma circleCutoff_zero_outside (u : Plane) (hu : u ∉ Metric.closedBall (0 : Plane) 2) : circleCutoff u = 0 := by
  apply circleCutoff_zero_of_large
  by_contra hn
  have hr : planeNormSq u < 2 := lt_of_not_ge hn
  have h0 : |u 0| ≤ 2 := by
    dsimp [planeNormSq] at hr
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : |u 1| ≤ 2 := by
    dsimp [planeNormSq] at hr
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have hc : ∀ i : Fin 2, ‖u i‖ ≤ 2 := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hnorm : ‖u‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hc
  exact hu (by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)

end
end BirkhoffGlobalSection.ContactGenerator


set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma deriv_eq_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a b : F} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) (heq : EqOn f g (Icc 0 1)) : a = b := by
  apply (uniqueDiffOn_Icc_zero_one t ht).eq_deriv (Icc (0 : ℝ) 1)
    (hf.hasDerivWithinAt.congr heq.symm (heq ht).symm) hg.hasDerivWithinAt

noncomputable def circleCurve (u : Plane) (s : ℝ) : Plane :=
  Real.cos s • u + Real.sin s • circleTangent u

lemma circleCurve_zero (u : Plane) : circleCurve u 0 = u := by simp [circleCurve]

lemma circleCurve_mem (u : Plane) (hu : u ∈ unitCircle) (s : ℝ) : circleCurve u s ∈ unitCircle := by
  have he : planeNormSq (circleCurve u s) =
      (Real.cos s ^ 2 + Real.sin s ^ 2) * planeNormSq u := by
    simp only [circleCurve, circleTangent, planeNormSq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  change planeNormSq (circleCurve u s) = 1
  rw [he, Real.cos_sq_add_sin_sq, one_mul]
  exact hu

lemma circleCurve_hasDerivAt (u : Plane) : HasDerivAt (circleCurve u) (circleTangent u) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos 0).mul_const (u i)).add
    ((Real.hasDerivAt_sin 0).mul_const (circleTangent u i))
  change HasDerivAt (fun s => Real.cos s * u i + Real.sin s * circleTangent u i)
    (circleTangent u i) 0
  convert! h using 1 <;>
    simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul, zero_add]


lemma circleCurve_hasDerivAt_all (u : Plane) (s : ℝ) :
    HasDerivAt (circleCurve u) (circleTangent (circleCurve u s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos s).mul_const (u i)).add
    ((Real.hasDerivAt_sin s).mul_const (circleTangent u i))
  change HasDerivAt (fun r => Real.cos r * u i + Real.sin r * circleTangent u i)
    (circleTangent (circleCurve u s) i) s
  convert! h using 1
  fin_cases i <;> simp [circleTangent, circleCurve] <;> ring

lemma fderiv_circle_tangent_eq (f g : Plane → Phase) (u : Plane) (hu : u ∈ unitCircle)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (he : EqOn f g unitCircle) :
    fderiv ℝ f u (circleTangent u) = fderiv ℝ g u (circleTangent u) := by
  have hf' : DifferentiableAt ℝ f (circleCurve u 0) := by rwa [circleCurve_zero]
  have hg' : DifferentiableAt ℝ g (circleCurve u 0) := by rwa [circleCurve_zero]
  have hff := hf'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  have hgg := hg'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  rw [circleCurve_zero] at hff hgg
  have heq : (fun s => f (circleCurve u s)) = (fun s => g (circleCurve u s)) := by
    funext s
    exact he (circleCurve_mem u hu s)
  change HasDerivAt (fun s => f (circleCurve u s)) (fderiv ℝ f u (circleTangent u)) 0 at hff
  rw [heq] at hff
  exact hff.unique hgg

lemma isotopy_time_hasDerivAt {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    HasDerivAt (fun s => I.isotopy (s, u)) (fderiv ℝ I.isotopy (t, u) (1, 0)) t := by
  have h := (I.smooth t ht u hu).differentiableAt (by simp) |>.hasFDerivAt
  exact h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))

lemma phaseDot_self_hasDerivAt {q : ℝ → Phase} {V : Phase} {t : ℝ}
    (h : HasDerivAt q V t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) V) t := by
  have hd := fun i => hasDerivAt_pi.mp h i
  have he := ((((hd 0).mul (hd 0)).add ((hd 1).mul (hd 1))).add
    ((hd 2).mul (hd 2))).add ((hd 3).mul (hd 3))
  apply he.congr_deriv
  simp only [phaseDot]
  ring

lemma isotopy_velocity_tangent {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    phaseDot (I.isotopy (t, u)) (fderiv ℝ I.isotopy (t, u) (1, 0)) = 0 := by
  have hd := phaseDot_self_hasDerivAt (isotopy_time_hasDerivAt I t ht u hu)
  have heq : EqOn (fun s => phaseDot (I.isotopy (s, u)) (I.isotopy (s, u)))
      (fun _ => (1 : ℝ)) (Icc (0 : ℝ) 1) := by
    intro s hs
    have he := I.sphere s hs u hu
    simpa [unitThreeSphere, zNormSq, wNormSq, phaseDot, pow_two, add_assoc] using he
  have hz := deriv_eq_of_eqOn_Icc ht hd (hasDerivAt_const t (1 : ℝ)) heq
  linarith

lemma isotopy_velocity_antipodal {K : Set Phase} (I : EquivariantTransverseHopfIsotopy K)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ I.isotopy (t, -u) (1, 0) = - fderiv ℝ I.isotopy (t, u) (1, 0) := by
  have hnu : -u ∈ unitCircle := by simpa [unitCircle, planeNormSq] using hu
  exact deriv_eq_of_eqOn_Icc ht (isotopy_time_hasDerivAt I t ht (-u) hnu)
    (isotopy_time_hasDerivAt I t ht u hu).neg (fun s hs => I.antipodal s hs u hu)

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Complex
open scoped ContDiff Topology
noncomputable section

def planeComplex (u : Plane) : ℂ := ⟨u 0, u 1⟩

def circleAngle (u v : Plane) : ℝ := Complex.arg (star (planeComplex u) * planeComplex v)

lemma planeComplex_continuous : Continuous planeComplex := by
  unfold planeComplex
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

lemma planeComplex_norm {u : Plane} (hu : u ∈ unitCircle) : ‖planeComplex u‖ = 1 := by
  have hs : ‖planeComplex u‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [unitCircle, planeNormSq, planeComplex, Complex.normSq_apply, pow_two] using hu
  nlinarith [norm_nonneg (planeComplex u)]

lemma planeComplex_mul_star {u : Plane} (hu : u ∈ unitCircle) :
    planeComplex u * star (planeComplex u) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, planeComplex_norm hu]
  norm_num

lemma planeComplex_circleCurve (u : Plane) (s : ℝ) :
    planeComplex (circleCurve u s) = planeComplex u * Complex.exp ((s : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp [planeComplex, circleCurve, circleTangent, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

lemma circleCurve_angle {u v : Plane} (hu : u ∈ unitCircle) (hv : v ∈ unitCircle) :
    circleCurve u (circleAngle u v) = v := by
  have hn : ‖star (planeComplex u) * planeComplex v‖ = 1 := by
    simp [norm_mul, planeComplex_norm hu, planeComplex_norm hv]
  have he := Complex.norm_mul_exp_arg_mul_I (star (planeComplex u) * planeComplex v)
  rw [hn, Complex.ofReal_one, one_mul] at he
  have hcv : planeComplex (circleCurve u (circleAngle u v)) = planeComplex v := by
    rw [planeComplex_circleCurve]
    change planeComplex u * Complex.exp ((Complex.arg (star (planeComplex u) * planeComplex v) : ℂ) * Complex.I) = _
    rw [he, ← mul_assoc, planeComplex_mul_star hu, one_mul]
  ext i
  fin_cases i
  · exact congrArg Complex.re hcv
  · exact congrArg Complex.im hcv

lemma circleAngle_self {u : Plane} (hu : u ∈ unitCircle) : circleAngle u u = 0 := by
  have he : star (planeComplex u) * planeComplex u = 1 := by
    rw [mul_comm, planeComplex_mul_star hu]
  simp only [circleAngle, he, Complex.arg_one]

lemma circleAngle_continuousAt {u : Plane} (hu : u ∈ unitCircle) : ContinuousAt (circleAngle u) u := by
  have he : star (planeComplex u) * planeComplex u = 1 := by
    rw [mul_comm, planeComplex_mul_star hu]
  have hm : star (planeComplex u) * planeComplex u ∈ Complex.slitPlane := by
    rw [he]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  exact (Complex.continuousAt_arg hm).comp
    (f := fun v => star (planeComplex u) * planeComplex v)
    (continuous_const.mul planeComplex_continuous).continuousAt

end
end BirkhoffGlobalSection.ContactGenerator


open Set Function
open scoped ContDiff
namespace SmoothJetExtension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth finite-dimensional immersion has a smooth local left inverse.
The inverse-function theorem is applied after a fixed linear left inverse of
its derivative; no global tubular-neighborhood theorem is assumed. -/
lemma exists_smooth_local_leftInverse (f : E → F) (hf : ContDiff ℝ ∞ f)
    (a : E) (hinj : Injective (fderiv ℝ f a))
    (W : Set E) (hW : IsOpen W) (haW : a ∈ W) :
    ∃ (r : F → E) (U : Set E) (V : Set F),
      IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧ IsOpen V ∧ f a ∈ V ∧ ContDiffOn ℝ ∞ r V ∧
      MapsTo r V U ∧
      ∀ x ∈ U, f x ∈ V ∧ r (f x) = x := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  let g : E → E := L ∘ f
  have hg : ContDiff ℝ ∞ g := L.contDiff.comp hf
  have hD : fderiv ℝ g a = ContinuousLinearMap.id ℝ E := by
    have hd := L.hasFDerivAt.comp a (hf.differentiable (by simp) a).hasFDerivAt
    rw [hd.fderiv]
    ext v
    exact hL v
  have hd0 : HasFDerivAt g ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) a := by
    simpa only [ContinuousLinearEquiv.coe_refl, hD] using (hg.differentiable (by simp) a).hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd0 (by simp)
  have he₀ : (e₀ : E → E) = g := hg.contDiffAt.toOpenPartialHomeomorph_coe hd0 (by simp)
  let N : Set E := {x | IsUnit (fderiv ℝ g x)} ∩ W
  have hDc : Continuous (fderiv ℝ g) := (hg.fderiv_right (m := ∞) (by simp)).continuous
  have hNo : IsOpen N := (Units.isOpen.preimage hDc).inter hW
  have haN : a ∈ N := by
    refine ⟨?_, haW⟩
    change IsUnit (fderiv ℝ g a)
    rw [hD]
    exact isUnit_one
  let e := e₀.restrOpen N hNo
  have he : (e : E → E) = g := by simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using he₀
  have hae : a ∈ e.source := ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd0 (by simp), haN⟩
  let V : Set F := L ⁻¹' e.target
  let r : F → E := e.symm ∘ L
  refine ⟨r, e.source, V, e.open_source, hae, (fun x hx => hx.2.2),
    e.open_target.preimage L.continuous, ?_, ?_, (fun q hq => e.map_target hq), ?_⟩
  · change L (f a) ∈ e.target
    change g a ∈ e.target
    rw [← he]
    exact e.map_source hae
  · intro q hq
    have hxe : e.symm (L q) ∈ e.source := e.map_target hq
    have hxN : e.symm (L q) ∈ N := hxe.2
    have hj : Bijective (fderiv ℝ g (e.symm (L q))) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hxN.1
    let A : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (fderiv ℝ g (e.symm (L q))).toLinearMap hj).toContinuousLinearEquiv
    have hA : (A : E →L[ℝ] E) = fderiv ℝ g (e.symm (L q)) := by ext v; rfl
    have hgd : HasFDerivAt (e : E → E) (A : E →L[ℝ] E) (e.symm (L q)) := by
      rw [he, hA]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    have hgc : ContDiffAt ℝ ∞ (e : E → E) (e.symm (L q)) := by rw [he]; exact hg.contDiffAt
    exact ((e.contDiffAt_symm hq hgd hgc).comp q L.contDiff.contDiffAt).contDiffWithinAt
  · intro x hx
    have hfx : L (f x) ∈ e.target := by
      change g x ∈ e.target
      rw [← he]
      exact e.map_source hx
    refine ⟨hfx, ?_⟩
    change e.symm (g x) = x
    rw [← he]
    exact e.left_inv hx

end SmoothJetExtension


open scoped ContDiff
namespace SmoothJetExtension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend a compatible first jet along a parametrized submanifold by a smooth
local retraction. This is the affine-in-normal-directions construction. -/
lemma affine_extension_hasFDerivAt
    (f : E → F) (h : E → ℝ) (L : E → (F →L[ℝ] ℝ)) (r : F → E)
    (p : E) (hrp : r (f p) = p)
    (f' : E →L[ℝ] F) (L' : E →L[ℝ] (F →L[ℝ] ℝ)) (r' : F →L[ℝ] E)
    (hf : HasFDerivAt f f' p) (hL : HasFDerivAt L L' p)
    (hh : HasFDerivAt h ((L p).comp f') p)
    (hr : HasFDerivAt r r' (f p)) :
    HasFDerivAt (fun q => h (r q) + L (r q) (q - f (r q))) (L p) (f p) := by
  have hf' : HasFDerivAt f f' (r (f p)) := by rwa [hrp]
  have hL' : HasFDerivAt L L' (r (f p)) := by rwa [hrp]
  have hh' : HasFDerivAt h ((L p).comp f') (r (f p)) := by rwa [hrp]
  have hd := (hasFDerivAt_id (f p)).sub (hf'.comp (f p) hr)
  have hc := (hh'.comp (f p) hr).add ((hL'.comp (f p) hr).clm_apply hd)
  apply hc.congr_fderiv
  ext v
  simp [hrp, ContinuousLinearMap.comp_apply]

lemma affine_extension_contDiffAt
    (f : E → F) (h : E → ℝ) (L : E → (F →L[ℝ] ℝ)) (r : F → E)
    (q : F) (hf : ContDiffAt ℝ ∞ f (r q)) (hh : ContDiffAt ℝ ∞ h (r q))
    (hL : ContDiffAt ℝ ∞ L (r q)) (hr : ContDiffAt ℝ ∞ r q) :
    ContDiffAt ℝ ∞ (fun q => h (r q) + L (r q) (q - f (r q))) q := by
  exact (hh.comp q hr).add ((hL.comp q hr).clm_apply
    (contDiffAt_id.sub (hf.comp q hr)))

end SmoothJetExtension


open Set
namespace SmoothJetExtension
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- Near the image of one point, a compact injective parametrization has no
contributions from parameters outside a specified neighborhood of that point. -/
lemma compact_injective_localization (A : Set X) (hA : IsCompact A)
    (f : X → Y) (hf : ContinuousOn f A) (hinj : InjOn f A)
    (p : X) (hp : p ∈ A) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ V : Set Y, IsOpen V ∧ f p ∈ V ∧ ∀ q ∈ A, f q ∈ V → q ∈ O := by
  let B := A ∩ Oᶜ
  have hB : IsCompact B := hA.inter_right hO.isClosed_compl
  have hFB : IsCompact (f '' B) := hB.image_of_continuousOn (hf.mono inter_subset_left)
  refine ⟨(f '' B)ᶜ, hFB.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨q, hq, he⟩
    have hqp := hinj hq.1 hp he
    exact hq.2 (hqp ▸ hpO)
  · intro q hq hqV
    by_contra hn
    exact hqV ⟨q, ⟨hq, hn⟩, rfl⟩

end SmoothJetExtension

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section

def circleCylinder : Set (ℝ × Plane) := Icc (0 : ℝ) 1 ×ˢ unitCircle

def circleWorld (k : ℝ × Plane → Phase) (p : ℝ × Plane) : ℝ × Phase := (p.1, k p)

def curveParam (u : Plane) (z : ℝ × ℝ) : ℝ × Plane := (z.1, circleCurve u z.2)

def curveWorld (k : ℝ × Plane → Phase) (u : Plane) (z : ℝ × ℝ) : ℝ × Phase :=
  circleWorld k (curveParam u z)

lemma circleCurve_contDiff (u : Plane) : ContDiff ℝ ∞ (circleCurve u) := by
  unfold circleCurve
  fun_prop

lemma curveParam_contDiff (u : Plane) : ContDiff ℝ ∞ (curveParam u) :=
  contDiff_fst.prodMk ((circleCurve_contDiff u).comp contDiff_snd)

lemma curveParam_fderiv_apply (u : Plane) (z v : ℝ × ℝ) :
    fderiv ℝ (curveParam u) z v = (v.1, v.2 • circleTangent (circleCurve u z.2)) := by
  have hd := (hasFDerivAt_fst (p := z)).prodMk
    ((circleCurve_hasDerivAt_all u z.2).hasFDerivAt.comp z (hasFDerivAt_snd (p := z)))
  change fderiv ℝ (fun z : ℝ × ℝ => (z.1, (circleCurve u ∘ Prod.snd) z)) z v = _
  rw [hd.fderiv]
  rfl

lemma curveWorld_contDiff (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k) (u : Plane) :
    ContDiff ℝ ∞ (curveWorld k u) :=
  contDiff_fst.prodMk (hk.comp (curveParam_contDiff u))

lemma curveWorld_fderiv_apply (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (u : Plane) (z v : ℝ × ℝ) :
    fderiv ℝ (curveWorld k u) z v =
      (v.1, fderiv ℝ k (curveParam u z) (v.1, v.2 • circleTangent (circleCurve u z.2))) := by
  have hd := (hasFDerivAt_fst (p := z)).prodMk
    ((hk.differentiable (by simp) (curveParam u z)).hasFDerivAt.comp z
      ((curveParam_contDiff u).differentiable (by simp) z).hasFDerivAt)
  change fderiv ℝ (fun z : ℝ × ℝ => (z.1, (k ∘ curveParam u) z)) z v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, curveParam_fderiv_apply]
  rfl

lemma curveWorld_derivative_injective (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (u : Plane) (t : ℝ) (hreg : fderiv ℝ k (t, u) (0, circleTangent u) ≠ 0) :
    Injective (fderiv ℝ (curveWorld k u) (t, 0)) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨a, b⟩ he
  rw [curveWorld_fderiv_apply k hk] at he
  simp only [curveParam, circleCurve_zero] at he
  have ha : a = 0 := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  rw [ha] at hb
  have heq : (0, b • circleTangent u) = b • ((0, circleTangent u) : ℝ × Plane) := by simp
  rw [heq, map_smul] at hb
  have hb0 : b = 0 := (smul_eq_zero.mp hb).resolve_right hreg
  exact Prod.ext ha hb0

lemma curveWorld_jet_compatible
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (h : ℝ × Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ))
    (hcomp : ∀ p ∈ circleCylinder, ∀ a b : ℝ,
      fderiv ℝ h p (a, b • circleTangent p.2) =
        L p (a, fderiv ℝ k p (a, b • circleTangent p.2)))
    (u : Plane) (z : ℝ × ℝ) (hz : curveParam u z ∈ circleCylinder) :
    fderiv ℝ (h ∘ curveParam u) z =
      (L (curveParam u z)).comp (fderiv ℝ (curveWorld k u) z) := by
  rw [fderiv_comp z (hh.differentiable (by simp) _) ((curveParam_contDiff u).differentiable (by simp) z)]
  apply ContinuousLinearMap.ext
  rintro ⟨a, b⟩
  simp only [ContinuousLinearMap.comp_apply, curveParam_fderiv_apply, curveWorld_fderiv_apply k hk]
  exact hcomp (curveParam u z) hz a b

end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Filter Function
open scoped ContDiff Topology
noncomputable section

lemma unitCircle_compact : IsCompact unitCircle := by
  have hc : IsClosed unitCircle := isClosed_eq planeNormSq_contDiff.continuous continuous_const
  apply (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hc
  intro u hu
  have he : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
  have h0 : |u 0| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : |u 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have hi : ∀ i : Fin 2, ‖u i‖ ≤ 1 := by intro i; fin_cases i <;> assumption
  have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hi
  simpa [Metric.mem_closedBall, dist_zero_right] using hn

lemma worldsheet_local_first_jet
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hinj : InjOn (circleWorld k) circleCylinder)
    (hreg : ∀ p ∈ circleCylinder, fderiv ℝ k p (0, circleTangent p.2) ≠ 0)
    (h : ℝ × Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ))
    (P : Set (ℝ × Plane)) (hPo : IsOpen P) (hAP : circleCylinder ⊆ P)
    (hL : ContDiffOn ℝ ∞ L P)
    (hcomp : ∀ p ∈ circleCylinder, ∀ a b : ℝ,
      fderiv ℝ h p (a, b • circleTangent p.2) =
        L p (a, fderiv ℝ k p (a, b • circleTangent p.2)))
    (p₀ : ℝ × Plane) (hp₀ : p₀ ∈ circleCylinder) :
    ∃ V : Set (ℝ × Phase), IsOpen V ∧ circleWorld k p₀ ∈ V ∧
      ∃ H : ℝ × Phase → ℝ, ContDiffOn ℝ ∞ H V ∧
        ∀ p ∈ circleCylinder, circleWorld k p ∈ V →
          H (circleWorld k p) = h p ∧ fderiv ℝ H (circleWorld k p) = L p := by
  let f := curveWorld k p₀.2
  let a₀ : ℝ × ℝ := (p₀.1, 0)
  let W := curveParam p₀.2 ⁻¹' P
  have hW : IsOpen W := hPo.preimage (curveParam_contDiff p₀.2).continuous
  have haW : a₀ ∈ W := by simpa [W, a₀, curveParam, circleCurve_zero] using hAP hp₀
  obtain ⟨r, U, V, hUo, haU, hUW, hVo, hfaV, hr, hrVU, hleft⟩ :=
    SmoothJetExtension.exists_smooth_local_leftInverse f (curveWorld_contDiff k hk p₀.2)
      a₀ (curveWorld_derivative_injective k hk p₀.2 p₀.1 (hreg p₀ hp₀)) W hW haW
  let π : ℝ × Plane → ℝ × ℝ := fun p => (p.1, circleAngle p₀.2 p.2)
  have hπ : ContinuousAt π p₀ :=
    continuousAt_fst.prodMk ((circleAngle_continuousAt hp₀.2).comp continuousAt_snd)
  have hπ₀ : π p₀ = a₀ := by simp [π, a₀, circleAngle_self hp₀.2]
  have hπU : π ⁻¹' U ∈ 𝓝 p₀ := hπ.preimage_mem_nhds (by rw [hπ₀]; exact hUo.mem_nhds haU)
  obtain ⟨O, hOU, hOo, hpO⟩ := mem_nhds_iff.mp hπU
  have hA : IsCompact circleCylinder := isCompact_Icc.prod unitCircle_compact
  have hF : Continuous (circleWorld k) := continuous_fst.prodMk hk.continuous
  obtain ⟨B, hBo, hpB, hB⟩ := SmoothJetExtension.compact_injective_localization
    circleCylinder hA (circleWorld k) hF.continuousOn hinj p₀ hp₀ O hOo hpO
  have hfa₀ : f a₀ = circleWorld k p₀ := by simp [f, a₀, curveWorld, curveParam, circleCurve_zero, circleWorld]
  let H : ℝ × Phase → ℝ := fun q => h (curveParam p₀.2 (r q)) +
    L (curveParam p₀.2 (r q)) (q - f (r q))
  have hHr : ContDiffOn ℝ ∞ H V := by
    intro q hq
    have hrq : ContDiffAt ℝ ∞ r q := hr.contDiffAt (hVo.mem_nhds hq)
    have hpP : curveParam p₀.2 (r q) ∈ P := hUW (hrVU hq)
    have hLq : ContDiffAt ℝ ∞ (L ∘ curveParam p₀.2) (r q) :=
      (hL.contDiffAt (hPo.mem_nhds hpP)).comp _ (curveParam_contDiff p₀.2).contDiffAt
    exact (SmoothJetExtension.affine_extension_contDiffAt f (h ∘ curveParam p₀.2)
      (L ∘ curveParam p₀.2) r q (curveWorld_contDiff k hk p₀.2).contDiffAt
      (hh.comp (curveParam_contDiff p₀.2)).contDiffAt hLq hrq).contDiffWithinAt
  refine ⟨V ∩ B, hVo.inter hBo, ⟨by rwa [← hfa₀], hpB⟩, H, hHr.mono inter_subset_left, ?_⟩
  intro p hp hq
  have hpO' := hB p hp hq.2
  have ha : π p ∈ U := hOU hpO'
  have hcurve : curveParam p₀.2 (π p) = p := by
    rcases p with ⟨t, u⟩
    dsimp [curveParam, π]
    rw [circleCurve_angle hp₀.2 hp.2]
  have hfa : f (π p) = circleWorld k p := by dsimp [f, curveWorld]; rw [hcurve]
  have hra : r (f (π p)) = π p := (hleft (π p) ha).2
  have hpP : curveParam p₀.2 (π p) ∈ P := hUW ha
  have hLpa : ContDiffAt ℝ ∞ (L ∘ curveParam p₀.2) (π p) :=
    (hL.contDiffAt (hPo.mem_nhds hpP)).comp _ (curveParam_contDiff p₀.2).contDiffAt
  have hha : HasFDerivAt (h ∘ curveParam p₀.2)
      ((L (curveParam p₀.2 (π p))).comp (fderiv ℝ f (π p))) (π p) := by
    rw [← curveWorld_jet_compatible k hk h hh L hcomp p₀.2 (π p) (by rwa [hcurve])]
    exact ((hh.comp (curveParam_contDiff p₀.2)).differentiable (by simp) _).hasFDerivAt
  have hd := SmoothJetExtension.affine_extension_hasFDerivAt f (h ∘ curveParam p₀.2)
    (L ∘ curveParam p₀.2) r (π p) hra _ _ _
    ((curveWorld_contDiff k hk p₀.2).differentiable (by simp) _).hasFDerivAt
    (hLpa.differentiableAt (by simp)).hasFDerivAt hha
    ((hr.contDiffAt (hVo.mem_nhds ((hleft (π p) ha).1))).differentiableAt (by simp)).hasFDerivAt
  constructor
  · change h (curveParam p₀.2 (r (circleWorld k p))) +
      L (curveParam p₀.2 (r (circleWorld k p))) (circleWorld k p - f (r (circleWorld k p))) = _
    rw [← hfa, hra, sub_self, map_zero, add_zero, hcurve]
  · simpa only [H, Function.comp_apply, hfa, hcurve] using hd.fderiv

end
end BirkhoffGlobalSection.ContactGenerator
namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section

lemma worldsheet_compact_first_jet
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hinj : InjOn (circleWorld k) circleCylinder)
    (hreg : ∀ p ∈ circleCylinder, fderiv ℝ k p (0, circleTangent p.2) ≠ 0)
    (h : ℝ × Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ))
    (P : Set (ℝ × Plane)) (hPo : IsOpen P) (hAP : circleCylinder ⊆ P)
    (hL : ContDiffOn ℝ ∞ L P)
    (hcomp : ∀ p ∈ circleCylinder, ∀ a b : ℝ,
      fderiv ℝ h p (a, b • circleTangent p.2) =
        L p (a, fderiv ℝ k p (a, b • circleTangent p.2))) :
    ∃ H : ℝ × Phase → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ circleCylinder, H (circleWorld k p) = h p ∧ fderiv ℝ H (circleWorld k p) = L p := by
  classical
  let F : circleCylinder → ℝ × Phase := fun p => circleWorld k p
  have hFi : Injective F := by
    intro p q he
    exact Subtype.ext (hinj p.2 q.2 he)
  let h₀ : ℝ × Phase → ℝ := Function.extend F (fun p => h p) (fun _ => 0)
  let L₀ : ℝ × Phase → ((ℝ × Phase) →L[ℝ] ℝ) := Function.extend F (fun p => L p) (fun _ => 0)
  have hh₀ : ∀ p ∈ circleCylinder, h₀ (circleWorld k p) = h p := fun p hp =>
    hFi.extend_apply (fun p => h p) (fun _ => 0) ⟨p, hp⟩
  have hL₀ : ∀ p ∈ circleCylinder, L₀ (circleWorld k p) = L p := fun p hp =>
    hFi.extend_apply (fun p => L p) (fun _ => 0) ⟨p, hp⟩
  let C := circleWorld k '' circleCylinder
  have hC : IsCompact C := (isCompact_Icc.prod unitCircle_compact).image
    (continuous_fst.prodMk hk.continuous)
  have hlocal : ∀ q ∈ C, ∃ V : Set (ℝ × Phase), IsOpen V ∧ q ∈ V ∧
      ∃ H : ℝ × Phase → ℝ, ContDiffOn ℝ ∞ H V ∧
        ∀ r ∈ C ∩ V, H r = h₀ r ∧ fderiv ℝ H r = L₀ r := by
    rintro q ⟨p, hp, rfl⟩
    obtain ⟨V, hVo, hpV, H, hH, hHjet⟩ :=
      worldsheet_local_first_jet k hk hinj hreg h hh L P hPo hAP hL hcomp p hp
    refine ⟨V, hVo, hpV, H, hH, ?_⟩
    rintro r ⟨⟨p', hp', rfl⟩, hrV⟩
    have he := hHjet p' hp' hrV
    exact ⟨he.1.trans (hh₀ p' hp').symm, he.2.trans (hL₀ p' hp').symm⟩
  obtain ⟨H, hH, hHc, hjet⟩ := SmoothJetExtension.compact_first_jet_extension C hC h₀ L₀ hlocal
  refine ⟨H, hH, hHc, ?_⟩
  intro p hp
  have he := hjet (circleWorld k p) ⟨p, hp, rfl⟩
  exact ⟨he.1.trans (hh₀ p hp), he.2.trans (hL₀ p hp)⟩

end
end BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set Function
open scoped ContDiff
theorem solution
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hinj : InjOn ((fun p : ℝ × Plane => (p.1, k p))) (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0, circleTangent p.2) ≠ 0)
    (h : ℝ × Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ × Plane → ((ℝ × Phase) →L[ℝ] ℝ))
    (P : Set (ℝ × Plane)) (hPo : IsOpen P) (hAP : (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle) ⊆ P)
    (hL : ContDiffOn ℝ ∞ L P)
    (hcomp : ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), ∀ a b : ℝ,
      fderiv ℝ h p (a, b • circleTangent p.2) =
        L p (a, fderiv ℝ k p (a, b • circleTangent p.2))) :
    ∃ H : ℝ × Phase → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ (Set.Icc (0 : ℝ) 1 ×ˢ unitCircle), H ((fun p : ℝ × Plane => (p.1, k p)) p) = h p ∧ fderiv ℝ H ((fun p : ℝ × Plane => (p.1, k p)) p) = L p := by
  simpa only [BirkhoffGlobalSection.ContactGenerator.circleWorld,
    BirkhoffGlobalSection.ContactGenerator.circleCylinder] using
    BirkhoffGlobalSection.ContactGenerator.worldsheet_compact_first_jet k hk hinj hreg h hh L P hPo hAP hL hcomp
