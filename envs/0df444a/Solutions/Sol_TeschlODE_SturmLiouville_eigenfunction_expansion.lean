-- Prove2me | solution 1 for TeschlODE.SturmLiouville.eigenfunction_expansion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T23:20:44.613677+00:00
-- url     : https://prove2.me/submissions/a0ad8933-fec5-489d-9d88-2d48c0bafe2f

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_RegularSL
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLDomain
import Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction
import Definitions.Def_TeschlODE_SturmLiouville_SLInner

-- BEGIN COMPLETE MODULE WeightedFunctions
section

noncomputable section

namespace TeschlODE.SturmLiouville.Proof

structure IntervalWeight where
  a : ℝ
  b : ℝ
  lt : a < b
  weight : ℝ → ℝ
  continuous : ContinuousOn weight (Set.Icc a b)
  positive : ∀x∈Set.Icc a b, 0 < weight x

namespace IntervalWeight
variable (W : IntervalWeight)

def Space := C(Set.Icc W.a W.b, ℂ)

instance : AddCommGroup W.Space := inferInstanceAs (AddCommGroup C(Set.Icc W.a W.b, ℂ))
instance : Module ℂ W.Space := inferInstanceAs (Module ℂ C(Set.Icc W.a W.b, ℂ))

def toContinuous (f : W.Space) : C(Set.Icc W.a W.b, ℂ) := f

def extend (f : W.Space) (x : ℝ) : ℂ :=
  W.toContinuous f (Set.projIcc W.a W.b W.lt.le x)

lemma extend_continuous (f : W.Space) : Continuous (W.extend f) :=
  (W.toContinuous f).continuous.comp continuous_projIcc

lemma extend_eq (f : W.Space) {x : ℝ} (hx : x∈Set.Icc W.a W.b) :
    W.extend f x = W.toContinuous f ⟨x,hx⟩ := by rw [extend, Set.projIcc_of_mem W.lt.le hx]

@[ext] lemma space_ext {f g : W.Space} (h : ∀x∈Set.Icc W.a W.b, W.extend f x = W.extend g x) : f=g := by
  apply ContinuousMap.ext
  intro x
  change W.toContinuous f x = W.toContinuous g x
  simpa only [W.extend_eq _ x.property] using h x x.property

@[simp] lemma extend_zero (x : ℝ) : W.extend 0 x = 0 := rfl
@[simp] lemma extend_add (f g : W.Space) (x : ℝ) : W.extend (f+g) x = W.extend f x + W.extend g x := rfl
@[simp] lemma extend_neg (f : W.Space) (x : ℝ) : W.extend (-f) x = -W.extend f x := rfl
@[simp] lemma extend_sub (f g : W.Space) (x : ℝ) : W.extend (f-g) x = W.extend f x - W.extend g x := rfl
@[simp] lemma extend_smul (c : ℂ) (f : W.Space) (x : ℝ) : W.extend (c•f) x = c * W.extend f x := rfl

def restrict (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc W.a W.b)) : W.Space :=
  ⟨fun x => f x, hf.domRestrict⟩

lemma extend_restrict (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc W.a W.b))
    {x : ℝ} (hx : x∈Set.Icc W.a W.b) : W.extend (W.restrict f hf) x = f x := by
  rw [extend_eq _ _ hx]
  rfl

noncomputable def scalar (f g : W.Space) : ℂ :=
  SLInner W.weight W.a W.b (W.extend f) (W.extend g)

lemma scalar_integrable (f g : W.Space) :
    IntervalIntegrable (fun x => starRingEnd ℂ (W.extend f x) * W.extend g x * (W.weight x : ℂ))
      MeasureTheory.volume W.a W.b := by
  apply ContinuousOn.intervalIntegrable_of_Icc W.lt.le
  exact ((W.extend_continuous f).star.continuousOn.mul (W.extend_continuous g).continuousOn).mul
    (Complex.continuous_ofReal.comp_continuousOn W.continuous)

end IntervalWeight
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE WeightedFunctions

-- BEGIN COMPLETE MODULE WeightedScalar
section

open MeasureTheory
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

lemma scalar_conj (f g : W.Space) : starRingEnd ℂ (W.scalar g f) = W.scalar f g := by
  unfold scalar SLInner
  rw [intervalIntegral.integral_of_le W.lt.le, intervalIntegral.integral_of_le W.lt.le,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ring

lemma scalar_add (f g h : W.Space) : W.scalar (f+g) h = W.scalar f h + W.scalar g h := by
  unfold scalar SLInner
  simp only [extend_add, map_add, add_mul]
  exact intervalIntegral.integral_add (W.scalar_integrable f h) (W.scalar_integrable g h)

lemma scalar_smul (f g : W.Space) (c : ℂ) : W.scalar (c•f) g = starRingEnd ℂ c * W.scalar f g := by
  unfold scalar SLInner
  simp only [extend_smul, map_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

lemma self_integrand (z : ℂ) (r : ℝ) :
    (starRingEnd ℂ z * z * (r:ℂ)).re = ‖z‖^2 * r := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, neg_mul, sub_neg_eq_add,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

lemma scalar_self_re (f : W.Space) :
    (W.scalar f f).re = ∫x in W.a..W.b, ‖W.extend f x‖^2 * W.weight x := by
  unfold scalar SLInner
  rw [intervalIntegral.integral_of_le W.lt.le, intervalIntegral.integral_of_le W.lt.le]
  calc
    _ = ∫ x in Set.Ioc W.a W.b,
        (starRingEnd ℂ (W.extend f x) * W.extend f x * (W.weight x : ℂ)).re :=
      (integral_re (W.scalar_integrable f f).1).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact self_integrand _ _

lemma self_continuous (f : W.Space) :
    ContinuousOn (fun x => ‖W.extend f x‖^2 * W.weight x) (Set.Icc W.a W.b) :=
  ((W.extend_continuous f).norm.pow 2).continuousOn.mul W.continuous

lemma scalar_nonneg (f : W.Space) : 0 ≤ (W.scalar f f).re := by
  rw [scalar_self_re]
  apply intervalIntegral.integral_nonneg W.lt.le
  intro x hx
  exact mul_nonneg (sq_nonneg _) (W.positive x hx).le

lemma scalar_definite (f : W.Space) (hf : W.scalar f f = 0) : f=0 := by
  have hi : ∫x in W.a..W.b, ‖W.extend f x‖^2 * W.weight x = 0 := by
    rw [← scalar_self_re, hf]; rfl
  have hnon : 0 ≤ᵐ[volume.restrict (Set.Ioc W.a W.b)]
      (fun x => ‖W.extend f x‖^2 * W.weight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (sq_nonneg _) (W.positive x (Set.Ioc_subset_Icc_self hx)).le
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae W.lt.le hnon
    ((W.self_continuous f).intervalIntegrable_of_Icc W.lt.le)).mp hi
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
  have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume W.lt.ne hae (W.self_continuous f) continuousOn_const
  apply W.space_ext
  intro x hx
  have hz := heq hx
  have hp := W.positive x hx
  change ‖W.extend f x‖^2 * W.weight x = 0 at hz
  have hs : ‖W.extend f x‖^2 = 0 := (mul_eq_zero.mp hz).resolve_right hp.ne'
  have hn : ‖W.extend f x‖=0 := by nlinarith [norm_nonneg (W.extend f x)]
  simpa only [extend_zero] using norm_eq_zero.mp hn

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedScalar

-- BEGIN COMPLETE MODULE WeightedSpace
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

@[instance_reducible] def innerCore : InnerProductSpace.Core ℂ W.Space where
  inner := W.scalar
  conj_inner_symm := W.scalar_conj
  re_inner_nonneg := W.scalar_nonneg
  add_left := W.scalar_add
  smul_left := W.scalar_smul
  definite := W.scalar_definite

instance : NormedAddCommGroup W.Space := W.innerCore.toNormedAddCommGroup
instance : InnerProductSpace ℂ W.Space := InnerProductSpace.ofCore W.innerCore.toCore

lemma inner_eq (f g : W.Space) : inner ℂ f g = W.scalar f g := rfl

lemma norm_sq_eq (f : W.Space) : ‖f‖^2 = ∫ x in W.a..W.b, ‖W.extend f x‖^2 * W.weight x := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact W.scalar_self_re f

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedSpace

-- BEGIN COMPLETE MODULE WeightedUniform
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

 def mass : ℝ := ∫x in W.a..W.b, W.weight x

lemma mass_pos : 0 < W.mass := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (W.continuous.intervalIntegrable_of_Icc W.lt.le) _ W.lt
  intro x hx
  exact W.positive x (Set.Ioo_subset_Icc_self hx)

lemma norm_sq_le_uniform (f : W.Space) : ‖f‖^2 ≤ ‖W.toContinuous f‖^2 * W.mass := by
  rw [W.norm_sq_eq, mass, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on W.lt.le
    ((W.self_continuous f).intervalIntegrable_of_Icc W.lt.le)
    ((continuousOn_const.mul W.continuous).intervalIntegrable_of_Icc W.lt.le)
  intro x hx
  apply mul_le_mul_of_nonneg_right _ (W.positive x hx).le
  have hb := (W.toContinuous f).norm_coe_le_norm ⟨x,hx⟩
  rw [W.extend_eq f hx]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

lemma norm_le_uniform (f : W.Space) : ‖f‖ ≤ Real.sqrt W.mass * ‖W.toContinuous f‖ := by
  have hb := W.norm_sq_le_uniform f
  have hm := Real.sq_sqrt W.mass_pos.le
  have hs := Real.sqrt_nonneg W.mass
  have hn := norm_nonneg f
  have hc := norm_nonneg (W.toContinuous f)
  have he : (Real.sqrt W.mass * ‖W.toContinuous f‖)^2 = ‖W.toContinuous f‖^2 * W.mass := by rw [mul_pow, hm]; ring
  exact (sq_le_sq₀ hn (mul_nonneg hs hc)).mp (hb.trans_eq he.symm)

def uniformToWeighted : C(Set.Icc W.a W.b, ℂ) →L[ℂ] W.Space :=
  ({ toFun := fun f => f
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : C(Set.Icc W.a W.b, ℂ) →ₗ[ℂ] W.Space).mkContinuous
    (Real.sqrt W.mass) (fun f => W.norm_le_uniform f)

@[simp] lemma uniformToWeighted_apply (f : C(Set.Icc W.a W.b, ℂ)) :
    W.uniformToWeighted f = (f : W.Space) := rfl

lemma weighted_tendsto_of_uniform {ι : Type*} {l : Filter ι}
    {f : ι → C(Set.Icc W.a W.b, ℂ)} {g : C(Set.Icc W.a W.b, ℂ)}
    (hf : Filter.Tendsto f l (nhds g)) :
    Filter.Tendsto (fun i => W.uniformToWeighted (f i)) l (nhds (W.uniformToWeighted g)) :=
  W.uniformToWeighted.continuous.continuousAt.tendsto.comp hf

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedUniform

-- BEGIN COMPLETE MODULE InnerKernelCompact
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {I E : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def innerKernel (k : C(I,E)) (f : E) : C(I,ℂ) :=
  ⟨fun x => inner ℂ (k x) f, k.continuous.inner continuous_const⟩

lemma innerKernel_norm (k : C(I,E)) (f : E) : ‖innerKernel k f‖ ≤ ‖k‖*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  exact (norm_inner_le_norm (k x) f).trans
    (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg f))

omit [CompactSpace I] in
lemma innerKernel_equicontinuous (k : C(I,E)) (f : ℕ → E) (B : ℝ)
    (hB : ∀n, ‖f n‖ ≤ B) : Equicontinuous (fun n x => inner ℂ (k x) (f n)) := by
  intro x
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun y => ‖k x-k y‖*B) ?_
  · filter_upwards with y n
    rw [dist_eq_norm, ← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _))
  · simpa using (((continuous_const : Continuous (fun _ : I => k x)).sub k.continuous).norm.mul_const B).continuousAt.tendsto (x := x)

lemma innerKernel_subsequence (k : C(I,E)) (f : ℕ → E)
    (hf : Bornology.IsBounded (Set.range f)) :
    ∃φ : ℕ → ℕ, StrictMono φ ∧ ∃g : C(I,ℂ),
      Tendsto (fun n => innerKernel k (f (φ n))) atTop (nhds g) := by
  classical
  obtain ⟨B,hB⟩ := hf.exists_norm_le
  have hBn (n : ℕ) : ‖f n‖≤B := hB _ ⟨n,rfl⟩
  let F (n : ℕ) : BoundedContinuousFunction I ℂ := BoundedContinuousFunction.mkOfCompact (innerKernel k (f n))
  let A := Set.range F
  have he := innerKernel_equicontinuous k f B hBn
  have heA : Equicontinuous (fun g : A => (g.val : I → ℂ)) := by
    have hh := he.comp (fun g : A => Classical.choose g.property)
    convert hh using 1
    ext g x
    have hg := Classical.choose_spec g.property
    exact congrArg (fun h : BoundedContinuousFunction I ℂ => h x) hg.symm
  have hr : ∀g : BoundedContinuousFunction I ℂ, ∀x, g∈A → g x∈Metric.closedBall 0 (‖k‖*B) := by
    rintro g x ⟨n,rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_inner_le_norm (k x) (f n)).trans
      (mul_le_mul (k.norm_coe_le_norm x) (hBn n) (norm_nonneg _) (norm_nonneg _))
  have hc := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℂ) (‖k‖*B))
    (isCompact_closedBall _ _) A hr heA
  obtain ⟨g,_,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨φ,hφ,g.toContinuousMap,?_⟩
  have hh := (ContinuousMap.isometryEquivBoundedOfCompact I ℂ).symm.continuous.continuousAt.tendsto.comp ht
  exact hh

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE InnerKernelCompact

-- BEGIN COMPLETE MODULE CompactnessDefinition
section

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 150: a linear operator `A` defined on all of the inner product space `H₀`
is *compact* if every sequence `A fₙ` has a convergent subsequence whenever `fₙ` is bounded.
The limit is required to lie in `H₀` itself (`H₀` is not assumed complete). -/
def IsCompactOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : Prop :=
  ∀ f : ℕ → E, Bornology.IsBounded (Set.range f) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : E,
      Filter.Tendsto (fun n => A (f (φ n))) Filter.atTop (nhds g)

end TeschlODE.SturmLiouville
end
-- END COMPLETE MODULE CompactnessDefinition

-- BEGIN COMPLETE MODULE WeightedKernel
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

/-- Continuous real kernels, viewed as weighted inner-product sections. -/
def kernelSections (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ)) :
    C(Set.Icc W.a W.b, W.Space) :=
  ⟨fun x => W.uniformToWeighted ((⟨fun z => (K z : ℂ), Complex.continuous_ofReal.comp K.continuous⟩ :
      C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℂ)).curry x),
    W.uniformToWeighted.continuous.comp (ContinuousMap.curry _).continuous⟩

@[simp] lemma kernelSections_apply (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ))
    (x t : Set.Icc W.a W.b) : W.toContinuous (W.kernelSections K x) t = (K (x,t) : ℂ) := rfl

def kernelUniform (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ)) :
    W.Space →L[ℂ] C(Set.Icc W.a W.b, ℂ) :=
  ({ toFun := innerKernel (W.kernelSections K)
     map_add' := by intros; ext x; simp [innerKernel]
     map_smul' := by intros; ext x; simp [innerKernel] } :
    W.Space →ₗ[ℂ] C(Set.Icc W.a W.b, ℂ)).mkContinuous
      ‖W.kernelSections K‖ (fun f => innerKernel_norm _ f)

def kernelOperator (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ)) : W.Space →L[ℂ] W.Space :=
  W.uniformToWeighted.comp (W.kernelUniform K)

lemma kernelOperator_compact (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ)) :
    TeschlODE.SturmLiouville.IsCompactOp (W.kernelOperator K).toLinearMap := by
  intro f hf
  obtain ⟨φ,hφ,g,hg⟩ := innerKernel_subsequence (W.kernelSections K) f hf
  exact ⟨φ,hφ,W.uniformToWeighted g,W.weighted_tendsto_of_uniform hg⟩

lemma kernelOperator_eq (K : C(Set.Icc W.a W.b × Set.Icc W.a W.b, ℝ))
    (f : W.Space) (x : Set.Icc W.a W.b) :
    W.toContinuous (W.kernelOperator K f) x =
      ∫ t in W.a..W.b, (K (x,Set.projIcc W.a W.b W.lt.le t) : ℂ) * W.extend f t *
        (W.weight t : ℂ) := by
  change W.scalar (W.kernelSections K x) f = _
  unfold scalar SLInner
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc W.a W.b := Set.uIcc_of_le W.lt.le ▸ ht
  dsimp only
  rw [W.extend_eq _ ht']
  simp [kernelSections_apply, Set.projIcc_of_mem W.lt.le ht']

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedKernel

-- BEGIN COMPLETE MODULE GreenInterface
section

namespace TeschlODE.SturmLiouville.Proof

noncomputable def greenApply (K : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (a b : ℝ)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in a..b, (K x t : ℂ) * f t * (r t : ℂ)

structure GreenData (p q r : ℝ → ℝ) (a b α β : ℝ) where
  param : ℝ
  kernel : ℝ → ℝ → ℝ
  continuous : ContinuousOn (fun z : ℝ × ℝ => kernel z.1 z.2)
    (Set.Icc a b ×ˢ Set.Icc a b)
  symmetric : ∀x∈Set.Icc a b, ∀y∈Set.Icc a b, kernel x y = kernel y x
  domain : ∀f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
    SLDomain p a b α β (greenApply kernel r a b f)
  right_inverse : ∀f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
    ∀x∈Set.Icc a b, SLOp p q r a b (greenApply kernel r a b f) x -
      (param : ℂ) * greenApply kernel r a b f x = f x
  left_inverse : ∀f : ℝ → ℂ, SLDomain p a b α β f →
    ∀x∈Set.Icc a b, greenApply kernel r a b
      (fun t => SLOp p q r a b f t - (param : ℂ)*f t) x = f x

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenInterface

-- BEGIN COMPLETE MODULE IntervalFubini
section

namespace TeschlODE.SturmLiouville.Proof
open MeasureTheory Set
lemma continuous_interval_swap {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ → ℂ)
    (hF : ContinuousOn F.uncurry (Icc a b ×ˢ Icc a b)) :
    (∫ x in a..b, ∫ y in a..b, F x y) = ∫ y in a..b, ∫ x in a..b, F x y := by
  apply intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma interval_conj (a b : ℝ) (f : ℝ → ℂ) :
    starRingEnd ℂ (∫x in a..b, f x) = ∫x in a..b, starRingEnd ℂ (f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE IntervalFubini

-- BEGIN COMPLETE MODULE GreenSymmetry
section

namespace TeschlODE.SturmLiouville.Proof
open Set
lemma green_inner_symmetric {a b : ℝ} (hab : a ≤ b) (K : ℝ → ℝ → ℝ)
    (r : ℝ → ℝ) (hK : ContinuousOn (fun z : ℝ × ℝ => K z.1 z.2) (Icc a b ×ˢ Icc a b))
    (hs : ∀x∈Icc a b, ∀y∈Icc a b, K x y = K y x)
    (hr : ContinuousOn r (Icc a b)) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    SLInner r a b (greenApply K r a b f) g = SLInner r a b f (greenApply K r a b g) := by
  unfold SLInner greenApply
  calc
    _ = ∫ x in a..b, ∫ t in a..b,
        (K x t : ℂ) * starRingEnd ℂ (f t) * g x * (r t : ℂ) * (r x : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [interval_conj, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [map_mul, Complex.conj_ofReal]
      ring
    _ = ∫ t in a..b, ∫ x in a..b,
        (K x t : ℂ) * starRingEnd ℂ (f t) * g x * (r t : ℂ) * (r x : ℂ) := by
      apply continuous_interval_swap hab
      have hKr := Complex.continuous_ofReal.comp_continuousOn hK
      have hrr := Complex.continuous_ofReal.comp_continuousOn hr
      exact (((hKr.mul (hf.comp continuousOn_snd (fun _ h => h.2)).star).mul
        (hg.comp continuousOn_fst (fun _ h => h.1))).mul
        (hrr.comp continuousOn_snd (fun _ h => h.2))).mul
        (hrr.comp continuousOn_fst (fun _ h => h.1))
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [hs x (uIcc_of_le hab ▸ hx) t (uIcc_of_le hab ▸ ht)]
      ring
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenSymmetry

-- BEGIN COMPLETE MODULE GreenWeightedOperator
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof

abbrev regularWeight {p q r : ℝ → ℝ} {a b : ℝ} (h : RegularSL p q r a b) : IntervalWeight :=
  ⟨a,b,h.1,r,h.2.1,fun x hx => (h.2.2.2.2 x hx).2⟩

namespace GreenData
variable {p q r : ℝ → ℝ} {a b α β : ℝ} (D : GreenData p q r a b α β)
  (h : RegularSL p q r a b)

def continuousKernel : C(Set.Icc a b × Set.Icc a b, ℝ) :=
  ⟨fun z => D.kernel z.1 z.2, D.continuous.comp_continuous
    (continuous_subtype_val.prodMap continuous_subtype_val) (fun z => ⟨z.1.property,z.2.property⟩)⟩

def operator : (regularWeight h).Space →L[ℂ] (regularWeight h).Space :=
  (regularWeight h).kernelOperator D.continuousKernel

lemma operator_compact : IsCompactOp (D.operator h).toLinearMap :=
  (regularWeight h).kernelOperator_compact _

lemma operator_apply (f : (regularWeight h).Space) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    (regularWeight h).extend (D.operator h f) x =
      greenApply D.kernel r a b ((regularWeight h).extend f) x := by
  rw [(regularWeight h).extend_eq _ hx]
  change (regularWeight h).toContinuous ((regularWeight h).kernelOperator D.continuousKernel f) ⟨x,hx⟩ = _
  rw [(regularWeight h).kernelOperator_eq]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le h.1.le ▸ ht
  simp [continuousKernel, regularWeight, Set.projIcc_of_mem h.1.le ht']

lemma operator_symmetric : (D.operator h).toLinearMap.IsSymmetric := by
  intro f g
  change (regularWeight h).scalar (D.operator h f) g =
    (regularWeight h).scalar f (D.operator h g)
  have hc := green_inner_symmetric h.1.le D.kernel r D.continuous D.symmetric h.2.1
    ((regularWeight h).extend f) ((regularWeight h).extend g)
    ((regularWeight h).extend_continuous f).continuousOn
    ((regularWeight h).extend_continuous g).continuousOn
  calc
    _ = SLInner r a b (greenApply D.kernel r a b ((regularWeight h).extend f))
        ((regularWeight h).extend g) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [D.operator_apply h f x (Set.uIcc_of_le h.1.le ▸ hx)]
    _ = _ := hc
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [D.operator_apply h g x (Set.uIcc_of_le h.1.le ▸ hx)]

end GreenData
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenWeightedOperator

-- BEGIN COMPLETE MODULE SLCongruence
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma slOp_congr {p q r : ℝ → ℝ} {a b : ℝ} {f g : ℝ → ℂ}
    (hfg : EqOn f g (Icc a b)) {x : ℝ} (hx : x∈Icc a b) :
    SLOp p q r a b f x=SLOp p q r a b g x := by
  have hd (t : ℝ) (ht : t∈Icc a b) : derivWithin f (Icc a b) t=derivWithin g (Icc a b) t :=
    derivWithin_congr hfg (hfg ht)
  have hflux : EqOn (fun t => (p t : ℂ)*derivWithin f (Icc a b) t)
      (fun t => (p t : ℂ)*derivWithin g (Icc a b) t) (Icc a b) := by
    intro t ht
    dsimp only
    rw [hd t ht]
  unfold SLOp
  rw [derivWithin_congr hflux (hflux hx),hfg hx]

lemma slDomain_congr {p : ℝ → ℝ} {a b α β : ℝ} {f g : ℝ → ℂ}
    (hab : a≤b) (hfg : EqOn f g (Icc a b)) (hf : SLDomain p a b α β f) :
    SLDomain p a b α β g := by
  have ha : a∈Icc a b := ⟨le_rfl,hab⟩
  have hb : b∈Icc a b := ⟨hab,le_rfl⟩
  refine ⟨hf.1.congr (fun t ht => (hfg ht).symm),?_,?_⟩
  · rw [← hfg ha, ← derivWithin_congr hfg (hfg ha)]
    exact hf.2.1
  · rw [← hfg hb, ← derivWithin_congr hfg (hfg hb)]
    exact hf.2.2

lemma slInner_congr {r : ℝ → ℝ} {a b : ℝ} (hab : a≤b) {f g u v : ℝ → ℂ}
    (hfg : EqOn f g (Icc a b)) (huv : EqOn u v (Icc a b)) :
    SLInner r a b f u=SLInner r a b g v := by
  unfold SLInner
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc a b := by simpa [uIcc_of_le hab] using ht
  dsimp only
  rw [hfg ht',huv ht']

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLCongruence

-- BEGIN COMPLETE MODULE GreenInjective
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.GreenData
variable {p q r : ℝ → ℝ} {a b α β : ℝ} (D : GreenData p q r a b α β)
  (h : RegularSL p q r a b)

lemma operator_injective : Function.Injective (D.operator h) := by
  apply (D.operator h).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  change D.operator h f = 0 at hf
  apply (regularWeight h).space_ext
  intro x hx
  have he : Set.EqOn (greenApply D.kernel r a b ((regularWeight h).extend f)) (fun _ => (0:ℂ)) (Set.Icc a b) := by
    intro y hy
    rw [← D.operator_apply h f y hy, hf]
    exact (regularWeight h).extend_zero y
  have hi := D.right_inverse ((regularWeight h).extend f)
    ((regularWeight h).extend_continuous f).continuousOn x hx
  rw [slOp_congr he hx,he hx] at hi
  simpa [SLOp] using hi.symm

end TeschlODE.SturmLiouville.Proof.GreenData
end
-- END COMPLETE MODULE GreenInjective

-- BEGIN COMPLETE MODULE SLOperatorContinuity
section

namespace TeschlODE.SturmLiouville.Proof
lemma slOp_continuous {p q r : ℝ → ℝ} {a b α β : ℝ}
    (h : RegularSL p q r a b) {f : ℝ → ℂ} (hf : SLDomain p a b α β f) :
    ContinuousOn (SLOp p q r a b f) (Set.Icc a b) := by
  have hu := uniqueDiffOn_Icc h.1
  have hd : ContDiffOn ℝ 1 (derivWithin f (Set.Icc a b)) (Set.Icc a b) :=
    hf.1.derivWithin hu (by norm_num)
  have hp : ContDiffOn ℝ 1 (fun x => (p x:ℂ)) (Set.Icc a b) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h.2.2.2.1
  have hflux := (hp.mul hd).derivWithin hu (m := 0) (by norm_num)
  have hr : ContinuousOn (fun x => ((r x:ℂ))⁻¹) (Set.Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn h.2.1).inv₀
      (fun x hx => by change (r x : ℂ) ≠ 0; exact_mod_cast (h.2.2.2.2 x hx).2.ne')
  exact hr.mul (hflux.continuousOn.neg.add
    ((Complex.continuous_ofReal.comp_continuousOn h.2.2.1).mul hf.1.continuousOn))
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLOperatorContinuity

-- BEGIN COMPLETE MODULE DomainTestFunctions
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof

def endpointWeight (a b x : ℝ) : ℝ := (x-a)^2*(x-b)^2

lemma endpointWeight_nonneg (a b x : ℝ) : 0 ≤ endpointWeight a b x :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma endpointWeight_pos {a b x : ℝ} (hx : x ∈ Set.Ioo a b) : 0 < endpointWeight a b x := by
  exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hx.1)))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hx.2)))

lemma endpointWeight_contDiff (a b : ℝ) : ContDiff ℝ 2 (endpointWeight a b) := by
  unfold endpointWeight
  fun_prop

lemma endpointWeight_deriv (a b x : ℝ) :
    HasDerivAt (fun x => ((endpointWeight a b x : ℝ) : ℂ))
      (((2*(x-a)*(x-b)^2+(x-a)^2*(2*(x-b)) : ℝ) : ℂ)) x := by
  convert (((hasDerivAt_id x).sub_const a).pow 2 |>.mul
    (((hasDerivAt_id x).sub_const b).pow 2)).ofReal_comp using 1 <;>
    simp [endpointWeight]

lemma weighted_test_domain (p : ℝ → ℝ) {a b : ℝ} (hab : a < b) (α β : ℝ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    SLDomain p a b α β (fun x => (endpointWeight a b x : ℂ)*f x) := by
  have hw : ContDiff ℝ 2 (fun x => (endpointWeight a b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (endpointWeight_contDiff a b)
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :=
    ((endpointWeight_deriv a b x).mul
      ((hf.differentiable (by norm_num) x).hasDerivAt)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hab) x hx)
  refine ⟨(hw.mul hf).contDiffOn, ?_, ?_⟩
  · have hh := hd a ⟨le_rfl,hab.le⟩
    change derivWithin (fun x => (endpointWeight a b x : ℂ)*f x) _ a = _ at hh
    rw [hh]
    simp [endpointWeight]
  · have hh := hd b ⟨hab.le,le_rfl⟩
    change derivWithin (fun x => (endpointWeight a b x : ℂ)*f x) _ b = _ at hh
    rw [hh]
    simp [endpointWeight]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE DomainTestFunctions

-- BEGIN COMPLETE MODULE WeightedDamping
section

noncomputable section
open MeasureTheory Filter Topology
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

lemma damping_integral_tendsto (f : W.Space) :
    Tendsto (fun n : ℕ => ∫ x in W.a..W.b,
      ( (1/((n:ℝ)+1)) / (endpointWeight W.a W.b x + 1/((n:ℝ)+1)))^2 *
        (‖W.extend f x‖^2 * W.weight x)) atTop (nhds 0) := by
  let F (n : ℕ) (x : ℝ) :=
    ((1/((n:ℝ)+1)) / (endpointWeight W.a W.b x + 1/((n:ℝ)+1)))^2 *
      (‖W.extend f x‖^2 * W.weight x)
  have he (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  have hc (n : ℕ) : ContinuousOn (F n) (Set.Icc W.a W.b) := by
    apply ContinuousOn.mul _ (W.self_continuous f)
    apply ContinuousOn.pow
    apply continuousOn_const.div
    · exact (endpointWeight_contDiff W.a W.b).continuous.continuousOn.add continuousOn_const
    · intro x hx
      exact ne_of_gt (add_pos_of_nonneg_of_pos (endpointWeight_nonneg _ _ _) (he n))
  have hb (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc W.a W.b) :
      ‖F n x‖ ≤ ‖W.extend f x‖^2 * W.weight x := by
    have h0 : 0 ≤ (1/((n:ℝ)+1))/(endpointWeight W.a W.b x+1/((n:ℝ)+1)) := div_nonneg (he n).le (add_nonneg (endpointWeight_nonneg _ _ _) (he n).le)
    have h1 : (1/((n:ℝ)+1))/(endpointWeight W.a W.b x+1/((n:ℝ)+1)) ≤ 1 :=
      (div_le_one (add_pos_of_nonneg_of_pos (endpointWeight_nonneg _ _ _) (he n))).mpr
        (le_add_of_nonneg_left (endpointWeight_nonneg _ _ _))
    have h2 : ((1/((n:ℝ)+1))/(endpointWeight W.a W.b x+1/((n:ℝ)+1)))^2 ≤ 1 := by nlinarith
    dsimp [F]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (W.positive x hx).le))]
    exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (W.positive x hx).le) h2
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioo W.a W.b))
    (fun x => ‖W.extend f x‖^2 * W.weight x)
    (fun n => ((hc n).mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    ((W.self_continuous f).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
    (fun n => by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx; exact hb n x (Set.Ioo_subset_Icc_self hx))
    (f := fun _ => (0:ℝ)) ?_
  · simpa only [intervalIntegral.integral_of_le W.lt.le,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc, integral_zero] using ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hp := endpointWeight_pos hx
    have hseq : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim := (hseq.div (tendsto_const_nhds.add hseq) (by simpa using hp.ne')).pow 2
    simpa [F] using hlim.mul_const (‖W.extend f x‖^2 * W.weight x)

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedDamping

-- BEGIN COMPLETE MODULE DampedFunctions
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

def damped (ε : ℝ) (hε : 0 < ε) (f : W.Space) : W.Space :=
  W.restrict (fun x => ((endpointWeight W.a W.b x / (endpointWeight W.a W.b x + ε) : ℝ):ℂ)*W.extend f x)
    ((Complex.continuous_ofReal.comp_continuousOn
      ((endpointWeight_contDiff W.a W.b).continuous.continuousOn.div
        ((endpointWeight_contDiff W.a W.b).continuous.continuousOn.add continuousOn_const)
        (fun _ _ => ne_of_gt (add_pos_of_nonneg_of_pos (endpointWeight_nonneg _ _ _) hε)))).mul
      (W.extend_continuous f).continuousOn)

lemma damped_norm_sq (ε : ℝ) (hε : 0 < ε) (f : W.Space) :
    ‖W.damped ε hε f-f‖^2 = ∫x in W.a..W.b,
      (ε/(endpointWeight W.a W.b x+ε))^2 * (‖W.extend f x‖^2*W.weight x) := by
  rw [W.norm_sq_eq]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc W.a W.b := Set.uIcc_of_le W.lt.le ▸ hx
  dsimp only
  rw [W.extend_sub, damped, W.extend_restrict _ _ hx']
  have hd : endpointWeight W.a W.b x+ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (endpointWeight_nonneg _ _ _) hε)
  have he : ((endpointWeight W.a W.b x/(endpointWeight W.a W.b x+ε):ℝ):ℂ)*W.extend f x-W.extend f x =
      ((-ε/(endpointWeight W.a W.b x+ε):ℝ):ℂ)*W.extend f x := by
    have hr : endpointWeight W.a W.b x/(endpointWeight W.a W.b x+ε)-1 =
        -ε/(endpointWeight W.a W.b x+ε) := by field_simp; ring
    calc
      _ = (((endpointWeight W.a W.b x/(endpointWeight W.a W.b x+ε)-1 : ℝ):ℂ))*W.extend f x := by push_cast; ring
      _ = _ := by rw [hr]
  rw [he, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma damped_tendsto (f : W.Space) :
    Tendsto (fun n : ℕ => W.damped (1/((n:ℝ)+1)) (by positivity) f) atTop (nhds f) := by
  have hh := W.damping_integral_tendsto f
  have heq : (fun n : ℕ => ‖W.damped (1/((n:ℝ)+1)) (by positivity) f-f‖^2) =
      (fun n : ℕ => ∫x in W.a..W.b, ((1/((n:ℝ)+1))/(endpointWeight W.a W.b x+1/((n:ℝ)+1)))^2 * (‖W.extend f x‖^2*W.weight x)) :=
    funext (fun n => W.damped_norm_sq _ (by positivity) f)
  rw [← heq] at hh
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE DampedFunctions

-- BEGIN COMPLETE MODULE SmoothApproximation
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof

lemma real_polynomial_approx {a b : ℝ} (f : C(Set.Icc a b,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃P : Polynomial ℝ, ∀x : Set.Icc a b, |P.eval (x:ℝ) - f x| < ε := by
  have hd : Dense (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b,ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions.topologicalClosure]
    rfl
  obtain ⟨g,hg,hgf⟩ := Metric.mem_closure_iff.mp (hd f) ε hε
  rw [polynomialFunctions_coe] at hg
  obtain ⟨P,rfl⟩ := hg
  refine ⟨P,fun x => ?_⟩
  have hp := ((Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)) P-f).norm_coe_le_norm x
  apply lt_of_le_of_lt hp
  simpa [dist_eq_norm, norm_sub_rev] using hgf

lemma complex_smooth_approx {a b : ℝ} (f : C(Set.Icc a b,ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃g : ℝ → ℂ, ContDiff ℝ 2 g ∧ ∀x : Set.Icc a b, ‖g x-f x‖ < ε := by
  obtain ⟨P,hP⟩ := real_polynomial_approx
    (⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩ : C(Set.Icc a b,ℝ)) (half_pos hε)
  obtain ⟨Q,hQ⟩ := real_polynomial_approx
    (⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩ : C(Set.Icc a b,ℝ)) (half_pos hε)
  refine ⟨fun x => ((P.eval x : ℝ) : ℂ)+Complex.I*((Q.eval x : ℝ) : ℂ), ?_, ?_⟩
  · have hp : ContDiff ℝ 2 (fun x : ℝ => P.eval x) := by simpa using P.contDiff_aeval (𝕜 := ℝ) 2
    have hq : ContDiff ℝ 2 (fun x : ℝ => Q.eval x) := by simpa using Q.contDiff_aeval (𝕜 := ℝ) 2
    exact (Complex.ofRealCLM.contDiff.comp hp).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hq))
  · intro x
    have hp := hP x
    have hq := hQ x
    have hh := Complex.norm_le_abs_re_add_abs_im (((P.eval (x:ℝ):ℝ):ℂ)+Complex.I*((Q.eval (x:ℝ):ℝ):ℂ)-f x)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      zero_add, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul] at hh
    change |P.eval (x:ℝ)-(f x).re| < ε/2 at hp
    change |Q.eval (x:ℝ)-(f x).im| < ε/2 at hq
    linarith

lemma smooth_closure {a b : ℝ} (S : Set C(Set.Icc a b,ℂ)) (hS : IsClosed S)
    (hs : ∀g : ℝ → ℂ, ∀hg : ContDiff ℝ 2 g,
      (⟨fun x => g x, hg.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b,ℂ)) ∈ S)
    (f : C(Set.Icc a b,ℂ)) : f ∈ S := by
  apply hS.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g,hg,hgf⟩ := complex_smooth_approx f (half_pos hε)
  refine ⟨⟨fun x => g x,hg.continuous.comp continuous_subtype_val⟩,hs g hg,?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
  intro x
  simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_mk, norm_sub_rev] using (hgf x).le

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SmoothApproximation

-- BEGIN COMPLETE MODULE WeightedDomainDensity
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

def domainSet (p : ℝ → ℝ) (α β : ℝ) : Set W.Space :=
  {f | ∃g : ℝ → ℂ, SLDomain p W.a W.b α β g ∧
    ∀x∈Set.Icc W.a W.b, W.extend f x = g x}

def weightMap : C(Set.Icc W.a W.b,ℂ) → W.Space := fun f =>
  W.uniformToWeighted ((⟨fun x => ((endpointWeight W.a W.b x : ℝ):ℂ),
    Complex.continuous_ofReal.comp ((endpointWeight_contDiff W.a W.b).continuous.comp continuous_subtype_val)⟩ : C(Set.Icc W.a W.b,ℂ))*f)

lemma weightMap_continuous : Continuous W.weightMap :=
  W.uniformToWeighted.continuous.comp (continuous_const.mul continuous_id)

lemma weightMap_closure (p : ℝ → ℝ) (α β : ℝ) (f : C(Set.Icc W.a W.b,ℂ)) :
    W.weightMap f ∈ closure (W.domainSet p α β) := by
  apply smooth_closure (W.weightMap ⁻¹' closure (W.domainSet p α β))
    (isClosed_closure.preimage W.weightMap_continuous) _ f
  intro g hg
  apply subset_closure
  refine ⟨fun x => (endpointWeight W.a W.b x : ℂ)*g x,
    weighted_test_domain p W.lt α β g hg,?_⟩
  intro x hx
  rw [W.extend_eq _ hx]
  rfl

lemma damped_mem_closure (p : ℝ → ℝ) (α β : ℝ) (ε : ℝ) (hε : 0 < ε) (f : W.Space) :
    W.damped ε hε f ∈ closure (W.domainSet p α β) := by
  let g : C(Set.Icc W.a W.b,ℂ) :=
    ⟨fun x => W.toContinuous f x / ((endpointWeight W.a W.b x+ε : ℝ):ℂ),
      (W.toContinuous f).continuous.div
        (Complex.continuous_ofReal.comp
          (((endpointWeight_contDiff W.a W.b).continuous.comp continuous_subtype_val).add continuous_const))
        (fun x => by exact_mod_cast ne_of_gt (add_pos_of_nonneg_of_pos (endpointWeight_nonneg _ _ _) hε))⟩
  have he : W.weightMap g = W.damped ε hε f := by
    apply W.space_ext
    intro x hx
    rw [W.extend_eq _ hx, damped, W.extend_restrict _ _ hx, W.extend_eq _ hx]
    change (((endpointWeight W.a W.b x:ℝ):ℂ)*(W.toContinuous f ⟨x,hx⟩ / ((endpointWeight W.a W.b x+ε:ℝ):ℂ))) = _
    push_cast
    ring
  rw [← he]
  exact W.weightMap_closure p α β g

lemma domainSet_dense (p : ℝ → ℝ) (α β : ℝ) : Dense (W.domainSet p α β) := by
  intro f
  exact isClosed_closure.mem_of_tendsto (W.damped_tendsto f)
    (Filter.Eventually.of_forall (fun n => W.damped_mem_closure p α β _ (by positivity) f))

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedDomainDensity

-- BEGIN COMPLETE MODULE GreenDenseRange
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.GreenData
variable {p q r : ℝ → ℝ} {a b α β : ℝ} (D : GreenData p q r a b α β)
  (h : RegularSL p q r a b)

lemma domain_mem_range {f : (regularWeight h).Space}
    (hf : f ∈ (regularWeight h).domainSet p α β) : f ∈ Set.range (D.operator h) := by
  obtain ⟨g,hg,he⟩ := hf
  let v : ℝ → ℂ := fun x => SLOp p q r a b g x-(D.param:ℂ)*g x
  have hv : ContinuousOn v (Set.Icc a b) :=
    (slOp_continuous h hg).sub (continuousOn_const.mul hg.1.continuousOn)
  refine ⟨(regularWeight h).restrict v hv,?_⟩
  apply (regularWeight h).space_ext
  intro x hx
  rw [D.operator_apply h _ x hx, he x hx]
  calc
    _ = greenApply D.kernel r a b v x := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [(regularWeight h).extend_restrict v hv (Set.uIcc_of_le h.1.le ▸ ht)]
    _ = g x := D.left_inverse g hg x hx

lemma operator_dense_range : DenseRange (D.operator h) :=
  ((regularWeight h).domainSet_dense p α β).mono (fun _ hf => D.domain_mem_range h hf)

end TeschlODE.SturmLiouville.Proof.GreenData
end
-- END COMPLETE MODULE GreenDenseRange

-- BEGIN COMPLETE MODULE WeightedInfiniteDimension
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)

def polynomialMap : Polynomial ℂ →ₗ[ℂ] W.Space where
  toFun P := W.restrict (fun x => P.eval (x:ℂ))
    (P.continuous.comp Complex.continuous_ofReal).continuousOn
  map_add' P Q := by apply W.space_ext; intro x hx; simp [W.extend_restrict, hx]
  map_smul' c P := by apply W.space_ext; intro x hx; simp [W.extend_restrict, hx]

lemma polynomialMap_injective : Function.Injective W.polynomialMap := by
  intro P Q hPQ
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Icc_infinite W.lt).image Complex.ofReal_injective.injOn).mono
  rintro _ ⟨x,hx,rfl⟩
  change P.eval (x:ℂ) = Q.eval (x:ℂ)
  have hh := congrArg (fun f : W.Space => W.extend f x) hPQ
  simpa only [polynomialMap, LinearMap.coe_mk, AddHom.coe_mk, W.extend_restrict _ _ hx] using hh

lemma infinite_dimensional : ¬ FiniteDimensional ℂ W.Space := by
  intro h
  let := h
  have hl := (Polynomial.basisMonomials ℂ).linearIndependent.map' W.polynomialMap
    (LinearMap.ker_eq_bot.mpr W.polynomialMap_injective)
  have hc := hl.lt_aleph0_of_finiteDimensional
  simp at hc

end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedInfiniteDimension

-- BEGIN COMPLETE MODULE PrefixGeometry
section

open scoped ComplexConjugate BigOperators
namespace TeschlODE.SturmLiouville.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The unused subspace after finitely many orthogonal eigenvectors. -/
noncomputable def prefixComplement {n : ℕ} (u : Fin n → E) : Submodule ℂ E :=
  (Submodule.span ℂ (Set.range u))ᗮ

theorem mem_prefixComplement {n : ℕ} (u : Fin n → E) (v : E) :
    v ∈ prefixComplement u ↔ ∀ i, inner ℂ (u i) v = 0 := by
  rw [prefixComplement, Submodule.mem_orthogonal]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span (Set.mem_range_self i))
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i,rfl⟩ := hw; exact h i
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul a x _ hx => simp [inner_smul_left, hx]

theorem prefixComplement_invariant {n : ℕ} (A : E →ₗ[ℂ] E)
    (hsym : A.IsSymmetric) (u : Fin n → E) (a : Fin n → ℝ)
    (hu : ∀ i, A (u i) = (a i : ℂ) • u i) :
    ∀ v ∈ prefixComplement u, A v ∈ prefixComplement u := by
  intro v hv
  rw [mem_prefixComplement] at hv ⊢
  intro i
  rw [← hsym, hu, inner_smul_left, hv, mul_zero]

theorem prefixComplement_nontrivial {n : ℕ} (u : Fin n → E)
    (hE : ¬ FiniteDimensional ℂ E) : Nontrivial (prefixComplement u) := by
  classical
  let K := Submodule.span ℂ (Set.range u)
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro heq
  have htop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp heq
  have : FiniteDimensional ℂ (⊤ : Submodule ℂ E) := htop ▸ inferInstance
  exact hE (FiniteDimensional.of_injective (Submodule.topEquiv : (⊤ : Submodule ℂ E) ≃ₗ[ℂ] E).symm.toLinearMap
    (Submodule.topEquiv.symm.injective))

theorem orthonormal_snoc {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u)
    (v : E) (hv : ‖v‖ = 1) (ho : v ∈ prefixComplement u) :
    Orthonormal ℂ (Fin.snoc u v) := by
  classical
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [inner_self_eq_norm_sq_to_K, hv]
  · simp only [Fin.snoc_last, Fin.snoc_castSucc, (Ne.symm (Fin.castSucc_ne_last j)), ite_false]
    exact inner_eq_zero_symm.mpr ((mem_prefixComplement u v).mp ho j)
  · simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last, ite_false]
    exact (mem_prefixComplement u v).mp ho i
  · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using hu i j

/-- Finite orthogonal expansion, defined without completing the ambient space. -/
noncomputable def prefixSum {n : ℕ} (u : Fin n → E) (x : E) : E :=
  ∑ i, inner ℂ (u i) x • u i

theorem prefixSum_remainder {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u) (x : E) :
    x - prefixSum u x ∈ prefixComplement u := by
  rw [mem_prefixComplement]
  intro i
  simp only [inner_sub_right, prefixSum, hu.inner_right_fintype, sub_self]

theorem prefixSum_remainder_norm {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u) (x : E) :
    ‖x-prefixSum u x‖ ≤ ‖x‖ := by
  have ho : inner ℂ (prefixSum u x) (x-prefixSum u x) = 0 := by
    change inner ℂ (∑ i, inner ℂ (u i) x • u i) (x-prefixSum u x) = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_left, (mem_prefixComplement u _).mp (prefixSum_remainder u hu x) i, mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (prefixSum u x) (x-prefixSum u x) ho
  rw [add_sub_cancel] at hp
  nlinarith [norm_nonneg (x-prefixSum u x), norm_nonneg x, sq_nonneg ‖prefixSum u x‖]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE PrefixGeometry

-- BEGIN COMPLETE MODULE EigenRecursion
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A finite orthonormal eigenvector prefix. -/
structure EigenPrefix (A : E →ₗ[ℂ] E) (n : ℕ) where
  u : Fin n → E
  a : Fin n → ℝ
  orth : Orthonormal ℂ u
  eigen : ∀ i, A (u i) = (a i : ℂ) • u i

/-- A maximal-modulus eigenvector on the unused complement. -/
structure EigenExtension {A : E →ₗ[ℂ] E} {n : ℕ} (p : EigenPrefix A n) where
  v : E
  b : ℝ
  unit : ‖v‖ = 1
  mem : v ∈ prefixComplement p.u
  eigen : A v = (b : ℂ) • v
  bound : ∀ w ∈ prefixComplement p.u, ‖A w‖ ≤ |b| * ‖w‖

def extendPrefix {A : E →ₗ[ℂ] E} {n : ℕ} {p : EigenPrefix A n}
    (e : EigenExtension p) : EigenPrefix A (n+1) where
  u := Fin.snoc p.u e.v
  a := Fin.snoc p.a e.b
  orth := orthonormal_snoc p.u p.orth e.v e.unit e.mem
  eigen i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using e.eigen
    · simpa using p.eigen j

def buildPrefix {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) : (n : ℕ) → EigenPrefix A n
  | 0 => ⟨Fin.elim0, Fin.elim0, by simp, by intro i; exact i.elim0⟩
  | n+1 => extendPrefix (next n (buildPrefix next n))

def eigenSequence {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) : E :=
  (next n (buildPrefix next n)).v

def valueSequence {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) : ℝ :=
  (next n (buildPrefix next n)).b

theorem buildPrefix_u {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (i : Fin n) :
    (buildPrefix next n).u i = eigenSequence next i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [buildPrefix,extendPrefix,eigenSequence]
    · simpa [buildPrefix,extendPrefix] using ih j

theorem buildPrefix_a {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (i : Fin n) :
    (buildPrefix next n).a i = valueSequence next i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [buildPrefix,extendPrefix,valueSequence]
    · simpa [buildPrefix,extendPrefix] using ih j

theorem eigenSequence_orthonormal {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) :
    Orthonormal ℂ (eigenSequence next) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  let N := max i j + 1
  let ii : Fin N := ⟨i,by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j,by dsimp [N]; omega⟩
  have h := (orthonormal_iff_ite.mp (buildPrefix next N).orth) ii jj
  simpa [buildPrefix_u, ii, jj] using h

theorem eigenSequence_eigen {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) :
    A (eigenSequence next n) = (valueSequence next n : ℂ) • eigenSequence next n :=
  (next n (buildPrefix next n)).eigen

theorem eigenSequence_bound {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (w : E)
    (hw : ∀ j < n, inner ℂ (eigenSequence next j) w = 0) :
    ‖A w‖ ≤ |valueSequence next n| * ‖w‖ := by
  apply (next n (buildPrefix next n)).bound
  rw [mem_prefixComplement]
  intro j
  rw [buildPrefix_u]
  exact hw j.val j.isLt

theorem valueSequence_antitone {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) :
    Antitone (fun n => |valueSequence next n|) := by
  apply antitone_nat_of_succ_le
  intro n
  have hu := eigenSequence_orthonormal next
  have h := eigenSequence_bound next n (eigenSequence next (n+1)) (by
    intro j hj
    exact hu.inner_eq_zero (by omega))
  simpa [eigenSequence_eigen, norm_smul, hu.norm_eq_one] using h

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE EigenRecursion

-- BEGIN COMPLETE MODULE CompactBounded
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem bound_of_unit_bound (A : E →ₗ[ℂ] E) (C : ℝ)
    (_hC : 0 ≤ C) (h : ∀ x : E, ‖x‖ = 1 → ‖A x‖ ≤ C) :
    ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb := h ((‖x‖⁻¹ : ℂ) • x) (norm_smul_inv_norm hx)
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn.le] at hb
  have := (mul_le_mul_iff_left₀ hn).mpr hb
  field_simp at this
  nlinarith

theorem compact_unit_bound (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖x‖ = 1 → ‖A x‖ ≤ C := by
  classical
  by_contra h
  have he : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧ (n : ℝ) < ‖A x‖ := by
    intro n
    by_contra hn
    push Not at hn
    exact h ⟨n, Nat.cast_nonneg n, hn⟩
  choose f hf hlt using he
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).le⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA f hb
  obtain ⟨C, hC⟩ := hg.cauchySeq.isBounded_range.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hle : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
  have hu := hC (A (f (φ n))) ⟨n, rfl⟩
  have hl := hlt (φ n)
  linarith

theorem compact_bound (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hb⟩ := compact_unit_bound A hA
  exact ⟨C, hC, bound_of_unit_bound A C hC hb⟩

theorem compact_continuous (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) : Continuous A := by
  obtain ⟨C, _, hC⟩ := compact_bound A hA
  exact (A.mkContinuous C hC).continuous

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE CompactBounded

-- BEGIN COMPLETE MODULE SpectralApprox
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_unit_norm_approx [Nontrivial E] (A : E →L[ℂ] E) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ = 1) ∧
      Tendsto (fun n => ‖A (f n)‖) atTop (𝓝 ‖A‖) := by
  classical
  let S : Set ℝ := (fun x : E => ‖A x‖) '' Metric.sphere 0 1
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := E) zero_le_one
    exact ⟨_, x, hx, rfl⟩
  have hb : BddAbove S := ⟨‖A‖, by
    rintro _ ⟨x, hx, rfl⟩
    exact A.unit_le_opNorm x (mem_sphere_zero_iff_norm.mp hx).le⟩
  obtain ⟨v, _, hv, hmem⟩ := exists_seq_tendsto_sSup hne hb
  choose f hf heq using hmem
  refine ⟨f, fun n => mem_sphere_zero_iff_norm.mp (hf n), ?_⟩
  have hs : sSup S = ‖A‖ := A.sSup_sphere_eq_norm
  simpa only [heq, hs] using hv

theorem square_residual_bound (A : E →L[ℂ] E)
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (x : E) (hx : ‖x‖ = 1) :
    ‖A (A x) - ((‖A‖ ^ 2 : ℝ) : ℂ) • x‖ ^ 2 ≤
      2 * ‖A‖ ^ 2 * (‖A‖ ^ 2 - ‖A x‖ ^ 2) := by
  have hi : inner ℂ (A (A x)) x = inner ℂ (A x) (A x) := hsym (A x) x
  have hnorm : ‖A (A x)‖ ≤ ‖A‖ ^ 2 := by
    calc
      ‖A (A x)‖ ≤ ‖A‖ * ‖A x‖ := A.le_opNorm _
      _ ≤ ‖A‖ * ‖A‖ := mul_le_mul_of_nonneg_left (A.unit_le_opNorm x hx.le) (norm_nonneg _)
      _ = ‖A‖ ^ 2 := by ring
  have hsq : ‖A (A x)‖ ^ 2 ≤ (‖A‖ ^ 2) ^ 2 := sq_le_sq₀ (norm_nonneg _) (sq_nonneg _) |>.mpr hnorm
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi, inner_self_eq_norm_sq_to_K,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hx]
  change ‖A (A x)‖ ^ 2 - 2 * (Complex.re ((↑(‖A‖ ^ 2) : ℂ) * (↑‖A x‖ : ℂ) ^ 2)) + (‖A‖ ^ 2 * 1) ^ 2 ≤ _
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_one]
  nlinarith

theorem square_residual_tendsto (A : E →L[ℂ] E)
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (f : ℕ → E)
    (hf : ∀ n, ‖f n‖ = 1) (hlim : Tendsto (fun n => ‖A (f n)‖) atTop (𝓝 ‖A‖)) :
    Tendsto (fun n => A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => square_residual_bound A hsym _ (hf n))
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hlim.pow 2))) using 1; simp
  have hn := (Real.continuous_sqrt.tendsto 0).comp hh
  change Tendsto (fun n => Real.sqrt (‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hn
  have hn' : Tendsto (fun n => ‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖)
      atTop (𝓝 0) := by simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SpectralApprox

-- BEGIN COMPLETE MODULE CompactSquareEigenvector
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem compact_square_unit_eigenvector [Nontrivial E] (A : E →L[ℂ] E)
    (hA : IsCompactOp (A : E →ₗ[ℂ] E))
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (hc : 0 < ‖A‖) :
    ∃ u : E, ‖u‖ = 1 ∧ A (A u) = ((‖A‖ ^ 2 : ℝ) : ℂ) • u := by
  obtain ⟨f, hf, hlim⟩ := exists_unit_norm_approx A
  have hres := square_residual_tendsto A hsym f hf hlim
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).le⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA f hb
  let c : ℂ := ((‖A‖ ^ 2 : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by dsimp [c]; exact_mod_cast (pow_ne_zero 2 hc.ne')
  let u : E := c⁻¹ • A g
  have hu : Tendsto (fun n => f (φ n)) atTop (𝓝 u) := by
    have ht := ((A.continuous.tendsto g).comp hg).sub (hres.comp hφ.tendsto_atTop)
    have ht' := ht.const_smul c⁻¹
    convert ht' using 1
    · ext n
      change f (φ n) = c⁻¹ • (A (A (f (φ n))) -
        (A (A (f (φ n))) - c • f (φ n)))
      rw [sub_sub_cancel, inv_smul_smul₀ hc0]
    · simp only [sub_zero]; rfl
  have hunorm : ‖u‖ = 1 := by
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖u‖) := by
      simpa only [hf] using hu.norm
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hgu : A u = g := tendsto_nhds_unique ((A.continuous.tendsto u).comp hu) hg
  refine ⟨u, hunorm, ?_⟩
  rw [hgu]
  exact (smul_inv_smul₀ hc0 (A g)).symm

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE CompactSquareEigenvector

-- BEGIN COMPLETE MODULE CompactRestriction
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem compact_restrict (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (K : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (hAK : ∀ x ∈ K, A x ∈ K) : IsCompactOp (A.restrict hAK) := by
  intro f hf
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  have hb : Bornology.IsBounded (Set.range (fun n => (f n : E))) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by
      rintro _ ⟨n, rfl⟩
      exact hC (f n) ⟨n, rfl⟩⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA (fun n => (f n : E)) hb
  have hgK : g ∈ K := hK.mem_of_tendsto hg (Filter.Eventually.of_forall
    (fun n => hAK (f (φ n)) (f (φ n)).property))
  exact ⟨φ, hφ, ⟨g, hgK⟩, tendsto_subtype_rng.mpr hg⟩

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE CompactRestriction

-- BEGIN COMPLETE MODULE CompactEigenpair
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem normalize_eigenvector (A : E →ₗ[ℂ] E) (a : ℝ) (w : E)
    (hw : w ≠ 0) (he : A w = (a : ℂ) • w) :
    ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u := by
  refine ⟨(‖w‖⁻¹ : ℂ) • w, norm_smul_inv_norm hw, ?_⟩
  rw [map_smul, he, smul_comm]

theorem clm_exists_unit_eigenpair_bound [Nontrivial E] (A : E →L[ℂ] E)
    (hA : IsCompactOp (A : E →ₗ[ℂ] E))
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ a : ℝ, ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u ∧
      ∀ x, ‖A x‖ ≤ |a| * ‖x‖ := by
  by_cases hzero : ‖A‖ = 0
  · have hAz : A = 0 := norm_eq_zero.mp hzero
    obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := E) zero_le_one
    refine ⟨0, u, mem_sphere_zero_iff_norm.mp hu, ?_, ?_⟩ <;> simp [hAz]
  have hc : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  obtain ⟨u, hu, heu⟩ := compact_square_unit_eigenvector A hA hsym hc
  let w : E := A u + (‖A‖ : ℂ) • u
  by_cases hw : w = 0
  · have he : A u = ((-‖A‖ : ℝ) : ℂ) • u := by
      have hh : A u + (‖A‖ : ℂ) • u = 0 := hw
      simpa using (eq_neg_of_add_eq_zero_left hh)
    refine ⟨-‖A‖, u, hu, he, ?_⟩
    intro x
    simpa only [abs_neg, abs_of_nonneg (norm_nonneg A)] using A.le_opNorm x
  · have he : A w = (‖A‖ : ℂ) • w := by
      simp only [w, map_add, map_smul, heu, Complex.ofReal_pow]
      module
    obtain ⟨v, hv, hev⟩ := normalize_eigenvector (A : E →ₗ[ℂ] E) ‖A‖ w hw he
    refine ⟨‖A‖, v, hv, hev, ?_⟩
    intro x
    simpa only [abs_of_nonneg (norm_nonneg A)] using A.le_opNorm x

theorem exists_unit_eigenpair_bound [Nontrivial E] (A : E →ₗ[ℂ] E)
    (hA : IsCompactOp A) (hsym : A.IsSymmetric) :
    ∃ a : ℝ, ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u ∧
      ∀ x, ‖A x‖ ≤ |a| * ‖x‖ := by
  obtain ⟨C, _, hC⟩ := compact_bound A hA
  exact clm_exists_unit_eigenpair_bound (A.mkContinuous C hC) hA hsym

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE CompactEigenpair

-- BEGIN COMPLETE MODULE SpectralDecay
section

open Filter Topology
namespace TeschlODE.SturmLiouville.Proof

/-- Compactness makes a decreasing sequence of orthogonal eigenvalues vanish. -/
theorem eigenvalues_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (u : ℕ → E) (a : ℕ → ℝ) (hu : Orthonormal ℂ u)
    (he : ∀ n, A (u n) = (a n : ℂ) • u n)
    (ha : Antitone (fun n => |a n|)) : Tendsto a atTop (𝓝 0) := by
  have hb : Bornology.IsBounded (Set.range u) := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    rintro _ ⟨n,rfl⟩
    simp [Metric.mem_closedBall, dist_zero_right, hu.norm_eq_one]
  obtain ⟨φ,hφ,g,hg⟩ := hA u hb
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg (ε/2) (half_pos hε)
  have hdist : dist (A (u (φ N))) (A (u (φ (N+1)))) < ε := by
    have h1 := hN N le_rfl
    have h2 := hN (N+1) (Nat.le_succ N)
    have ht := dist_triangle (A (u (φ N))) g (A (u (φ (N+1))))
    rw [dist_comm g] at ht
    linarith
  have ho : inner ℂ (A (u (φ N))) (A (u (φ (N+1)))) = 0 := by
    rw [he,he,inner_smul_left,inner_smul_right,
      hu.inner_eq_zero (hφ.injective.ne (by omega)),mul_zero,mul_zero]
  have hs := @norm_sub_sq ℂ E _ _ _ (A (u (φ N))) (A (u (φ (N+1))))
  rw [ho] at hs
  simp only [map_zero, mul_zero, sub_zero] at hs
  have heN : ‖A (u (φ N))‖ = |a (φ N)| := by
    rw [he, norm_smul, hu.norm_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hle : |a (φ N)| ≤ dist (A (u (φ N))) (A (u (φ (N+1)))) := by
    rw [dist_eq_norm, ← heN]
    nlinarith [norm_nonneg (A (u (φ N))), norm_nonneg (A (u (φ N))-A (u (φ (N+1)))),
      sq_nonneg ‖A (u (φ (N+1)))‖]
  refine ⟨φ N,fun n hn => ?_⟩
  simpa [Real.dist_eq] using (ha hn).trans_lt (hle.trans_lt hdist)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SpectralDecay

-- BEGIN COMPLETE MODULE CompactSequence
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_extension (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) (hE : ¬ FiniteDimensional ℂ E)
    (n : ℕ) (p : EigenPrefix A n) : Nonempty (EigenExtension p) := by
  let K := prefixComplement p.u
  have hK : IsClosed (K : Set E) := Submodule.isClosed_orthogonal _
  have hi : ∀ x ∈ K, A x ∈ K := prefixComplement_invariant A hsym p.u p.a p.eigen
  let : Nontrivial K := prefixComplement_nontrivial p.u hE
  obtain ⟨a,u,hu,he,hb⟩ := exists_unit_eigenpair_bound (A.restrict hi)
    (compact_restrict A hA K hK hi) (hsym.restrict_invariant hi)
  refine ⟨⟨u.val,a,hu,u.property,?_,?_⟩⟩
  · exact congrArg Subtype.val he
  · intro w hw
    exact hb ⟨w,hw⟩

/-- Countable maximal-modulus eigenvectors, constructed inside the original space. -/
theorem infinite_spectral_sequence (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) (hE : ¬ FiniteDimensional ℂ E) :
    ∃ (a : ℕ → ℝ) (u : ℕ → E), Orthonormal ℂ u ∧
      (∀ n, A (u n) = (a n : ℂ) • u n) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ n w, (∀ j < n, inner ℂ (u j) w = 0) → ‖A w‖ ≤ |a n| * ‖w‖) := by
  let next := fun n p => Classical.choice (exists_extension A hA hsym hE n p)
  refine ⟨valueSequence next,eigenSequence next,eigenSequence_orthonormal next,
    eigenSequence_eigen next,?_,eigenSequence_bound next⟩
  exact eigenvalues_tendsto_zero A hA _ _ (eigenSequence_orthonormal next)
    (eigenSequence_eigen next) (valueSequence_antitone next)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE CompactSequence

-- BEGIN COMPLETE MODULE SpectralExpansion
section

noncomputable section
open scoped BigOperators
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Finite-rank orthogonal expansion operator for a sequence. -/
def partialProjection (u : ℕ → E) (n : ℕ) : E →ₗ[ℂ] E where
  toFun x := ∑ j ∈ Finset.range n, inner ℂ (u j) x • u j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

theorem partialProjection_orthogonal (u : ℕ → E) (hu : Orthonormal ℂ u)
    (n : ℕ) (x : E) (j : ℕ) (hj : j < n) :
    inner ℂ (u j) (x-partialProjection u n x) = 0 := by
  change inner ℂ (u j) (x-∑ k ∈ Finset.range n, inner ℂ (u k) x • u k) = 0
  rw [inner_sub_right,hu.inner_right_sum _ (Finset.mem_range.mpr hj),sub_self]

theorem partialProjection_residual_bound (u : ℕ → E) (hu : Orthonormal ℂ u)
    (n : ℕ) (x : E) : ‖x-partialProjection u n x‖ ≤ ‖x‖ := by
  have ho : inner ℂ (partialProjection u n x) (x-partialProjection u n x) = 0 := by
    change inner ℂ (∑ j ∈ Finset.range n, inner ℂ (u j) x • u j) _ = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro j hj
    rw [inner_smul_left,partialProjection_orthogonal u hu n x j (Finset.mem_range.mp hj),mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (partialProjection u n x) (x-partialProjection u n x) ho
  rw [add_sub_cancel] at hp
  nlinarith [norm_nonneg (x-partialProjection u n x), norm_nonneg x,
    sq_nonneg ‖partialProjection u n x‖]

theorem partialProjection_commute (A : E →ₗ[ℂ] E) (hsym : A.IsSymmetric)
    (u : ℕ → E) (a : ℕ → ℝ) (he : ∀ j, A (u j) = (a j : ℂ) • u j)
    (n : ℕ) (x : E) : partialProjection u n (A x) = A (partialProjection u n x) := by
  change (∑ j ∈ Finset.range n, inner ℂ (u j) (A x) • u j) =
    A (∑ j ∈ Finset.range n, inner ℂ (u j) x • u j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hsym,he,inner_smul_left,map_smul,he,smul_smul]
  simp [mul_comm]

theorem partialProjection_range_tendsto (A : E →ₗ[ℂ] E) (hsym : A.IsSymmetric)
    (u : ℕ → E) (a : ℕ → ℝ) (hu : Orthonormal ℂ u)
    (he : ∀ j, A (u j) = (a j : ℂ) • u j)
    (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ n x, (∀ j < n, inner ℂ (u j) x = 0) → ‖A x‖ ≤ |a n| *‖x‖)
    (g : E) : Tendsto (fun n => partialProjection u n (A g)) atTop (𝓝 (A g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g := fun n => |a n| * ‖g‖) (fun _ => norm_nonneg _)
  · intro n
    rw [norm_sub_rev,partialProjection_commute A hsym u a he,← map_sub]
    exact (hb n _ (partialProjection_orthogonal u hu n g)).trans
      (mul_le_mul_of_nonneg_left (partialProjection_residual_bound u hu n g) (abs_nonneg _))
  · simpa using ha.abs.mul_const ‖g‖

theorem partialProjection_dense_tendsto (A : E →ₗ[ℂ] E) (u : ℕ → E)
    (hu : Orthonormal ℂ u)
    (hlim : ∀ g, Tendsto (fun n => partialProjection u n (A g)) atTop (𝓝 (A g)))
    (hd : Dense (LinearMap.range A : Set E)) (x : E) :
    Tendsto (fun n => partialProjection u n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp (hd x) (ε/2) (half_pos hε)
  obtain ⟨g,rfl⟩ := hy
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim g) (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have heq : x-partialProjection u n x =
      (x-A g)-partialProjection u n (x-A g) + (A g-partialProjection u n (A g)) := by
    rw [map_sub]
    abel
  have ht := norm_add_le ((x-A g)-partialProjection u n (x-A g))
    (A g-partialProjection u n (A g))
  rw [← heq] at ht
  have hb := partialProjection_residual_bound u hu n (x-A g)
  have hh := hN n hn
  rw [dist_eq_norm] at hxy hh ⊢
  rw [norm_sub_rev] at hh ⊢
  linarith

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SpectralExpansion

-- BEGIN COMPLETE MODULE GreenSpectralBasis
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof

structure GreenBasis {p q r : ℝ → ℝ} {a b α β : ℝ}
    (D : GreenData p q r a b α β) (h : RegularSL p q r a b) where
  value : ℕ → ℝ
  vector : ℕ → (regularWeight h).Space
  orthonormal : Orthonormal ℂ vector
  eigen : ∀n,D.operator h (vector n) = (value n:ℂ) • vector n
  vanish : Tendsto value atTop (nhds 0)
  complete : ∀f,Tendsto (fun n => partialProjection vector n f) atTop (nhds f)

lemma exists_green_basis {p q r : ℝ → ℝ} {a b α β : ℝ}
    (D : GreenData p q r a b α β) (h : RegularSL p q r a b) : Nonempty (GreenBasis D h) := by
  obtain ⟨s,u,hu,he,hs,hb⟩ := infinite_spectral_sequence (D.operator h).toLinearMap
    (D.operator_compact h) (D.operator_symmetric h) (regularWeight h).infinite_dimensional
  refine ⟨⟨s,u,hu,he,hs,?_⟩⟩
  exact partialProjection_dense_tendsto (D.operator h).toLinearMap u hu
    (partialProjection_range_tendsto _ (D.operator_symmetric h) u s hu he hs hb)
    (D.operator_dense_range h)

namespace GreenBasis
variable {p q r : ℝ → ℝ} {a b α β : ℝ} {D : GreenData p q r a b α β}
  {h : RegularSL p q r a b} (B : GreenBasis D h)

lemma exists_coefficient {f : (regularWeight h).Space} (hf : f ≠ 0) :
    ∃n, inner ℂ (B.vector n) f ≠ 0 := by
  by_contra hn
  have hz : ∀n, inner ℂ (B.vector n) f = 0 := by simpa only [not_exists, not_not] using hn
  have hp : ∀n,partialProjection B.vector n f=0 := by
    intro n
    simp [partialProjection,hz]
  have hc := B.complete f
  simp_rw [hp] at hc
  exact hf (tendsto_nhds_unique hc tendsto_const_nhds)

end GreenBasis
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenSpectralBasis

-- BEGIN COMPLETE MODULE GreenNativeEigen
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.GreenData
variable {p q r : ℝ → ℝ} {a b α β : ℝ} (D : GreenData p q r a b α β)
  (h : RegularSL p q r a b)

lemma native_eigen_resolvent {z : ℂ} {f : ℝ → ℂ}
    (hf : IsSLEigenfunction p q r a b α β z f) :
    (z-(D.param:ℂ)) • D.operator h ((regularWeight h).restrict f hf.1.1.continuousOn) =
      (regularWeight h).restrict f hf.1.1.continuousOn := by
  let v := (regularWeight h).restrict f hf.1.1.continuousOn
  have he : (D.operator h) ((z-(D.param:ℂ)) • v) = v := by
    apply (regularWeight h).space_ext
    intro x hx
    rw [D.operator_apply h _ x hx]
    calc
      _ = greenApply D.kernel r a b (fun t => SLOp p q r a b f t-(D.param:ℂ)*f t) x := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [(regularWeight h).extend_smul]
        have ht' : t∈Set.Icc a b := Set.uIcc_of_le h.1.le ▸ ht
        rw [(regularWeight h).extend_restrict f hf.1.1.continuousOn ht',hf.2.2 t ht']
        ring
      _ = _ := by rw [D.left_inverse f hf.1 x hx]; exact ((regularWeight h).extend_restrict f hf.1.1.continuousOn hx).symm
  simpa only [map_smul] using he

lemma native_eigen_vector_ne_zero {z : ℂ} {f : ℝ → ℂ}
    (hf : IsSLEigenfunction p q r a b α β z f) :
    (regularWeight h).restrict f hf.1.1.continuousOn ≠ 0 := by
  intro hz
  obtain ⟨x,hx,hfx⟩ := hf.2.1
  have he := congrArg (fun g => (regularWeight h).extend g x) hz
  rw [(regularWeight h).extend_restrict f hf.1.1.continuousOn hx] at he
  exact hfx he
end GreenData

namespace GreenBasis
variable {p q r : ℝ → ℝ} {a b α β : ℝ} {D : GreenData p q r a b α β}
  {h : RegularSL p q r a b} (B : GreenBasis D h)

lemma classify_native_eigenvalue {z : ℂ} {f : ℝ → ℂ}
    (hf : IsSLEigenfunction p q r a b α β z f) :
    ∃n, z=((D.param+1/B.value n:ℝ):ℂ) := by
  let v := (regularWeight h).restrict f hf.1.1.continuousOn
  obtain ⟨n,hn⟩ := B.exists_coefficient (GreenData.native_eigen_vector_ne_zero h hf)
  have he := congrArg (fun w => inner ℂ (B.vector n) w) (D.native_eigen_resolvent h hf)
  change inner ℂ (B.vector n) ((z-(D.param:ℂ)) • D.operator h v) = inner ℂ (B.vector n) v at he
  have hsym : inner ℂ (B.vector n) (D.operator h v) = inner ℂ (D.operator h (B.vector n)) v := (D.operator_symmetric h _ _).symm
  rw [inner_smul_right,hsym,B.eigen,inner_smul_left] at he
  simp only [Complex.conj_ofReal] at he
  have hz : (z-(D.param:ℂ))*(B.value n:ℂ)=1 := by
    apply (mul_right_cancel₀ hn)
    linear_combination he
  have hs : (B.value n:ℂ)≠0 := by intro hs; rw [hs,mul_zero] at hz; exact zero_ne_one hz
  refine ⟨n,?_⟩
  push_cast
  field_simp
  linear_combination hz
end GreenBasis
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenNativeEigen

-- BEGIN COMPLETE MODULE SLDomainScalar
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma slDomain_const_mul {p : ℝ → ℝ} {a b α β : ℝ} {f : ℝ → ℂ}
    (hab : a<b) (hf : SLDomain p a b α β f) (c : ℂ) :
    SLDomain p a b α β (fun t => c*f t) := by
  have hd (t : ℝ) (ht : t∈Icc a b) :
      derivWithin (fun t => c*f t) (Icc a b) t = c*derivWithin f (Icc a b) t :=
    ((hf.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt.const_mul c).derivWithin
      (uniqueDiffOn_Icc hab t ht)
  refine ⟨contDiffOn_const.mul hf.1,?_,?_⟩
  · rw [hd a ⟨le_rfl,hab.le⟩]
    linear_combination c*hf.2.1
  · rw [hd b ⟨hab.le,le_rfl⟩]
    linear_combination c*hf.2.2

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLDomainScalar

-- BEGIN COMPLETE MODULE SLOperatorScalar
section

namespace TeschlODE.SturmLiouville.Proof
lemma slOp_const_mul {p q r : ℝ → ℝ} {a b α β : ℝ} (h : RegularSL p q r a b)
    {f : ℝ → ℂ} (hf : SLDomain p a b α β f) (c : ℂ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    SLOp p q r a b (fun t => c*f t) x = c*SLOp p q r a b f x := by
  have hu := uniqueDiffOn_Icc h.1
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      derivWithin (fun t => c*f t) (Set.Icc a b) t = c*derivWithin f (Set.Icc a b) t :=
    ((hf.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt.const_mul c).derivWithin (hu t ht)
  have hp : ContDiffOn ℝ 1 (fun t => (p t:ℂ)) (Set.Icc a b) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h.2.2.2.1
  have hflux := hp.mul (hf.1.derivWithin hu (m := 1) (by norm_num))
  have he : Set.EqOn (fun t => (p t:ℂ)*derivWithin (fun t => c*f t) (Set.Icc a b) t)
      (fun t => c*((p t:ℂ)*derivWithin f (Set.Icc a b) t)) (Set.Icc a b) := by
    intro t ht
    dsimp only
    rw [hd t ht]
    ring
  unfold SLOp
  rw [derivWithin_congr he (he hx),
    ((hflux.differentiableOn (by norm_num) x hx).hasDerivWithinAt.const_mul c).derivWithin (hu x hx)]
  ring
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLOperatorScalar

-- BEGIN COMPLETE MODULE GreenEigenvectors
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.GreenData
variable {p q r : ℝ → ℝ} {a b α β : ℝ} (D : GreenData p q r a b α β)
  (h : RegularSL p q r a b)

lemma eigenvalue_ne_zero {u : (regularWeight h).Space} (hu : u ≠ 0) {s : ℝ}
    (he : D.operator h u = (s:ℂ) • u) : s ≠ 0 := by
  intro hs
  have hz : D.operator h u = D.operator h 0 := by simpa [hs] using he
  exact hu (D.operator_injective h hz)

lemma eigenvector_native {u : (regularWeight h).Space} (hu : u ≠ 0) {s : ℝ}
    (he : D.operator h u = (s:ℂ) • u) :
    IsSLEigenfunction p q r a b α β ((D.param+1/s:ℝ):ℂ) ((regularWeight h).extend u) := by
  let f := (regularWeight h).extend u
  let v := greenApply D.kernel r a b f
  have hs : (s:ℂ) ≠ 0 := by exact_mod_cast D.eigenvalue_ne_zero h hu he
  have hv := D.domain f ((regularWeight h).extend_continuous u).continuousOn
  have hev (x : ℝ) (hx : x ∈ Set.Icc a b) : v x = (s:ℂ)*f x := by
    dsimp only [v,f]
    rw [← D.operator_apply h u x hx, he, (regularWeight h).extend_smul]
  have hscaled : Set.EqOn (fun x => (s:ℂ)⁻¹*v x) f (Set.Icc a b) := by
    intro x hx
    dsimp only
    rw [hev x hx]
    simp [hs]
  refine ⟨slDomain_congr h.1.le hscaled (slDomain_const_mul h.1 hv _),?_,?_⟩
  · by_contra hn
    push Not at hn
    apply hu
    apply (regularWeight h).space_ext
    intro x hx
    have hz : f x = 0 := hn x hx
    simpa [f] using hz
  · intro x hx
    have hi := D.right_inverse f ((regularWeight h).extend_continuous u).continuousOn x hx
    rw [← slOp_congr hscaled hx, slOp_const_mul h hv _ hx]
    dsimp only [v] at hev
    rw [hev x hx] at hi
    push_cast
    have hle : SLOp p q r a b (greenApply D.kernel r a b f) x = f x+(D.param:ℂ)*((s:ℂ)*f x) := by linear_combination hi
    rw [hle]
    field_simp
    ring

end TeschlODE.SturmLiouville.Proof.GreenData
end
-- END COMPLETE MODULE GreenEigenvectors

-- BEGIN COMPLETE MODULE WeightedFiniteSums
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.IntervalWeight
variable (W : IntervalWeight)
@[simp] lemma extend_sum {ι : Type*} (s : Finset ι) (f : ι → W.Space) (x : ℝ) :
    W.extend (∑i∈s,f i) x = ∑i∈s,W.extend (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert,hi,ih]
end TeschlODE.SturmLiouville.Proof.IntervalWeight
end
-- END COMPLETE MODULE WeightedFiniteSums

-- BEGIN COMPLETE MODULE GreenUniformExpansion
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof.GreenBasis
variable {p q r : ℝ → ℝ} {a b α β : ℝ} {D : GreenData p q r a b α β}
  {h : RegularSL p q r a b} (B : GreenBasis D h)

lemma uniform_range_expansion (g : (regularWeight h).Space) :
    Tendsto (fun n => (regularWeight h).toContinuous (partialProjection B.vector n (D.operator h g)))
      atTop (nhds ((regularWeight h).toContinuous (D.operator h g))) := by
  have hc := ((regularWeight h).kernelUniform D.continuousKernel).continuous.continuousAt.tendsto.comp (B.complete g)
  have he (n : ℕ) := partialProjection_commute (D.operator h).toLinearMap (D.operator_symmetric h)
    B.vector B.value B.eigen n g
  change Tendsto (fun n => (regularWeight h).kernelUniform D.continuousKernel (partialProjection B.vector n g)) _ _ at hc
  convert hc using 1
  · funext n
    exact congrArg (regularWeight h).toContinuous (he n)
  · rfl

end TeschlODE.SturmLiouville.Proof.GreenBasis
end
-- END COMPLETE MODULE GreenUniformExpansion

-- BEGIN COMPLETE MODULE SLEigenScalar
section

namespace TeschlODE.SturmLiouville.Proof
lemma sl_eigen_const_mul {p q r : ℝ → ℝ} {a b α β : ℝ} (h : RegularSL p q r a b)
    {z : ℂ} {f : ℝ → ℂ} (hf : IsSLEigenfunction p q r a b α β z f) (c : ℂ) (hc : c ≠ 0) :
    IsSLEigenfunction p q r a b α β z (fun x => c*f x) := by
  obtain ⟨x,hx,hfx⟩ := hf.2.1
  refine ⟨slDomain_const_mul h.1 hf.1 c,⟨x,hx,mul_ne_zero hc hfx⟩,?_⟩
  intro t ht
  rw [slOp_const_mul h hf.1 c ht,hf.2.2 t ht]
  ring
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLEigenScalar

-- BEGIN COMPLETE MODULE ExponentialKernel
section

open MeasureTheory Set
namespace TeschlODE.SturmLiouville.Proof

lemma integral_exp_shift (a t L : ℝ) (hL : L ≠ 0) :
    (∫ s in a..t, Real.exp (L*(s-a))) = (Real.exp (L*(t-a))-1)/L := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (L*(s-a))/L)
      (Real.exp (L*(s-a))) s := by
    have hh := (((hasDerivAt_id s).sub_const a).const_mul L).exp.div_const L
    simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ hL] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (L*(s-a)))).intervalIntegrable a t)]
  simp
  ring

lemma weighted_exp_integral_le (a t L : ℝ) (hL : 0 < L) :
    Real.exp (-L*(t-a)) * (∫ s in a..t, Real.exp (L*(s-a))) ≤ 1/L := by
  rw [integral_exp_shift a t L hL.ne']
  have he : Real.exp (-L*(t-a))*Real.exp (L*(t-a))=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hL).mpr
  nlinarith [Real.exp_pos (-L*(t-a))]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE ExponentialKernel

-- BEGIN COMPLETE MODULE BieleckiMap
section

open MeasureTheory Set
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def intervalExtend {a b : ℝ} (hab : a ≤ b)
    (f : C(Icc a b, E)) (t : ℝ) : E := f (projIcc a b hab t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma intervalExtend_continuous {a b : ℝ} (hab : a ≤ b) (f : C(Icc a b, E)) :
    Continuous (intervalExtend hab f) := f.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma intervalExtend_of_mem {a b t : ℝ} (hab : a ≤ b) (f : C(Icc a b, E))
    (ht : t ∈ Icc a b) : intervalExtend hab f t = f ⟨t,ht⟩ := by
  exact congrArg f (projIcc_of_mem hab ht)

lemma continuous_primitive (f : ℝ → E) (hf : Continuous f) (a : ℝ) :
    Continuous (fun t => ∫ s in a..t, f s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hf.integral_hasStrictDerivAt a t).hasDerivAt.continuousAt

noncomputable def weightedInput {a b : ℝ} (hab : a ≤ b) (L : ℝ)
    (A : C(Icc a b, E →L[ℝ] E)) (z : C(Icc a b,E)) (s : ℝ) : E :=
  Real.exp (L*(s-a)) • A (projIcc a b hab s) (intervalExtend hab z s)

omit [CompleteSpace E] in
lemma weightedInput_continuous {a b : ℝ} (hab : a ≤ b) (L : ℝ)
    (A : C(Icc a b, E →L[ℝ] E)) (z : C(Icc a b,E)) :
    Continuous (weightedInput hab L A z) := by
  unfold weightedInput
  exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (L*(s-a)))).smul
    ((A.continuous.comp continuous_projIcc).clm_apply (intervalExtend_continuous hab z))

noncomputable def bieleckiMap {a b : ℝ} (hab : a ≤ b) (L : ℝ)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) (z : C(Icc a b,E)) : C(Icc a b,E) where
  toFun t := Real.exp (-L*(t.val-a)) • (y + ∫ s in a..t.val, weightedInput hab L A z s)
  continuous_toFun := (by fun_prop : Continuous (fun t : Icc a b => Real.exp (-L*(t.val-a)))).smul (continuous_const.add
    ((continuous_primitive _ (weightedInput_continuous hab L A z) a).comp continuous_subtype_val))

lemma bieleckiMap_sub {a b : ℝ} (hab : a ≤ b) (L : ℝ)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) (z w : C(Icc a b,E)) (t : Icc a b) :
    bieleckiMap hab L A y z t - bieleckiMap hab L A y w t =
      Real.exp (-L*(t.val-a)) • (∫ s in a..t.val,
        Real.exp (L*(s-a)) • A (projIcc a b hab s)
          (intervalExtend hab z s - intervalExtend hab w s)) := by
  change (Real.exp (-L*(t.val-a)) : ℝ) • (y + _) -
    (Real.exp (-L*(t.val-a)) : ℝ) • (y + _) = _
  rw [← smul_sub, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
    ((weightedInput_continuous hab L A z).intervalIntegrable a t.val)
    ((weightedInput_continuous hab L A w).intervalIntegrable a t.val)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp [weightedInput, map_sub, smul_sub]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE BieleckiMap

-- BEGIN COMPLETE MODULE BieleckiContraction
section

open MeasureTheory Set
open scoped NNReal
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma weightedInput_diff_bound {a b : ℝ} (hab : a ≤ b) (L : ℝ)
    (A : C(Icc a b, E →L[ℝ] E)) (z w : C(Icc a b,E)) (s : ℝ) :
    ‖Real.exp (L*(s-a)) • A (projIcc a b hab s)
       (intervalExtend hab z s - intervalExtend hab w s)‖ ≤
      Real.exp (L*(s-a)) * (‖A‖ * ‖z-w‖) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ ‖A (projIcc a b hab s)‖ *
        ‖intervalExtend hab z s - intervalExtend hab w s‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖z-w‖ := mul_le_mul (A.norm_coe_le_norm _)
      ((z-w).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg A)

lemma bieleckiMap_norm_sub_le {a b : ℝ} (hab : a ≤ b) (L : ℝ) (hL : 0<L)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) (z w : C(Icc a b,E)) :
    ‖bieleckiMap hab L A y z - bieleckiMap hab L A y w‖ ≤ (‖A‖/L)*‖z-w‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖bieleckiMap hab L A y z t - bieleckiMap hab L A y w t‖ ≤ _
  rw [bieleckiMap_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) t.property.1
    (Filter.Eventually.of_forall (fun s _ => weightedInput_diff_bound hab L A z w s))
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (L*(s-a))*(‖A‖*‖z-w‖))).intervalIntegrable a t.val)
  have hh := mul_le_mul_of_nonneg_left hi (Real.exp_pos (-L*(t.val-a))).le
  rw [intervalIntegral.integral_mul_const] at hh
  calc
    _ ≤ Real.exp (-L*(t.val-a)) * ((∫ s in a..t.val, Real.exp (L*(s-a)))*(‖A‖*‖z-w‖)) := hh
    _ = (Real.exp (-L*(t.val-a)) * (∫ s in a..t.val, Real.exp (L*(s-a))))*(‖A‖*‖z-w‖) := by ring
    _ ≤ (1/L)*(‖A‖*‖z-w‖) := mul_le_mul_of_nonneg_right
      (weighted_exp_integral_le a t.val L hL) (by positivity)
    _ = _ := by ring

lemma bieleckiMap_exists_fixed {a b : ℝ} (hab : a ≤ b)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) :
    ∃ z : C(Icc a b,E), bieleckiMap hab (‖A‖+1) A y z = z := by
  let K : ℝ≥0 := ⟨‖A‖/(‖A‖+1), by positivity⟩
  have hK : (K : ℝ)<1 := by dsimp [K]; exact (div_lt_one (by positivity)).mpr (by linarith)
  have hc : ContractingWith K (bieleckiMap hab (‖A‖+1) A y) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul (fun z w => ?_)⟩
    rw [dist_eq_norm, dist_eq_norm]
    change ‖bieleckiMap hab (‖A‖+1) A y z - bieleckiMap hab (‖A‖+1) A y w‖ ≤
      (‖A‖/(‖A‖+1))*‖z-w‖
    exact bieleckiMap_norm_sub_le hab (‖A‖+1) (by positivity) A y z w
  exact ⟨hc.fixedPoint _, hc.fixedPoint_isFixedPt⟩

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE BieleckiContraction

-- BEGIN COMPLETE MODULE LinearIntervalODE
section

open MeasureTheory Set
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma linear_interval_solution {a b : ℝ} (hab : a ≤ b)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) :
    ∃ u : ℝ → E, ContDiff ℝ 1 u ∧ u a = y ∧
      ∀ t (ht : t ∈ Icc a b), HasDerivAt u (A ⟨t,ht⟩ (u t)) t := by
  obtain ⟨z,hz⟩ := bieleckiMap_exists_fixed hab A y
  let L := ‖A‖+1
  let v := weightedInput hab L A z
  have hv : Continuous v := weightedInput_continuous hab L A z
  let u : ℝ → E := fun t => y + ∫ s in a..t, v s
  have hd (t : ℝ) : HasDerivAt u (v t) t := by
    simpa [u] using (hv.integral_hasStrictDerivAt a t).hasDerivAt.const_add y
  have hu : ContDiff ℝ 1 u := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (hd t).differentiableAt,
      (show deriv u = v from funext (fun t => (hd t).deriv)).symm ▸ hv⟩
  refine ⟨u, hu, by simp [u], ?_⟩
  intro t ht
  have heq : z ⟨t,ht⟩ = Real.exp (-L*(t-a)) • u t := by
    have hh := congrArg (fun f : C(Icc a b,E) => f ⟨t,ht⟩) hz
    exact hh.symm
  have hexp : Real.exp (L*(t-a))*Real.exp (-L*(t-a))=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring
  have hvt : v t = A ⟨t,ht⟩ (u t) := by
    dsimp [v, weightedInput]
    rw [intervalExtend_of_mem hab z ht, projIcc_of_mem hab ht, heq,
      map_smul, smul_smul, hexp, one_smul]
  exact hvt ▸ hd t

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE LinearIntervalODE

-- BEGIN COMPLETE MODULE SLSystem
section

open Set
namespace TeschlODE.SturmLiouville.Proof

noncomputable def slUpper : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).prod 0

noncomputable def slLower : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (0 : (ℂ × ℂ) →L[ℝ] ℂ).prod (ContinuousLinearMap.fst ℝ ℂ ℂ)

noncomputable def slSystem (p q r : ℝ → ℝ) (z : ℂ) (t : ℝ) :
    (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (p t : ℂ)⁻¹ • slUpper + ((q t : ℂ)-z*(r t : ℂ)) • slLower

lemma slSystem_apply (p q r : ℝ → ℝ) (z : ℂ) (t : ℝ) (v : ℂ × ℂ) :
    slSystem p q r z t v = ((p t : ℂ)⁻¹*v.2, ((q t : ℂ)-z*(r t : ℂ))*v.1) := by
  simp [slSystem, slUpper, slLower, smul_eq_mul]

lemma slSystem_continuousOn {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) :
    ContinuousOn (slSystem p q r z) (Icc a b) := by
  have hp : ContinuousOn (fun t => (p t : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hreg.2.2.2.1.continuousOn
  have hq : ContinuousOn (fun t => (q t : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hreg.2.2.1
  have hr : ContinuousOn (fun t => (r t : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hreg.2.1
  exact (hp.inv₀ (fun t ht => by exact_mod_cast (hreg.2.2.2.2 t ht).1.ne')).smul continuousOn_const |>.add
    ((hq.sub (continuousOn_const.mul hr)).smul continuousOn_const)

lemma slSystem_solution {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (v : ℂ × ℂ) :
    ∃ U : ℝ → ℂ × ℂ, ContDiff ℝ 1 U ∧ U a = v ∧
      ∀ t ∈ Icc a b, HasDerivAt U
        ((p t : ℂ)⁻¹*(U t).2, ((q t : ℂ)-z*(r t : ℂ))*(U t).1) t := by
  let A : C(Icc a b, (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) :=
    ⟨fun t => slSystem p q r z t.val, (slSystem_continuousOn hreg z).domRestrict⟩
  obtain ⟨U,hU,ha,hd⟩ := linear_interval_solution hreg.1.le A v
  refine ⟨U,hU,ha,?_⟩
  intro t ht
  have hh := hd t ht
  change HasDerivAt U (slSystem p q r z t (U t)) t at hh
  rwa [slSystem_apply] at hh

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLSystem

-- BEGIN COMPLETE MODULE SLSystemRegularity
section

open Set
open scoped ContDiff
namespace TeschlODE.SturmLiouville.Proof

lemma sl_system_regularity {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (U : ℝ → ℂ × ℂ)
    (hU : ContDiff ℝ 1 U)
    (hd : ∀ t∈Icc a b, HasDerivAt U
      ((p t : ℂ)⁻¹*(U t).2, ((q t : ℂ)-z*(r t : ℂ))*(U t).1) t) :
    ContDiffOn ℝ 2 (fun t => (U t).1) (Icc a b) ∧
    (∀t∈Icc a b, (p t : ℂ)*derivWithin (fun t => (U t).1) (Icc a b) t = (U t).2) ∧
    (∀t∈Icc a b, SLOp p q r a b (fun t => (U t).1) t = z*(U t).1) := by
  have huniq := uniqueDiffOn_Icc hreg.1
  have hp (t : ℝ) (ht : t∈Icc a b) : (p t : ℂ) ≠ 0 := by
    exact_mod_cast (hreg.2.2.2.2 t ht).1.ne'
  have hr (t : ℝ) (ht : t∈Icc a b) : (r t : ℂ) ≠ 0 := by
    exact_mod_cast (hreg.2.2.2.2 t ht).2.ne'
  have hd1 (t : ℝ) (ht : t∈Icc a b) : HasDerivAt (fun s => (U s).1)
      ((p t : ℂ)⁻¹*(U t).2) t := by
    convert! (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hd t ht) using 1
  have hd2 (t : ℝ) (ht : t∈Icc a b) : HasDerivAt (fun s => (U s).2)
      (((q t : ℂ)-z*(r t : ℂ))*(U t).1) t := by
    convert! (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hd t ht) using 1
  have hdf (t : ℝ) (ht : t∈Icc a b) :
      derivWithin (fun t => (U t).1) (Icc a b) t = (p t : ℂ)⁻¹*(U t).2 :=
    (hd1 t ht).hasDerivWithinAt.derivWithin (huniq t ht)
  have hflux (t : ℝ) (ht : t∈Icc a b) :
      (p t : ℂ)*derivWithin (fun t => (U t).1) (Icc a b) t = (U t).2 := by
    rw [hdf t ht]
    simp [hp t ht]
  have hpc : ContDiffOn ℝ 1 (fun t => (p t : ℂ)) (Icc a b) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hreg.2.2.2.1
  have hc : ContDiffOn ℝ 1 (fun t => (p t : ℂ)⁻¹*(U t).2) (Icc a b) :=
    (hpc.inv hp).mul hU.snd.contDiffOn
  refine ⟨?_,hflux,?_⟩
  · rw [show (2 : ℕ∞ω)=1+1 from rfl, contDiffOn_succ_iff_derivWithin huniq]
    refine ⟨hU.fst.contDiffOn.differentiableOn (by norm_num), by simp, ?_⟩
    exact hc.congr (fun t ht => hdf t ht)
  · intro t ht
    have hfluxd : HasDerivWithinAt
        (fun t => (p t : ℂ)*derivWithin (fun t => (U t).1) (Icc a b) t)
        (((q t : ℂ)-z*(r t : ℂ))*(U t).1) (Icc a b) t := by
      apply (hd2 t ht).hasDerivWithinAt.congr
      · exact fun s hs => hflux s hs
      · exact hflux t ht
    rw [SLOp, hfluxd.derivWithin (huniq t ht)]
    field_simp [hr t ht]
    ring

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLSystemRegularity

-- BEGIN COMPLETE MODULE LinearIntervalTerminal
section

open Set
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma linear_interval_terminal [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (A : C(Icc a b, E →L[ℝ] E)) (y : E) :
    ∃ u : ℝ → E, ContDiff ℝ 1 u ∧ u b = y ∧
      ∀ t (ht : t ∈ Icc a b), HasDerivAt u (A ⟨t,ht⟩ (u t)) t := by
  let flip : C(Icc (-b) (-a), Icc a b) := {
    toFun := fun t => ⟨-t.val, by constructor <;> linarith [t.property.1,t.property.2]⟩
    continuous_toFun := by fun_prop }
  let B : C(Icc (-b) (-a), E →L[ℝ] E) := -(A.comp flip)
  obtain ⟨v,hv,hb,hd⟩ := linear_interval_solution (neg_le_neg hab) B y
  refine ⟨fun t => v (-t), hv.comp contDiff_neg, by simpa using hb, ?_⟩
  intro t ht
  have ht' : -t ∈ Icc (-b) (-a) := ⟨neg_le_neg ht.2,neg_le_neg ht.1⟩
  have hh := (hd (-t) ht').scomp t (hasDerivAt_neg t)
  simpa [B, flip, neg_smul, Function.comp_def] using hh

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE LinearIntervalTerminal

-- BEGIN COMPLETE MODULE SLEndpointSolutions
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma sl_left_solution {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z u v : ℂ) :
    ∃ f : ℝ → ℂ, ContDiffOn ℝ 2 f (Icc a b) ∧ f a=u ∧
      (p a : ℂ)*derivWithin f (Icc a b) a=v ∧
      ∀t∈Icc a b, SLOp p q r a b f t=z*f t := by
  obtain ⟨U,hU,ha,hd⟩ := slSystem_solution hreg z (u,v)
  obtain ⟨hf,hflux,he⟩ := sl_system_regularity hreg z U hU hd
  exact ⟨fun t => (U t).1,hf,congrArg Prod.fst ha,
    (hflux a ⟨le_rfl,hreg.1.le⟩).trans (congrArg Prod.snd ha),he⟩

lemma sl_right_solution {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z u v : ℂ) :
    ∃ f : ℝ → ℂ, ContDiffOn ℝ 2 f (Icc a b) ∧ f b=u ∧
      (p b : ℂ)*derivWithin f (Icc a b) b=v ∧
      ∀t∈Icc a b, SLOp p q r a b f t=z*f t := by
  let A : C(Icc a b, (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) :=
    ⟨fun t => slSystem p q r z t.val, (slSystem_continuousOn hreg z).domRestrict⟩
  obtain ⟨U,hU,hb,hd⟩ := linear_interval_terminal hreg.1.le A (u,v)
  have hd' : ∀t∈Icc a b, HasDerivAt U
      ((p t : ℂ)⁻¹*(U t).2, ((q t : ℂ)-z*(r t : ℂ))*(U t).1) t := by
    intro t ht
    have hh := hd t ht
    change HasDerivAt U (slSystem p q r z t (U t)) t at hh
    rwa [slSystem_apply] at hh
  obtain ⟨hf,hflux,he⟩ := sl_system_regularity hreg z U hU hd'
  exact ⟨fun t => (U t).1,hf,congrArg Prod.fst hb,
    (hflux b ⟨hreg.1.le,le_rfl⟩).trans (congrArg Prod.snd hb),he⟩

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLEndpointSolutions

-- BEGIN COMPLETE MODULE LinearIntervalUnique
section

open Set Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivWithinAt_right_of_Icc {a b t : ℝ} {f : ℝ → E} {v : E}
    (ht : t ∈ Ico a b) (hf : HasDerivWithinAt f v (Icc a b) t) :
    HasDerivWithinAt f v (Ici t) t := by
  apply hf.mono_of_mem_nhdsWithin
  apply Filter.mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)))
  intro x hx
  exact ⟨ht.1.trans hx.1, hx.2.le⟩

lemma linear_interval_unique {a b : ℝ} (hab : a ≤ b)
    (A : C(Icc a b, E →L[ℝ] E)) {f g : ℝ → E}
    (hf : ∀t (ht : t∈Icc a b), HasDerivWithinAt f (A ⟨t,ht⟩ (f t)) (Icc a b) t)
    (hg : ∀t (ht : t∈Icc a b), HasDerivWithinAt g (A ⟨t,ht⟩ (g t)) (Icc a b) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hv (t : ℝ) : LipschitzWith ‖A‖₊ (A (projIcc a b hab t)) :=
    (A (projIcc a b hab t)).lipschitz.weaken (by exact_mod_cast A.norm_coe_le_norm (projIcc a b hab t))
  apply ODE_solution_unique hv (fun t ht => (hf t ht).continuousWithinAt) ?_
    (fun t ht => (hg t ht).continuousWithinAt) ?_ ha
  · intro t ht
    rw [projIcc_of_mem hab ⟨ht.1,ht.2.le⟩]
    exact hasDerivWithinAt_right_of_Icc ht (hf t ⟨ht.1,ht.2.le⟩)
  · intro t ht
    rw [projIcc_of_mem hab ⟨ht.1,ht.2.le⟩]
    exact hasDerivWithinAt_right_of_Icc ht (hg t ⟨ht.1,ht.2.le⟩)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE LinearIntervalUnique

-- BEGIN COMPLETE MODULE LinearIntervalUniqueRight
section

open Set Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivWithinAt_left_of_Icc {a b t : ℝ} {f : ℝ → E} {v : E}
    (ht : t ∈ Ioc a b) (hf : HasDerivWithinAt f v (Icc a b) t) :
    HasDerivWithinAt f v (Iic t) t := by
  apply hf.mono_of_mem_nhdsWithin
  apply Filter.mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1)))
  intro x hx
  exact ⟨hx.2.le,hx.1.trans ht.2⟩

lemma linear_interval_unique_right {a b : ℝ} (hab : a ≤ b)
    (A : C(Icc a b, E →L[ℝ] E)) {f g : ℝ → E}
    (hf : ∀t (ht : t∈Icc a b), HasDerivWithinAt f (A ⟨t,ht⟩ (f t)) (Icc a b) t)
    (hg : ∀t (ht : t∈Icc a b), HasDerivWithinAt g (A ⟨t,ht⟩ (g t)) (Icc a b) t)
    (hb : f b = g b) : EqOn f g (Icc a b) := by
  have hv (t : ℝ) : LipschitzWith ‖A‖₊ (A (projIcc a b hab t)) :=
    (A (projIcc a b hab t)).lipschitz.weaken (by exact_mod_cast A.norm_coe_le_norm (projIcc a b hab t))
  apply ODE_solution_unique_of_mem_Icc_left (s := fun _ => Set.univ)
    (fun t _ => (hv t).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) ?_ (fun _ _ => trivial)
    (fun t ht => (hg t ht).continuousWithinAt) ?_ (fun _ _ => trivial) hb
  · intro t ht
    rw [projIcc_of_mem hab ⟨ht.1.le,ht.2⟩]
    exact hasDerivWithinAt_left_of_Icc ht (hf t ⟨ht.1.le,ht.2⟩)
  · intro t ht
    rw [projIcc_of_mem hab ⟨ht.1.le,ht.2⟩]
    exact hasDerivWithinAt_left_of_Icc ht (hg t ⟨ht.1.le,ht.2⟩)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE LinearIntervalUniqueRight

-- BEGIN COMPLETE MODULE SLNativeSystem
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma sl_native_system {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (he : ∀t∈Icc a b, SLOp p q r a b f t = z*f t) :
    ∀t∈Icc a b, HasDerivWithinAt
      (fun t => (f t, (p t : ℂ)*derivWithin f (Icc a b) t))
      (slSystem p q r z t (f t, (p t : ℂ)*derivWithin f (Icc a b) t)) (Icc a b) t := by
  have hu := uniqueDiffOn_Icc hreg.1
  have hp : ContDiffOn ℝ 1 (fun t => (p t : ℂ)) (Icc a b) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hreg.2.2.2.1
  have hflux : ContDiffOn ℝ 1
      (fun t => (p t : ℂ)*derivWithin f (Icc a b) t) (Icc a b) :=
    hp.mul (hf.derivWithin hu (by norm_num))
  intro t ht
  have hpt : (p t : ℂ) ≠ 0 := by exact_mod_cast (hreg.2.2.2.2 t ht).1.ne'
  have hrt : (r t : ℂ) ≠ 0 := by exact_mod_cast (hreg.2.2.2.2 t ht).2.ne'
  have hd := (hf.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hg := (hflux.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hv : derivWithin (fun t => (p t : ℂ)*derivWithin f (Icc a b) t) (Icc a b) t =
      ((q t : ℂ)-z*(r t : ℂ))*f t := by
    have hh := he t ht
    unfold SLOp at hh
    field_simp [hrt] at hh
    linear_combination -hh
  rw [slSystem_apply]
  rw [hv] at hg
  simpa [← mul_assoc,hpt] using hd.prodMk hg

lemma sl_solution_unique {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) (hg : ContDiffOn ℝ 2 g (Icc a b))
    (hef : ∀t∈Icc a b, SLOp p q r a b f t = z*f t)
    (heg : ∀t∈Icc a b, SLOp p q r a b g t = z*g t)
    (ha : f a = g a)
    (hda : (p a : ℂ)*derivWithin f (Icc a b) a =
      (p a : ℂ)*derivWithin g (Icc a b) a) : EqOn f g (Icc a b) := by
  let A : C(Icc a b, (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) :=
    ⟨fun t => slSystem p q r z t.val, (slSystem_continuousOn hreg z).domRestrict⟩
  have heq := linear_interval_unique hreg.1.le A
    (sl_native_system hreg z f hf hef) (sl_native_system hreg z g hg heg)
    (Prod.ext ha hda)
  intro t ht
  exact congrArg Prod.fst (heq ht)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLNativeSystem

-- BEGIN COMPLETE MODULE SLRealSolutions
section

open Set
open scoped ComplexConjugate
namespace TeschlODE.SturmLiouville.Proof

lemma slSystem_star (p q r : ℝ → ℝ) (lam t : ℝ) (v : ℂ × ℂ) :
    slSystem p q r (lam : ℂ) t (star v) = star (slSystem p q r (lam : ℂ) t v) := by
  apply Prod.ext <;> simp [slSystem_apply]

lemma sl_real_of_real_initial {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (lam : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (he : ∀t∈Icc a b, SLOp p q r a b f t=(lam : ℂ)*f t)
    (e : ℝ) (hend : e=a ∨ e=b)
    (he0 : star (f e)=f e)
    (he1 : star ((p e : ℂ)*derivWithin f (Icc a b) e)=
      (p e : ℂ)*derivWithin f (Icc a b) e) :
    ∀t∈Icc a b, (f t).re=f t := by
  let A : C(Icc a b, (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) :=
    ⟨fun t => slSystem p q r (lam : ℂ) t.val, (slSystem_continuousOn hreg (lam : ℂ)).domRestrict⟩
  let U := fun t => (f t,(p t : ℂ)*derivWithin f (Icc a b) t)
  have hU : ∀t (ht : t∈Icc a b), HasDerivWithinAt U (A ⟨t,ht⟩ (U t)) (Icc a b) t :=
    sl_native_system hreg (lam : ℂ) f hf he
  have hstar : ∀t (ht : t∈Icc a b), HasDerivWithinAt (fun t => star (U t))
      (A ⟨t,ht⟩ (star (U t))) (Icc a b) t := by
    intro t ht
    change HasDerivWithinAt _ (slSystem p q r (lam : ℂ) t (star (U t))) _ _
    rw [slSystem_star]
    exact (hU t ht).star
  have hinit : U e = star (U e) := Prod.ext he0.symm he1.symm
  have hEq : EqOn U (fun t => star (U t)) (Icc a b) := by
    rcases hend with rfl | rfl
    · exact linear_interval_unique hreg.1.le A hU hstar hinit
    · exact linear_interval_unique_right hreg.1.le A hU hstar hinit
  intro t ht
  apply Complex.conj_eq_iff_re.mp
  exact (congrArg Prod.fst (hEq ht)).symm

lemma sl_real_left_solution {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (lam u v : ℝ) :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ 2 (fun t => (f t : ℂ)) (Icc a b) ∧ f a=u ∧
      (p a : ℂ)*derivWithin (fun t => (f t : ℂ)) (Icc a b) a=(v : ℂ) ∧
      ∀t∈Icc a b, SLOp p q r a b (fun t => (f t : ℂ)) t=(lam : ℂ)*(f t : ℂ) := by
  obtain ⟨f,hf,ha,hda,he⟩ := sl_left_solution hreg (lam : ℂ) (u : ℂ) (v : ℂ)
  have hr := sl_real_of_real_initial hreg lam f hf he a (Or.inl rfl)
    (by rw [ha]; simp) (by rw [hda]; simp)
  refine ⟨fun t => (f t).re,hf.congr hr,?_,?_,?_⟩
  · simpa using congrArg Complex.re ha
  · rw [derivWithin_congr hr (hr a ⟨le_rfl,hreg.1.le⟩)]
    exact hda
  · intro t ht
    rw [slOp_congr hr ht,hr t ht]
    exact he t ht

lemma sl_real_right_solution {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (lam u v : ℝ) :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ 2 (fun t => (f t : ℂ)) (Icc a b) ∧ f b=u ∧
      (p b : ℂ)*derivWithin (fun t => (f t : ℂ)) (Icc a b) b=(v : ℂ) ∧
      ∀t∈Icc a b, SLOp p q r a b (fun t => (f t : ℂ)) t=(lam : ℂ)*(f t : ℂ) := by
  obtain ⟨f,hf,hb,hdb,he⟩ := sl_right_solution hreg (lam : ℂ) (u : ℂ) (v : ℂ)
  have hr := sl_real_of_real_initial hreg lam f hf he b (Or.inr rfl)
    (by rw [hb]; simp) (by rw [hdb]; simp)
  refine ⟨fun t => (f t).re,hf.congr hr,?_,?_,?_⟩
  · simpa using congrArg Complex.re hb
  · rw [derivWithin_congr hr (hr b ⟨hreg.1.le,le_rfl⟩)]
    exact hdb
  · intro t ht
    rw [slOp_congr hr ht,hr t ht]
    exact he t ht

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLRealSolutions

-- BEGIN COMPLETE MODULE SLProportional
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma boundary_initial_span (α : ℝ) (x y : ℂ)
    (hb : (Real.cos α : ℂ)*x-(Real.sin α : ℂ)*y=0) :
    (x,y) = ((Real.sin α : ℂ)*x+(Real.cos α : ℂ)*y) •
      ((Real.sin α : ℂ),(Real.cos α : ℂ)) := by
  have hs : (Real.sin α : ℂ)^2+(Real.cos α : ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq α
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination -x*hs+(Real.cos α : ℂ)*hb
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination -y*hs-(Real.sin α : ℂ)*hb

lemma slSystem_complex_smul (p q r : ℝ → ℝ) (z c : ℂ) (t : ℝ) (v : ℂ × ℂ) :
    slSystem p q r z t (c • v) = c • slSystem p q r z t v := by
  simp only [slSystem_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

lemma sl_left_proportional {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (α : ℝ) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) (hg : ContDiffOn ℝ 2 g (Icc a b))
    (hef : ∀t∈Icc a b, SLOp p q r a b f t=z*f t)
    (heg : ∀t∈Icc a b, SLOp p q r a b g t=z*g t)
    (hfa : (Real.cos α : ℂ)*f a-(Real.sin α : ℂ)*(p a : ℂ)*derivWithin f (Icc a b) a=0)
    (hga : g a=(Real.sin α : ℂ))
    (hgda : (p a : ℂ)*derivWithin g (Icc a b) a=(Real.cos α : ℂ)) :
    ∃c : ℂ, ∀t∈Icc a b, f t=c*g t := by
  let c := (Real.sin α : ℂ)*f a+(Real.cos α : ℂ)*((p a : ℂ)*derivWithin f (Icc a b) a)
  let A : C(Icc a b, (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) :=
    ⟨fun t => slSystem p q r z t.val, (slSystem_continuousOn hreg z).domRestrict⟩
  have hscaled (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt
      (fun t => c • (g t,(p t : ℂ)*derivWithin g (Icc a b) t))
      (A ⟨t,ht⟩ (c • (g t,(p t : ℂ)*derivWithin g (Icc a b) t))) (Icc a b) t := by
    change HasDerivWithinAt _ (slSystem p q r z t (c • _)) _ _
    rw [slSystem_complex_smul]
    exact (sl_native_system hreg z g hg heg t ht).const_smul c
  have hinit : (f a,(p a : ℂ)*derivWithin f (Icc a b) a) =
      c • (g a,(p a : ℂ)*derivWithin g (Icc a b) a) := by
    rw [hga,hgda]
    exact boundary_initial_span α _ _ (by simpa only [mul_assoc] using hfa)
  have huniq := linear_interval_unique hreg.1.le A
    (sl_native_system hreg z f hf hef) hscaled hinit
  refine ⟨c,fun t ht => ?_⟩
  exact congrArg Prod.fst (huniq ht)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLProportional

-- BEGIN COMPLETE MODULE SLEigenSimplicity
section

open Set
namespace TeschlODE.SturmLiouville.Proof

lemma sl_eigenfunctions_proportional {p q r : ℝ → ℝ} {a b α β : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (f g : ℝ → ℂ)
    (hf : IsSLEigenfunction p q r a b α β z f)
    (hg : IsSLEigenfunction p q r a b α β z g) :
    ∃c : ℂ, ∀t∈Icc a b, f t=c*g t := by
  obtain ⟨u,hu,hua,huda,hue⟩ := sl_left_solution hreg z (Real.sin α : ℂ) (Real.cos α : ℂ)
  obtain ⟨cf,hcf⟩ := sl_left_proportional hreg α z f u hf.1.1 hu hf.2.2 hue hf.1.2.1 hua huda
  obtain ⟨cg,hcg⟩ := sl_left_proportional hreg α z g u hg.1.1 hu hg.2.2 hue hg.1.2.1 hua huda
  have hcg0 : cg≠0 := by
    intro hzero
    obtain ⟨t,ht,hgt⟩ := hg.2.1
    exact hgt (by rw [hcg t ht,hzero,zero_mul])
  refine ⟨cf/cg,fun t ht => ?_⟩
  rw [hcf t ht,hcg t ht]
  field_simp

lemma sl_real_eigenfunction {p q r : ℝ → ℝ} {a b α β : ℝ}
    (hreg : RegularSL p q r a b) (E : ℝ) (f : ℝ → ℂ)
    (hf : IsSLEigenfunction p q r a b α β (E : ℂ) f) :
    ∃g : ℝ → ℝ, IsSLEigenfunction p q r a b α β (E : ℂ) (fun t => (g t : ℂ)) ∧
      ∃c : ℂ, ∀t∈Icc a b, f t=c*(g t : ℂ) := by
  obtain ⟨g,hg,hga,hgda,hge⟩ := sl_real_left_solution hreg E (Real.sin α) (Real.cos α)
  obtain ⟨c,hc⟩ := sl_left_proportional hreg α (E : ℂ) f (fun t => (g t : ℂ))
    hf.1.1 hg hf.2.2 hge hf.1.2.1 (by exact_mod_cast hga) hgda
  obtain ⟨t,ht,hft⟩ := hf.2.1
  have hc0 : c≠0 := by intro hc0; exact hft (by rw [hc t ht,hc0,zero_mul])
  have hgf : EqOn (fun t => c⁻¹*f t) (fun t => (g t : ℂ)) (Icc a b) := by
    intro s hs
    dsimp only
    rw [hc s hs]
    simp [hc0]
  have hdomain := slDomain_congr hreg.1.le hgf (slDomain_const_mul hreg.1 hf.1 c⁻¹)
  refine ⟨g,⟨hdomain,⟨t,ht,?_⟩,hge⟩,c,hc⟩
  intro hgt
  dsimp only at hgt
  exact hft (by rw [hc t ht,hgt,mul_zero])

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLEigenSimplicity

-- BEGIN COMPLETE MODULE RealEigenPhase
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof
lemma real_eigen_phase {p q r : ℝ → ℝ} {a b α β : ℝ} (h : RegularSL p q r a b)
    (E : ℝ) (f : ℝ → ℂ) (hf : IsSLEigenfunction p q r a b α β (E:ℂ) f) :
    ∃v : ℝ → ℝ, IsSLEigenfunction p q r a b α β (E:ℂ) (fun x => (v x:ℂ)) ∧
      ∃c : ℂ, ‖c‖=1 ∧ ∀x∈Set.Icc a b,f x=c*(v x:ℂ) := by
  obtain ⟨g,hg,c,hc⟩ := sl_real_eigenfunction h E f hf
  have hc0 : c ≠ 0 := by
    obtain ⟨x,hx,hfx⟩ := hf.2.1
    intro hz
    exact hfx (by rw [hc x hx,hz,zero_mul])
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
  have hnc : (‖c‖:ℂ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun x => ‖c‖*g x,?_,c/(‖c‖:ℂ),?_,?_⟩
  · simpa only [Complex.ofReal_mul] using sl_eigen_const_mul h hg (‖c‖:ℂ) hnc
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]
  · intro x hx
    rw [hc x hx,Complex.ofReal_mul]
    field_simp
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE RealEigenPhase

-- BEGIN COMPLETE MODULE PhaseProjection
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma phase_conj_mul {c : ℂ} (hc : ‖c‖=1) : starRingEnd ℂ c*c=1 := by
  have hh : inner ℂ c c = (1:ℂ) := by rw [inner_self_eq_norm_sq_to_K, hc]; norm_num
  change c * starRingEnd ℂ c = 1 at hh
  simpa only [mul_comm] using hh

lemma phase_orthonormal (u v : ℕ → E) (c : ℕ → ℂ) (hc : ∀n,‖c n‖=1)
    (he : ∀n,u n=c n • v n) (hu : Orthonormal ℂ u) : Orthonormal ℂ v := by
  refine ⟨fun n => ?_,fun m n hmn => ?_⟩
  · have hh := hu.1 n
    rwa [he n,norm_smul,hc n,one_mul] at hh
  · have hh := hu.2 hmn
    dsimp only at hh ⊢
    rw [he m,he n,inner_smul_left,inner_smul_right] at hh
    have hm : starRingEnd ℂ (c m) ≠ 0 := by
      simp only [map_ne_zero]; exact norm_ne_zero_iff.mp (by rw [hc m]; norm_num)
    have hn : c n ≠ 0 := norm_ne_zero_iff.mp (by rw [hc n]; norm_num)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hm)).resolve_left hn

lemma phase_projection (u v : ℕ → E) (c : ℕ → ℂ) (hc : ∀n,‖c n‖=1)
    (he : ∀n,u n=c n • v n) (N : ℕ) (f : E) :
    partialProjection u N f=partialProjection v N f := by
  change (∑n∈Finset.range N,inner ℂ (u n) f • u n)=_
  apply Finset.sum_congr rfl
  intro n _
  rw [he n,inner_smul_left,smul_smul]
  have hh : starRingEnd ℂ (c n)*inner ℂ (v n) f*c n=inner ℂ (v n) f := by
    calc
      _ = (starRingEnd ℂ (c n)*c n)*inner ℂ (v n) f := by ring
      _ = _ := by rw [phase_conj_mul (hc n),one_mul]
  rw [hh]
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE PhaseProjection

-- BEGIN COMPLETE MODULE ReciprocalEscape
section

open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
lemma reciprocal_escape (c : ℝ) (s : ℕ → ℝ) (hs : ∀n,s n ≠ 0)
    (ht : Tendsto s atTop (nhds 0)) :
    Tendsto (fun n => |c+1/s n|) atTop atTop := by
  have ha : Tendsto (fun n => |s n|) atTop (nhds 0) := by simpa using ht.abs
  have hp : Tendsto (fun n => |s n|) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha,Eventually.of_forall (fun n => abs_pos.mpr (hs n))⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hp
  apply tendsto_atTop.2
  intro M
  filter_upwards [tendsto_atTop.1 hi (M+|c|)] with n hn
  have htri := abs_add_le (c+1/s n) (-c)
  have he : |1/s n| ≤ |c+1/s n|+|c| := by simpa [add_comm, add_left_comm, add_assoc] using htri
  rw [one_div, abs_inv] at he
  dsimp only [Function.comp_apply] at hn
  simp only [one_div] at *
  linarith
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE ReciprocalEscape

-- BEGIN COMPLETE MODULE RealGreenBasis
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof

structure RealGreenBasis {p q r : ℝ → ℝ} {a b α β : ℝ}
    (D : GreenData p q r a b α β) (h : RegularSL p q r a b) where
  energy : ℕ → ℝ
  function : ℕ → ℝ → ℝ
  vector : ℕ → (regularWeight h).Space
  native : ∀n,IsSLEigenfunction p q r a b α β (energy n:ℂ) (fun x => (function n x:ℂ))
  evaluate : ∀n x, x∈Set.Icc a b → (regularWeight h).extend (vector n) x=(function n x:ℂ)
  orthonormal : Orthonormal ℂ vector
  complete : ∀f,Tendsto (fun n => partialProjection vector n f) atTop (nhds f)
  uniform_range : ∀g,Tendsto
    (fun n => (regularWeight h).toContinuous (partialProjection vector n (D.operator h g)))
    atTop (nhds ((regularWeight h).toContinuous (D.operator h g)))
  spectrum : ∀z f, IsSLEigenfunction p q r a b α β z f → ∃n,z=(energy n:ℂ)
  escape : Tendsto (fun n => |energy n|) atTop atTop

lemma exists_real_green_basis {p q r : ℝ → ℝ} {a b α β : ℝ}
    (D : GreenData p q r a b α β) (h : RegularSL p q r a b) :
    Nonempty (RealGreenBasis D h) := by
  classical
  let B := Classical.choice (exists_green_basis D h)
  have hu (n : ℕ) : B.vector n ≠ 0 := by
    intro hz
    have hh := B.orthonormal.1 n
    rw [hz,norm_zero] at hh
    exact zero_ne_one hh
  have he (n : ℕ) := D.eigenvector_native h (hu n) (B.eigen n)
  choose v hv c hc heq using (fun n => real_eigen_phase h
    (D.param+1/B.value n) ((regularWeight h).extend (B.vector n)) (he n))
  let w (n : ℕ) : (regularWeight h).Space :=
    (regularWeight h).restrict (fun x => (v n x:ℂ)) (hv n).1.1.continuousOn
  have hw (n : ℕ) : B.vector n = c n • w n := by
    apply (regularWeight h).space_ext
    intro x hx
    rw [(regularWeight h).extend_smul]
    change (regularWeight h).extend (B.vector n) x = c n * (regularWeight h).extend ((regularWeight h).restrict _ _) x
    rw [(regularWeight h).extend_restrict _ _ hx]
    exact heq n x hx
  have hp := phase_projection B.vector w c hc hw
  refine ⟨⟨(fun n => D.param+1/B.value n),v,w,hv,?_,
    phase_orthonormal B.vector w c hc hw B.orthonormal,?_,?_,?_,?_⟩⟩
  · intro n x hx
    exact (regularWeight h).extend_restrict _ _ hx
  · intro f
    simpa only [hp] using B.complete f
  · intro g
    simpa only [hp] using B.uniform_range_expansion g
  · intro z f hf
    exact B.classify_native_eigenvalue hf
  · exact reciprocal_escape D.param B.value (fun n => D.eigenvalue_ne_zero h (hu n) (B.eigen n)) B.vanish

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE RealGreenBasis

-- BEGIN COMPLETE MODULE RealBasisProperties
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof.RealGreenBasis
variable {p q r : ℝ → ℝ} {a b α β : ℝ} {D : GreenData p q r a b α β}
  {h : RegularSL p q r a b} (B : RealGreenBasis D h)

lemma inner_native (m n : ℕ) :
    SLInner r a b (fun x => (B.function m x:ℂ)) (fun x => (B.function n x:ℂ)) =
      if m=n then 1 else 0 := by
  have he : inner ℂ (B.vector m) (B.vector n) =
      SLInner r a b (fun x => (B.function m x:ℂ)) (fun x => (B.function n x:ℂ)) :=
    slInner_congr h.1.le (B.evaluate m) (B.evaluate n)
  rw [← he]
  exact orthonormal_iff_ite.mp B.orthonormal m n

lemma energy_injective : Function.Injective B.energy := by
  intro m n he
  by_contra hmn
  have hf := B.native m
  rw [he] at hf
  obtain ⟨c,hc⟩ := sl_eigenfunctions_proportional h (B.energy n:ℂ)
    (fun x => (B.function m x:ℂ)) (fun x => (B.function n x:ℂ)) hf (B.native n)
  have hv : B.vector m=c • B.vector n := by
    apply (regularWeight h).space_ext
    intro x hx
    rw [(regularWeight h).extend_smul,B.evaluate m x hx,B.evaluate n x hx]
    exact hc x hx
  have hi := B.orthonormal.2 hmn
  change inner ℂ (B.vector m) (B.vector n)=0 at hi
  rw [hv,inner_smul_left,orthonormal_iff_ite.mp B.orthonormal n n,if_pos rfl,mul_one] at hi
  have hc0 : c=0 := by simpa using congrArg (starRingEnd ℂ) hi
  have hn := B.orthonormal.1 m
  rw [hv,hc0,zero_smul,norm_zero] at hn
  exact zero_ne_one hn

lemma classify (z : ℂ) (f : ℝ → ℂ) (hf : IsSLEigenfunction p q r a b α β z f) :
    ∃n,z=(B.energy n:ℂ) ∧ ∃c:ℂ,∀x∈Set.Icc a b,f x=c*(B.function n x:ℂ) := by
  obtain ⟨n,hn⟩ := B.spectrum z f hf
  refine ⟨n,hn,?_⟩
  rw [hn] at hf
  exact sl_eigenfunctions_proportional h _ _ _ hf (B.native n)
end TeschlODE.SturmLiouville.Proof.RealGreenBasis
end
-- END COMPLETE MODULE RealBasisProperties

-- BEGIN COMPLETE MODULE RealBasisExpansion
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof.RealGreenBasis
variable {p q r : ℝ → ℝ} {a b α β : ℝ} {D : GreenData p q r a b α β}
  {h : RegularSL p q r a b} (B : RealGreenBasis D h)

def expansion (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑n∈Finset.range N,SLInner r a b (fun y => (B.function n y:ℂ)) f * (B.function n x:ℂ)

lemma coefficient_eq (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc a b)) (n : ℕ) :
    inner ℂ (B.vector n) ((regularWeight h).restrict f hf) =
      SLInner r a b (fun y => (B.function n y:ℂ)) f :=
  slInner_congr h.1.le (B.evaluate n) (fun _ hx => (regularWeight h).extend_restrict f hf hx)

lemma projection_evaluate (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc a b)) (N : ℕ)
    (x : ℝ) (hx : x∈Set.Icc a b) :
    (regularWeight h).extend (partialProjection B.vector N ((regularWeight h).restrict f hf)) x =
      B.expansion f N x := by
  change (regularWeight h).extend (∑n∈Finset.range N,inner ℂ (B.vector n) ((regularWeight h).restrict f hf) • B.vector n) x = _
  rw [(regularWeight h).extend_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [(regularWeight h).extend_smul,B.coefficient_eq f hf n,B.evaluate n x hx]

lemma l2_expansion (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun N => (SLInner r a b (f-B.expansion f N) (f-B.expansion f N)).re)
      atTop (nhds 0) := by
  let v := (regularWeight h).restrict f hf
  have hv := ((tendsto_const_nhds (x := v)).sub (B.complete v)).norm.pow 2
  have he (N : ℕ) : (SLInner r a b (f-B.expansion f N) (f-B.expansion f N)).re =
      ‖v-partialProjection B.vector N v‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    apply congrArg Complex.re
    symm
    apply slInner_congr h.1.le
    all_goals
      intro x hx
      rw [(regularWeight h).extend_sub,(regularWeight h).extend_restrict f hf hx,B.projection_evaluate f hf N x hx]
      rfl
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : 2≠0)] using hv

lemma uniform_expansion (f : ℝ → ℂ) (hf : SLDomain p a b α β f) :
    TendstoUniformlyOn (B.expansion f) f atTop (Set.Icc a b) := by
  let v := (regularWeight h).restrict f hf.1.continuousOn
  have hv : v ∈ (regularWeight h).domainSet p α β :=
    ⟨f,hf,fun x hx => (regularWeight h).extend_restrict f hf.1.continuousOn hx⟩
  obtain ⟨g,hg⟩ := D.domain_mem_range h hv
  have hc := B.uniform_range g
  rw [hg] at hc
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with N hN x hx
  have hb := (((regularWeight h).toContinuous (partialProjection B.vector N v))-
    (regularWeight h).toContinuous v).norm_coe_le_norm ⟨x,hx⟩
  have hp := B.projection_evaluate f hf.1.continuousOn N x hx
  rw [(regularWeight h).extend_eq _ hx] at hp
  rw [dist_eq_norm] at hN ⊢
  change ‖(regularWeight h).toContinuous (partialProjection B.vector N v) ⟨x,hx⟩-
    (regularWeight h).toContinuous v ⟨x,hx⟩‖ ≤ _ at hb
  change ‖f x-B.expansion f N x‖ < ε
  rw [norm_sub_rev]
  change (regularWeight h).toContinuous (partialProjection B.vector N v) ⟨x,hx⟩ = B.expansion f N x at hp
  rw [hp] at hb
  exact lt_of_le_of_lt hb hN
end TeschlODE.SturmLiouville.Proof.RealGreenBasis
end
-- END COMPLETE MODULE RealBasisExpansion

-- BEGIN COMPLETE MODULE SLConditionalRoot
section

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.11, p. 160: under (5.45), the regular Sturm–Liouville problem
`L = r⁻¹(−(d/dx) p (d/dx) + q)` on `D(L)` (5.53)–(5.55) has countably many discrete, simple
eigenvalues `Eₙ` accumulating only at `∞`: there are real `Eₙ` (pairwise distinct, `|Eₙ| → ∞`)
and real-valued eigenfunctions `uₙ ∈ D(L)`, `L uₙ = Eₙ uₙ`, such that every eigenvalue `z ∈ ℂ` of
`L` is some `Eₙ` and every eigenfunction for it is a multiple of `uₙ`. The `uₙ` are orthonormal
for (5.52) and form an orthonormal basis of `H₀ = C([a, b], ℂ)`: for every `f ∈ H₀` the partial
sums of `Σ ⟨uₙ, f⟩ uₙ` (5.70) converge to `f` in the `H₀`-norm; for `f ∈ D(L)` they converge
uniformly on `[a, b]`. -/
theorem eigenfunction_expansion_of_green {p q r : ℝ → ℝ} {a b : ℝ} (α β : ℝ)
    (hreg : RegularSL p q r a b) (D : Proof.GreenData p q r a b α β) :
    ∃ (E : ℕ → ℝ) (u : ℕ → ℝ → ℝ),
      (∀ n, IsSLEigenfunction p q r a b α β (E n : ℂ) (fun x => ((u n x : ℝ) : ℂ))) ∧
      Function.Injective E ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSLEigenfunction p q r a b α β z f →
        ∃ n, z = (E n : ℂ) ∧ ∃ c : ℂ, ∀ x ∈ Set.Icc a b, f x = c * (u n x : ℂ)) ∧
      Filter.Tendsto (fun n => |E n|) Filter.atTop Filter.atTop ∧
      (∀ m n, SLInner r a b (fun x => ((u m x : ℝ) : ℂ)) (fun x => ((u n x : ℝ) : ℂ)) =
        if m = n then 1 else 0) ∧
      (∀ f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
        Filter.Tendsto
          (fun N => (SLInner r a b
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))).re)
          Filter.atTop (nhds 0)) ∧
      (∀ f : ℝ → ℂ, SLDomain p a b α β f →
        TendstoUniformlyOn
          (fun N x => ∑ n ∈ Finset.range N,
            SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
          f Filter.atTop (Set.Icc a b)) := by
  classical
  let B := Classical.choice (Proof.exists_real_green_basis D hreg)
  exact ⟨B.energy, B.function, B.native, B.energy_injective, B.classify, B.escape,
    B.inner_native, B.l2_expansion, B.uniform_expansion⟩

end TeschlODE.SturmLiouville

end
-- END COMPLETE MODULE SLConditionalRoot

-- BEGIN COMPLETE MODULE SLWronskian
section

open Set
namespace TeschlODE.SturmLiouville.Proof

noncomputable def slFlux (p : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (p t : ℂ)*derivWithin f (Icc a b) t

noncomputable def slWronskian (p : ℝ → ℝ) (a b : ℝ) (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  slFlux p a b f t*g t-f t*slFlux p a b g t

lemma sl_solution_derivatives {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (he : ∀t∈Icc a b, SLOp p q r a b f t=z*f t) {t : ℝ} (ht : t∈Icc a b) :
    HasDerivWithinAt f ((p t : ℂ)⁻¹*slFlux p a b f t) (Icc a b) t ∧
    HasDerivWithinAt (slFlux p a b f) (((q t : ℂ)-z*(r t : ℂ))*f t) (Icc a b) t := by
  have hs := sl_native_system hreg z f hf he t ht
  constructor
  · convert! (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivWithinAt t hs using 1
    simp only [slSystem_apply]
    rfl
  · convert! (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivWithinAt t hs using 1
    simp only [slSystem_apply]
    rfl

lemma slWronskian_constant {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) (hg : ContDiffOn ℝ 2 g (Icc a b))
    (hef : ∀t∈Icc a b, SLOp p q r a b f t=z*f t)
    (heg : ∀t∈Icc a b, SLOp p q r a b g t=z*g t) :
    ∀t∈Icc a b, slWronskian p a b f g t=slWronskian p a b f g a := by
  have hd (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt (slWronskian p a b f g) 0 (Icc a b) t := by
    obtain ⟨hf1,hf2⟩ := sl_solution_derivatives hreg z f hf hef ht
    obtain ⟨hg1,hg2⟩ := sl_solution_derivatives hreg z g hg heg ht
    convert! (hf2.mul hg1).sub (hf1.mul hg2) using 1
    ring
  intro t ht
  apply (convex_Icc a b).is_const_of_fderivWithin_eq_zero
    (fun t ht => (hd t ht).differentiableWithinAt) ?_ ht ⟨le_rfl,hreg.1.le⟩
  intro t ht
  simpa using (hd t ht).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hreg.1 t ht)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLWronskian

-- BEGIN COMPLETE MODULE ScalarEnergy
section

open Set
open scoped RealInnerProductSpace
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma energy_square_identity (f v : E) (p c h dh : ℝ) (hp : p ≠ 0) :
    ⟪p⁻¹ • v,v⟫ + ⟪f,c • f⟫ - (dh*‖f‖^2+h*(2*⟪f,p⁻¹ • v⟫)) =
      p⁻¹*‖v-h • f‖^2 + (c-dh-h^2/p)*‖f‖^2 := by
  rw [norm_sub_sq_real]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm v f]
  field_simp
  ring

lemma completed_energy_derivative {s : Set ℝ} {t : ℝ} {f v : ℝ → E} {h : ℝ → ℝ}
    (p c dh : ℝ) (hp : p ≠ 0)
    (hf : HasDerivWithinAt f (p⁻¹ • v t) s t)
    (hv : HasDerivWithinAt v (c • f t) s t)
    (hh : HasDerivWithinAt h dh s t) :
    HasDerivWithinAt (fun t => ⟪f t,v t⟫ - h t*‖f t‖^2)
      (p⁻¹*‖v t-h t • f t‖^2 + (c-dh-(h t)^2/p)*‖f t‖^2) s t := by
  rw [← energy_square_identity (f t) (v t) p c (h t) dh hp]
  convert! (hf.inner ℝ hv).sub (hh.mul hf.norm_sq) using 1
  ring

lemma nonnegative_derivative_zero {a b : ℝ} (hab : a<b) (g d : ℝ → ℝ)
    (hd : ∀t∈Icc a b, HasDerivWithinAt g (d t) (Icc a b) t)
    (hn : ∀t∈Icc a b, 0≤d t) (ha : g a=0) (hb : g b=0) :
    ∀t∈Icc a b, d t=0 := by
  have hm : MonotoneOn g (Icc a b) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
    (fun t ht => hn t (interior_subset ht))
  have hg (t : ℝ) (ht : t∈Icc a b) : g t=0 := by
    have h1 := hm ⟨le_rfl,hab.le⟩ ht ht.1
    have h2 := hm ht ⟨hab.le,le_rfl⟩ ht.2
    rw [ha] at h1
    rw [hb] at h2
    exact le_antisymm h2 h1
  intro t ht
  have hz : HasDerivWithinAt g 0 (Icc a b) t := by
    apply (hasDerivWithinAt_const t (Icc a b) (0 : ℝ)).congr
    · exact fun x hx => hg x hx
    · exact hg t ht
  have hu := uniqueDiffOn_Icc hab t ht
  exact ((hd t ht).derivWithin hu).symm.trans (hz.derivWithin hu)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE ScalarEnergy

-- BEGIN COMPLETE MODULE BoundaryEnergy
section

open Set
open scoped RealInnerProductSpace
namespace TeschlODE.SturmLiouville.Proof

lemma boundary_energy_zero (α : ℝ) (f v : ℂ)
    (hb : (Real.cos α : ℂ)*f-(Real.sin α : ℂ)*v=0) :
    ⟪f,v⟫ - (Real.cos α/Real.sin α)*‖f‖^2=0 := by
  by_cases hs : Real.sin α=0
  · have hc : Real.cos α≠0 := by
      intro hc
      have hh := Real.sin_sq_add_cos_sq α
      rw [hs,hc] at hh
      norm_num at hh
    have hc' : (Real.cos α : ℂ) ≠ 0 := by exact_mod_cast hc
    have hf : f=0 := by
      simp only [hs,Complex.ofReal_zero,zero_mul,sub_zero] at hb
      exact (mul_eq_zero.mp hb).resolve_left hc'
    simp [hf,hs]
  · have hs' : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast hs
    have hv : v = (Real.cos α/Real.sin α) • f := by
      apply (mul_left_cancel₀ hs')
      rw [Complex.real_smul]
      rw [Complex.ofReal_div]
      field_simp [hs']
      linear_combination -hb
    rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring

noncomputable def boundaryAffine (a b α β t : ℝ) : ℝ :=
  Real.cos α/Real.sin α + (Real.cos β/Real.sin β-Real.cos α/Real.sin α)*(t-a)/(b-a)

lemma boundaryAffine_left (a b α β : ℝ) :
    boundaryAffine a b α β a=Real.cos α/Real.sin α := by simp [boundaryAffine]

lemma boundaryAffine_right {a b : ℝ} (hab : a<b) (α β : ℝ) :
    boundaryAffine a b α β b=Real.cos β/Real.sin β := by
  unfold boundaryAffine
  rw [mul_div_cancel_right₀ _ (sub_ne_zero.mpr hab.ne')]
  ring

lemma boundaryAffine_deriv (a b α β t : ℝ) :
    HasDerivAt (boundaryAffine a b α β)
      ((Real.cos β/Real.sin β-Real.cos α/Real.sin α)/(b-a)) t := by
  convert! ((((hasDerivAt_id t).sub_const a).const_mul
      (Real.cos β/Real.sin β-Real.cos α/Real.sin α)).div_const (b-a)).const_add
      (Real.cos α/Real.sin α) using 1
  simp only [mul_one]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE BoundaryEnergy

-- BEGIN COMPLETE MODULE SLNonresonance
section

open Set
open scoped RealInnerProductSpace
namespace TeschlODE.SturmLiouville.Proof

lemma exists_real_nonresonant {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (α β : ℝ) :
    ∃ lam : ℝ, ∀f : ℝ → ℂ, SLDomain p a b α β f →
      (∀t∈Icc a b, SLOp p q r a b f t=(lam : ℂ)*f t) →
      ∀t∈Icc a b, f t=0 := by
  let h := boundaryAffine a b α β
  let D := (Real.cos β/Real.sin β-Real.cos α/Real.sin α)/(b-a)
  have hh : Continuous h := by unfold h boundaryAffine; fun_prop
  let F : ℝ → ℝ := fun t => (q t-D-(h t)^2/p t)/r t
  have hF : ContinuousOn F (Icc a b) := by
    apply ContinuousOn.div
    · exact (hreg.2.2.1.sub continuousOn_const).sub
        ((hh.continuousOn.pow 2).div hreg.2.2.2.1.continuousOn
          (fun t ht => (hreg.2.2.2.2 t ht).1.ne'))
    · exact hreg.2.1
    · exact fun t ht => (hreg.2.2.2.2 t ht).2.ne'
  obtain ⟨m,hm⟩ := isCompact_Icc.bddBelow_image hF
  refine ⟨m-1,?_⟩
  intro f hf he
  let v := fun t => (p t : ℂ)*derivWithin f (Icc a b) t
  let g := fun t => ⟪f t,v t⟫-h t*‖f t‖^2
  let c := fun t => q t-(m-1)*r t-D-(h t)^2/p t
  let d := fun t => (p t)⁻¹*‖v t-h t • f t‖^2+c t*‖f t‖^2
  have hc (t : ℝ) (ht : t∈Icc a b) : 0<c t := by
    have hlow : m≤F t := hm (mem_image_of_mem F ht)
    have hlt : m-1<F t := by linarith
    have hr := (hreg.2.2.2.2 t ht).2
    have hh' := (lt_div_iff₀ hr).mp hlt
    dsimp [c]
    linarith
  have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt g (d t) (Icc a b) t := by
    have hs := sl_native_system hreg (m-1 : ℝ) f hf.1 he t ht
    have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivWithinAt t hs
    have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivWithinAt t hs
    have h1' : HasDerivWithinAt f ((p t)⁻¹ • v t) (Icc a b) t := by
      convert! h1 using 1
      simp [slSystem_apply, v, Complex.real_smul]
    have h2' : HasDerivWithinAt v ((q t-(m-1)*r t) • f t) (Icc a b) t := by
      convert! h2 using 1
      simp [slSystem_apply, Complex.real_smul]
    exact completed_energy_derivative (p t) (q t-(m-1)*r t) D
      (hreg.2.2.2.2 t ht).1.ne' h1' h2'
      (boundaryAffine_deriv a b α β t).hasDerivWithinAt
  have hn (t : ℝ) (ht : t∈Icc a b) : 0≤d t := by
    dsimp [d]
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr (hreg.2.2.2.2 t ht).1.le) (sq_nonneg _))
      (mul_nonneg (hc t ht).le (sq_nonneg _))
  have ha : g a=0 := by
    dsimp [g,h]
    rw [boundaryAffine_left]
    exact boundary_energy_zero α (f a) (v a) (by simpa [v,mul_assoc] using hf.2.1)
  have hb : g b=0 := by
    dsimp [g,h]
    rw [boundaryAffine_right hreg.1]
    exact boundary_energy_zero β (f b) (v b) (by simpa [v,mul_assoc] using hf.2.2)
  have hz := nonnegative_derivative_zero hreg.1 g d hd hn ha hb
  intro t ht
  have hzero := hz t ht
  have hp := (hreg.2.2.2.2 t ht).1
  have hpos := hc t ht
  have hsquare : ‖f t‖^2=0 := by
    have hother : 0≤(p t)⁻¹*‖v t-h t • f t‖^2 := mul_nonneg (inv_nonneg.mpr hp.le) (sq_nonneg _)
    change (p t)⁻¹*‖v t-h t • f t‖^2+c t*‖f t‖^2=0 at hzero
    nlinarith [sq_nonneg ‖f t‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLNonresonance

-- BEGIN COMPLETE MODULE SLFundamentalData
section

open Set
open scoped ComplexConjugate
namespace TeschlODE.SturmLiouville.Proof

structure SLFundamentalData (p q r : ℝ → ℝ) (a b α β : ℝ) where
  param : ℝ
  left : ℝ → ℝ
  right : ℝ → ℝ
  wronskian : ℝ
  nonzero : wronskian ≠ 0
  left_smooth : ContDiffOn ℝ 2 (fun t => (left t : ℂ)) (Icc a b)
  right_smooth : ContDiffOn ℝ 2 (fun t => (right t : ℂ)) (Icc a b)
  left_value : left a=Real.sin α
  left_flux : slFlux p a b (fun t => (left t : ℂ)) a=(Real.cos α : ℂ)
  right_value : right b=Real.sin β
  right_flux : slFlux p a b (fun t => (right t : ℂ)) b=(Real.cos β : ℂ)
  left_equation : ∀t∈Icc a b, SLOp p q r a b (fun t => (left t : ℂ)) t=(param : ℂ)*(left t : ℂ)
  right_equation : ∀t∈Icc a b, SLOp p q r a b (fun t => (right t : ℂ)) t=(param : ℂ)*(right t : ℂ)
  wronskian_eq : ∀t∈Icc a b,
    slWronskian p a b (fun t => (left t : ℂ)) (fun t => (right t : ℂ)) t=(wronskian : ℂ)

lemma slFlux_real (p : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    star (slFlux p a b (fun t => (f t : ℂ)) t)=slFlux p a b (fun t => (f t : ℂ)) t := by
  have hd : star (derivWithin (fun t => (f t : ℂ)) (Icc a b) t)=
      derivWithin (fun t => (f t : ℂ)) (Icc a b) t := by
    rw [← derivWithin.star]
    congr 1
    funext s
    simp
  unfold slFlux
  rw [star_mul,hd]
  simp [mul_comm]

lemma endpoint_nonzero {p : ℝ → ℝ} {a b β : ℝ} (hab : a<b) (g : ℝ → ℂ)
    (hg : g b=(Real.sin β : ℂ)) (hgd : slFlux p a b g b=(Real.cos β : ℂ)) :
    ∃t∈Icc a b, g t≠0 := by
  by_contra hh
  push Not at hh
  have hb : b∈Icc a b := ⟨hab.le,le_rfl⟩
  have hs : Real.sin β=0 := by exact_mod_cast hg.symm.trans (hh b hb)
  have hd : derivWithin g (Icc a b) b=0 := by
    rw [derivWithin_congr hh (hh b hb)]
    simp
  have hc : Real.cos β=0 := by
    have hh' := hgd.symm
    unfold slFlux at hh'
    rw [hd,mul_zero] at hh'
    exact_mod_cast hh'
  have h := Real.sin_sq_add_cos_sq β
  rw [hs,hc] at h
  norm_num at h

lemma exists_slFundamentalData {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (α β : ℝ) : Nonempty (SLFundamentalData p q r a b α β) := by
  obtain ⟨lam,hnon⟩ := exists_real_nonresonant hreg α β
  obtain ⟨u,hu,hua,huf,hue⟩ := sl_real_left_solution hreg lam (Real.sin α) (Real.cos α)
  obtain ⟨v,hv,hvb,hvf,hve⟩ := sl_real_right_solution hreg lam (Real.sin β) (Real.cos β)
  let U := fun t => (u t : ℂ)
  let V := fun t => (v t : ℂ)
  change slFlux p a b U a=(Real.cos α : ℂ) at huf
  change slFlux p a b V b=(Real.cos β : ℂ) at hvf
  let W := slWronskian p a b U V a
  have hW : W≠0 := by
    intro hw
    have hbc : SLDomain p a b α β V := by
      refine ⟨hv,?_,?_⟩
      · rw [mul_assoc]
        change (Real.cos α : ℂ)*V a-(Real.sin α : ℂ)*slFlux p a b V a=0
        have hh : U a=(Real.sin α : ℂ) := by simpa only [U] using congrArg Complex.ofReal hua
        simpa only [W,slWronskian,huf,hh] using hw
      · rw [mul_assoc]
        change (Real.cos β : ℂ)*(v b : ℂ)-(Real.sin β : ℂ)*slFlux p a b V b=0
        rw [hvb,hvf]
        ring
    obtain ⟨t,ht,hvt⟩ := endpoint_nonzero hreg.1 V (by simpa only [V] using congrArg Complex.ofReal hvb) hvf
    exact hvt (hnon V hbc hve t ht)
  have hreal : (W.re : ℂ)=W := by
    apply Complex.conj_eq_iff_re.mp
    dsimp [W,slWronskian,U,V]
    rw [map_sub,map_mul,map_mul]
    simp only [Complex.conj_ofReal]
    rw [show conj (slFlux p a b (fun t => (u t : ℂ)) a)=slFlux p a b (fun t => (u t : ℂ)) a from slFlux_real p a b u a,
      show conj (slFlux p a b (fun t => (v t : ℂ)) a)=slFlux p a b (fun t => (v t : ℂ)) a from slFlux_real p a b v a]
  refine ⟨⟨lam,u,v,W.re,?_,hu,hv,hua,huf,hvb,hvf,hue,hve,?_⟩⟩
  · intro hzero
    apply hW
    rw [← hreal,hzero,Complex.ofReal_zero]
  · intro t ht
    rw [hreal]
    exact slWronskian_constant hreg (lam : ℂ) U V hu hv hue hve t ht

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLFundamentalData

-- BEGIN COMPLETE MODULE GreenKernel
section

open Set
namespace TeschlODE.SturmLiouville.Proof
variable {p q r : ℝ → ℝ} {a b α β : ℝ}

noncomputable def SLFundamentalData.kernel (D : SLFundamentalData p q r a b α β) (x t : ℝ) : ℝ :=
  D.left (min x t)*D.right (max x t)/D.wronskian

lemma SLFundamentalData.kernel_symmetric (D : SLFundamentalData p q r a b α β) (x t : ℝ) :
    D.kernel x t=D.kernel t x := by simp only [SLFundamentalData.kernel,min_comm,max_comm]

lemma SLFundamentalData.kernel_continuous (D : SLFundamentalData p q r a b α β) :
    ContinuousOn (fun z : ℝ × ℝ => D.kernel z.1 z.2) (Icc a b ×ˢ Icc a b) := by
  have hu : ContinuousOn D.left (Icc a b) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp_continuousOn D.left_smooth.continuousOn
  have hv : ContinuousOn D.right (Icc a b) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp_continuousOn D.right_smooth.continuousOn
  have hmin : MapsTo (fun z : ℝ × ℝ => min z.1 z.2) (Icc a b ×ˢ Icc a b) (Icc a b) := by
    intro z hz
    exact ⟨le_min hz.1.1 hz.2.1,(min_le_left _ _).trans hz.1.2⟩
  have hmax : MapsTo (fun z : ℝ × ℝ => max z.1 z.2) (Icc a b ×ˢ Icc a b) (Icc a b) := by
    intro z hz
    exact ⟨hz.1.1.trans (le_max_left _ _),max_le hz.1.2 hz.2.2⟩
  exact ((hu.comp (by fun_prop) hmin).mul (hv.comp (by fun_prop) hmax)).div_const D.wronskian

lemma SLFundamentalData.kernel_left (D : SLFundamentalData p q r a b α β) {x t : ℝ} (ht : t≤x) :
    (D.kernel x t : ℂ) = (D.right x : ℂ)*(D.left t : ℂ)/(D.wronskian : ℂ) := by
  simp only [SLFundamentalData.kernel,min_eq_right ht,max_eq_left ht,
    Complex.ofReal_div,Complex.ofReal_mul]
  ring

lemma SLFundamentalData.kernel_right (D : SLFundamentalData p q r a b α β) {x t : ℝ} (ht : x≤t) :
    (D.kernel x t : ℂ) = (D.left x : ℂ)*(D.right t : ℂ)/(D.wronskian : ℂ) := by
  simp only [SLFundamentalData.kernel,min_eq_left ht,max_eq_right ht,
    Complex.ofReal_div,Complex.ofReal_mul]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenKernel

-- BEGIN COMPLETE MODULE GreenKernelSplit
section

open Set MeasureTheory
namespace TeschlODE.SturmLiouville.Proof
variable {p q r : ℝ → ℝ} {a b α β : ℝ}

lemma SLFundamentalData.kernel_split (D : SLFundamentalData p q r a b α β)
    (hreg : RegularSL p q r a b) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (x : ℝ) (hx : x∈Icc a b) :
    greenApply D.kernel r a b f x =
      ((D.right x : ℂ)*(∫t in a..x, (D.left t : ℂ)*f t*(r t : ℂ))+
       (D.left x : ℂ)*(∫t in x..b, (D.right t : ℂ)*f t*(r t : ℂ)))/(D.wronskian : ℂ) := by
  have hk : ContinuousOn (fun t => D.kernel x t) (Icc a b) :=
    D.kernel_continuous.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hx,ht⟩)
  have hK : ContinuousOn (fun t => (D.kernel x t : ℂ)*f t*(r t : ℂ)) (Icc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn hk).mul hf).mul
      (Complex.continuous_ofReal.comp_continuousOn hreg.2.1)
  have hax : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
  have hxb : Icc x b ⊆ Icc a b := Icc_subset_Icc_left hx.1
  rw [greenApply, ← intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hax).intervalIntegrable_of_Icc hx.1)
    ((hK.mono hxb).intervalIntegrable_of_Icc hx.2)]
  have hl : (∫t in a..x, (D.kernel x t : ℂ)*f t*(r t : ℂ)) =
      ((D.right x : ℂ)/(D.wronskian : ℂ))*(∫t in a..x, (D.left t : ℂ)*f t*(r t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc a x := by simpa only [uIcc_of_le hx.1] using ht
    dsimp only
    rw [D.kernel_left ht'.2]
    ring
  have hr : (∫t in x..b, (D.kernel x t : ℂ)*f t*(r t : ℂ)) =
      ((D.left x : ℂ)/(D.wronskian : ℂ))*(∫t in x..b, (D.right t : ℂ)*f t*(r t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc x b := by simpa only [uIcc_of_le hx.2] using ht
    dsimp only
    rw [D.kernel_right ht'.1]
    ring
  rw [hl,hr]
  ring

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenKernelSplit

-- BEGIN COMPLETE MODULE IntervalPrimitive
section

open Set MeasureTheory
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma interval_primitive {a b : ℝ} (hab : a≤b) (f : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ P : ℝ → E, ContDiff ℝ 1 P ∧ P a=0 ∧
      (∀t∈Icc a b, HasDerivAt P (f t) t) ∧
      ∀t∈Icc a b, P t=∫s in a..t, f s := by
  let F : C(Icc a b,E) := ⟨fun t => f t.val,hf.domRestrict⟩
  let e := intervalExtend hab F
  have he : Continuous e := intervalExtend_continuous hab F
  let P := fun t => ∫s in a..t, e s
  have hd (t : ℝ) : HasDerivAt P (e t) t := (he.integral_hasStrictDerivAt a t).hasDerivAt
  have hP : ContDiff ℝ 1 P := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt,?_⟩
    have hh : deriv P=e := funext (fun t => (hd t).deriv)
    rw [hh]
    exact he
  have hef (t : ℝ) (ht : t∈Icc a b) : e t=f t := intervalExtend_of_mem hab F ht
  refine ⟨P,hP,by simp [P],?_,?_⟩
  · intro t ht
    rw [← hef t ht]
    exact hd t
  · intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc a t := by simpa only [uIcc_of_le ht.1] using hs
    exact hef s ⟨hs'.1,hs'.2.trans ht.2⟩

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE IntervalPrimitive

-- BEGIN COMPLETE MODULE VariationAlgebra
section

namespace TeschlODE.SturmLiouville.Proof

lemma variation_derivatives {s : Set ℝ} {t : ℝ}
    (u v U V P Q : ℝ → ℂ) (p c F w : ℂ) (hw : w≠0)
    (hu : HasDerivWithinAt u (p⁻¹*U t) s t)
    (hv : HasDerivWithinAt v (p⁻¹*V t) s t)
    (hU : HasDerivWithinAt U (c*u t) s t)
    (hV : HasDerivWithinAt V (c*v t) s t)
    (hP : HasDerivWithinAt P (u t*F) s t)
    (hQ : HasDerivWithinAt Q (-v t*F) s t)
    (hW : U t*v t-u t*V t=w) :
    HasDerivWithinAt (fun t => (v t*P t+u t*Q t)/w)
      (p⁻¹*((V t*P t+U t*Q t)/w)) s t ∧
    HasDerivWithinAt (fun t => (V t*P t+U t*Q t)/w)
      (c*((v t*P t+u t*Q t)/w)-F) s t := by
  constructor
  · convert! ((hv.mul hP).add (hu.mul hQ)).div_const w using 1
    ring
  · convert! ((hV.mul hP).add (hU.mul hQ)).div_const w using 1
    apply (eq_div_iff hw).mpr
    field_simp
    linear_combination F*hW

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE VariationAlgebra

-- BEGIN COMPLETE MODULE SLInhomogeneousRegularity
section

open Set
open scoped ContDiff
namespace TeschlODE.SturmLiouville.Proof

lemma slFlux_smooth {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (f : ℝ → ℂ) (hf : ContDiffOn ℝ 2 f (Icc a b)) :
    ContDiffOn ℝ 1 (slFlux p a b f) (Icc a b) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn hreg.2.2.2.1).mul
    (hf.derivWithin (uniqueDiffOn_Icc hreg.1) (by norm_num))

lemma inhomogeneous_regularity {p q r : ℝ → ℝ} {a b : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (u v f : ℝ → ℂ)
    (hu : ContDiffOn ℝ 1 u (Icc a b)) (hv : ContDiffOn ℝ 1 v (Icc a b))
    (hdu : ∀t∈Icc a b, HasDerivWithinAt u ((p t : ℂ)⁻¹*v t) (Icc a b) t)
    (hdv : ∀t∈Icc a b, HasDerivWithinAt v
      (((q t : ℂ)-z*(r t : ℂ))*u t-f t*(r t : ℂ)) (Icc a b) t) :
    ContDiffOn ℝ 2 u (Icc a b) ∧
      (∀t∈Icc a b, slFlux p a b u t=v t) ∧
      ∀t∈Icc a b, SLOp p q r a b u t-z*u t=f t := by
  have hi := uniqueDiffOn_Icc hreg.1
  have hp (t : ℝ) (ht : t∈Icc a b) : (p t : ℂ)≠0 := by
    exact_mod_cast (hreg.2.2.2.2 t ht).1.ne'
  have hr (t : ℝ) (ht : t∈Icc a b) : (r t : ℂ)≠0 := by
    exact_mod_cast (hreg.2.2.2.2 t ht).2.ne'
  have hder (t : ℝ) (ht : t∈Icc a b) : derivWithin u (Icc a b) t=(p t : ℂ)⁻¹*v t :=
    (hdu t ht).derivWithin (hi t ht)
  have hflux (t : ℝ) (ht : t∈Icc a b) : slFlux p a b u t=v t := by
    rw [slFlux,hder t ht]
    simp [hp t ht]
  refine ⟨?_,hflux,?_⟩
  · rw [show (2 : ℕ∞ω)=1+1 from rfl,contDiffOn_succ_iff_derivWithin hi]
    refine ⟨hu.differentiableOn (by norm_num),by simp,?_⟩
    have hc : ContDiffOn ℝ 1 (fun t => (p t : ℂ)⁻¹*v t) (Icc a b) :=
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hreg.2.2.2.1).inv hp).mul hv
    exact hc.congr hder
  · intro t ht
    have hd : HasDerivWithinAt (slFlux p a b u)
        (((q t : ℂ)-z*(r t : ℂ))*u t-f t*(r t : ℂ)) (Icc a b) t :=
      (hdv t ht).congr hflux (hflux t ht)
    change (r t : ℂ)⁻¹*(-derivWithin (slFlux p a b u) (Icc a b) t+(q t : ℂ)*u t)-z*u t=f t
    rw [hd.derivWithin (hi t ht)]
    field_simp [hr t ht]
    ring

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLInhomogeneousRegularity

-- BEGIN COMPLETE MODULE GreenVariation
section

open Set MeasureTheory
namespace TeschlODE.SturmLiouville.Proof
variable {p q r : ℝ → ℝ} {a b α β : ℝ}

lemma SLFundamentalData.green_auxiliary (D : SLFundamentalData p q r a b α β)
    (hreg : RegularSL p q r a b) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) :
    ∃ y : ℝ → ℂ, SLDomain p a b α β y ∧
      (∀t∈Icc a b, SLOp p q r a b y t-(D.param : ℂ)*y t=f t) ∧
      EqOn y (greenApply D.kernel r a b f) (Icc a b) := by
  let u := fun t => (D.left t : ℂ)
  let v := fun t => (D.right t : ℂ)
  let U := slFlux p a b u
  let V := slFlux p a b v
  let w := (D.wronskian : ℂ)
  have hw : w≠0 := by
    dsimp only [w]
    exact_mod_cast D.nonzero
  have hr : ContinuousOn (fun t => (r t : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hreg.2.1
  have hF : ContinuousOn (fun t => u t*f t*(r t : ℂ)) (Icc a b) :=
    (D.left_smooth.continuousOn.mul hf).mul hr
  have hG : ContinuousOn (fun t => v t*f t*(r t : ℂ)) (Icc a b) :=
    (D.right_smooth.continuousOn.mul hf).mul hr
  obtain ⟨P,hP,hPa,hPd,hPi⟩ := interval_primitive hreg.1.le _ hF
  obtain ⟨T,hT,hTa,hTd,hTi⟩ := interval_primitive hreg.1.le _ hG
  let Q := fun t => T b-T t
  have hQ : ContDiff ℝ 1 Q := contDiff_const.sub hT
  have hQb : Q b=0 := sub_self _
  have hQd (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt Q (-v t*(f t*(r t : ℂ))) (Icc a b) t := by
    convert! (hTd t ht).const_sub (T b) |>.hasDerivWithinAt using 1
    ring
  let y := fun t => (v t*P t+u t*Q t)/w
  let z := fun t => (V t*P t+U t*Q t)/w
  have hu1 : ContDiffOn ℝ 1 u (Icc a b) := D.left_smooth.of_le (by norm_num)
  have hv1 : ContDiffOn ℝ 1 v (Icc a b) := D.right_smooth.of_le (by norm_num)
  have hU1 : ContDiffOn ℝ 1 U (Icc a b) := slFlux_smooth hreg u D.left_smooth
  have hV1 : ContDiffOn ℝ 1 V (Icc a b) := slFlux_smooth hreg v D.right_smooth
  have hy1 : ContDiffOn ℝ 1 y (Icc a b) :=
    ((hv1.mul hP.contDiffOn).add (hu1.mul hQ.contDiffOn)).div_const w
  have hz1 : ContDiffOn ℝ 1 z (Icc a b) :=
    ((hV1.mul hP.contDiffOn).add (hU1.mul hQ.contDiffOn)).div_const w
  have hd (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt y ((p t : ℂ)⁻¹*z t) (Icc a b) t ∧
      HasDerivWithinAt z (((q t : ℂ)-(D.param : ℂ)*(r t : ℂ))*y t-f t*(r t : ℂ)) (Icc a b) t := by
    obtain ⟨hu,hU⟩ := sl_solution_derivatives hreg (D.param : ℂ) u D.left_smooth D.left_equation ht
    obtain ⟨hv,hV⟩ := sl_solution_derivatives hreg (D.param : ℂ) v D.right_smooth D.right_equation ht
    apply variation_derivatives u v U V P Q (p t : ℂ)
      ((q t : ℂ)-(D.param : ℂ)*(r t : ℂ)) (f t*(r t : ℂ)) w hw hu hv hU hV
    · convert! (hPd t ht).hasDerivWithinAt using 1
      ring
    · exact hQd t ht
    · exact D.wronskian_eq t ht
  obtain ⟨hy2,hyflux,hye⟩ := inhomogeneous_regularity hreg (D.param : ℂ) y z f hy1 hz1
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
  have hdomain : SLDomain p a b α β y := by
    refine ⟨hy2,?_,?_⟩
    · rw [mul_assoc]
      change (Real.cos α : ℂ)*y a-(Real.sin α : ℂ)*slFlux p a b y a=0
      rw [hyflux a ⟨le_rfl,hreg.1.le⟩]
      dsimp only [y,z,U,V,u,v]
      rw [hPa,D.left_value,D.left_flux]
      ring
    · rw [mul_assoc]
      change (Real.cos β : ℂ)*y b-(Real.sin β : ℂ)*slFlux p a b y b=0
      rw [hyflux b ⟨hreg.1.le,le_rfl⟩]
      dsimp only [y,z,U,V,u,v]
      rw [hQb,D.right_value,D.right_flux]
      ring
  refine ⟨y,hdomain,hye,?_⟩
  intro t ht
  have hQi : Q t=∫s in t..b, v s*f s*(r s : ℂ) := by
    dsimp only [Q]
    rw [hTi b ⟨hreg.1.le,le_rfl⟩,hTi t ht]
    exact intervalIntegral.integral_interval_sub_left
      (hG.intervalIntegrable_of_Icc hreg.1.le)
      ((hG.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
  dsimp only [y]
  rw [hPi t ht,hQi,D.kernel_split hreg f hf t ht]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenVariation

-- BEGIN COMPLETE MODULE GreenUniqueness
section

open Set
namespace TeschlODE.SturmLiouville.Proof
variable {p q r : ℝ → ℝ} {a b α β : ℝ}

lemma SLFundamentalData.homogeneous_zero (D : SLFundamentalData p q r a b α β)
    (hreg : RegularSL p q r a b) (f : ℝ → ℂ) (hf : SLDomain p a b α β f)
    (he : ∀t∈Icc a b, SLOp p q r a b f t=(D.param : ℂ)*f t) :
    ∀t∈Icc a b, f t=0 := by
  obtain ⟨c,hc⟩ := sl_left_proportional hreg α (D.param : ℂ) f
    (fun t => (D.left t : ℂ)) hf.1 D.left_smooth he D.left_equation hf.2.1
    (by exact_mod_cast D.left_value) D.left_flux
  have hb : b∈Icc a b := ⟨hreg.1.le,le_rfl⟩
  have hd : derivWithin f (Icc a b) b = c*derivWithin (fun t => (D.left t : ℂ)) (Icc a b) b := by
    rw [derivWithin_congr hc (hc b hb)]
    exact ((D.left_smooth.differentiableOn (by norm_num) b hb).hasDerivWithinAt.const_mul c).derivWithin
      (uniqueDiffOn_Icc hreg.1 b hb)
  have hw := D.wronskian_eq b hb
  unfold slWronskian at hw
  dsimp only at hw
  rw [D.right_value,D.right_flux] at hw
  have hbc := hf.2.2
  rw [hc b hb,hd] at hbc
  have hcw : c*(D.wronskian : ℂ)=0 := by
    dsimp only [slFlux] at hw
    linear_combination -c*hw-hbc
  have hc0 : c=0 := (mul_eq_zero.mp hcw).resolve_right (by exact_mod_cast D.nonzero)
  intro t ht
  rw [hc t ht,hc0,zero_mul]

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenUniqueness

-- BEGIN COMPLETE MODULE SLOperatorSub
section

namespace TeschlODE.SturmLiouville.Proof
lemma slDomain_sub {p : ℝ → ℝ} {a b α β : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hf : SLDomain p a b α β f) (hg : SLDomain p a b α β g) :
    SLDomain p a b α β (f-g) := by
  have hd (t : ℝ) (ht : t∈Set.Icc a b) : derivWithin (f-g) (Set.Icc a b) t =
      derivWithin f (Set.Icc a b) t-derivWithin g (Set.Icc a b) t :=
    (((hf.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt).sub
      ((hg.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt)).derivWithin
      (uniqueDiffOn_Icc hab t ht)
  refine ⟨hf.1.sub hg.1,?_,?_⟩
  · rw [hd a ⟨le_rfl,hab.le⟩]
    change (Real.cos α:ℂ)*(f a-g a)-(Real.sin α:ℂ)*(p a:ℂ)*_ = 0
    linear_combination hf.2.1-hg.2.1
  · rw [hd b ⟨hab.le,le_rfl⟩]
    change (Real.cos β:ℂ)*(f b-g b)-(Real.sin β:ℂ)*(p b:ℂ)*_ = 0
    linear_combination hf.2.2-hg.2.2

lemma slOp_sub {p q r : ℝ → ℝ} {a b α β : ℝ} (h : RegularSL p q r a b)
    {f g : ℝ → ℂ} (hf : SLDomain p a b α β f) (hg : SLDomain p a b α β g)
    {x : ℝ} (hx : x∈Set.Icc a b) :
    SLOp p q r a b (f-g) x=SLOp p q r a b f x-SLOp p q r a b g x := by
  have hu := uniqueDiffOn_Icc h.1
  have hd (t : ℝ) (ht : t∈Set.Icc a b) : derivWithin (f-g) (Set.Icc a b) t =
      derivWithin f (Set.Icc a b) t-derivWithin g (Set.Icc a b) t :=
    (((hf.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt).sub
      ((hg.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt)).derivWithin (hu t ht)
  have hp : ContDiffOn ℝ 1 (fun t => (p t:ℂ)) (Set.Icc a b) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h.2.2.2.1
  have hff := hp.mul (hf.1.derivWithin hu (m := 1) (by norm_num))
  have hgg := hp.mul (hg.1.derivWithin hu (m := 1) (by norm_num))
  have he : Set.EqOn (fun t => (p t:ℂ)*derivWithin (f-g) (Set.Icc a b) t)
      (fun t => (p t:ℂ)*derivWithin f (Set.Icc a b) t-(p t:ℂ)*derivWithin g (Set.Icc a b) t) (Set.Icc a b) := by
    intro t ht
    dsimp only
    rw [hd t ht,mul_sub]
  have hdiff := (((hff.differentiableOn (by norm_num) x hx).hasDerivWithinAt).sub
      ((hgg.differentiableOn (by norm_num) x hx).hasDerivWithinAt)).derivWithin (hu x hx)
  change derivWithin (fun t => (p t:ℂ)*derivWithin f (Set.Icc a b) t-(p t:ℂ)*derivWithin g (Set.Icc a b) t) (Set.Icc a b) x = _ at hdiff
  unfold SLOp
  rw [derivWithin_congr he (he hx), hdiff]
  change (r x:ℂ)⁻¹*(-(_-_)+(q x:ℂ)*(f x-g x))=_
  ring
end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE SLOperatorSub

-- BEGIN COMPLETE MODULE GreenExistence
section

open Set
namespace TeschlODE.SturmLiouville.Proof
variable {p q r : ℝ → ℝ} {a b α β : ℝ}

lemma exists_greenData (hreg : RegularSL p q r a b) (α β : ℝ) :
    Nonempty (GreenData p q r a b α β) := by
  obtain ⟨D⟩ := exists_slFundamentalData hreg α β
  have hright (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) :
      SLDomain p a b α β (greenApply D.kernel r a b f) ∧
      ∀t∈Icc a b, SLOp p q r a b (greenApply D.kernel r a b f) t-
        (D.param : ℂ)*greenApply D.kernel r a b f t=f t := by
    obtain ⟨y,hy,he,hEq⟩ := D.green_auxiliary hreg f hf
    refine ⟨slDomain_congr hreg.1.le hEq hy,fun t ht => ?_⟩
    rw [← slOp_congr hEq ht,← hEq ht]
    exact he t ht
  refine ⟨⟨D.param,D.kernel,D.kernel_continuous,
    (fun x _ y _ => D.kernel_symmetric x y),
    (fun f hf => (hright f hf).1),
    (fun f hf => (hright f hf).2),?_⟩⟩
  intro f hf
  let g := fun t => SLOp p q r a b f t-(D.param : ℂ)*f t
  have hg : ContinuousOn g (Icc a b) :=
    (slOp_continuous hreg hf).sub (continuousOn_const.mul hf.1.continuousOn)
  obtain ⟨hu,he⟩ := hright g hg
  have hz := D.homogeneous_zero hreg (greenApply D.kernel r a b g-f)
    (slDomain_sub hreg.1 hu hf) (fun t ht => ?_)
  · intro t ht
    exact sub_eq_zero.mp (hz t ht)
  · rw [slOp_sub hreg hu hf ht]
    have ht' := he t ht
    dsimp only [g] at ht'
    change _=(D.param : ℂ)*(greenApply D.kernel r a b g t-f t)
    linear_combination ht'

end TeschlODE.SturmLiouville.Proof
end
-- END COMPLETE MODULE GreenExistence

-- BEGIN COMPLETE MODULE SLRoot
section

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.11, p. 160: under (5.45), the regular Sturm–Liouville problem
`L = r⁻¹(−(d/dx) p (d/dx) + q)` on `D(L)` (5.53)–(5.55) has countably many discrete, simple
eigenvalues `Eₙ` accumulating only at `∞`: there are real `Eₙ` (pairwise distinct, `|Eₙ| → ∞`)
and real-valued eigenfunctions `uₙ ∈ D(L)`, `L uₙ = Eₙ uₙ`, such that every eigenvalue `z ∈ ℂ` of
`L` is some `Eₙ` and every eigenfunction for it is a multiple of `uₙ`. The `uₙ` are orthonormal
for (5.52) and form an orthonormal basis of `H₀ = C([a, b], ℂ)`: for every `f ∈ H₀` the partial
sums of `Σ ⟨uₙ, f⟩ uₙ` (5.70) converge to `f` in the `H₀`-norm; for `f ∈ D(L)` they converge
uniformly on `[a, b]`. -/
theorem eigenfunction_expansion {p q r : ℝ → ℝ} {a b : ℝ} (α β : ℝ)
    (hreg : RegularSL p q r a b) :
    ∃ (E : ℕ → ℝ) (u : ℕ → ℝ → ℝ),
      (∀ n, IsSLEigenfunction p q r a b α β (E n : ℂ) (fun x => ((u n x : ℝ) : ℂ))) ∧
      Function.Injective E ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSLEigenfunction p q r a b α β z f →
        ∃ n, z = (E n : ℂ) ∧ ∃ c : ℂ, ∀ x ∈ Set.Icc a b, f x = c * (u n x : ℂ)) ∧
      Filter.Tendsto (fun n => |E n|) Filter.atTop Filter.atTop ∧
      (∀ m n, SLInner r a b (fun x => ((u m x : ℝ) : ℂ)) (fun x => ((u n x : ℝ) : ℂ)) =
        if m = n then 1 else 0) ∧
      (∀ f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
        Filter.Tendsto
          (fun N => (SLInner r a b
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))).re)
          Filter.atTop (nhds 0)) ∧
      (∀ f : ℝ → ℂ, SLDomain p a b α β f →
        TendstoUniformlyOn
          (fun N x => ∑ n ∈ Finset.range N,
            SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
          f Filter.atTop (Set.Icc a b)) := by
  exact eigenfunction_expansion_of_green α β hreg (Classical.choice (Proof.exists_greenData hreg α β))

end TeschlODE.SturmLiouville

open TeschlODE.SturmLiouville in
theorem solution {p q r : ℝ → ℝ} {a b : ℝ} (α β : ℝ)
    (hreg : RegularSL p q r a b) :
    ∃ (E : ℕ → ℝ) (u : ℕ → ℝ → ℝ),
      (∀ n, IsSLEigenfunction p q r a b α β (E n : ℂ) (fun x => ((u n x : ℝ) : ℂ))) ∧
      Function.Injective E ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSLEigenfunction p q r a b α β z f →
        ∃ n, z = (E n : ℂ) ∧ ∃ c : ℂ, ∀ x ∈ Set.Icc a b, f x = c * (u n x : ℂ)) ∧
      Filter.Tendsto (fun n => |E n|) Filter.atTop Filter.atTop ∧
      (∀ m n, SLInner r a b (fun x => ((u m x : ℝ) : ℂ)) (fun x => ((u n x : ℝ) : ℂ)) =
        if m = n then 1 else 0) ∧
      (∀ f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
        Filter.Tendsto
          (fun N => (SLInner r a b
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))).re)
          Filter.atTop (nhds 0)) ∧
      (∀ f : ℝ → ℂ, SLDomain p a b α β f →
        TendstoUniformlyOn
          (fun N x => ∑ n ∈ Finset.range N,
            SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
          f Filter.atTop (Set.Icc a b)) := by
  exact eigenfunction_expansion α β hreg
end
-- END COMPLETE MODULE SLRoot
