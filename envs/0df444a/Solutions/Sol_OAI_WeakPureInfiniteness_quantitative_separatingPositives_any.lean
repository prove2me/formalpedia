-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.quantitative_separatingPositives_any
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:24.847109+00:00
-- url     : https://prove2.me/submissions/a7232e99-2ff8-49e0-b577-bdbf7a5f7389

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003
import Theorems.Thm_OAI_WeakPureInfiniteness_exists_separation_cores
import Theorems.Thm_OAI_WeakPureInfiniteness_separation_core_comparisons

section
-- module Solutions.OAIQ246_WI.Compat
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Intertwining
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.WeakPureInfiniteness.instAlgebraRealProd_solutions
lemma cfc_star_mul_intertwine (D : B) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (D*star D)*D=D*cfc f (star D*D) := by
  have hm : (D*star D,star D*D) ∈ intertwiningAlgebra D := by
    constructor <;> simp only [mul_assoc]
  have h := cfc_mem f hm
  have hprod : IsSelfAdjoint (D*star D,star D*D) := by
    change star (D*star D,star D*D)=(D*star D,star D*D)
    apply Prod.ext
    · exact IsSelfAdjoint.mul_star_self D
    · exact IsSelfAdjoint.star_mul_self D
  have hfst := (StarAlgHom.fst ℂ B B).map_cfc f (D*star D,star D*D)
    hf.continuousOn continuous_fst hprod (IsSelfAdjoint.mul_star_self D)
  have hsnd := (StarAlgHom.snd ℂ B B).map_cfc f (D*star D,star D*D)
    hf.continuousOn continuous_snd hprod (IsSelfAdjoint.star_mul_self D)
  change (cfc f (D*star D,star D*D)).1=cfc f (D*star D) at hfst
  change (cfc f (D*star D,star D*D)).2=cfc f (star D*D) at hsnd
  change (cfc f (D*star D,star D*D)).1*D=D*(cfc f (D*star D,star D*D)).2 ∧ _ at h
  rw [hfst,hsnd] at h
  exact h.1

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ColumnNormalization
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma continuous_columnMetricFunction {τ : ℝ} (hτ : 0 < τ) :
    Continuous (columnMetricFunction τ) := by
  apply Continuous.inv₀ (continuous_const.max Real.continuous_sqrt)
  intro s
  exact ne_of_gt (lt_of_lt_of_le hτ (le_max_left _ _))

lemma continuous_columnCoreFunction (τ : ℝ) : Continuous (columnCoreFunction τ) := by
  unfold columnCoreFunction
  fun_prop

lemma columnMetricFunction_nonneg {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    0 ≤ columnMetricFunction τ s := inv_nonneg.mpr (hτ.le.trans (le_max_left _ _))

lemma columnMetricFunction_bound {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    columnMetricFunction τ s ≤ τ⁻¹ :=
  inv_anti₀ hτ (le_max_left _ _)

lemma columnMetricFunction_scalar {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) :
    0 ≤ s*(columnMetricFunction τ s)^2 ∧ s*(columnMetricFunction τ s)^2 ≤ 1 ∧
      (s*(columnMetricFunction τ s)^2)*columnCoreFunction τ s=columnCoreFunction τ s := by
  have hm : 0 < max τ (Real.sqrt s) := hτ.trans_le (le_max_left _ _)
  have he : s*(columnMetricFunction τ s)^2=(Real.sqrt s/max τ (Real.sqrt s))^2 := by
    rw [div_pow,Real.sq_sqrt hs]
    simp only [columnMetricFunction,div_eq_mul_inv,inv_pow]
  have hr0 : 0 ≤ Real.sqrt s/max τ (Real.sqrt s) := div_nonneg (Real.sqrt_nonneg _) hm.le
  have hr1 : Real.sqrt s/max τ (Real.sqrt s) ≤ 1 := (div_le_one₀ hm).mpr (le_max_right _ _)
  refine ⟨by positivity,by rw [he]; nlinarith,?_⟩
  by_cases h : Real.sqrt s ≤ τ
  · have hc : columnCoreFunction τ s=0 := max_eq_right (sub_nonpos.mpr h)
    rw [hc,mul_zero]
  · have hp : 0 < Real.sqrt s := hτ.trans (lt_of_not_ge h)
    have hmax : max τ (Real.sqrt s)=Real.sqrt s := max_eq_right (le_of_not_ge h)
    rw [he,hmax,div_self (ne_of_gt hp),one_pow,one_mul]

lemma column_left_normalization (D : B) {τ : ℝ} (hτ : 0 < τ) :
    let F := cfc (columnMetricFunction τ) (D*star D)
    let p := F*D
    let h := cfc (columnCoreFunction τ) (star D*D)
    ‖F‖ ≤ τ⁻¹ ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ star p*p*h=h := by
  dsimp only
  let f := columnMetricFunction τ
  let G := cfc f (star D*D)
  have hf := continuous_columnMetricFunction hτ
  have hc := continuous_columnCoreFunction τ
  have hF : ‖cfc f (D*star D)‖ ≤ τ⁻¹ := by
    apply norm_cfc_le (by positivity)
    intro s _
    rw [Real.norm_eq_abs,abs_of_nonneg (columnMetricFunction_nonneg hτ s)]
    exact columnMetricFunction_bound hτ s
  have hG : IsSelfAdjoint G := cfc_predicate _ _
  have hpair : star (cfc f (D*star D)*D)*(cfc f (D*star D)*D)=
      cfc (fun s : ℝ => s*(f s)^2) (star D*D) := by
    rw [cfc_star_mul_intertwine D f hf,star_mul,hG.star_eq]
    have hfun : cfc (fun s : ℝ => s*(f s)^2) (star D*D)=(star D*D)*G*G := by
      rw [show (fun s : ℝ => s*(f s)^2)=(fun s : ℝ => s*f s*f s) by ext; ring]
      rw [cfc_mul (fun s : ℝ => s*f s) f _ (continuous_id.mul hf).continuousOn hf.continuousOn,
        cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,cfc_id' ℝ (star D*D) (IsSelfAdjoint.star_mul_self D)]
    rw [hfun]
    have hcomm : Commute G (star D*D) := (Commute.refl (star D*D)).cfc_real f
    calc
      G*star D*(D*G)=G*(star D*D)*G := by simp only [mul_assoc]
      _=(star D*D)*G*G := by rw [hcomm.eq]
  have hp : ‖cfc f (D*star D)*D‖ ≤ 1 := by
    have hn : ‖cfc (fun s : ℝ => s*(f s)^2) (star D*D)‖ ≤ 1 := by
      apply norm_cfc_le (by positivity)
      intro s hs
      have h := columnMetricFunction_scalar hτ (spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs)
      rw [Real.norm_eq_abs,abs_of_nonneg h.1]
      exact h.2.1
    rw [← hpair,CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg (cfc f (D*star D)*D)]
  refine ⟨hF,hp,cfc_nonneg (fun s _ => le_max_right _ _),?_⟩
  rw [hpair,← cfc_mul (fun s : ℝ => s*(f s)^2) (columnCoreFunction τ) _
    (continuous_id.mul (hf.pow 2)).continuousOn hc.continuousOn]
  apply cfc_congr
  intro s hs
  exact (columnMetricFunction_scalar hτ (spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs)).2.2

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ColumnCoreNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_column_core (D : B) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖cfc (columnCoreFunction τ) (star D*D)‖=max (‖D‖-τ) 0 := by
  obtain hB | hB := subsingleton_or_nontrivial B
  · have hD : D=0 := Subsingleton.elim _ _
    have hz : cfc (columnCoreFunction τ) (star D*D)=0 := Subsingleton.elim _ _
    rw [hz,norm_zero,hD,norm_zero]
    simp only [zero_sub,max_eq_right (neg_nonpos.mpr hτ)]
  let : Nontrivial B := hB
  apply le_antisymm
  · apply norm_cfc_le (le_max_right _ _)
    intro s hs
    have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs
    have hsn := (Real.le_norm_self s).trans (spectrum.norm_le_norm_of_mem hs)
    rw [CStarRing.norm_star_mul_self] at hsn
    have hsr : Real.sqrt s ≤ ‖D‖ := by
      nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s,norm_nonneg D]
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith) le_rfl
  · have he := norm_apply_le_norm_cfc (columnCoreFunction τ) (star D*D)
      (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := star D * D) (star_mul_self_nonneg D))
      (continuous_columnCoreFunction τ).continuousOn (IsSelfAdjoint.star_mul_self D)
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),CStarRing.norm_star_mul_self] at he
    simpa only [columnCoreFunction,Real.sqrt_mul_self (norm_nonneg D)] using he

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CompatibleInverse
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section Unital

variable {B : Type*} [CStarAlgebra B] [Nontrivial B]

lemma exists_small_inverse (a : B) {d : ℝ} (had : ‖a‖ ≤ d) (hd : d < 1) :
    ∃ b : B,(1+a)*b=1 ∧ b*(1+a)=1 ∧ ‖b‖ ≤ (1-d)⁻¹ := by
  have ha : ‖-a‖ < 1 := by simpa only [norm_neg] using had.trans_lt hd
  let u := Units.oneSub (-a) ha
  let b : B := ↑u⁻¹
  have hl : (1+a)*b=1 := by simpa only [u,Units.val_oneSub,sub_neg_eq_add] using u.mul_inv
  have hr : b*(1+a)=1 := by simpa only [u,Units.val_oneSub,sub_neg_eq_add] using u.inv_mul
  refine ⟨b,hl,hr,?_⟩
  have he : b=1-a*b := by
    rw [add_mul,one_mul] at hl
    exact (eq_sub_iff_add_eq).mpr hl
  have hb := norm_sub_le (1 : B) (a*b)
  have hn1 : ‖(1 : B)‖ ≤ 1 := norm_one.le
  have hm := norm_mul_le a b
  have hab : ‖a‖*‖b‖ ≤ d*‖b‖ := mul_le_mul_of_nonneg_right had (norm_nonneg b)
  rw [← he] at hb
  rw [inv_eq_one_div]
  change ‖b‖ ≤ 1/(1-d)
  apply (le_div_iff₀ (by linarith : 0 < 1-d)).mpr
  nlinarith

lemma exists_factored_inverse (g a : B) (hg : ‖g‖ ≤ 1) {d : ℝ}
    (had : ‖a‖ ≤ d) (hd : d < 1) :
    ∃ z : B, ‖z‖ ≤ d/(1-d) ∧
      (1+g*a*g)*(1+g*z*g)=1 ∧ (1+g*z*g)*(1+g*a*g)=1 := by
  have hd0 : 0 ≤ d := (norm_nonneg a).trans had
  have hagg : ‖a*g*g‖ ≤ d := by
    calc
      _≤‖a‖*‖g‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤d*1*1 := by gcongr
      _=d := by ring
  obtain ⟨b,hl,hr,hb⟩ := exists_small_inverse (a*g*g) hagg hd
  refine ⟨-b*a,?_,?_,?_⟩
  · calc
      ‖-b*a‖≤‖-b‖*‖a‖ := norm_mul_le _ _
      _≤(1-d)⁻¹*d := by rw [norm_neg]; gcongr
      _=d/(1-d) := by ring
  · calc
      _=1+g*a*g-g*((1+a*g*g)*b)*a*g := by noncomm_ring
      _=1 := by rw [hl]; noncomm_ring
  · calc
      _=1+g*a*g-g*(b*(1+a*g*g))*a*g := by noncomm_ring
      _=1 := by rw [hr]; noncomm_ring

lemma norm_one_add_le (a : B) : ‖1+a‖ ≤ 1+‖a‖ := by
  simpa only [norm_one] using norm_add_le (1 : B) a

lemma norm_factored_perturbation_le (g z : B) (hg : ‖g‖ ≤ 1) :
    ‖1+g*z*g‖ ≤ 1+‖z‖ := by
  apply (norm_one_add_le _).trans
  apply add_le_add_right
  calc
    _≤‖g‖*‖z‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _≤1*‖z‖*1 := by gcongr
    _=‖z‖ := by ring

lemma normalized_inverse_difference_bound
    (g z Z Z₁ W W₁ p F C e y : B) {η : ℝ}
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1) (hz : ‖z‖ ≤ 1/3) (hZ₁ : ‖Z₁‖ ≤ 9/8)
    (hp : ‖p‖ ≤ 1) (he : ‖e‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hgself : IsSelfAdjoint g) (hZ : Z=1+g*z*g) (hFCg : F*C*g=p)
    (hZW : Z*star W=1) (hW₁Z₁ : star W₁*Z₁=1)
    (hW : W=W₁+(η : ℂ) • (g*y*g)) :
    ‖F*C*(Z-Z₁)*e‖ ≤ 3/2*η := by
  have hdiff : Z-Z₁= -(η : ℂ) • (Z*g*star y*g*Z₁) := by
    have heq : Z*(star W₁-star W)*Z₁=Z-Z₁ := by
      rw [mul_sub,sub_mul,mul_assoc Z (star W₁) Z₁,hW₁Z₁,hZW,mul_one,one_mul]
    rw [← heq,hW,star_add,star_smul,star_mul,star_mul,hgself.star_eq]
    simp only [Complex.star_def,Complex.conj_ofReal,sub_add_cancel_left,neg_mul,mul_neg,mul_smul_comm,smul_mul_assoc]
    simp only [mul_assoc,neg_smul]
  rw [hdiff,mul_smul_comm,smul_mul_assoc,norm_smul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hη]
  have halg : F*C*(Z*g*star y*g*Z₁)*e=p*(1+z*g*g)*star y*g*Z₁*e := by
    rw [hZ,← hFCg]
    noncomm_ring
  rw [halg]
  have hh : ‖1+z*g*g‖ ≤ 4/3 := by
    have hmul : ‖z*g*g‖ ≤ 1/3 := by
      calc
        _≤‖z‖*‖g‖*‖g‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _≤(1/3)*1*1 := by gcongr
        _=1/3 := by ring
    exact (norm_one_add_le _).trans (by linarith)
  have hn : ‖p*(1+z*g*g)*star y*g*Z₁*e‖ ≤ 3/2 := by
    calc
      _≤‖p‖*‖1+z*g*g‖*‖star y‖*‖g‖*‖Z₁‖*‖e‖ := by
        repeat' first | apply (norm_mul_le _ _).trans | apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact le_refl _
      _≤1*(4/3)*1*1*(9/8)*1 := by rw [norm_star]; gcongr
      _=3/2 := by norm_num
  nlinarith

end Unital

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_Hereditary
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_mem (h b : A) (hh : IsSelfAdjoint h) : h*b*h ∈ hereditarySubalgebra h hh :=
  (sandwichSubalgebra h hh).le_topologicalClosure ⟨b, rfl⟩

lemma square_mem_hereditary (h : A) (hh : IsSelfAdjoint h) :
    h*h ∈ hereditarySubalgebra h hh := by
  have ht : Tendsto (fun e : A => h*e*h) (CStarAlgebra.approximateUnit A) (𝓝 (h*h)) :=
    ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const h
  exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Eventually.of_forall (fun e => sandwich_mem h e hh))

lemma sqrt_mem_hereditary (h x : A) (hh : IsSelfAdjoint h)
    (hx : x ∈ hereditarySubalgebra h hh) (hxpos : 0 ≤ x) :
    CFC.sqrt x ∈ hereditarySubalgebra h hh := by
  rw [CFC.sqrt_eq_real_sqrt x hxpos]
  exact cfcₙ_mem Real.sqrt hx

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) :
    h ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  convert sqrt_mem_hereditary h (h*h) hh.isSelfAdjoint
    (square_mem_hereditary h hh.isSelfAdjoint) (by simpa only [hh.star_eq] using star_mul_self_nonneg h) using 1
  all_goals try with_reducible_and_instances rfl
  exact (CFC.sqrt_mul_self h hh).symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_le_rightIdeal (h : A) (hh : IsSelfAdjoint h) :
    (hereditarySubalgebra h hh : Set A) ⊆ principalRightIdeal h := by
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨b, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨b*h, by change h*(b*h) = h*b*h; simp only [mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma rightIdeal_square_mem_hereditary (h a : A) (hh : IsSelfAdjoint h)
    (ha : a ∈ principalRightIdeal h) : a * star a ∈ hereditarySubalgebra h hh := by
  have hc : IsClosed {a : A | a * star a ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨b, rfl⟩
  change (h*b)*star (h*b) ∈ hereditarySubalgebra h hh
  convert sandwich_mem h (b*star b) hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [star_mul, hh.star_eq, mul_assoc]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_RectangularCStar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder


open scoped CStarAlgebra InnerProductSpace NNReal

open CStarMatrix CStarModule ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype k] in
lemma rectangular_toCLM_mul (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    toCLM (M*N) = (toCLM N).comp (toCLM M) := by
  ext v i
  simp only [toCLM_apply, comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v M N).symm i

lemma rectangular_norm_mul_le (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    ‖M*N‖ ≤ ‖M‖*‖N‖ := by
  rw [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

lemma rectangular_norm_conjTranspose_le (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  refine (congrArg (fun a : A => ‖a‖)
    (inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v))).trans_le ?_
  calc
    ‖⟪toCLM M w, v⟫_A‖ ≤ ‖toCLM M w‖*‖v‖ := norm_inner_le (WithCStarModule A (n → A))
    _ ≤ (‖M‖*‖w‖)*‖v‖ := by
      gcongr
      exact le_opNorm _ _
    _ = ‖M‖₊*‖v‖*‖w‖ := by simp only [coe_nnnorm] <;> ring

lemma rectangular_norm_conjTranspose (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (rectangular_norm_conjTranspose_le M)
  simpa only [rectangular_conjTranspose_conjTranspose] using
    rectangular_norm_conjTranspose_le M.conjTranspose

lemma rectangular_norm_sq_le_range (M : CStarMatrix m n A) :
    ‖M‖^2 ≤ ‖M*M.conjTranspose‖ := by
  have hmain : ‖M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖ := by
    change ‖toCLM M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖
    rw [opNorm_le_iff (by positivity)]
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have h₁ : ‖⟪v, (toCLM M.conjTranspose) ((toCLM M) v)⟫_A‖ ≤
        ‖M*M.conjTranspose‖ * ‖v‖^2 := calc
      _ ≤ ‖v‖ * ‖(toCLM M.conjTranspose) ((toCLM M) v)‖ := norm_inner_le (WithCStarModule A (m → A))
      _ ≤ ‖v‖ * (‖(toCLM M.conjTranspose).comp (toCLM M)‖ * ‖v‖) := by
        gcongr
        exact le_opNorm ((toCLM M.conjTranspose).comp (toCLM M)) v
      _ = ‖M*M.conjTranspose‖*‖v‖^2 := by
        rw [← rectangular_toCLM_mul, ← CStarMatrix.norm_def]
        ring
    conv_rhs => rw [show ‖v‖ = Real.sqrt (‖v‖^2) by simp]
    rw [← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h₁
  exact (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp hmain

lemma rectangular_norm_range (M : CStarMatrix m n A) :
    ‖M*M.conjTranspose‖ = ‖M‖^2 := by
  apply le_antisymm _ (rectangular_norm_sq_le_range M)
  simpa only [rectangular_norm_conjTranspose, pow_two] using
    rectangular_norm_mul_le M M.conjTranspose

lemma rectangular_norm_initial (M : CStarMatrix m n A) :
    ‖M.conjTranspose*M‖ = ‖M‖^2 := by
  simpa only [rectangular_conjTranspose_conjTranspose, rectangular_norm_conjTranspose] using
    rectangular_norm_range M.conjTranspose

lemma rectangular_initial_nonneg (M : CStarMatrix m n A) : 0 ≤ M.conjTranspose*M := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have : M.conjTranspose*M = 0 := by ext i j; exact hn.false i |>.elim
    rw [this]
  | inr hn =>
    let i₀ : n := Classical.choice hn
    let R (i : m) : CStarMatrix n n A := fun j k => if j = i₀ then M i k else 0
    have hrows (T : m → n → A) :
        Matrix.conjTranspose (Matrix.of T) * Matrix.of T = ∑ i : m,
          Matrix.conjTranspose (Matrix.of (fun j k : n => if j = i₀ then T i k else 0)) *
            Matrix.of (fun j k : n => if j = i₀ then T i k else 0) := by
      ext j k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.of_apply]
      simp
    have he : M.conjTranspose*M = ∑ i : m, star (R i)*R i :=
      hrows (Matrix.of.symm (CStarMatrix.ofMatrix.symm M))
    rw [he]
    exact Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (R i))


end WeakPureInfiniteness

end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpectralCut
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

open scoped Topology CStarAlgebra

lemma continuous_spectralRamp (θ : ℝ) : Continuous (spectralRamp θ) := by
  unfold spectralRamp
  fun_prop

lemma spectralRamp_nonneg (θ s : ℝ) : 0 ≤ spectralRamp θ s :=
  le_min zero_le_one (le_max_left _ _)

lemma spectralRamp_le_one (θ s : ℝ) : spectralRamp θ s ≤ 1 := min_le_left _ _

lemma spectralRamp_eq_zero {θ s : ℝ} (hθ : 0 < θ) (hs : s ≤ θ) :
    spectralRamp θ s = 0 := by
  unfold spectralRamp
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hθ.le)]
  exact min_eq_right zero_le_one

lemma spectralRamp_eq_one {θ s : ℝ} (hθ : 0 < θ) (hs : 2*θ ≤ s) :
    spectralRamp θ s = 1 := by
  unfold spectralRamp
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  rw [le_div_iff₀ hθ]
  linarith

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalSpectralTools
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma starLift_inr_apply_general (π : A →⋆ₙₐ[ℂ] B) (a : A) :
    (Unitization.starLift π) (a : Unitization ℂ A)=π a :=
  congrArg (fun f : A →⋆ₙₐ[ℂ] B => f a) (Equiv.symm_apply_apply Unitization.starLift π)

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalSpectralTools2
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

omit [NonUnitalCStarAlgebra A] in
lemma unitization_inr_snd_of_fst_eq_zero {z : Unitization ℂ A} (hz : z.fst=0) :
    (z.snd : Unitization ℂ A)=z := by
  ext <;> simp [hz]

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SupportedCorner
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma matrixSingletonHom_injective : Function.Injective (matrixSingletonHom (A := A)) := by
  intro x y h
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  exact h

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CompatibleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra

section Algebra

variable {B : Type*} [CStarAlgebra B]

lemma metric_column_expansion_any (F C g e p y Z : B) (η : ℝ)
    (hFCg : F*C*g=p) (hge : g*e=e) (hZ : Z=1+(η : ℂ) • (g*y*g)) :
    F*C*Z*e=F*C*e+(η : ℂ) • (p*y*e) := by
  rw [hZ,mul_add,add_mul,mul_one,mul_smul_comm,smul_mul_assoc]
  congr 2
  calc
    F*C*(g*y*g)*e = (F*C*g)*y*(g*e) := by simp only [mul_assoc]
    _ = p*y*e := by rw [hFCg,hge]

lemma metric_column_update_any (F C g e p y Z W : B) (η : ℝ)
    (hFCg : F*C*g=p) (hge : g*e=e) (hZ : Z=W+(η : ℂ) • (g*y*g)) :
    F*C*Z*e=F*C*W*e+(η : ℂ) • (p*y*e) := by
  rw [hZ,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  congr 2
  calc
    F*C*(g*y*g)*e = (F*C*g)*y*(g*e) := by simp only [mul_assoc]
    _ = p*y*e := by rw [hFCg,hge]

end Algebra

section Unitization

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_snd_mul_inr_any (u : Unitization ℂ A) (a : A) :
    ((u*(a : Unitization ℂ A)).snd : Unitization ℂ A)=u*(a : Unitization ℂ A) := by
  apply unitization_inr_snd_of_fst_eq_zero
  simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero]

lemma exists_compatible_metric_perturbations_any
    {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hτ : 0 < τ)
    (hpert : UniformPerturbationOne_any A σ)
    (g F₁ F₂ C₁ C₂ : Unitization ℂ A) (hg : ‖g‖ ≤ 1) (hgsa : IsSelfAdjoint g)
    (p₁ p₂ e f h₁ h₂ k₁ k₂ d₁ d₂ : A)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hph₁ : star p₁*p₁*h₁=h₁) (hph₂ : star p₂*p₂*h₂=h₂)
    (hek₁ : e*star e*k₁=k₁) (hfk₂ : f*star f*k₂=k₂)
    (hdh₁ : CuntzSubequiv (diagonalCopies 1 d₁) (diagonalCopies 1 h₁))
    (hdh₂ : CuntzSubequiv (diagonalCopies 1 d₂) (diagonalCopies 1 h₂))
    (hdk₁ : CuntzSubequiv (diagonalCopies 1 d₁) (diagonalCopies 1 k₁))
    (hdk₂ : CuntzSubequiv (diagonalCopies 1 d₂) (diagonalCopies 1 k₂))
    (hge : g*(e : Unitization ℂ A)=(e : Unitization ℂ A))
    (hgf : g*(f : Unitization ℂ A)=(f : Unitization ℂ A))
    (hFC₁ : F₁*C₁*g=(p₁ : Unitization ℂ A))
    (hFC₂ : F₂*C₂*g=(p₂ : Unitization ℂ A)) :
    ∃ Z W z w : Unitization ℂ A,
      Z=1+g*z*g ∧ W=1+g*w*g ∧ star Z*W=1 ∧
      ‖Z‖ ≤ 2 ∧ ‖W‖ ≤ 2 ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        τ ≤ ‖π d₁‖ → σ/16 ≤ ‖(Unitization.starLift π) (F₁*C₁*Z*(e : Unitization ℂ A))‖) ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        τ ≤ ‖π d₂‖ → σ^2/128 ≤ ‖(Unitization.starLift π) (F₂*C₂*W*(f : Unitization ℂ A))‖) := by
  let B := Unitization ℂ A
  let η : ℝ := 1/8
  let η' : ℝ := σ/128
  have hη : 0 < η := by norm_num [η]
  have hη' : 0 < η' := by dsimp [η'] <;> positivity
  let T₁ : A := (F₁*C₁*(e : B)).snd
  have hT₁ : (T₁ : B)=F₁*C₁*(e : B) := inr_snd_mul_inr_any _ _
  obtain ⟨y,hy,hytest⟩ := hpert p₁ e h₁ k₁ d₁ hp₁ he hh₁ hk₁ hd₁ hph₁ hek₁ hdh₁ hdk₁ T₁ η τ hη hτ
  let a₁ : B := (η : ℂ) • (y : B)
  have ha₁ : ‖a₁‖ ≤ 1/8 := by
    dsimp only [a₁,η]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/8),Unitization.norm_inr]
    nlinarith
  let Z₁ : B := 1+g*a₁*g
  have hZ₁ : ‖Z₁‖ ≤ 9/8 := (norm_factored_perturbation_le g a₁ hg).trans (by linarith)
  obtain ⟨w₁,hw₁,hleft₁,hright₁⟩ := exists_factored_inverse g (star a₁) hg
    (by simpa only [norm_star] using ha₁) (by norm_num : (1/8 : ℝ) < 1)
  have hw₁' : ‖w₁‖ ≤ 1/7 := by norm_num at hw₁; exact hw₁
  let W₁ : B := 1+g*w₁*g
  have hstarZ₁ : star Z₁=1+g*star a₁*g := by
    dsimp only [Z₁]
    rw [star_add,star_one,star_mul,star_mul,hgsa.star_eq]
    simp only [mul_assoc]
  have hW₁Z₁ : star W₁*Z₁=1 := by
    have h := congrArg star hleft₁
    simpa only [← hstarZ₁,star_mul,star_star,star_one] using h
  have hfirst (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (hπ : τ ≤ ‖π d₁‖) :
      σ/8 ≤ ‖(Unitization.starLift π) (F₁*C₁*Z₁*(e : B))‖ := by
    have hz : Z₁=1+(η : ℂ) • (g*(y : B)*g) := by simp only [Z₁,a₁,mul_smul_comm,smul_mul_assoc]
    rw [metric_column_expansion_any F₁ C₁ g (e : B) (p₁ : B) (y : B) Z₁ η hFC₁ hge hz,← hT₁]
    rw [← Unitization.inr_mul,← Unitization.inr_mul,← Unitization.inr_smul,← Unitization.inr_add,
      starLift_inr_apply_general]
    simpa only [η,div_eq_mul_inv,one_mul] using hytest H π hπ
  let T₂ : A := (F₂*C₂*W₁*(f : B)).snd
  have hT₂ : (T₂ : B)=F₂*C₂*W₁*(f : B) := inr_snd_mul_inr_any _ _
  obtain ⟨y',hy',hytest'⟩ := hpert p₂ f h₂ k₂ d₂ hp₂ hf hh₂ hk₂ hd₂ hph₂ hfk₂ hdh₂ hdk₂ T₂ η' τ hη' hτ
  let w : B := w₁+(η' : ℂ) • (y' : B)
  have hw : ‖w‖ ≤ 1/4 := by
    have hn : ‖(η' : ℂ) • (y' : B)‖ ≤ η' := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη',Unitization.norm_inr]
      nlinarith
    have hsum := norm_add_le w₁ ((η' : ℂ) • (y' : B))
    dsimp only [η'] at hn
    dsimp only [w]
    linarith
  obtain ⟨z,hz,hleft,hright⟩ := exists_factored_inverse g (star w) hg
    (by simpa only [norm_star] using hw) (by norm_num : (1/4 : ℝ) < 1)
  have hz' : ‖z‖ ≤ 1/3 := by norm_num at hz; exact hz
  let Z : B := 1+g*z*g
  let W : B := 1+g*w*g
  have hstarW : star W=1+g*star w*g := by
    dsimp only [W]
    rw [star_add,star_one,star_mul,star_mul,hgsa.star_eq]
    simp only [mul_assoc]
  have hZW : Z*star W=1 := by simpa only [hstarW] using hright
  have hstarZW : star Z*W=1 := by
    have h := congrArg star hleft
    simpa only [← hstarW,star_mul,star_star,star_one] using h
  have hW : W=W₁+(η' : ℂ) • (g*(y' : B)*g) := by
    simp only [W,W₁,w,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_assoc]
  have hdiff : ‖F₁*C₁*(Z-Z₁)*(e : B)‖ ≤ 3/2*η' :=
    normalized_inverse_difference_bound g z Z Z₁ W W₁ (p₁ : B) F₁ C₁ (e : B) (y' : B)
      hη'.le hg hz' hZ₁ (by simpa only [Unitization.norm_inr] using hp₁)
      (by simpa only [Unitization.norm_inr] using he) (by simpa only [Unitization.norm_inr] using hy')
      hgsa rfl hFC₁ hZW hW₁Z₁ hW
  refine ⟨Z,W,z,w,rfl,rfl,hstarZW,?_,?_,?_,?_⟩
  · exact (norm_factored_perturbation_le g z hg).trans (by linarith)
  · exact (norm_factored_perturbation_le g w hg).trans (by linarith)
  · intro H π hπ
    have ht := hfirst H π hπ
    have hnorm := norm_sub_norm_le ((Unitization.starLift π) (F₁*C₁*Z₁*(e : B)))
      ((Unitization.starLift π) (F₁*C₁*Z*(e : B)))
    have hc : ‖(Unitization.starLift π) (F₁*C₁*Z₁*(e : B))-
        (Unitization.starLift π) (F₁*C₁*Z*(e : B))‖ ≤ 3/2*η' := by
      rw [← map_sub]
      have halg : F₁*C₁*Z₁*(e : B)-F₁*C₁*Z*(e : B)= -(F₁*C₁*(Z-Z₁)*(e : B)) := by noncomm_ring
      rw [halg,map_neg,norm_neg]
      exact (NonUnitalStarAlgHom.norm_apply_le (Unitization.starLift π).toNonUnitalStarAlgHom _).trans hdiff
    dsimp only [η'] at hc
    linarith
  · intro H π hπ
    rw [metric_column_update_any F₂ C₂ g (f : B) (p₂ : B) (y' : B) W W₁ η' hFC₂ hgf hW,← hT₂]
    rw [← Unitization.inr_mul,← Unitization.inr_mul,← Unitization.inr_smul,← Unitization.inr_add,
      starLift_inr_apply_general]
    have ht := hytest' H π hπ
    dsimp only [η'] at ht
    nlinarith

end Unitization

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FourColumnNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModuleFour
lemma norm_rectangular_sqrt_left (U : CStarMatrix m n A) (V : CStarMatrix n k A) :
    ‖CFC.sqrt (U.conjTranspose*U)*V‖=‖U*V‖ := by
  have he : (CFC.sqrt (U.conjTranspose*U)*V).conjTranspose*
      (CFC.sqrt (U.conjTranspose*U)*V)=(U*V).conjTranspose*(U*V) := by
    rw [rectangular_star_mul,rectangular_star_mul]
    change (V.conjTranspose*star (CFC.sqrt (U.conjTranspose*U)))*
      (CFC.sqrt (U.conjTranspose*U)*V)=(V.conjTranspose*U.conjTranspose)*(U*V)
    rw [(CFC.sqrt_nonneg (U.conjTranspose*U)).star_eq]
    calc
      _=V.conjTranspose*(CFC.sqrt (U.conjTranspose*U)*CFC.sqrt (U.conjTranspose*U))*V := by
        simp only [rectangular_mul_assoc]
      _=V.conjTranspose*(U.conjTranspose*U)*V := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg U)]
      _=_ := by simp only [rectangular_mul_assoc]
  have hn := congrArg norm he
  rw [rectangular_norm_initial,rectangular_norm_initial] at hn
  nlinarith [norm_nonneg (CFC.sqrt (U.conjTranspose*U)*V),norm_nonneg (U*V)]

lemma norm_rectangular_sqrt_right (U : CStarMatrix m n A) (V : CStarMatrix k n A) :
    ‖U*CFC.sqrt (V.conjTranspose*V)‖=‖U*V.conjTranspose‖ := by
  have h := norm_rectangular_sqrt_left V U.conjTranspose
  have h1 : (U*CFC.sqrt (V.conjTranspose*V)).conjTranspose=
      CFC.sqrt (V.conjTranspose*V)*U.conjTranspose := by
    rw [rectangular_star_mul]
    change star (CFC.sqrt (V.conjTranspose*V))*U.conjTranspose=_
    rw [(CFC.sqrt_nonneg (V.conjTranspose*V)).star_eq]
  have h2 : (U*V.conjTranspose).conjTranspose=V*U.conjTranspose := by
    rw [rectangular_star_mul,rectangular_conjTranspose_conjTranspose]
  rw [← h1,← h2,rectangular_norm_conjTranspose,rectangular_norm_conjTranspose] at h
  exact h

lemma norm_rectangular_range_roots (U : CStarMatrix m n A) (V : CStarMatrix m k A) :
    ‖CFC.sqrt (U*U.conjTranspose)*CFC.sqrt (V*V.conjTranspose)‖=
      ‖U.conjTranspose*V‖ := by
  have h1 := norm_rectangular_sqrt_left U.conjTranspose (CFC.sqrt (V*V.conjTranspose))
  have h2 := norm_rectangular_sqrt_right U.conjTranspose V.conjTranspose
  simp only [rectangular_conjTranspose_conjTranspose] at h1 h2
  exact h1.trans h2

open WithCStarModule in
lemma norm_matrix_le_sum_entries (M : CStarMatrix m n A) : ‖M‖ ≤ ∑ j,∑ i,‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [CStarMatrix.toCLM_apply_eq_sum,Finset.sum_mul]
  apply (pi_norm_le_sum_norm _).trans
  gcongr with i _
  apply (norm_sum_le _ _).trans
  gcongr with j _
  apply (norm_mul_le _ _).trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationScalar
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

lemma separationFloor_pos {l : ℝ} (hl : 0 < l) (s : ℝ) : 0 < separationFloor l s :=
  hl.trans_le (le_max_left _ _)

lemma continuous_separationFloor (l : ℝ) : Continuous (separationFloor l) :=
  continuous_const.max Real.continuous_sqrt

lemma continuous_separationR {l : ℝ} (hl : 0 < l) : Continuous (separationR l) := by
  unfold separationR
  exact continuous_const.div (Real.continuous_sqrt.comp (continuous_separationFloor l))
    (fun s => ne_of_gt (Real.sqrt_pos.mpr (separationFloor_pos hl s)))

lemma continuous_separationV {l : ℝ} (hl : 0 < l) : Continuous (separationV l) := by
  unfold separationV
  exact (continuous_separationR hl).div (continuous_separationFloor l)
    (fun s => ne_of_gt (separationFloor_pos hl s))

lemma continuous_separationK {l : ℝ} (hl : 0 < l) : Continuous (separationK l) := by
  unfold separationK
  exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_separationFloor l))).inv₀
    (fun s => ne_of_gt (mul_pos (Real.sqrt_pos.mpr hl) (Real.sqrt_pos.mpr (separationFloor_pos hl s))))

lemma continuous_separationG (l : ℝ) : Continuous (separationG l) :=
  (continuous_spectralRamp l).comp Real.continuous_sqrt

lemma continuous_separationN (l : ℝ) : Continuous (separationN l) :=
  (continuous_spectralRamp (4*l)).comp Real.continuous_sqrt

lemma continuous_separationL (l : ℝ) : Continuous (separationL l) :=
  continuous_const.sub (continuous_separationN l)

lemma separationR_nonneg {l : ℝ} (_hl : 0 ≤ l) (s : ℝ) : 0 ≤ separationR l s := by
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma separationV_nonneg {l : ℝ} (hl : 0 < l) (s : ℝ) : 0 ≤ separationV l s :=
  div_nonneg (separationR_nonneg hl.le s) (separationFloor_pos hl s).le

lemma separationR_sq {l : ℝ} (hl : 0 < l) (s : ℝ) :
    (separationR l s)^2=l/separationFloor l s := by
  rw [separationR,div_pow,Real.sq_sqrt hl.le,Real.sq_sqrt (separationFloor_pos hl s).le]

lemma separation_floor_ge_sqrt (l s : ℝ) : Real.sqrt s ≤ separationFloor l s := le_max_right _ _

lemma separation_floor_eq {l s : ℝ} (h : l ≤ Real.sqrt s) : separationFloor l s=Real.sqrt s :=
  max_eq_right h

lemma separationG_zero {l : ℝ} (hl : 0 < l) : separationG l 0=0 := by
  exact spectralRamp_eq_zero hl (by simpa using hl.le)

lemma separationN_zero {l : ℝ} (hl : 0 < l) : separationN l 0=0 := by
  exact spectralRamp_eq_zero (by positivity) (by simpa using (show 0 ≤ 4*l by positivity))

lemma separationVRG {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*separationV l s*separationR l s*separationG l s=l*separationG l s := by
  by_cases h : Real.sqrt s ≤ l
  · rw [show separationG l s=0 from spectralRamp_eq_zero hl h,mul_zero,mul_zero]
  · have hp : 0 < Real.sqrt s := hl.trans (lt_of_not_ge h)
    have he : s*separationV l s*separationR l s=l := by
      rw [separationV]
      calc
        s*(separationR l s/separationFloor l s)*separationR l s =
            s*(separationR l s)^2/separationFloor l s := by ring
        _=l := by rw [separationR_sq hl,separation_floor_eq (le_of_not_ge h)]
                  field_simp
                  nlinarith [Real.sq_sqrt hs]
    rw [he]

lemma separation_low_support {l s : ℝ} (hl : 0 < l) (h : 8*l ≤ Real.sqrt s) :
    separationL l s=0 := by
  have hn : separationN l s=1 := spectralRamp_eq_one (by positivity) (by linarith)
  simp only [separationL,hn,sub_self]

lemma separationL_bounds (l s : ℝ) : 0 ≤ separationL l s ∧ separationL l s ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (spectralRamp_le_one (4*l) (Real.sqrt s))
  · exact sub_le_self _ (spectralRamp_nonneg (4*l) (Real.sqrt s))

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationScalarBounds
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

lemma separationK_sq {l : ℝ} (hl : 0 < l) (s : ℝ) :
    (separationK l s)^2=(l*separationFloor l s)⁻¹ := by
  rw [separationK,inv_pow,mul_pow,Real.sq_sqrt hl.le,Real.sq_sqrt (separationFloor_pos hl s).le]

lemma separation_low_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*(separationL l s)^4 ≤ 64*l^2 := by
  by_cases h : 8*l ≤ Real.sqrt s
  · rw [separation_low_support hl h]; nlinarith [sq_nonneg l]
  · have hsqrt : Real.sqrt s ≤ 8*l := (lt_of_not_ge h).le
    have hL := separationL_bounds l s
    have hL2 : (separationL l s)^2 ≤ 1 := by nlinarith
    have hL4 : (separationL l s)^4 ≤ 1 := by nlinarith [sq_nonneg ((separationL l s)^2)]
    have hs' : s ≤ 64*l^2 := by nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s]
    nlinarith

lemma separation_mixed_R_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*(separationR l s)^2*(separationL l s)^2 ≤ 9*l^2 := by
  by_cases h : 8*l ≤ Real.sqrt s
  · rw [separation_low_support hl h]; nlinarith [sq_nonneg l]
  · have hu : Real.sqrt s ≤ 8*l := (lt_of_not_ge h).le
    have hm := separationFloor_pos hl s
    have hu0 := Real.sqrt_nonneg s
    have hum := separation_floor_ge_sqrt l s
    have hsq : s ≤ Real.sqrt s*separationFloor l s := by
      nlinarith [Real.sq_sqrt hs,mul_nonneg hu0 (sub_nonneg.mpr hum)]
    have hbase : s*(separationR l s)^2 ≤ 8*l^2 := by
      rw [separationR_sq hl,← mul_div_assoc]
      apply (div_le_iff₀ hm).mpr
      have hmul := mul_le_mul_of_nonneg_right hsq hl.le
      have hmul2 := mul_le_mul_of_nonneg_right hu (mul_nonneg hl.le hm.le)
      nlinarith
    have hL := separationL_bounds l s
    have hL2 : (separationL l s)^2 ≤ 1 := by nlinarith
    have hbase0 : 0 ≤ s*(separationR l s)^2 := by positivity
    nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hL2)]

lemma separation_mixed_V_square_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s^2*(separationV l s)^2*(separationL l s)^2 ≤ 9*l^2 := by
  have hm := separationFloor_pos hl s
  have hum := separation_floor_ge_sqrt l s
  have hs2 : s ≤ (separationFloor l s)^2 := by nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s]
  have hbase : s^2*(separationV l s)^2 ≤ s*(separationR l s)^2 := by
    rw [separationV,div_pow]
    have he : s^2*((separationR l s)^2/(separationFloor l s)^2)=
        (s^2*(separationR l s)^2)/(separationFloor l s)^2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    have h := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hs (sq_nonneg (separationR l s)))
    nlinarith
  exact (mul_le_mul_of_nonneg_right hbase (sq_nonneg _)).trans (separation_mixed_R_square_bound hl hs)

lemma separation_coverage_VKN {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) :
    s*separationV l s*separationK l s*separationN l s=separationN l s := by
  by_cases h : Real.sqrt s ≤ 4*l
  · rw [show separationN l s=0 from spectralRamp_eq_zero (by positivity) h,mul_zero]
  · have hu : 0 < Real.sqrt s := by linarith [lt_of_not_ge h]
    have hm : separationFloor l s=Real.sqrt s := separation_floor_eq (by linarith [lt_of_not_ge h])
    have he : s*separationV l s*separationK l s=1 := by
      unfold separationV separationR separationK
      rw [hm]
      have hl' : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl)
      have hu' : Real.sqrt (Real.sqrt s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
      field_simp
      nlinarith [Real.sq_sqrt hs,Real.sq_sqrt hu.le]
    rw [he,one_mul]

lemma separation_coverage_K_bound {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s*(separationK l s)^2 ≤ l⁻¹ := by
  have hm := separationFloor_pos hl s
  have hum := separation_floor_ge_sqrt l s
  have hu0 := Real.sqrt_nonneg s
  have hu1 : Real.sqrt s ≤ 1 := by nlinarith [Real.sq_sqrt hs]
  have hsle : s ≤ separationFloor l s := by nlinarith [Real.sq_sqrt hs,mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  rw [separationK_sq hl,← div_eq_mul_inv]
  apply (div_le_iff₀ (mul_pos hl hm)).mpr
  rw [show l⁻¹*(l*separationFloor l s)=separationFloor l s by field_simp]
  exact hsle

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolarCFC
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma initial_mul_cfc (X : B) (f : ℝ → ℝ) (hf : Continuous f) :
    star (X*cfc f (star X*X))*(X*cfc f (star X*X))=
      cfc (fun s => s*(f s)^2) (star X*X) := by
  have hF : IsSelfAdjoint (cfc f (star X*X)) := cfc_predicate _ _
  have hcomm : Commute (cfc f (star X*X)) (star X*X) := (Commute.refl _).cfc_real f
  rw [star_mul,hF.star_eq]
  calc
    _=cfc f (star X*X)*(star X*X)*cfc f (star X*X) := by simp only [mul_assoc]
    _=(star X*X)*cfc f (star X*X)*cfc f (star X*X) := by rw [hcomm.eq]
    _=cfc (fun s : ℝ => s*f s*f s) (star X*X) := by
      rw [cfc_mul (fun s : ℝ => s*f s) f _ (continuous_id.mul hf).continuousOn hf.continuousOn,
        cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,
        cfc_id' ℝ (star X*X) (IsSelfAdjoint.star_mul_self X)]
    _=_ := by congr 1; ext s; ring

lemma norm_mul_cfc_initial_le (X : B) (f : ℝ → ℝ) (hf : Continuous f)
    {c : ℝ} (hc : 0 ≤ c)
    (hscalar : ∀ s ∈ spectrum ℝ (star X*X),s*(f s)^2 ≤ c^2) :
    ‖X*cfc f (star X*X)‖ ≤ c := by
  have hn : ‖cfc (fun s => s*(f s)^2) (star X*X)‖ ≤ c^2 := by
    apply norm_cfc_le (sq_nonneg c)
    intro s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs) (sq_nonneg _))]
    exact hscalar s hs
  rw [← initial_mul_cfc X f hf,CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (X*cfc f (star X*X))]

omit [PartialOrder B] [StarOrderedRing B] in
lemma sandwich_cfc_initial (X : B) (f : ℝ → ℝ) (hf : Continuous f) :
    X*cfc f (star X*X)*star X=cfc (fun s => s*f s) (X*star X) := by
  rw [← cfc_star_mul_intertwine X f hf,mul_assoc]
  have hcomm : Commute (cfc f (X*star X)) (X*star X) := (Commute.refl _).cfc_real f
  rw [hcomm.eq]
  rw [cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,
    cfc_id' ℝ (X*star X) (IsSelfAdjoint.mul_star_self X)]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cfc_real_mul_three (a : B) (_ha : IsSelfAdjoint a)
    (f g k : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    cfc f a*cfc g a*cfc k a=cfc (fun s => f s*g s*k s) a := by
  rw [cfc_mul (fun s => f s*g s) k a (hf.mul hg).continuousOn hk.continuousOn,
    cfc_mul f g a hf.continuousOn hg.continuousOn]

lemma norm_separation_low (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationL l) (X*star X)*X*cfc (separationL l) (star X*X)‖ ≤ 8*l := by
  rw [cfc_star_mul_intertwine X _ (continuous_separationL l),mul_assoc,
    ← cfc_mul _ _ _ (continuous_separationL l).continuousOn (continuous_separationL l).continuousOn]
  apply norm_mul_cfc_initial_le X _ ((continuous_separationL l).mul (continuous_separationL l)) (by positivity)
  intro s hs
  have h := separation_low_square_bound hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  change s * (separationL l s * separationL l s)^2 ≤ (8*l)^2
  nlinarith

lemma norm_separation_mixedR (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationL l) (X*star X)*X*cfc (separationR l) (star X*X)‖ ≤ 3*l := by
  rw [cfc_star_mul_intertwine X _ (continuous_separationL l),mul_assoc,
    ← cfc_mul _ _ _ (continuous_separationL l).continuousOn (continuous_separationR hl).continuousOn]
  apply norm_mul_cfc_initial_le X _ ((continuous_separationL l).mul (continuous_separationR hl)) (by positivity)
  intro s hs
  have h := separation_mixed_R_square_bound hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  change s * (separationL l s * separationR l s)^2 ≤ (3*l)^2
  nlinarith

lemma norm_separation_mixedV (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationV l) (star X*X)*(star X*X)*cfc (separationL l) (star X*X)‖ ≤ 3*l := by
  have he : cfc (separationV l) (star X*X)*(star X*X)*cfc (separationL l) (star X*X)=
      cfc (fun s => s*separationV l s*separationL l s) (star X*X) := by
    rw [(Commute.refl (star X*X)).cfc_real (separationV l) |>.eq]
    conv_lhs => lhs; lhs; rw [← cfc_id' ℝ (star X*X) (IsSelfAdjoint.star_mul_self X)]
    exact cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) (fun s => s) _ _ continuous_id
      (continuous_separationV hl) (continuous_separationL l)
  rw [he]
  apply norm_cfc_le (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg hs0 (separationV_nonneg hl s))
    (separationL_bounds l s).1)]
  have h := separation_mixed_V_square_bound hl hs0
  nlinarith [mul_nonneg (mul_nonneg hs0 (separationV_nonneg hl s)) (separationL_bounds l s).1]

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationMetric
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma separation_metric_identity (a b : B) (ha : IsSelfAdjoint a)
    {l : ℝ} (hl : 0 < l) :
    let X := a*b
    let T := star X*X
    let C₁ := a*X*cfc (separationV l) T
    let C₂ := b*cfc (separationR l) T
    star C₁*C₂*cfc (separationG l) T=(l : ℂ) • cfc (separationG l) T := by
  dsimp only
  have hV : IsSelfAdjoint (cfc (separationV l) (star (a*b)*(a*b))) := cfc_predicate _ _
  have hstar : star (a*(a*b)*cfc (separationV l) (star (a*b)*(a*b)))=
      cfc (separationV l) (star (a*b)*(a*b))*star (a*b)*a := by
    rw [star_mul (a*(a*b)) _,star_mul a (a*b),hV.star_eq,ha.star_eq,mul_assoc]
  rw [hstar]
  let X := a*b
  let T := star X*X
  have halg : (cfc (separationV l) T*star X*a)*(b*cfc (separationR l) T)*cfc (separationG l) T=
      cfc (separationV l) T*T*cfc (separationR l) T*cfc (separationG l) T := by
    dsimp only [T,X]
    simp only [mul_assoc]
  rw [halg]
  rw [(Commute.refl T).cfc_real (separationV l) |>.eq]
  have hid : cfc (fun s : ℝ => s) T=T := cfc_id' ℝ T (IsSelfAdjoint.star_mul_self X)
  conv_lhs => lhs; lhs; lhs; rw [← hid]
  rw [cfc_real_mul_three T (IsSelfAdjoint.star_mul_self X) (fun s => s) _ _ continuous_id
    (continuous_separationV hl) (continuous_separationR hl),
    ← cfc_mul (fun s => s*separationV l s*separationR l s) (separationG l) T ((continuous_id.mul (continuous_separationV hl)).mul (continuous_separationR hl)).continuousOn
      (continuous_separationG l).continuousOn]
  have he : cfc (fun s => s*separationV l s*separationR l s*separationG l s) T=
      cfc (fun s => l*separationG l s) T := by
    apply cfc_congr
    intro s hs
    exact separationVRG hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  rw [he,cfc_const_mul l (separationG l) T (continuous_separationG l).continuousOn]
  exact (IsScalarTower.algebraMap_smul ℂ l (cfc (separationG l) T)).symm

omit [PartialOrder B] [StarOrderedRing B] in
lemma compatible_columns_orthogonal (C₁ C₂ g e f Z W w : B) (l : ℝ)
    (he : IsSelfAdjoint e) (hef : e*f=0) (hgf : g*f=f)
    (hW : W=1+g*w*g) (hZW : star Z*W=1)
    (hmetric : star C₁*C₂*g=(l : ℂ) • g) :
    star (C₁*Z*e)*(C₂*W*f)=0 := by
  let D := star C₁*C₂-(l : ℂ) • (1 : B)
  have hDg : D*g=0 := by
    dsimp only [D]
    rw [sub_mul,hmetric,smul_mul_assoc,one_mul,sub_self]
  have hDf : D*f=0 := by rw [← hgf,← mul_assoc,hDg,zero_mul]
  have hDWf : D*W*f=0 := by
    rw [hW,mul_add,mul_one,add_mul,hDf]
    have heq : D*(g*w*g)*f=(D*g)*w*g*f := by simp only [mul_assoc]
    rw [heq,hDg,zero_mul,zero_mul,zero_mul,add_zero]
  have hM : (star C₁*C₂)*W*f=(l : ℂ) • (W*f) := by
    have h : D*W*f=(star C₁*C₂)*W*f-(l : ℂ) • (W*f) := by
      dsimp only [D]
      simp only [sub_mul,smul_mul_assoc,one_mul,mul_assoc]
    rw [h] at hDWf
    exact sub_eq_zero.mp hDWf
  rw [star_mul,star_mul,he.star_eq]
  calc
    _=e*star Z*((star C₁*C₂)*W*f) := by simp only [mul_assoc]
    _=(l : ℂ) • (e*(star Z*W)*f) := by rw [hM]; simp only [mul_smul_comm,mul_assoc]
    _=0 := by rw [hZW,mul_one,hef,smul_zero]

lemma separation_first_coverage_identity (a X : B) {l : ℝ} (hl : 0 < l) :
    (a*X*cfc (separationV l) (star X*X))*cfc (separationN l) (star X*X)*
      star (X*cfc (separationK l) (star X*X))=
      a*cfc (separationN l) (X*star X) := by
  have hK : IsSelfAdjoint (cfc (separationK l) (star X*X)) := cfc_predicate _ _
  rw [star_mul,hK.star_eq]
  have he : (a*X*cfc (separationV l) (star X*X))*cfc (separationN l) (star X*X)*
      (cfc (separationK l) (star X*X)*star X)=
      a*(X*(cfc (separationV l) (star X*X)*cfc (separationN l) (star X*X)*
        cfc (separationK l) (star X*X))*star X) := by simp only [mul_assoc]
  rw [he,cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) _ _ _
    (continuous_separationV hl) (continuous_separationN l) (continuous_separationK hl),
    sandwich_cfc_initial X (fun s => separationV l s*separationN l s*separationK l s) (((continuous_separationV hl).mul (continuous_separationN l)).mul (continuous_separationK hl))]
  congr 1
  apply cfc_congr
  intro s hs
  have h := separation_coverage_VKN hl (spectrum_nonneg_of_nonneg (mul_star_self_nonneg X) hs)
  nlinarith

lemma norm_separation_coverage_factor (X : B) (hX : ‖X‖ ≤ 1)
    {l : ℝ} (hl : 0 < l) :
    ‖X*cfc (separationK l) (star X*X)‖ ≤ (Real.sqrt l)⁻¹ := by
  nontriviality B
  apply norm_mul_cfc_initial_le X _ (continuous_separationK hl) (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hs1 : s ≤ 1 := by
    have hn : s ≤ ‖star X*X‖ := by
      have h := spectrum.norm_le_norm_of_mem hs
      simpa only [Real.norm_eq_abs,abs_of_nonneg hs0] using h
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg X]
  have h := separation_coverage_K_bound hl hs0 hs1
  simpa only [inv_pow,Real.sq_sqrt hl.le] using h

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationColumnBounds
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma separation_four_column_bounds (a b e f Z W w : B)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hef : e*f=0)
    {l : ℝ} (hl : 0 < l)
    (hen : ‖e‖ ≤ 1) (hfn : ‖f‖ ≤ 1) (hZ : ‖Z‖ ≤ 2) (hWn : ‖W‖ ≤ 2)
    (hgf : cfc (separationG l) (star (a*b)*(a*b))*f=f)
    (hW : W=1+cfc (separationG l) (star (a*b)*(a*b))*w*cfc (separationG l) (star (a*b)*(a*b)))
    (hZW : star Z*W=1) :
    let X := a*b
    let T := star X*X
    let S := X*star X
    let C₁ := a*X*cfc (separationV l) T
    let C₂ := b*cfc (separationR l) T
    let x₀ := a*cfc (separationL l) S
    let y₀ := b*cfc (separationL l) T
    let x₁ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (C₁*Z*e)
    let y₁ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (C₂*W*f)
    ‖star x₀*y₀‖ ≤ 8*l ∧ ‖star x₁*y₀‖ ≤ 6*Real.sqrt l ∧
      ‖star x₀*y₁‖ ≤ 6*Real.sqrt l ∧ star x₁*y₁=0 := by
  dsimp only
  let X := a*b
  let T := star X*X
  let S := X*star X
  let V := cfc (separationV l) T
  let R := cfc (separationR l) T
  let Lₛ := cfc (separationL l) S
  let Lₜ := cfc (separationL l) T
  have hV : IsSelfAdjoint V := cfc_predicate _ _
  have hLs : IsSelfAdjoint Lₛ := cfc_predicate _ _
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hscale : (Real.sqrt l)⁻¹*l=Real.sqrt l := by
    have hsq := Real.sq_sqrt hl.le
    field_simp
    nlinarith
  have hs_norm : ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ)‖=(Real.sqrt l)⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hroot)]
  have hx0 : star (a*Lₛ)*(b*Lₜ)=Lₛ*X*Lₜ := by
    rw [star_mul,hLs.star_eq,ha.star_eq]
    dsimp only [X]
    simp only [mul_assoc]
  have hx1 : star (a*X*V*Z*e)*(b*Lₜ)=e*star Z*(V*T*Lₜ) := by
    rw [star_mul (a*X*V*Z) e,star_mul (a*X*V) Z,star_mul (a*X) V,star_mul a X,
      he.star_eq,hV.star_eq,ha.star_eq]
    dsimp only [T,X]
    simp only [mul_assoc]
  have hxy1 : star (a*Lₛ)*(b*R*W*f)=(Lₛ*X*R)*W*f := by
    rw [star_mul,hLs.star_eq,ha.star_eq]
    dsimp only [X]
    simp only [mul_assoc]
  refine ⟨?_,?_,?_,?_⟩
  · change ‖star (a*Lₛ)*(b*Lₜ)‖ ≤ _
    rw [hx0]
    exact norm_separation_low X hl
  · change ‖star ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (a*X*V*Z*e))*(b*Lₜ)‖ ≤ _
    rw [star_smul,Complex.star_def,Complex.conj_ofReal,smul_mul_assoc,hx1,norm_smul,hs_norm]
    have hn : ‖e*star Z*(V*T*Lₜ)‖ ≤ 1*2*(3*l) := by
      apply (norm_mul_le _ _).trans
      apply mul_le_mul _ (norm_separation_mixedV X hl) (norm_nonneg _) (by positivity)
      apply (norm_mul_le _ _).trans
      rw [norm_star]
      gcongr
    calc
      _≤(Real.sqrt l)⁻¹*(1*2*(3*l)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _=6*Real.sqrt l := by nlinarith [hscale]
  · change ‖star (a*Lₛ)*((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (b*R*W*f))‖ ≤ _
    rw [mul_smul_comm,hxy1,norm_smul,hs_norm]
    have hn : ‖(Lₛ*X*R)*W*f‖ ≤ (3*l)*2*1 := by
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
        (by gcongr; exact norm_separation_mixedR X hl))
    calc
      _≤(Real.sqrt l)⁻¹*((3*l)*2*1) := mul_le_mul_of_nonneg_left hn (by positivity)
      _=6*Real.sqrt l := by nlinarith [hscale]
  · change star ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (a*X*V*Z*e))*
      ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (b*R*W*f))=0
    rw [star_smul,smul_mul_assoc,mul_smul_comm]
    have hh : star (a*X*V*Z*e)*(b*R*W*f)=0 := compatible_columns_orthogonal
      (a*X*V) (b*R) (cfc (separationG l) T) e f Z W w l he.isSelfAdjoint hef hgf hW hZW
      (separation_metric_identity a b ha.isSelfAdjoint hl)
    rw [hh,smul_zero,smul_zero]

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationFourColumns
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma map_positive_sqrt (φ : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) :
    φ (CFC.sqrt a)=CFC.sqrt (φ a) := by
  symm
  apply CFC.sqrt_unique
  · rw [← map_mul,CFC.sqrt_mul_sqrt_self a ha]
  · exact map_nonneg φ (CFC.sqrt_nonneg a)

lemma norm_column_le_sqrt_sum (x y : A) : ‖x‖ ≤ ‖CFC.sqrt (x*star x+y*star y)‖ := by
  have hxy : 0 ≤ x*star x+y*star y := add_nonneg (mul_star_self_nonneg x) (mul_star_self_nonneg y)
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (le_add_of_nonneg_right (mul_star_self_nonneg y)) (mul_star_self_nonneg x)
  have he : ‖CFC.sqrt (x*star x+y*star y)‖^2=‖x*star x+y*star y‖ := by
    rw [pow_two,← CStarRing.norm_star_mul_self,(CFC.sqrt_nonneg _).star_eq,CFC.sqrt_mul_sqrt_self _ hxy]
  rw [CStarRing.norm_self_mul_star] at h
  nlinarith [norm_nonneg x,norm_nonneg (CFC.sqrt (x*star x+y*star y))]

lemma norm_other_column_le_sqrt_sum (x y : A) : ‖y‖ ≤ ‖CFC.sqrt (x*star x+y*star y)‖ := by
  simpa only [add_comm] using norm_column_le_sqrt_sum y x

omit [PartialOrder A] [StarOrderedRing A] in
lemma twoEntryRow_range (x y : A) :
    matrixSingletonHom (twoEntryRow x y*(twoEntryRow x y).conjTranspose)=x*star x+y*star y := by
  change (∑ i : Fin 2, (![x,y] i)*star (![x,y] i))=x*star x+y*star y
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

attribute [local instance] OAI.WeakPureInfiniteness.matrixRealModuleFourAssembly
lemma norm_two_sqrt_sums_le (x₀ x₁ y₀ y₁ : A) :
    ‖CFC.sqrt (x₀*star x₀+x₁*star x₁)*CFC.sqrt (y₀*star y₀+y₁*star y₁)‖ ≤
      ‖star x₀*y₀‖+‖star x₁*y₀‖+‖star x₀*y₁‖+‖star x₁*y₁‖ := by
  let U := twoEntryRow x₀ x₁
  let V := twoEntryRow y₀ y₁
  have hU : 0 ≤ U*U.conjTranspose := by
    simpa only [rectangular_conjTranspose_conjTranspose] using rectangular_initial_nonneg U.conjTranspose
  have hV : 0 ≤ V*V.conjTranspose := by
    simpa only [rectangular_conjTranspose_conjTranspose] using rectangular_initial_nonneg V.conjTranspose
  have hsU := map_positive_sqrt (matrixSingletonHom (A := A)) hU
  have hsV := map_positive_sqrt (matrixSingletonHom (A := A)) hV
  have hnorm := NonUnitalStarAlgHom.norm_map (matrixSingletonHom (A := A)) matrixSingletonHom_injective
    (CFC.sqrt (U*U.conjTranspose)*CFC.sqrt (V*V.conjTranspose))
  rw [map_mul,hsU,hsV,twoEntryRow_range,twoEntryRow_range] at hnorm
  rw [hnorm,norm_rectangular_range_roots]
  apply (norm_matrix_le_sum_entries _).trans_eq
  change (∑ j : Fin 2,∑ i : Fin 2, ‖(∑ k : Fin 1,star (![x₀,x₁] i)*(![y₀,y₁] j))‖)=_
  simp only [Fin.sum_univ_two,Fin.sum_univ_one,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

end

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_snd_inr_mul (a : A) (u : Unitization ℂ A) :
    (((a : Unitization ℂ A)*u).snd : Unitization ℂ A)=(a : Unitization ℂ A)*u := by
  apply unitization_inr_snd_of_fst_eq_zero
  simp only [Unitization.fst_mul,Unitization.fst_inr,zero_mul]

lemma unitizedRight_mem_principal (a : A) (ha : 0 ≤ a) (u : Unitization ℂ A) :
    ((a : Unitization ℂ A)*u).snd ∈ principalRightIdeal a := by
  have haself : a ∈ principalRightIdeal a := hereditary_le_rightIdeal a ha.isSelfAdjoint
    (self_mem_hereditary a ha)
  change (0 : ℂ) • u.snd+u.fst • a+a*u.snd ∈ principalRightIdeal a
  rw [zero_smul,zero_add]
  exact (principalRightIdeal a).add_mem ((principalRightIdeal a).smul_mem _ haself)
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (LinearMap.mulLeft ℂ a) u.snd))

lemma norm_sqrt_sum_representation {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) (x y : A) :
    ‖π x‖ ≤ ‖π (CFC.sqrt (x*star x+y*star y))‖ ∧
      ‖π y‖ ≤ ‖π (CFC.sqrt (x*star x+y*star y))‖ := by
  rw [map_positive_sqrt π (add_nonneg (mul_star_self_nonneg x) (mul_star_self_nonneg y)),
    map_add,map_mul,map_mul,map_star,map_star]
  exact ⟨norm_column_le_sqrt_sum _ _,norm_other_column_le_sqrt_sum _ _⟩

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationPreassembly
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_unitizedRight (a : A) (u : Unitization ℂ A) :
    ((unitizedRight a u : A) : Unitization ℂ A)=(a : Unitization ℂ A)*u := inr_snd_inr_mul a u

lemma inr_factor_mem_principal {a x : A} (ha : 0 ≤ a) (u : Unitization ℂ A)
    (hx : (x : Unitization ℂ A)=(a : Unitization ℂ A)*u) :
    x ∈ principalRightIdeal a := by
  have he : x=unitizedRight a u := by
    apply Unitization.inr_injective (R := ℂ)
    rw [inr_unitizedRight,hx]
  rw [he]
  exact unitizedRight_mem_principal a ha u

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_separationG (X : A) {l : ℝ} (hl : 0 < l) :
    ((cfcₙ (separationG l) (star X*X) : A) : Unitization ℂ A)=
      cfc (separationG l) (star (X : Unitization ℂ A)*(X : Unitization ℂ A)) := by
  rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (separationG_zero hl),Unitization.inr_mul,Unitization.inr_star]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_separationN (X : A) {l : ℝ} (hl : 0 < l) :
    ((cfcₙ (separationN l) (star X*X) : A) : Unitization ℂ A)=
      cfc (separationN l) (star (X : Unitization ℂ A)*(X : Unitization ℂ A)) := by
  rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (separationN_zero hl),Unitization.inr_mul,Unitization.inr_star]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_separationG (X : Unitization ℂ A) (l : ℝ) :
    ‖cfc (separationG l) (star X*X)‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro s _
  change ‖spectralRamp l (Real.sqrt s)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg _ _)]
  exact spectralRamp_le_one _ _

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCores
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma columnCoreFunction_zero {τ : ℝ} (hτ : 0 ≤ τ) : columnCoreFunction τ 0=0 := by
  simp only [columnCoreFunction,Real.sqrt_zero,zero_sub]
  exact max_eq_right (neg_nonpos.mpr hτ)

lemma nonunital_column_left_normalization (D : A) {τ : ℝ} (hτ : 0 < τ) :
    let F : Unitization ℂ A := cfc (columnMetricFunction τ) ((D : Unitization ℂ A)*star (D : Unitization ℂ A))
    let h : A := cfcₙ (columnCoreFunction τ) (star D*D)
    ∃ p : A,F*(D : Unitization ℂ A)=(p : Unitization ℂ A) ∧
      ‖F‖ ≤ τ⁻¹ ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ star p*p*h=h := by
  dsimp only
  let F : Unitization ℂ A := cfc (columnMetricFunction τ) ((D : Unitization ℂ A)*star (D : Unitization ℂ A))
  let p : A := (F*(D : Unitization ℂ A)).snd
  let h : A := cfcₙ (columnCoreFunction τ) (star D*D)
  have hp : (p : Unitization ℂ A)=F*(D : Unitization ℂ A) := by
    apply unitization_inr_snd_of_fst_eq_zero
    simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero]
  have hh : (h : Unitization ℂ A)=cfc (columnCoreFunction τ) (star (D : Unitization ℂ A)*(D : Unitization ℂ A)) := by
    dsimp only [h]
    rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (columnCoreFunction_zero hτ.le),Unitization.inr_mul,Unitization.inr_star]
  obtain ⟨hF,hpn,hhn,hph⟩ := column_left_normalization (D : Unitization ℂ A) hτ
  refine ⟨p,hp.symm,hF,?_,?_,?_⟩
  · rw [← Unitization.norm_inr (𝕜 := ℂ) p,hp]
    exact hpn
  · exact cfcₙ_nonneg (fun s _ => le_max_right _ _)
  · apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_mul,Unitization.inr_mul,Unitization.inr_star,hp,hh]
    exact hph

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCoreSelection
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

universe u v

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_column_core_norm (π : A →⋆ₙₐ[ℂ] B) (D : A) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖π (cfcₙ (columnCoreFunction τ) (star D*D))‖=max (‖π D‖-τ) 0 := by
  rw [π.map_cfcₙ (columnCoreFunction τ) (star D*D)
    (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)
    (by fun_prop) (IsSelfAdjoint.star_mul_self D)
    ((IsSelfAdjoint.star_mul_self D).map π)]
  rw [map_mul,map_star,cfcₙ_eq_cfc (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)]
  exact norm_column_core _ hτ

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationCoverage
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

lemma continuous_separationJ (l : ℝ) : Continuous (separationJ l) :=
  (Real.continuous_sqrt.comp (continuous_separationFloor l)).div_const _

lemma separationRJ {l : ℝ} (hl : 0 < l) (s : ℝ) : separationR l s*separationJ l s=1 := by
  unfold separationR separationJ
  have h1 : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl)
  have h2 : Real.sqrt (separationFloor l s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (separationFloor_pos hl s))
  field_simp

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma separation_second_coverage_identity (b X : B) {l : ℝ} (hl : 0 < l) :
    (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=b*cfc (separationN l) (star X*X) := by
  have he : (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=
      b*(cfc (separationR l) (star X*X)*cfc (separationN l) (star X*X)*cfc (separationJ l) (star X*X)) := by
    simp only [mul_assoc]
  rw [he,cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) _ _ _
    (continuous_separationR hl) (continuous_separationN l) (continuous_separationJ l)]
  congr 1
  apply cfc_congr
  intro s _
  calc
    _=(separationR l s*separationJ l s)*separationN l s := by ring
    _=_ := by rw [separationRJ hl,one_mul]

lemma norm_separationJ (X : B) (hX : ‖X‖ ≤ 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    ‖cfc (separationJ l) (star X*X)‖ ≤ (Real.sqrt l)⁻¹ := by
  nontriviality B
  apply norm_cfc_le (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  have hs1 : s ≤ 1 := by
    have hn : s ≤ ‖star X*X‖ := by
      have h := spectrum.norm_le_norm_of_mem hs
      simpa only [Real.norm_eq_abs,abs_of_nonneg hs0] using h
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg X]
  have hfloor : separationFloor l s ≤ 1 := by
    apply max_le hl1
    nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s]
  have hroot : Real.sqrt (separationFloor l s) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hfloor
    simpa using h
  rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp only [separationJ] <;> positivity),separationJ,div_eq_mul_inv]
  calc
    _≤1*(Real.sqrt l)⁻¹ := mul_le_mul_of_nonneg_right hroot (by positivity)
    _=_ := one_mul _

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationNormCoverage
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B]

lemma separation_detection_alternative (a x₀ D K : B) {r l τ : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8)
    (ha : r ≤ ‖a‖) (haeq : a=x₀+D*K) (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹) :
    r/2 ≤ ‖x₀‖ ∨ τ ≤ max (‖D‖-2*τ) 0 := by
  by_cases hx : r/2 ≤ ‖x₀‖
  · exact Or.inl hx
  right
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hn : r ≤ ‖x₀‖+‖D‖*(Real.sqrt l)⁻¹ := by
    apply ha.trans
    rw [haeq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left hK (norm_nonneg _))))
  have hmul := mul_le_mul_of_nonneg_right hn hroot.le
  have hinv : (Real.sqrt l)⁻¹*Real.sqrt l=1 := inv_mul_cancel₀ (ne_of_gt hroot)
  have hnorm : ‖D‖*(Real.sqrt l)⁻¹*Real.sqrt l=‖D‖ := by rw [mul_assoc,hinv,mul_one]
  have hsmall := mul_lt_mul_of_pos_right (lt_of_not_ge hx) hroot
  have hτeq : 8*τ=r*Real.sqrt l := by rw [hτ]; ring
  exact (by nlinarith : τ ≤ ‖D‖-2*τ).trans (le_max_left _ _)

lemma separation_normalized_column_lower (F Y : B) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8)
    (hF : ‖F‖ ≤ τ⁻¹) (hY : c ≤ ‖F*Y‖) :
    r*c/8 ≤ ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y‖ := by
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hn : c ≤ τ⁻¹*‖Y‖ := hY.trans ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right hF (norm_nonneg _)))
  have hmul := mul_le_mul_of_nonneg_left hn hτpos.le
  have hinv : τ*τ⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hτpos)
  have hy : τ*c ≤ ‖Y‖ := by simpa only [← mul_assoc,hinv,one_mul] using hmul
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hroot),mul_comm ((Real.sqrt l)⁻¹) ‖Y‖,← div_eq_mul_inv]
  apply (le_div_iff₀ hroot).mpr
  rw [hτ] at hy
  nlinarith

lemma separation_column_coverage (a x₀ C N K F Y : B) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8) (hc : c ≤ 4)
    (ha : r ≤ ‖a‖) (haeq : a=x₀+(C*N)*K) (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹)
    (hF : ‖F‖ ≤ τ⁻¹)
    (hdet : τ ≤ max (‖C*N‖-2*τ) 0 → c ≤ ‖F*Y‖) :
    r*c/8 ≤ max ‖x₀‖ ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y‖ := by
  obtain hx | hd := separation_detection_alternative a x₀ (C*N) K hr hl hτ ha haeq hK
  · exact (by nlinarith : r*c/8 ≤ ‖x₀‖).trans (le_max_left _ _)
  · exact (separation_normalized_column_lower F Y hr hl hτ hF (hdet hd)).trans (le_max_right _ _)

end

section

variable {B : Type*} [CStarAlgebra B]

lemma separation_LN_decomposition (a T : B) (hT : IsSelfAdjoint T) (l : ℝ) :
    a=a*cfc (separationL l) T+a*cfc (separationN l) T := by
  rw [← mul_add]
  have he : cfc (separationL l) T+cfc (separationN l) T=1 := by
    rw [← cfc_add _ _ _ (continuous_separationL l).continuousOn (continuous_separationN l).continuousOn]
    have hfun : (fun s => separationL l s+separationN l s)=(fun _ => (1 : ℝ)) := by
      funext s
      unfold separationL
      ring
    rw [hfun,cfc_const_one ℝ T hT]
  rw [he,mul_one]

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SeparationTransferredCoverage
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

universe u

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma separation_transferred_coverage
    (a x₀ x₁ C N : A) (K F Y : Unitization ℂ A) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8) (hc : c ≤ 4)
    (haeq : (a : Unitization ℂ A)=(x₀ : Unitization ℂ A)+((C : Unitization ℂ A)*(N : Unitization ℂ A))*K)
    (hx₁ : (x₁ : Unitization ℂ A)=(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y)
    (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹) (hF : ‖F‖ ≤ τ⁻¹)
    (hdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      τ ≤ ‖π (cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N)))‖ →
      c ≤ ‖(Unitization.starLift π) (F*Y)‖) :
    ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ →
      r*c/8 ≤ max ‖π x₀‖ ‖π x₁‖ := by
  intro H π hπ
  let φ := Unitization.starLift π
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hD : ‖π (C*N)‖=‖φ (C : Unitization ℂ A)*φ (N : Unitization ℂ A)‖ := by
    rw [← map_mul,← Unitization.inr_mul,starLift_inr_apply_general]
  have hFπ : ‖φ F‖ ≤ τ⁻¹ := (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom _).trans hF
  have hKπ : ‖φ K‖ ≤ (Real.sqrt l)⁻¹ := (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom _).trans hK
  have hxπ : φ (x₁ : Unitization ℂ A)=(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • φ Y := by rw [hx₁,map_smul]
  have haπ : φ (a : Unitization ℂ A)=φ (x₀ : Unitization ℂ A)+
      (φ (C : Unitization ℂ A)*φ (N : Unitization ℂ A))*φ K := by
    rw [haeq,map_add,map_mul,map_mul]
  have ht := separation_column_coverage (φ (a : Unitization ℂ A)) (φ (x₀ : Unitization ℂ A))
    (φ (C : Unitization ℂ A)) (φ (N : Unitization ℂ A)) (φ K) (φ F) (φ Y)
    hr hl hτ hc (by simpa only [φ,starLift_inr_apply_general] using hπ) haπ hKπ hFπ
    (fun hd => by
      rw [← map_mul]
      apply hdet H π
      rw [map_column_core_norm π (C*N) (by positivity),hD]
      exact hd)
  rw [← hxπ] at ht
  simpa only [φ,starLift_inr_apply_general] using ht

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_QuantitativeSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma separatingPositives_of_four_columns_any
    (a b x₀ x₁ y₀ y₁ : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {r l σ : ℝ} (hr : 0 < r) (hl : 0 < l) (hl1 : l < 1/10)
    (hσ : 0 < σ) (hσ1 : σ < 1)
    (hx₀mem : x₀ ∈ principalRightIdeal a) (hx₁mem : x₁ ∈ principalRightIdeal a)
    (hy₀mem : y₀ ∈ principalRightIdeal b) (hy₁mem : y₁ ∈ principalRightIdeal b)
    (h00 : ‖star x₀*y₀‖ ≤ 8*l) (h10 : ‖star x₁*y₀‖ ≤ 6*Real.sqrt l)
    (h01 : ‖star x₀*y₁‖ ≤ 6*Real.sqrt l) (h11 : star x₁*y₁=0)
    (hcoverage₁ : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      r ≤ ‖π a‖ → r*(σ/16)/8 ≤ max ‖π x₀‖ ‖π x₁‖)
    (hcoverage₂ : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      r ≤ ‖π b‖ → r*(σ^2/128)/8 ≤ max ‖π y₀‖ ‖π y₁‖) :
    ∃ Q R : A,0 ≤ Q ∧ 0 ≤ R ∧
      Q ∈ hereditarySubalgebra a ha.isSelfAdjoint ∧
      R ∈ hereditarySubalgebra b hb.isSelfAdjoint ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        NonUnitalRepresentationIrreducible π →
        (r ≤ ‖π a‖ → r*σ^2/1024 ≤ ‖π Q‖) ∧
        (r ≤ ‖π b‖ → r*σ^2/1024 ≤ ‖π R‖)) ∧ ‖Q*R‖ ≤ 20*Real.sqrt l := by
  let Q : A := CFC.sqrt (x₀*star x₀+x₁*star x₁)
  let R : A := CFC.sqrt (y₀*star y₀+y₁*star y₁)
  have hQQ : 0 ≤ x₀*star x₀+x₁*star x₁ := add_nonneg (mul_star_self_nonneg x₀) (mul_star_self_nonneg x₁)
  have hRR : 0 ≤ y₀*star y₀+y₁*star y₁ := add_nonneg (mul_star_self_nonneg y₀) (mul_star_self_nonneg y₁)
  refine ⟨Q,R,CFC.sqrt_nonneg _,CFC.sqrt_nonneg _,?_,?_,?_,?_⟩
  · exact sqrt_mem_hereditary a _ ha.isSelfAdjoint ((hereditarySubalgebra a ha.isSelfAdjoint).add_mem
      (rightIdeal_square_mem_hereditary a x₀ ha.isSelfAdjoint hx₀mem)
      (rightIdeal_square_mem_hereditary a x₁ ha.isSelfAdjoint hx₁mem)) hQQ
  · exact sqrt_mem_hereditary b _ hb.isSelfAdjoint ((hereditarySubalgebra b hb.isSelfAdjoint).add_mem
      (rightIdeal_square_mem_hereditary b y₀ hb.isSelfAdjoint hy₀mem)
      (rightIdeal_square_mem_hereditary b y₁ hb.isSelfAdjoint hy₁mem)) hRR
  · intro H π _
    constructor
    · intro hπ
      have h := hcoverage₁ H π hπ
      obtain ⟨hx,hy⟩ := norm_sqrt_sum_representation π x₀ x₁
      have hm := max_le hx hy
      have hs : σ^2 ≤ 8*σ := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hs hr.le
      exact (by nlinarith : r*σ^2/1024 ≤ r*(σ/16)/8).trans (h.trans hm)
    · intro hπ
      have h := hcoverage₂ H π hπ
      obtain ⟨hx,hy⟩ := norm_sqrt_sum_representation π y₀ y₁
      have hm := max_le hx hy
      have heq : r*(σ^2/128)/8 = r*σ^2/1024 := by ring
      rw [heq] at h
      exact h.trans hm
  · have hn := norm_two_sqrt_sums_le x₀ x₁ y₀ y₁
    rw [h11,norm_zero] at hn
    have hls : l ≤ Real.sqrt l := by nlinarith [Real.sq_sqrt hl.le,Real.sqrt_nonneg l]
    change ‖CFC.sqrt (x₀*star x₀+x₁*star x₁)*CFC.sqrt (y₀*star y₀+y₁*star y₁)‖ ≤ _
    linarith

theorem quantitative_separatingPositives_any_oai
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hpert : UniformPerturbationOne_any A σ) :
    QuantitativeSeparatingPositives A σ := by
  intro a b ha hb han hbn r l hr _ hl hl1
  let B := Unitization ℂ A
  let X : A := a*b
  let Xu : B := X
  let T : B := star Xu*Xu
  let S : B := Xu*star Xu
  let V : B := cfc (separationV l) T
  let R₀ : B := cfc (separationR l) T
  let g₀ : A := cfcₙ (separationG l) (star X*X)
  let N₀ : A := cfcₙ (separationN l) (star X*X)
  let g : B := cfc (separationG l) T
  let N : B := cfc (separationN l) T
  let Lₛ : B := cfc (separationL l) S
  let Lₜ : B := cfc (separationL l) T
  let C₁ : A := unitizedRight a (Xu*V)
  let C₂ : A := unitizedRight b R₀
  have hg₀ : (g₀ : B)=g := inr_separationG X hl
  have hN₀ : (N₀ : B)=N := inr_separationN X hl
  have hC₁ : (C₁ : B)=(a : B)*Xu*V := by rw [inr_unitizedRight]; simp only [mul_assoc]
  have hC₂ : (C₂ : B)=(b : B)*R₀ := inr_unitizedRight b R₀
  have hXu : Xu=(a : B)*(b : B) := by simp only [Xu,X,Unitization.inr_mul]
  have hXn : ‖Xu‖ ≤ 1 := by
    rw [show Xu=(X : B) from rfl,Unitization.norm_inr]
    exact (norm_mul_le a b).trans (by nlinarith [norm_nonneg a,norm_nonneg b])
  obtain ⟨e,f,k₁,k₂,he,hf,hk₁,hk₂,hen,hfn,hef,hek₁,hfk₂,hge,hgf,hkdet⟩ :=
    exists_separation_cores hpi X hl
  have hgeu : g*(e : B)=(e : B) := by
    rw [← hg₀,← Unitization.inr_mul,hge]
  have hgfu : g*(f : B)=(f : B) := by
    rw [← hg₀,← Unitization.inr_mul,hgf]
  let τ : ℝ := r*Real.sqrt l/8
  have hτ : 0 < τ := by dsimp only [τ] <;> positivity
  let D₁ : A := C₁*g₀
  let D₂ : A := C₂*g₀
  let h₁ : A := cfcₙ (columnCoreFunction τ) (star D₁*D₁)
  let h₂ : A := cfcₙ (columnCoreFunction τ) (star D₂*D₂)
  let d₁ : A := cfcₙ (columnCoreFunction (2*τ)) (star (C₁*N₀)*(C₁*N₀))
  let d₂ : A := cfcₙ (columnCoreFunction (2*τ)) (star (C₂*N₀)*(C₂*N₀))
  let F₁ : B := cfc (columnMetricFunction τ) ((D₁ : B)*star (D₁ : B))
  let F₂ : B := cfc (columnMetricFunction τ) ((D₂ : B)*star (D₂ : B))
  obtain ⟨p₁,hp₁eq,hF₁,hp₁,hh₁,hph₁⟩ := nonunital_column_left_normalization D₁ hτ
  obtain ⟨p₂,hp₂eq,hF₂,hp₂,hh₂,hph₂⟩ := nonunital_column_left_normalization D₂ hτ
  have hFC₁ : F₁*(C₁ : B)*g=(p₁ : B) := by
    rw [mul_assoc,← hg₀,← Unitization.inr_mul]
    exact hp₁eq
  have hFC₂ : F₂*(C₂ : B)*g=(p₂ : B) := by
    rw [mul_assoc,← hg₀,← Unitization.inr_mul]
    exact hp₂eq
  have hd₁ : 0 ≤ d₁ := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hd₂ : 0 ≤ d₂ := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  obtain ⟨hdh₁,hdk₁⟩ := separation_core_comparisons hpi X C₁ k₁ hk₁ hl hτ
    (fun H π hπ => (hkdet H π hπ).1)
  obtain ⟨hdh₂,hdk₂⟩ := separation_core_comparisons hpi X C₂ k₂ hk₂ hl hτ
    (fun H π hπ => (hkdet H π hπ).2)
  obtain ⟨Z,W,z,w,hZfact,hWfact,hZW,hZn,hWn,htest₁,htest₂⟩ :=
    exists_compatible_metric_perturbations_any hσ hσ1 hτ hpert g F₁ F₂ (C₁ : B) (C₂ : B)
      (norm_separationG Xu l) (cfc_predicate _ _) p₁ p₂ e f h₁ h₂ k₁ k₂ d₁ d₂
      hp₁ hp₂ hen hfn hh₁ hh₂ hk₁ hk₂ hd₁ hd₂ hph₁ hph₂ hek₁ hfk₂
      hdh₁ hdh₂ hdk₁ hdk₂ hgeu hgfu hFC₁ hFC₂
  let s : ℂ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ)
  let x₀ : A := unitizedRight a Lₛ
  let y₀ : A := unitizedRight b Lₜ
  let x₁ : A := s • unitizedRight C₁ (Z*(e : B))
  let y₁ : A := s • unitizedRight C₂ (W*(f : B))
  have hx₀ : (x₀ : B)=(a : B)*Lₛ := inr_unitizedRight a Lₛ
  have hy₀ : (y₀ : B)=(b : B)*Lₜ := inr_unitizedRight b Lₜ
  have hx₁ : (x₁ : B)=s • ((C₁ : B)*Z*(e : B)) := by
    rw [Unitization.inr_smul,inr_unitizedRight]
    simp only [mul_assoc]
  have hy₁ : (y₁ : B)=s • ((C₂ : B)*W*(f : B)) := by
    rw [Unitization.inr_smul,inr_unitizedRight]
    simp only [mul_assoc]
  have hx₀mem : x₀ ∈ principalRightIdeal a := inr_factor_mem_principal ha Lₛ hx₀
  have hy₀mem : y₀ ∈ principalRightIdeal b := inr_factor_mem_principal hb Lₜ hy₀
  have hx₁mem : x₁ ∈ principalRightIdeal a := by
    apply inr_factor_mem_principal ha (s • (Xu*V*Z*(e : B)))
    rw [hx₁,hC₁,mul_smul_comm]
    simp only [mul_assoc]
  have hy₁mem : y₁ ∈ principalRightIdeal b := by
    apply inr_factor_mem_principal hb (s • (R₀*W*(f : B)))
    rw [hy₁,hC₂,mul_smul_comm]
    simp only [mul_assoc]
  have haU : 0 ≤ (a : B) := Unitization.inr_nonneg_iff.mpr ha
  have heU : 0 ≤ (e : B) := Unitization.inr_nonneg_iff.mpr he
  have hefU : (e : B)*(f : B)=0 := by rw [← Unitization.inr_mul,hef,Unitization.inr_zero]
  have hcols := separation_four_column_bounds (a : B) (b : B) (e : B) (f : B) Z W w haU heU hefU hl
    (by simpa only [Unitization.norm_inr] using hen) (by simpa only [Unitization.norm_inr] using hfn)
    hZn hWn (by simpa only [← hXu] using hgfu) (by simpa only [← hXu] using hWfact) hZW
  have h00 : ‖star x₀*y₀‖ ≤ 8*l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₀*y₀),Unitization.inr_mul,Unitization.inr_star,hx₀,hy₀]
    simpa only [← hXu] using hcols.1
  have h10 : ‖star x₁*y₀‖ ≤ 6*Real.sqrt l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₁*y₀),Unitization.inr_mul,Unitization.inr_star,hx₁,hy₀,hC₁]
    simpa only [← hXu] using hcols.2.1
  have h01 : ‖star x₀*y₁‖ ≤ 6*Real.sqrt l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₀*y₁),Unitization.inr_mul,Unitization.inr_star,hx₀,hy₁,hC₂]
    simpa only [← hXu] using hcols.2.2.1
  have h11 : star x₁*y₁=0 := by
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_mul,Unitization.inr_star,hx₁,hy₁,hC₁,hC₂,Unitization.inr_zero]
    simpa only [← hXu] using hcols.2.2.2
  let K₁ : B := star (Xu*cfc (separationK l) T)
  let K₂ : B := cfc (separationJ l) T
  have hK₁ : ‖K₁‖ ≤ (Real.sqrt l)⁻¹ := by
    rw [norm_star]
    exact norm_separation_coverage_factor Xu hXn hl
  have hK₂ : ‖K₂‖ ≤ (Real.sqrt l)⁻¹ := norm_separationJ Xu hXn hl (by linarith)
  have haeq : (a : B)=(x₀ : B)+((C₁ : B)*(N₀ : B))*K₁ := by
    rw [hx₀,hC₁,hN₀]
    rw [separation_first_coverage_identity (a : B) Xu hl]
    exact separation_LN_decomposition (a : B) S (IsSelfAdjoint.mul_star_self Xu) l
  have hbeq : (b : B)=(y₀ : B)+((C₂ : B)*(N₀ : B))*K₂ := by
    rw [hy₀,hC₂,hN₀]
    rw [separation_second_coverage_identity (b : B) Xu hl]
    exact separation_LN_decomposition (b : B) T (IsSelfAdjoint.star_mul_self Xu) l
  have hcoverage₁ := separation_transferred_coverage a x₀ x₁ C₁ N₀ K₁ F₁ ((C₁ : B)*Z*(e : B))
    hr hl (rfl : τ=r*Real.sqrt l/8) (by linarith : σ/16 ≤ 4) haeq hx₁ hK₁ hF₁
    (fun H π hπ => by
      have ht := htest₁ H π hπ
      simpa only [mul_assoc] using ht)
  have hcoverage₂ := separation_transferred_coverage b y₀ y₁ C₂ N₀ K₂ F₂ ((C₂ : B)*W*(f : B))
    hr hl (rfl : τ=r*Real.sqrt l/8) (by nlinarith : σ^2/128 ≤ 4) hbeq hy₁ hK₂ hF₂
    (fun H π hπ => by
      have ht := htest₂ H π hπ
      simpa only [mul_assoc] using ht)
  exact separatingPositives_of_four_columns_any a b x₀ x₁ y₀ y₁ ha hb hr hl hl1 hσ hσ1
    hx₀mem hx₁mem hy₀mem hy₁mem h00 h10 h01 h11 hcoverage₁ hcoverage₂

end

end

end WeakPureInfiniteness
end

end OAI
end

theorem solution.{u} : type_of% @OAI.WeakPureInfiniteness.quantitative_separatingPositives_any_oai.{u} := @OAI.WeakPureInfiniteness.quantitative_separatingPositives_any_oai.{u}
