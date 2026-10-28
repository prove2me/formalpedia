-- Prove2me | solution 1 for OAI.WitnessConstruction.shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:58:17.446382+00:00
-- url     : https://prove2.me/submissions/41d9573a-870c-4bb1-95ec-373352abc681

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Theorems.Thm_OAI_Blocks_block_estimates
import Theorems.Thm_OAI_CapCost_clipped_cost
import Theorems.Thm_OAI_CapCost_raw_upper
import Theorems.Thm_OAI_NormalizedCaps_clipped_affinity
import Theorems.Thm_OAI_RadiusLens_lens_at_radius

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma sphere_singleton_zero {n : ℕ} (hn : 2 ≤ n) (u : Sphere n) :
    (volume : Measure (Space n)).toSphere {u} = 0 := by
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have hspan : Submodule.span ℝ ({u.val} : Set (Space n)) ≠ ⊤ := by
    intro he
    have hu : u.val ≠ 0 := by
      intro hu
      have hh := u.property
      simp [hu] at hh
    have h := finrank_span_singleton (K := ℝ) hu
    rw [he, finrank_top, hdim] at h
    omega
  have hnull := Measure.addHaar_submodule (volume : Measure (Space n)) _ hspan
  rw [Measure.toSphere_apply' _ (measurableSet_singleton u)]
  have hc : Ioo (0 : ℝ) 1 • ((↑) '' ({u} : Set (Sphere n))) ⊆
      (Submodule.span ℝ ({u.val} : Set (Space n)) : Set (Space n)) := by
    rintro y ⟨r, _, x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hx
    have hv' : v = u := Set.mem_singleton_iff.mp hv
    subst v
    exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton _))
  rw [measure_mono_null hc hnull, mul_zero]

instance nonatomic {n : ℕ} [hn : Fact (2 ≤ n)] : NullSingletonClass (σ n) := by
  constructor
  intro u
  rw [σ, Measure.smul_apply, sphere_singleton_zero hn.out, smul_zero]

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma cap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (cap x t) :=
  (cap_open x t).measurableSet

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialShell
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialShell
open Filter
open scoped Topology

lemma inv_limit : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma eta_limit : Tendsto η atTop (𝓝 0) := by
  unfold η
  simpa only [zero_pow (by norm_num : (4:ℕ) ≠ 0)] using inv_limit.pow 4
lemma log_div_limit : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact ht.comp tendsto_natCast_atTop_atTop
lemma low_limit (a : ℝ) : Tendsto (low a) atTop (𝓝 a) := by
  unfold low
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub (log_div_limit.const_mul 10)).const_mul a).sub (eta_limit.const_mul 3)
lemma high_limit (a : ℝ) : Tendsto (high a) atTop (𝓝 a) := by
  unfold high
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).add inv_limit).const_mul a).add (eta_limit.const_mul 3)

lemma n_eta {n : ℕ} (hn : 1 ≤ n) : (n:ℝ)*η n ≤ 1 := by
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hinv : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnreal
  have hinv0 : (0:ℝ) ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hnp.le
  have hpow : ((n:ℝ)⁻¹)^4 ≤ (n:ℝ)⁻¹ := by nlinarith [sq_nonneg ((n:ℝ)⁻¹),sq_nonneg (1-(n:ℝ)⁻¹),mul_le_mul_of_nonneg_left hinv hinv0, mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 3) hinv0 hinv) hinv0]
  calc
    (n:ℝ)*η n ≤ (n:ℝ)*(n:ℝ)⁻¹ := mul_le_mul_of_nonneg_left hpow hnp.le
    _ = 1 := mul_inv_cancel₀ hnp.ne'

lemma thresholds {a l u : ℝ} (ha : 0 < a) (hl : l < 1/a) (hu : 1/a < u) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → 2 ≤ n ∧ 1 ≤ Real.log n ∧
      a/2 ≤ low a n ∧ (n:ℝ)*η n ≤ 1 ∧
      ∀ r : ℝ,low a n ≤ r → r ≤ high a n →
        l ≤ (1+3*η n)/r ∧ (1+3*η n)/r ≤ u := by
  have hupper : Tendsto (fun n => (1+3*η n)/low a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (low_limit a) ha.ne' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp
  have hlower : Tendsto (fun n => (1+3*η n)/high a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (high_limit a) ha.ne' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp
  have hev : ∀ᶠ n : ℕ in atTop,2 ≤ n ∧ 1 ≤ Real.log n ∧ a/2 ≤ low a n ∧
      (1+3*η n)/low a n ≤ u ∧ l ≤ (1+3*η n)/high a n := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      (low_limit a).eventually_const_le (by linarith : a/2 < a),
      hupper.eventually_le_const hu,hlower.eventually_const_le hl] with n hn hlog hlo hup hdown
    exact ⟨hn,hlog,hlo,hup,hdown⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀,?_⟩
  intro n hn
  obtain ⟨hn2,hlog,hlo,hup,hdown⟩ := hn₀ n hn
  refine ⟨hn2,hlog,hlo,n_eta (by omega),?_⟩
  intro r hr hrü
  have hlo0 : 0 < low a n := lt_of_lt_of_le (by linarith) hlo
  have hr0 : 0 < r := hlo0.trans_le hr
  have hnum : 0 ≤ 1+3*η n := by unfold η; positivity
  exact ⟨hdown.trans (div_le_div_of_nonneg_left hnum hr0 hrü),
    (div_le_div_of_nonneg_left hnum hlo0 hr).trans hup⟩

lemma weight_upper {n : ℕ} {a r : ℝ} (ha : 1 ≤ a)
    (hlog : 1 ≤ Real.log n) (_hr : 0 ≤ r) (hlo : low a n ≤ r)
    (hnη : (n:ℝ)*η n ≤ 1) :
    1+(n:ℝ)*max (1-r^2/a^2) 0 ≤ 27*Real.log n := by
  have hap : 0 < a := by linarith
  have hnpos : (0:ℝ) < n := by
    by_contra h
    have hz : n = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    simp [hz] at hlog
    norm_num at hlog
  have hx : a-r ≤ 10*a*(Real.log n/(n:ℝ))+3*η n := by
    dsimp [low] at hlo
    linarith only [hlo]
  have hq : max (1-r^2/a^2) 0 ≤ (20*Real.log n/(n:ℝ))+6*η n/a := by
    apply max_le _ (by unfold η; positivity)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hap)).mp
    have hh := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 2*a)
    have hh2 : a^2-r^2 ≤ 2*a*(10*a*(Real.log n/(n:ℝ))+3*η n) := by
      nlinarith only [hh,sq_nonneg (a-r)]
    convert hh2 using 1 <;> (try field_simp [hap.ne'])
    all_goals first | rfl | ring
  have hh := mul_le_mul_of_nonneg_left hq hnpos.le
  have he : (n:ℝ)*(20*Real.log n/(n:ℝ)+6*η n/a) = 20*Real.log n+6*((n:ℝ)*η n)/a := by field_simp
  rw [he] at hh
  have hdiv : ((n:ℝ)*η n)/a ≤ 1 := (div_le_one hap).mpr (hnη.trans ha)
  rw [mul_div_assoc 6] at hh
  linarith only [hh,hdiv,hlog]

end RadialShell

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ProjectiveCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
  le_min (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_nonneg _ _)

lemma angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 := by
  rw [angle, InnerProductGeometry.angle_self hx, min_eq_left]
  exact InnerProductGeometry.angle_nonneg _ _

lemma angle_comm (x y : V) : angle x y = angle y x := by
  simp only [angle, InnerProductGeometry.angle_neg_right]
  rw [InnerProductGeometry.angle_comm x y]

lemma angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  unfold angle
  by_cases hxy : InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle x (-y)
  · rw [min_eq_left hxy]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      exact (min_le_left _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y z)
    · rw [min_eq_right (le_of_not_ge hyz)]
      exact (min_le_right _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y (-z))
  · rw [min_eq_right (le_of_not_ge hxy)]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) (-z)
      rw [InnerProductGeometry.angle_neg_neg] at h
      exact (min_le_right _ _).trans h
    · rw [min_eq_right (le_of_not_ge hyz)]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) z
      have he : InnerProductGeometry.angle (-y) z = InnerProductGeometry.angle y (-z) := by
        simp only [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right]
      rw [he] at h
      exact (min_le_left _ _).trans h

lemma costDist_nonneg {I : Type u_3} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) :
    0 ≤ costDist n x s i j :=
  add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (angle_nonneg _ _)) (Real.sqrt_nonneg _)

lemma costDist_self {I : Type u_4} (n : ℕ) (x : I → V) (s : I → ℝ)
    (hx : ∀ i, x i ≠ 0) (i : I) : costDist n x s i i = 0 := by
  simp [costDist, angle_self (hx i)]

lemma costDist_comm {I : Type u_5} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) :
    costDist n x s i j = costDist n x s j i := by
  rw [costDist, costDist, angle_comm, abs_sub_comm]

lemma costDist_triangle {I : Type u_6} (n : ℕ) (x : I → V) (s : I → ℝ) (i j k : I) :
    costDist n x s i k ≤ costDist n x s i j + costDist n x s j k := by
  have ha := mul_le_mul_of_nonneg_left (angle_triangle (x i) (x j) (x k)) (Real.sqrt_nonneg (n:ℝ))
  have hb : Real.sqrt |s i-s k| ≤ Real.sqrt |s i-s j| + Real.sqrt |s j-s k| :=
    (Real.sqrt_le_sqrt (abs_sub_le (s i) (s j) (s k))).trans (by
      have h1 := Real.sq_sqrt (abs_nonneg (s i-s j))
      have h2 := Real.sq_sqrt (abs_nonneg (s j-s k))
      have h3 := Real.sq_sqrt (add_nonneg (abs_nonneg (s i-s j)) (abs_nonneg (s j-s k)))
      nlinarith [Real.sqrt_nonneg |s i-s j|, Real.sqrt_nonneg |s j-s k|,
        Real.sqrt_nonneg (|s i-s j|+|s j-s k|),
        mul_nonneg (Real.sqrt_nonneg |s i-s j|) (Real.sqrt_nonneg |s j-s k|)])
  dsimp [costDist]
  nlinarith

end ProjectiveCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

instance intensity_null {n : ℕ} [Fact (2 ≤ n)] (e : Sphere n) (t : ℝ) :
    NullSingletonClass (intensity e t) := ⟨by intro u; simp [intensity]⟩

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

end CapCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockGeometry
open Finset
variable {I : Type u_1}

lemma radius_nonneg (d : I → I → ℝ) (S : Finset I) : 0 ≤ radius d S := by
  classical
  unfold radius
  split_ifs with h
  · apply le_inf'
    intro j _
    obtain ⟨i,hi⟩ := h
    exact (sq_nonneg _).trans (le_sup' (fun i => d j i ^ 2) hi)
  · rfl

end BlockGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_GeometryDimension
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace GeometryDimension
open Filter
open scoped Topology

lemma log_div_nat : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h.comp tendsto_natCast_atTop_atTop

lemma lens_threshold {l u₀ u B : ℝ} (hl : 0 < l) (hu₀ : 0 ≤ u₀)
    (hu : u₀ < u) (_hB : 0 < B) :
    ∃ n₀ : ℕ, ∀ n : ℕ,n₀ ≤ n → 2 ≤ n ∧
      2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l ∧
      B*Real.log n/(n:ℝ) < 2 ∧
      (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+(12/l)*(Real.log n/(n:ℝ)) ≤ u^2 := by
  have hsq : u₀^2 < u^2 := by nlinarith
  have ht : Tendsto (fun n : ℕ => (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+
      (12/l)*(Real.log n/(n:ℝ))) atTop (𝓝 (u₀^2)) := by
    convert ((tendsto_const_nhds.add (log_div_nat.const_mul (B+6/l))).pow 2).add
      (log_div_nat.const_mul (12/l)) using 1; simp
  have hsmall : ∀ᶠ n : ℕ in atTop,B*Real.log n/(n:ℝ) < 2 := by
    have htB : Tendsto (fun n : ℕ => B*(Real.log n/(n:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using log_div_nat.const_mul B
    have h := htB.eventually_lt_const (by norm_num : (0:ℝ) < 2)
    simpa only [mul_zero,mul_div_assoc] using h
  have hd : ∀ᶠ n : ℕ in atTop,2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2*(1/l+1/(1-u^2))/l))
    filter_upwards [h] with n hn
    exact (div_le_iff₀ hl).mp hn
  have he : ∀ᶠ n : ℕ in atTop,2 ≤ n ∧ 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l ∧
      B*Real.log n/(n:ℝ) < 2 ∧
      (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+(12/l)*(Real.log n/(n:ℝ)) ≤ u^2 := by
    filter_upwards [eventually_ge_atTop 2,hd,hsmall,ht.eventually_le_const hsq] with n hn hd hs he
    exact ⟨hn,hd,hs,he⟩
  exact eventually_atTop.mp he

lemma logarithm_card {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n^2) :
    Real.log (2*(m:ℝ)) ≤ 3*Real.log n := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hm' : (m:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hmn
  have h3 := Real.log_le_log hmpos hm'
  rw [Real.log_pow] at h3
  rw [Real.log_mul (by norm_num) hmpos.ne']
  norm_num only [Nat.cast_ofNat] at h3
  linarith

lemma small_family {n m : ℕ} {l u₀ u B r : ℝ}
    (hn : 2 ≤ n) (hl : 0 < l) (hu₀ : 0 ≤ u₀) (_hB : 0 ≤ B)
    (hm : 1 ≤ m) (hmn : m ≤ n^2) (hr : 0 ≤ r) (hrB : r ≤ B*Real.log n)
    (hsmall : (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+
      (12/l)*(Real.log n/(n:ℝ)) ≤ u^2) :
    (u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l))^2+
      4*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤ u^2 := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmn' : Real.log (2*(m:ℝ)) ≤ 3*Real.log n := logarithm_card hn hm hmn
  have hlog : 0 ≤ Real.log (2*(m:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*m by omega))
  have hr' := div_le_div_of_nonneg_right hrB hnp.le
  have hlog' := div_le_div_of_nonneg_right hmn' (mul_pos hnp hl).le
  have h1 : 0 ≤ u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l) := by positivity
  have h2 : u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤
      u₀+(B+6/l)*(Real.log n/(n:ℝ)) := by
    have he : u₀+(B+6/l)*(Real.log n/(n:ℝ)) = u₀+B*Real.log n/(n:ℝ)+
        2*(3*Real.log n/((n:ℝ)*l)) := by ring
    rw [he]
    simp only [mul_div_assoc] at *
    linarith only [hr',hlog']
  have hs := (sq_le_sq₀ h1 (h1.trans h2)).mpr h2
  have h3 : 4*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤ (12/l)*(Real.log n/(n:ℝ)) := by
    have he : (12/l)*(Real.log n/(n:ℝ)) = 4*(3*Real.log n/((n:ℝ)*l)) := by ring
    rw [he]
    simp only [mul_div_assoc] at *
    linarith only [hlog']
  linarith only [hs,h3,hsmall]

end GeometryDimension

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalBlocks
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2 u_3

namespace SphericalBlocks
open Set MeasureTheory SphericalLaw CapCost BlockGeometry BlockSets ProjectiveCaps
open scoped BigOperators

lemma uniform_lens {l u₀ u B : ℝ} (hl : 0 < l) (hu₀ : 0 ≤ u₀)
    (hu : u₀ < u) (hu1 : u < 1) (hB : 0 < B) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (I : Type u_1) [Fintype I] [DecidableEq I],Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ) (t : ℝ),
    0 ≤ t → t < 1 → (∀ i,l ≤ τ i) → (∀ i,τ i ≤ u₀) →
    (∀ i j,(n:ℝ)*(angle (axes i).val (axes j).val)^2 ≤ d i j^2) →
    ∀ S : Finset I,S.Nonempty → radius d S ≤ B*Real.log n →
    ∀ a ∈ S,(∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
      (intensity e t).real (cap (axes i).val (τ i))) →
    Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
      (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
      (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
  obtain ⟨n₀,hn₀⟩ := GeometryDimension.lens_threshold hl hu₀ hu hB
  refine ⟨n₀,?_⟩
  intro n hn _ I _ _ hcard e axes τ d t ht ht1 hτl hτu hd S hS hr a ha hmin
  obtain ⟨hn2,hdim,hsmall,hsq⟩ := hn₀ n hn
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply RadiusLens.lens_at_radius e axes τ d hl hu1 hu₀ ht ht1 hτl hτu hd S hS a ha hmin hdim
  · exact (div_le_div_of_nonneg_right hr hnp.le).trans_lt hsmall
  · exact GeometryDimension.small_family hn2 hl hu₀ hB.le (Finset.one_le_card.mpr hS)
      ((Finset.card_le_univ S).trans hcard) (radius_nonneg d S) hr hsq
  · exact hu₀.trans hu.le

lemma cost_metric_lower {n : ℕ} {I : Type u_2} (axes : I → Sphere n) (s : I → ℝ) (i j : I) :
    (n:ℝ)*(angle (axes i).val (axes j).val)^2 ≤
      (costDist n (fun i => (axes i).val) s i j)^2 := by
  have h : Real.sqrt n*angle (axes i).val (axes j).val ≤
      costDist n (fun i => (axes i).val) s i j := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (angle_nonneg _ _)) h 2
  simpa only [mul_pow,hn] using hp

theorem blocks {l u₀ u H : ℝ} (hl : 0 < l) (hlu : l ≤ u₀)
    (hu : u₀ < u) (hu1 : u < 1) (hH : 1 ≤ H) :
    ∃ K C : ℝ,0 < K ∧ 0 < C ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (I : Type u_3) [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (t : ℝ),0 ≤ t → t < 1 →
    ∀ (axes : I → Sphere n) (τ : I → ℝ), (∀ i,l ≤ τ i) → (∀ i,τ i ≤ u₀) →
    (∀ i,(intensity e t).real (cap (axes i).val (τ i)) ≤ H) →
    let μ := intensity e t
    let caps := fun i => cap (axes i).val (τ i)
    ∃ (P : Finpartition (Finset.univ : Finset I)) (a : Finset I → I) (E : Finset I → Set (Sphere n)),
      (∀ S ∈ P.parts,a S ∈ S ∧ (∀ i ∈ S,μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
        MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        Real.exp (-K*Real.log n)*clipped μ caps (a S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      (∑ S ∈ P.parts,-Real.log (μ.real (E S))) ≤ ∑ i,cost μ caps i+(Fintype.card I:ℝ)/10 ∧
      (∑ S ∈ P.parts,Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
      (∑ S ∈ P.parts,Real.log (1+∑ T ∈ P.parts.erase S,Blocks.weight μ (E S) (E T))) ≤
        C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) := by
  let L := 3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l
  let k := min (l/16) ((u-u₀)/4)
  let c := min ((2*l*k/Real.pi^2)/4) (1/8)
  have hu0 : 0 ≤ u₀ := (hl.trans_le hlu).le
  have hup : 0 ≤ u := hu0.trans hu.le
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hh : 0 < 1-u^2 := by nlinarith only [hup,hu1]
    positivity
  have hL : 1 ≤ L := by
    dsimp [L]
    have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) hl.le
    linarith
  have hk : 0 < k := by
    dsimp [k]
    exact lt_min (div_pos hl (by norm_num)) (div_pos (sub_pos.mpr hu) (by norm_num))
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  obtain ⟨B,K,C,hB,hK,hC,hblocks⟩ := Blocks.block_estimates hL (by linarith : 1 ≤ 4*H) hc
  obtain ⟨nL,hnL⟩ := uniform_lens hl hu0 hu hu1 hB
  obtain ⟨nD,hnD⟩ := GeometryDimension.lens_threshold hl hu0 hu hB
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨nE,hnE⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K,C,hK,hC,max nL (max nD nE),?_⟩
  intro n hn _ _ I _ _ _ hcard e t ht ht1 axes τ hτl hτu hraw
  dsimp only
  let μ := intensity e t
  let caps := fun i => cap (axes i).val (τ i)
  let s := cost μ caps
  let d := costDist n (fun i => (axes i).val) s
  have hlog : 1 ≤ Real.log n := hnE n ((le_max_right nD nE).trans ((le_max_right nL _).trans hn))
  have hdim := (hnD n ((le_max_left nD nE).trans ((le_max_right nL _).trans hn))).2.1
  have hnp : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcard' : (Fintype.card I:ℝ) ≤ Real.exp (2*Real.log n) := by
    rw [show 2*Real.log n = Real.log ((n:ℝ)^2) by rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (sq_pos_of_pos hnp)]
    exact_mod_cast hcard
  have hpos (i : I) : 0 < μ.real (caps i) := by
    rw [show μ.real (caps i) = (σ n).real (caps i)/(σ n).real (cap e.val t) from intensity_real e t _]
    exact div_pos (cap_real_pos (axes i) ((hτu i).trans_lt (hu.trans hu1))) (cap_real_pos e ht1)
  apply hblocks (Sphere n) I μ (Real.log n) hlog hcard' caps (fun i => cap_measurable _ _) hpos d
    (costDist_nonneg _ _ _) ?_ (costDist_comm _ _ _) (costDist_triangle _ _ _) ?_ ?_
  · intro i
    apply costDist_self
    intro j
    have hh := mem_sphere_zero_iff_norm.mp (axes j).property
    intro he
    simp only [he,norm_zero] at hh
    norm_num at hh
  · intro i j
    exact NormalizedCaps.clipped_affinity e axes τ hl hu1 ht ht1 hτl hτu hu.le
      hk.le (min_le_left _ _) (by have := min_le_right (l/16) ((u-u₀)/4); dsimp [k] at *; linarith)
      hdim hH hraw hc.le (min_le_left _ _) (min_le_right _ _) i j
  · intro S hS hr a ha hmin
    exact hnL n ((le_max_left _ _).trans hn) I hcard e axes τ d t ht ht1 hτl hτu
      (cost_metric_lower axes s) S hS hr a ha hmin

end SphericalBlocks

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingBounds
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingBounds
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

lemma all_matchings_eq (w : I × J → ℝ) :
    (∑ M : Matching I J, ∏ e ∈ M.val, w e) =
    1 + ∑ M : Matching I J, if M.val.Nonempty then ∏ e ∈ M.val, w e else 0 := by
  have ht (M : Matching I J) : (∏ e ∈ M.val, w e) =
      (if M.val.Nonempty then ∏ e ∈ M.val, w e else 0) +
      (if M = emptyMatching then 1 else 0) := by
    by_cases he : M.val = ∅
    · have hM : M = emptyMatching := Subtype.ext he
      simp [hM, emptyMatching]
    · have hne := Finset.nonempty_iff_ne_empty.mpr he
      have hM : M ≠ emptyMatching := fun h => he (congrArg Subtype.val h)
      simp only [ite_eq_left hne, ite_eq_right hM, add_zero]
  conv_lhs => arg 2; ext M; rw [ht M]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end MatchingBounds

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingSelf
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingSelf
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} [Fintype I]

lemma join_product (h : I × I → ℝ) (P : OffMatching I) (L : Loops P) :
    (∏ e ∈ (join P L).val, h e) =
      (∏ e ∈ P.val.val, h e) * ∏ i ∈ L.val, h (i,i) := by
  have hd : Disjoint P.val.val L.val.diag := by
    apply Finset.disjoint_left.mpr
    intro e he hl
    exact P.property e he (Finset.mem_diag.mp hl).2
  dsimp only [join]
  rw [Finset.prod_union hd, Finset.prod_diag]

lemma loop_sum (h : I × I → ℝ) :
    (∑ M : Matching I I, ∏ e ∈ M.val, h e) =
      ∑ P : OffMatching I, (∏ e ∈ P.val.val, h e) *
        ∏ i ∈ available P, (1+h (i,i)) := by
  rw [← Equiv.sum_comp splitEquiv.symm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simp only [splitEquiv, Equiv.coe_fn_symm_mk, join_product]
  rw [← Finset.mul_sum, Finset.prod_one_add]
  congr 1
  apply Finset.sum_bij (fun L _ => L.val)
  · intro L _; exact Finset.mem_powerset.mpr L.property
  · intro L _ N _ h; exact Subtype.ext h
  · intro L hL; exact ⟨⟨L, Finset.mem_powerset.mp hL⟩, Finset.mem_univ _, rfl⟩
  · intro L _; rfl

lemma endpoint_product_le (P : OffMatching I) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i)
    (f : I × I → I) (hf : Set.InjOn f ↑P.val.val)
    (hav : Disjoint (available P) (P.val.val.image f)) :
    (∏ i ∈ available P, s i) * (∏ e ∈ P.val.val, s (f e)) ≤ ∏ i, s i := by
  rw [← Finset.prod_image hf, ← Finset.prod_union hav]
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
  · intro i _; exact le_trans (by norm_num) (hs i)
  · intro i _ _; exact hs i

lemma endpoint_compensation (P : OffMatching I) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i) :
    (∏ i ∈ available P, s i ^ 2) *
      (∏ e ∈ P.val.val, s e.1 * s e.2) ≤ ∏ i, s i ^ 2 := by
  have hf : Set.InjOn (Prod.fst : I × I → I) (P.val.val : Set (I × I)) := by
    intro ⟨i,j⟩ hij ⟨k,l⟩ hkl he
    dsimp only at he
    subst k
    congr 1
    exact P.val.property.1 _ _ _ hij hkl
  have hg : Set.InjOn (Prod.snd : I × I → I) (P.val.val : Set (I × I)) := by
    intro ⟨i,j⟩ hij ⟨k,l⟩ hkl he
    dsimp only at he
    subst l
    congr 1
    exact P.val.property.2 _ _ _ hij hkl
  have ha : Disjoint (available P) (P.val.val.image Prod.fst) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨e, hmem, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hi).2.1 e.2 hmem
  have hb : Disjoint (available P) (P.val.val.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨e, hmem, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hi).2.2 e.1 hmem
  have hn : ∀ i, 0 ≤ s i := fun i => le_trans zero_le_one (hs i)
  have h := mul_le_mul (endpoint_product_le P s hs Prod.fst hf ha)
    (endpoint_product_le P s hs Prod.snd hg hb)
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hn i))
      (Finset.prod_nonneg (fun e _ => hn e.2)))
    (Finset.prod_nonneg (fun i _ => hn i))
  simp only [Finset.prod_pow, Finset.prod_mul_distrib]
  nlinarith [h]

lemma normalized_term_bound (P : OffMatching I) (h : I × I → ℝ)
    (hh : ∀ e, 0 ≤ h e) (s : I → ℝ) (hs : ∀ i, 1 ≤ s i) :
    (∏ e ∈ P.val.val, h e) * (∏ i ∈ available P, s i ^ 2) ≤
      (∏ i, s i ^ 2) * (∏ e ∈ P.val.val, h e / (s e.1 * s e.2)) := by
  have hs0 : ∀ i, 0 < s i := fun i => lt_of_lt_of_le zero_lt_one (hs i)
  have hd : 0 < ∏ e ∈ P.val.val, s e.1 * s e.2 :=
    Finset.prod_pos (fun e _ => mul_pos (hs0 _) (hs0 _))
  rw [Finset.prod_div_distrib, ← mul_div_assoc, le_div_iff₀ hd]
  have hc := mul_le_mul_of_nonneg_left (endpoint_compensation P s hs)
    (Finset.prod_nonneg (s := P.val.val) (fun e _ => hh e))
  nlinarith [hc]

lemma leftChoice_eq_some (P : OffMatching I) (i j : I) :
    leftChoice P i = some j ↔ (i,j) ∈ P.val.val := by
  unfold leftChoice
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hj; exact P.val.property.1 _ _ _ h.choose_spec hj
  · simp only [false_iff]
    exact fun hj => h ⟨j,hj⟩

lemma leftChoice_injective : Function.Injective (leftChoice (I := I)) := by
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  ext ⟨i,j⟩
  rw [← leftChoice_eq_some, ← leftChoice_eq_some, he]

lemma row_product (w : I × I → ℝ) (P : OffMatching I) :
    (∏ i, rowWeight w i (leftChoice P i)) = ∏ e ∈ P.val.val, w e := by
  rw [← Finset.prod_fiberwise (g := Prod.fst)]
  apply Finset.prod_congr rfl
  intro i _
  unfold leftChoice
  split_ifs with h
  · have hf : P.val.val.filter (fun e => e.1 = i) = {(i,h.choose)} := by
      ext ⟨j,k⟩
      simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨he,rfl⟩
        exact ⟨rfl, P.val.property.1 _ _ _ he h.choose_spec⟩
      · rintro ⟨rfl,rfl⟩; exact ⟨h.choose_spec,rfl⟩
    rw [hf, Finset.prod_singleton]
    exact ite_eq_left (P.property _ h.choose_spec)
  · have hf : P.val.val.filter (fun e => e.1 = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ⟨j,k⟩ he
      have hm := Finset.mem_filter.mp he
      have hj : j = i := hm.2
      subst j
      exact h ⟨k,hm.1⟩
    rw [hf, Finset.prod_empty]
    rfl

lemma off_sum_le_rows (w : I × I → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ P : OffMatching I, ∏ e ∈ P.val.val, w e) ≤
      ∏ i, (1 + ∑ j ∈ Finset.univ.erase i, w (i,j)) := by
  have hrow (i : I) : (∑ o : Option I, rowWeight w i o) =
      1 + ∑ j ∈ Finset.univ.erase i, w (i,j) := by
    rw [Fintype.sum_option]
    dsimp only [rowWeight]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true, ne_comm]
    · intro j _; rfl
  simp_rw [← hrow]
  rw [Fintype.prod_sum]
  let t := Finset.univ.image (leftChoice (I := I))
  have he : (∑ P : OffMatching I, ∏ e ∈ P.val.val, w e) =
      ∑ f ∈ t, ∏ i, rowWeight w i (f i) := by
    dsimp only [t]
    rw [Finset.sum_image (fun _ _ _ _ he => leftChoice_injective he)]
    apply Finset.sum_congr rfl
    intro P _; exact (row_product w P).symm
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro f _ _
  apply Finset.prod_nonneg
  intro i _
  cases f i <;> simp only [rowWeight]
  · norm_num
  · split_ifs <;> first | exact hw _ | exact le_rfl

lemma self_matching_bound (h : I × I → ℝ) (hh : ∀ e, 0 ≤ h e) :
    (∑ M : Matching I I, ∏ e ∈ M.val, h e) ≤
      (∏ i, (1+h (i,i))) *
        ∏ i, (1 + ∑ j ∈ Finset.univ.erase i,
          h (i,j) / (Real.sqrt (1+h (i,i)) * Real.sqrt (1+h (j,j)))) := by
  let s := fun i => Real.sqrt (1+h (i,i))
  have hs : ∀ i, 1 ≤ s i := by
    intro i
    dsimp only [s]
    exact Real.one_le_sqrt.mpr (by linarith [hh (i,i)])
  have he : ∀ i, s i ^ 2 = 1+h (i,i) := by
    intro i
    exact Real.sq_sqrt (by linarith [hh (i,i)])
  rw [loop_sum]
  calc
    _ ≤ ∑ P : OffMatching I, (∏ i, s i ^ 2) *
        (∏ e ∈ P.val.val, h e / (s e.1 * s e.2)) := by
      apply Finset.sum_le_sum
      intro P _
      simpa only [he] using normalized_term_bound P h hh s hs
    _ = (∏ i, s i ^ 2) *
        ∑ P : OffMatching I, ∏ e ∈ P.val.val, h e / (s e.1*s e.2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (∏ i, s i ^ 2) * ∏ i,
        (1 + ∑ j ∈ Finset.univ.erase i, h (i,j) / (s i * s j)) := by
      apply mul_le_mul_of_nonneg_left
      · exact off_sum_le_rows _ (fun e => div_nonneg (hh e)
          (mul_nonneg (le_trans zero_le_one (hs e.1)) (le_trans zero_le_one (hs e.2))))
      · exact Finset.prod_nonneg (fun i _ => sq_nonneg (s i))
    _ = _ := by simp only [he, s]

end MatchingSelf

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DiagramSelfBounds
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace PoissonDiagrams
open MeasureTheory CellMatching MatchingBounds MatchingSelf
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω] [Fintype I]

lemma self_bound (μ : Measure Ω) (E : I → Set Ω)
    (hpos : ∀ i, 0 < μ.real (E i)) :
    1 + diagram μ E E / (∏ i, μ.real (E i))^2 ≤
      (∏ i, (1 + (μ.real (E i))⁻¹)) *
        ∏ i, (1 + ∑ j ∈ Finset.univ.erase i,
          μ.real (E i ∩ E j) /
            Real.sqrt (μ.real (E i) * (1+μ.real (E i)) *
              μ.real (E j) * (1+μ.real (E j)))) := by
  let lam := fun i => μ.real (E i)
  let h := fun e : I × I => μ.real (E e.1 ∩ E e.2) / (lam e.1*lam e.2)
  have hdiag (i : I) : h (i,i) = (lam i)⁻¹ := by
    dsimp only [h, lam]
    rw [Set.inter_self]
    field_simp [(hpos i).ne']
  have hnorm (i j : I) : h (i,j) /
      (Real.sqrt (1+h (i,i)) * Real.sqrt (1+h (j,j))) =
      μ.real (E i ∩ E j) /
        Real.sqrt (lam i * (1+lam i) * lam j * (1+lam j)) := by
    rw [hdiag, hdiag]
    have hi := hpos i
    have hj := hpos j
    change 0 < lam i at hi
    change 0 < lam j at hj
    have hi' : 0 ≤ 1+(lam i)⁻¹ := by positivity
    have hj' : 0 ≤ 1+(lam j)⁻¹ := by positivity
    have hroot : Real.sqrt (lam i*(1+lam i)*lam j*(1+lam j)) =
        lam i*lam j*(Real.sqrt (1+(lam i)⁻¹)*Real.sqrt (1+(lam j)⁻¹)) := by
      have he : lam i*(1+lam i)*lam j*(1+lam j) =
          (lam i*lam j)^2 * ((1+(lam i)⁻¹)*(1+(lam j)⁻¹)) := by
        field_simp
        ring
      rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hi.le hj.le),
        Real.sqrt_mul hi']
    rw [hroot]
    dsimp only [h]
    rw [div_div]
  have hh : ∀ e, 0 ≤ h e := fun e => div_nonneg (measureReal_nonneg)
    (mul_nonneg (hpos e.1).le (hpos e.2).le)
  have hb := self_matching_bound h hh
  rw [all_matchings_eq] at hb
  simp_rw [hnorm, hdiag] at hb
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  unfold diagram
  have hp : (∏ i, μ.real (E i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hpos i))
  dsimp only [h, lam]
  field_simp

end PoissonDiagrams

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DiagramActivity
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace DiagramActivity
open MeasureTheory CellMatching PoissonDiagrams
open scoped BigOperators Classical
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]

lemma prod_exp_log (a : I → ℝ) (ha : ∀ i,0 < a i) :
    ∏ i,a i = Real.exp (∑ i,Real.log (a i)) := by
  rw [Real.exp_sum]
  simp_rw [Real.exp_log (ha _)]

lemma activity_lower (μ : Measure Ω) (E : I → Set Ω) (hpos : ∀ i,0 < μ.real (E i))
    {B : ℝ} (hbudget : ∑ i,Real.log (1+(μ.real (E i))⁻¹) ≤ B) :
    Real.exp (-B) ≤ ∏ i,μ.real (E i) := by
  rw [prod_exp_log _ hpos]
  apply Real.exp_le_exp.mpr
  have hh : ∑ i,-Real.log (μ.real (E i)) ≤ ∑ i,Real.log (1+(μ.real (E i))⁻¹) := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.mpr (hpos i))
    linarith
  rw [Finset.sum_neg_distrib] at hh
  linarith

lemma activity_upper (μ : Measure Ω) (E : I → Set Ω) (hle : ∀ i,μ.real (E i) ≤ 1) :
    ∏ i,μ.real (E i) ≤ 1 := Finset.prod_le_one (fun _ _ => measureReal_nonneg) (fun i _ => hle i)

lemma self_activity_normalized (μ : Measure Ω) (E : I → Set Ω) (hpos : ∀ i,0 < μ.real (E i))
    {B T : ℝ} (hfirst : ∑ i,Real.log (1+(μ.real (E i))⁻¹) ≤ B)
    (hrow : ∑ i,Real.log (1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j)))) ≤ T) :
    diagram μ E E ≤ (∏ i,μ.real (E i))^2*Real.exp (B+T) := by
  have hprod : 0 < (∏ i,μ.real (E i))^2 := sq_pos_of_pos (Finset.prod_pos fun i _ => hpos i)
  have hfirstprod : (∏ i,(1+(μ.real (E i))⁻¹)) ≤ Real.exp B := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hfirst
  have hrowprod : (∏ i,(1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j))))) ≤ Real.exp T := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hrow
  have hh := self_bound μ E hpos
  have hmul := mul_le_mul hfirstprod hrowprod (by positivity) (Real.exp_pos B).le
  rw [← Real.exp_add] at hmul
  have hh2 : diagram μ E E/(∏ i,μ.real (E i))^2 ≤ Real.exp (B+T) := by linarith only [hh.trans hmul]
  exact (div_le_iff₀ hprod).mp hh2 |>.trans_eq (mul_comm _ _)

end DiagramActivity

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_WitnessBlocks
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4

namespace WitnessBlocks
open MeasureTheory PoissonDiagrams
open scoped BigOperators Classical

lemma certificates {Ω : Type u_1} {J : Type u_2} [MeasurableSpace Ω] [DecidableEq J]
    (S : Finset J) (μ : Measure Ω) (E : J → Set Ω) {B T : ℝ}
    (hpos : ∀ i ∈ S,0 < μ.real (E i)) (hle : ∀ i ∈ S,μ.real (E i) ≤ 1)
    (hfirst : ∑ i ∈ S,Real.log (1+(μ.real (E i))⁻¹) ≤ B)
    (hrow : ∑ i ∈ S,Real.log (1+∑ j ∈ S.erase i,Blocks.weight μ (E i) (E j)) ≤ T) :
    Real.exp (-B) ≤ (∏ i : S,μ.real (E i)) ∧ (∏ i : S,μ.real (E i)) ≤ 1 ∧
      diagram μ (fun i : S => E i) (fun i : S => E i) ≤
        (∏ i : S,μ.real (E i))^2*Real.exp (B+T) := by
  have hfirst' : ∑ i : S,Real.log (1+(μ.real (E i))⁻¹) ≤ B := by
    simpa using (Finset.sum_coe_sort S (fun i => Real.log (1+(μ.real (E i))⁻¹))).trans_le hfirst
  have he (i : S) :
      ∑ j ∈ (Finset.univ : Finset S).erase i,Blocks.weight μ (E i) (E j) =
      ∑ j ∈ S.erase i.val,Blocks.weight μ (E i) (E j) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),Finset.sum_erase_eq_sub i.property]
    congr 1
    simpa using Finset.sum_coe_sort S (fun j => Blocks.weight μ (E i) (E j))
  have hrow' : ∑ i : S,Real.log (1+∑ j ∈ (Finset.univ : Finset S).erase i,
      Blocks.weight μ (E i) (E j)) ≤ T := by
    simp_rw [he]
    simpa using (Finset.sum_coe_sort S (fun i => Real.log (1+∑ j ∈ S.erase i,Blocks.weight μ (E i) (E j)))).trans_le hrow
  refine ⟨DiagramActivity.activity_lower μ (fun i : S => E i) (fun i => hpos i i.property) hfirst',
    DiagramActivity.activity_upper μ (fun i : S => E i) (fun i => hle i i.property),?_⟩
  exact DiagramActivity.self_activity_normalized μ (fun i : S => E i) (fun i => hpos i i.property) hfirst' (by simpa only [Finset.sum_erase_eq_sub (Finset.mem_univ _),Blocks.weight] using hrow')

end WitnessBlocks

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace RadialCost

lemma weight_ge_one (n : ℕ) (a r : ℝ) : 1 ≤ weight n a r := by
  unfold weight
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _))

lemma radial_deficit {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    a-r ≤ a*max (1-r^2/a^2) 0 := by
  by_cases h : r ≤ a
  · have haa : 0 < a^2 := sq_pos_of_pos ha
    have hr2 : r^2 ≤ a^2 := (sq_le_sq₀ hr ha.le).mpr h
    rw [max_eq_left (by exact sub_nonneg.mpr ((div_le_one haa).mpr hr2))]
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith only [sq_nonneg (a-r),mul_nonneg hr (sub_nonneg.mpr h)]
  · have hq := mul_nonneg ha.le (le_max_right (1-r^2/a^2) 0)
    linarith only [hq,le_of_not_ge h]

lemma upper_threshold {n : ℕ} {a r η : ℝ} (ha : 1 ≤ a) (hr : a/2 ≤ r)
    (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1) :
    (n:ℝ)*max ((1+3*η)/r-1/a) 0 ≤ (8/a)*weight n a r := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  let q := max (1-r^2/a^2) 0
  have hq : 0 ≤ q := le_max_right _ _
  have hd : a-r ≤ a*q := radial_deficit hap hrp.le
  have ht : (1+3*η)/r-1/a ≤ (2*q+6*η)/a := by
    apply (le_div_iff₀ hap).mpr
    rw [show ((1+3*η)/r-1/a)*a = ((1+3*η)*a-r)/r by field_simp]
    apply (div_le_iff₀ hrp).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hq) (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hη))
    nlinarith only [hd,hh]
  have ht0 : 0 ≤ (2*q+6*η)/a := by positivity
  have hh := mul_le_mul_of_nonneg_left (max_le ht ht0) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hw : 0 ≤ (n:ℝ)*q := mul_nonneg (Nat.cast_nonneg n) hq
  calc
    _ ≤ (n:ℝ)*((2*q+6*η)/a) := hh
    _ = (2*((n:ℝ)*q)+6*((n:ℝ)*η))/a := by ring
    _ ≤ (2*((n:ℝ)*q)+6)/a := div_le_div_of_nonneg_right (by linarith only [hnη]) hap.le
    _ ≤ (8/a)*weight n a r := by
      change (2*((n:ℝ)*q)+6)/a ≤ (8/a)*(1+(n:ℝ)*q)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith only [hw]) hap.le

lemma lower_threshold {n : ℕ} {a r η : ℝ} (hn : 0 < n) (ha : 1 ≤ a)
    (hr : a/2 ≤ r) (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1)
    (hru : r ≤ a*(1+1/(n:ℝ))+3*η) :
    (n:ℝ)*max (1/a-(1+3*η)/r) 0 ≤ 8 := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hu : (n:ℝ)*(r-a) ≤ a+3 := by
    have h := mul_le_mul_of_nonneg_left hru hnp.le
    field_simp at h
    nlinarith only [h,hnη]
  have ht : (n:ℝ)*(1/a-(1+3*η)/r) ≤ 8 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hap hrp)).mp
    field_simp
    have hp := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (mul_nonneg hap.le hη)
    have har := mul_le_mul_of_nonneg_left hr hap.le
    nlinarith only [hu,hp,har,ha,sq_nonneg (a-1)]
  rw [mul_max_of_nonneg _ _ hnp.le,mul_zero]
  exact max_le ht (by norm_num)

end RadialCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ShellCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace ShellCaps
open Set MeasureTheory SphericalLaw CapCost
open scoped BigOperators

lemma A_pos {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < A l u := by
  have hu0 : 0 < u := hl.trans_le hlu
  have hsq : 0 < 1-u^2 := by nlinarith only [hu0,hu]
  unfold A
  positivity

lemma C_pos {a l u : ℝ} (ha : 0 < a) (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < C a l u := by
  have hA := A_pos hl hlu hu
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold C
  positivity

lemma shell_cost {a l u : ℝ} (ha : 1 ≤ a) (hl : 0 < l) (hlt : l < 1/a)
    (hu : 1/a < u) (hu1 : u < 1) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (e f : Sphere n) (r : ℝ),RadialShell.low a n ≤ r → r ≤ RadialShell.high a n →
    let μ := intensity e (1/a)
    let E := cap f.val ((1+3*RadialShell.η n)/r)
    l ≤ (1+3*RadialShell.η n)/r ∧ (1+3*RadialShell.η n)/r ≤ u ∧
    μ.real E ≤ Real.exp (8*A l u) ∧
    -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r ∧
    -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n ∧
    Real.exp (-(27*C a l u)*Real.log n) ≤ min (μ.real E) (1/2) := by
  have hap : 0 < a := by linarith only [ha]
  have hA : 0 < A l u := A_pos hl (hlt.le.trans hu.le) hu1
  have hC : 0 < C a l u := C_pos hap hl (hlt.le.trans hu.le) hu1
  obtain ⟨n₀,hn₀⟩ := RadialShell.thresholds hap hlt hu
  refine ⟨n₀,?_⟩
  intro n hn _ e f r hlo hhi
  obtain ⟨hn2,hlog,hlow,hnη,hτ⟩ := hn₀ n hn
  obtain ⟨hτl,hτu⟩ := hτ r hlo hhi
  have hr : a/2 ≤ r := hlow.trans hlo
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith only [hap]) hr
  have hη : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
  have htlo := RadialCost.lower_threshold (by omega : 0 < n) ha hr hη hnη (by simpa [RadialShell.high,one_div] using hhi)
  have hthi := RadialCost.upper_threshold ha hr hη hnη
  let μ := intensity e (1/a)
  let E := cap f.val ((1+3*RadialShell.η n)/r)
  have hraw : μ.real E ≤ Real.exp (8*A l u) := by
    apply (raw_upper e f hl hu1 hlt.le hu.le hτl hτu).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left htlo hA.le
    dsimp [A] at hh ⊢
    nlinarith only [hh]
  have hcost : -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r := by
    have hc := clipped_cost e f hl hu1 hlt.le hu.le hτl hτu
    have hh := mul_le_mul_of_nonneg_left hthi hA.le
    have hw := mul_le_mul_of_nonneg_left (RadialCost.weight_ge_one n a r)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    dsimp [C,A] at hh ⊢
    dsimp [μ,E]
    linear_combination hc+hh+hw
  have hcost' : -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n := by
    have hw := mul_le_mul_of_nonneg_left (RadialShell.weight_upper ha hlog hr0.le hlo hnη) hC.le
    apply hcost.trans
    dsimp [RadialCost.weight]
    nlinarith only [hw]
  have hpos : 0 < min (μ.real E) (1/2) := by
    apply lt_min _ (by norm_num)
    rw [show μ.real E = (σ n).real E/(σ n).real (cap e.val (1/a)) from intensity_real e _ _]
    exact div_pos (cap_real_pos f (hτu.trans_lt hu1)) (cap_real_pos e (hu.trans hu1))
  refine ⟨hτl,hτu,hraw,hcost,hcost',?_⟩
  calc
    _ ≤ Real.exp (Real.log (min (μ.real E) (1/2))) := Real.exp_le_exp.mpr (by linarith only [hcost'])
    _ = _ := Real.exp_log hpos

end ShellCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_WitnessConstruction
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1

namespace WitnessConstruction
open Set MeasureTheory SphericalLaw CapCost BlockSets PoissonDiagrams
open scoped BigOperators

theorem shell_oai {a l u₀ u W : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hW : 0 < W) :
    ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (I : Type u_1) [Fintype I] [DecidableEq I] [Nonempty I],Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (axes : I → Sphere n) (r : I → ℝ) (R : ℝ),
    (∀ i,RadialShell.low a n ≤ r i) → (∀ i,r i ≤ RadialShell.high a n) →
    (Fintype.card I:ℝ)+(∑ i,RadialCost.weight n a (r i)) ≤ W*R →
    let μ := intensity e (1/a)
    let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
    ∃ (P : Finpartition (Finset.univ : Finset I)) (anchor : Finset I → I)
      (E : Finset I → Set (Sphere n)),
      (∀ S ∈ P.parts,anchor S ∈ S ∧ MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        E S ⊆ caps (anchor S) ∧
        Real.exp (-K*Real.log n)*clipped μ caps (anchor S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      Real.exp (-A*R) ≤ (∏ S : P.parts,μ.real (E S)) ∧
      (∏ S : P.parts,μ.real (E S)) ≤ 1 ∧
      diagram μ (fun S : P.parts => E S) (fun S : P.parts => E S) ≤
        (∏ S : P.parts,μ.real (E S))^2*Real.exp (2*A*R) := by
  have hap : 0 < a := lt_trans (by norm_num) ha
  have hu₀1 : u₀ < 1 := hu.trans hu1
  have hlu : l ≤ u₀ := hlt.le.trans hu₀.le
  let Cₐ := ShellCaps.C a l u₀
  let H := Real.exp (8*ShellCaps.A l u₀)
  have hCₐ : 0 < Cₐ := ShellCaps.C_pos hap hl hlu hu₀1
  have hH : 1 ≤ H := Real.one_le_exp (by
    have hh := (ShellCaps.A_pos hl hlu hu₀1).le
    dsimp [ShellCaps.A] at hh ⊢
    positivity)
  obtain ⟨K,C,hK,hC,nB,hnB⟩ := SphericalBlocks.blocks hl hlu hu hu1 hH
  obtain ⟨nS,hnS⟩ := ShellCaps.shell_cost ha.le hl hlt hu₀ hu₀1
  refine ⟨K,C*(1+Cₐ)*W,hK,by positivity,max nB nS,?_⟩
  intro n hn _ _ I _ _ _ hcard e axes r R hrlo hrhi hbudget
  dsimp only
  let μ := intensity e (1/a)
  let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
  have hs (i : I) := hnS n ((le_max_right nB nS).trans hn) e (axes i) (r i) (hrlo i) (hrhi i)
  have ht0 : 0 ≤ 1/a := by positivity
  have ht1 : 1/a < 1 := (div_lt_one hap).mpr ha
  obtain ⟨P,b,E,hE,_,hfirst,hrow⟩ := hnB n ((le_max_left nB nS).trans hn)
    I hcard e (1/a) ht0 ht1 axes (fun i => (1+3*RadialShell.η n)/r i)
    (fun i => (hs i).1) (fun i => (hs i).2.1) (fun i => (hs i).2.2.1)
  have hcost : ∑ i,cost μ caps i ≤ Cₐ*(∑ i,RadialCost.weight n a (r i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hs i).2.2.2.1
  have hw : 0 ≤ ∑ i,RadialCost.weight n a (r i) := Finset.sum_nonneg fun i _ =>
    (by norm_num : (0:ℝ) ≤ 1).trans (RadialCost.weight_ge_one n a (r i))
  have hm : 0 ≤ (Fintype.card I:ℝ) := Nat.cast_nonneg _
  have hbudget' : (Fintype.card I:ℝ)+∑ i,cost μ caps i ≤ (1+Cₐ)*W*R := by
    have hx := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 1+Cₐ)
    have hmc := mul_nonneg hCₐ.le hm
    nlinarith only [hcost,hw,hx,hmc]
  have hfirst' : ∑ S ∈ P.parts,Real.log (1+(μ.real (E S))⁻¹) ≤ (C*(1+Cₐ)*W)*R := by
    have hh := mul_le_mul_of_nonneg_left hbudget' hC.le
    exact hfirst.trans (by convert hh using 1 ; ring)
  have hrow' : ∑ S ∈ P.parts,Real.log (1+∑ T ∈ P.parts.erase S,Blocks.weight μ (E S) (E T)) ≤ (C*(1+Cₐ)*W)*R := by
    have hh := mul_le_mul_of_nonneg_left hbudget' hC.le
    exact hrow.trans (by convert hh using 1 ; ring)
  obtain ⟨hν,hν1,hD⟩ := WitnessBlocks.certificates P.parts μ E
    (fun S hS => (hE S hS).2.2.2.2.2.1)
    (fun S hS => (hE S hS).2.2.2.2.2.2.trans (by norm_num)) hfirst' hrow'
  refine ⟨P,b,E,?_,?_,hν1,?_⟩
  · intro S hS
    obtain ⟨hb,hm,hmeas,hsub,hslot,hpos,hle⟩ := hE S hS
    exact ⟨hb,hmeas,hsub,fun x hx => (mem_iInter₂.mp (hsub hx)) (b S) hb,hslot,hpos,hle⟩
  · simpa only [neg_mul] using hν
  · dsimp [μ] at hD ⊢
    convert hD using 1 ; ring_nf

end WitnessConstruction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WitnessConstruction.shell_oai.{u_1} := @OAI.WitnessConstruction.shell_oai.{u_1}
