-- Prove2me | solution 1 for XiMultiplicityPublished.xi_zero_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:58:19.047971+00:00
-- url     : https://prove2.me/submissions/b0cd6a6d-ec14-4f54-8177-9f261b8f9147

import Mathlib

set_option maxRecDepth 4000

open scoped BigOperators
open Filter Topology

namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  have hz := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_centered_even (u : ℂ) : xi (1/2-u) = xi (1/2+u) := by
  convert xi_functional_equation (1/2+u) using 1 <;> congr 1 <;> ring

theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp


end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set

theorem xi_zero_value : xi 0 = 1/2 := by simp [xi]
theorem xi_one_value : xi 1 = 1/2 := by simp [xi]

theorem xi_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one_value]; norm_num
  have hr : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_zeta s hr h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hr))
    (riemannZeta_ne_zero_of_one_le_re hs)) (by norm_num)

theorem xi_ne_zero_left (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_functional_equation s]
  apply xi_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem xi_zero_iff (s : ℂ) :
    xi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hx
    have hr : 0 < s.re := lt_of_not_ge (fun h => xi_ne_zero_left s h hx)
    have hl : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_right s h hx)
    have h0 : s ≠ 0 := by intro h; simp [h] at hr
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1] at hx
    have hz : riemannZeta s = 0 := by
      rcases (div_eq_zero_iff).mp hx with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left
          (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
            (Complex.Gammaℝ_ne_zero_of_re_pos hr))
      · norm_num at hh
    exact ⟨hz, hr, hl⟩
  · rintro ⟨hz, hr, hl⟩
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1, hz]
    ring

theorem xi_zero_reflection (s : ℂ) : xi (1-s) = 0 ↔ xi s = 0 := by
  rw [xi_functional_equation]

theorem xi_zeros_compact_finite (S : Set ℂ) (hS : IsCompact S) :
    (S ∩ {s | xi s = 0}).Finite := by
  apply hS.inter_riemannZetaZeros_finite.subset
  intro s hs
  exact ⟨hs.1, (xi_zero_iff s).mp hs.2 |>.1⟩

theorem centered_zero_strip (s : ℂ) (hs : xi s = 0) : |s.re - 1/2| < 1/2 := by
  have h := (xi_zero_iff s).mp hs
  rw [abs_lt]
  constructor <;> linarith [h.2.1, h.2.2]

end XiZeroGeometry

namespace XiMultiplicity
open EtaQBridge Set Filter Topology

theorem xi_analytic (s : ℂ) : AnalyticAt ℂ xi s := xi_differentiable.analyticAt s

theorem xi_order_finite (s : ℂ) : analyticOrderAt xi s ≠ ⊤ := by
  intro h
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s xi_analytic).mp h
  have hh := congrFun hz 0
  rw [XiZeroGeometry.xi_zero_value] at hh
  norm_num at hh

theorem xi_multiplicity_pos (s : ℂ) (hs : xi s = 0) :
    0 < analyticOrderNatAt xi s := by
  exact ENat.toNat_pos ((xi_analytic s).analyticOrderAt_ne_zero.mpr hs) (xi_order_finite s)

theorem xi_zeta_order_eq (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt xi s = analyticOrderAt riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hg0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have hg : AnalyticAt ℂ Complex.Gammaℝ s := by
    have hh := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hg0)
    simpa only [Pi.inv_def, inv_inv] using hh
  let a : ℂ → ℂ := fun z => z*(z-1)*Complex.Gammaℝ z/2
  have ha : AnalyticAt ℂ a s := by
    dsimp [a]
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hg).div_const
  have ha0 : a s ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hg0) (by norm_num)
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s h1
  have he : xi =ᶠ[𝓝 s] a*riemannZeta := by
    have hR : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr
    filter_upwards [hR, eventually_ne_nhds h1] with z hz hz1
    rw [xi_eq_zeta z hz hz1]
    simp only [Pi.mul_apply, a]
    ring
  rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hz,
    ha.analyticOrderAt_eq_zero.mpr ha0, zero_add]

theorem xi_zeta_multiplicity_eq (s : ℂ) (hs : xi s = 0) :
    analyticOrderNatAt xi s = analyticOrderNatAt riemannZeta s := by
  have h := (XiZeroGeometry.xi_zero_iff s).mp hs
  have h1 : s ≠ 1 := by intro he; simp [he] at h
  unfold analyticOrderNatAt
  rw [xi_zeta_order_eq s h.2.1 h1]

theorem xi_zero_set_countable : {s : ℂ | xi s = 0}.Countable := by
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) ∩ {s | xi s = 0}).Countable :=
    Set.countable_iUnion (fun n =>
      (XiZeroGeometry.xi_zeros_compact_finite _ (isCompact_closedBall _ _)).countable)
  apply hc.mono
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt ‖s‖
  exact mem_iUnion.mpr ⟨n, ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hn.le, hs⟩⟩

def UpperZero := {s : ℂ // xi s = 0 ∧ 0 < s.im}

instance upperZero_countable : Countable UpperZero :=
  (xi_zero_set_countable.mono (fun s hs => hs.1)).to_subtype

def Occurrence := (s : UpperZero) × Fin (analyticOrderNatAt xi s.val)

instance occurrence_countable : Countable Occurrence := by
  unfold Occurrence
  infer_instance

def location (z : Occurrence) : ℂ := z.1.val

theorem occurrence_location (z : Occurrence) :
    riemannZeta (location z) = 0 ∧ 0 < (location z).re ∧
      (location z).re < 1 ∧ 0 < (location z).im := by
  have h := (XiZeroGeometry.xi_zero_iff z.1.val).mp z.1.property.1
  exact ⟨h.1, h.2.1, h.2.2, z.1.property.2⟩

theorem every_upper_zero_occurs (s : ℂ) (hz : riemannZeta s = 0)
    (hr : 0 < s.re) (hl : s.re < 1) (hi : 0 < s.im) :
    ∃ z : Occurrence, location z = s := by
  have hx := (XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩
  exact ⟨⟨⟨s,hx,hi⟩,⟨0,xi_multiplicity_pos s hx⟩⟩,rfl⟩

def fiberEquiv (s : UpperZero) : {z : Occurrence // z.1 = s} ≃
    Fin (analyticOrderNatAt xi s.val) where
  toFun z := z.property ▸ z.val.2
  invFun k := ⟨⟨s,k⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨v,k⟩,h⟩
    dsimp at h
    subst v
    rfl
  right_inv := by intro k; rfl

theorem fiber_card (s : UpperZero) :
    Nat.card {z : Occurrence // z.1 = s} = analyticOrderNatAt riemannZeta s.val := by
  rw [Nat.card_congr (fiberEquiv s), Nat.card_fin,
    xi_zeta_multiplicity_eq s.val s.property.1]

theorem occurrences_compact_finite (K : Set ℂ) (hK : IsCompact K) :
    {z : Occurrence | location z ∈ K}.Finite := by
  have hf : {s : UpperZero | s.val ∈ K}.Finite := by
    have hh := Set.Finite.preimage (f := fun s : UpperZero => s.val)
      (fun _ _ _ _ h => Subtype.ext h) (XiZeroGeometry.xi_zeros_compact_finite K hK)
    exact hh.subset (fun s hs => ⟨hs,s.property.1⟩)
  have hfi (s : UpperZero) : {z : Occurrence | z.1 = s}.Finite := by
    exact Set.finite_coe_iff.mp (Finite.of_equiv
      (Fin (analyticOrderNatAt xi s.val)) (fiberEquiv s).symm)
  apply (hf.biUnion (fun s _ => hfi s)).subset
  intro z hz
  exact mem_iUnion.mpr ⟨z.1,mem_iUnion.mpr ⟨hz,rfl⟩⟩

theorem occurrences_bounded_height_finite (T : ℝ) :
    {z : Occurrence | (location z).im ≤ T}.Finite := by
  apply (occurrences_compact_finite (Metric.closedBall 0 (|T|+1))
    (isCompact_closedBall _ _)).subset
  intro z hz
  have h := occurrence_location z
  rw [mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  calc
    ‖location z‖ ≤ |(location z).re|+|(location z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |T|+1 := by rw [abs_of_pos h.2.1, abs_of_pos h.2.2.2]; linarith [h.2.2.1, (show (location z).im ≤ T from hz), le_abs_self T]

theorem occurrence_indexing : ∃ code : Occurrence → ℕ, Function.Injective code :=
  Countable.exists_injective_nat Occurrence

def locationFiberEquiv (s : UpperZero) :
    {z : Occurrence // location z = s.val} ≃ {z : Occurrence // z.1 = s} where
  toFun z := ⟨z.val, Subtype.ext z.property⟩
  invFun z := ⟨z.val, congrArg Subtype.val z.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl

theorem complete_countable_zero_index :
    ∃ I : Type, Countable I ∧ ∃ rho : I → ℂ,
      (∀ s : ℂ, (∃ i, rho i = s) ↔
        riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im) ∧
      (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 < s.im →
        Nat.card {i : I // rho i = s} = analyticOrderNatAt riemannZeta s) ∧
      (∀ T : ℝ, {i : I | (rho i).im ≤ T}.Finite) := by
  refine ⟨Occurrence, inferInstance, location, ?_, ?_, occurrences_bounded_height_finite⟩
  · intro s
    constructor
    · rintro ⟨i,rfl⟩
      exact occurrence_location i
    · rintro ⟨hz,hr,hl,hi⟩
      exact every_upper_zero_occurs s hz hr hl hi
  · intro s hz hr hl hi
    let v : UpperZero := ⟨s,(XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩,hi⟩
    exact (Nat.card_congr (locationFiberEquiv v)).trans (fiber_card v)

theorem xi_meromorphic_order (s : ℂ) :
    meromorphicOrderAt xi s = ((analyticOrderNatAt xi s : ℕ) : WithTop ℤ) := by
  rw [(xi_analytic s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (xi_order_finite s)]
  simp

end XiMultiplicity
namespace XiFiniteFactor
open EtaQBridge XiMultiplicity Set Filter Topology Metric MeromorphicOn

noncomputable def diskProduct (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ z : ℂ, (fun w : ℂ => w-z) ^ (divisor xi (ball 0 R) z)

theorem finite_divisor_support (R : ℝ) : (divisor xi (ball 0 R)).support.Finite :=
  (show MeromorphicOn xi (closedBall 0 R) from
    fun s _ => (xi_analytic s).meromorphicAt).divisor_ball_support_finite

theorem diskProduct_analytic (R : ℝ) (s : ℂ) : AnalyticAt ℂ (diskProduct R) s := by
  apply Function.FactorizedRational.analyticAt
  exact (show AnalyticOnNhd ℂ xi (ball 0 R) from fun z _ => xi_analytic z).divisor_nonneg s

theorem xi_disk_factorization (R : ℝ) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      (∀ z ∈ ball 0 R, xi z = diskProduct R z * g z) := by
  have hm : MeromorphicOn xi (ball 0 R) := fun z _ => (xi_analytic z).meromorphicAt
  obtain ⟨g,hg,hgn,he⟩ := hm.extract_zeros_poles
    (fun z => by simp [xi_meromorphic_order]) (finite_divisor_support R)
  refine ⟨g,hg,fun z hz => hgn ⟨z,hz⟩,?_⟩
  intro z hz
  have hp : AnalyticAt ℂ (diskProduct R * g) z := (diskProduct_analytic R z).mul (hg z hz)
  have hev : xi =ᶠ[𝓝[≠] z] diskProduct R * g := by
    have he' := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he z hz
    have hu0 : ∀ᶠ w : ℂ in 𝓝 z, w ∈ ball 0 R := isOpen_ball.mem_nhds hz
    have hu : ∀ᶠ w : ℂ in 𝓝[≠] z, w ∈ ball 0 R :=
      hu0.filter_mono nhdsWithin_le_nhds
    filter_upwards [he',hu] with w hw hwu
    rcases hw with hw | hw
    · exact hw
    · exact False.elim (hw hwu)
  exact tendsto_nhds_unique
    ((xi_analytic z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

theorem xi_normalized_disk_factorization (R : ℝ) (hR : 0 < R) :
    diskProduct R 0 ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 R) ∧ H 0 = 1 ∧
      (∀ z ∈ ball 0 R, H z ≠ 0) ∧
      (∀ z ∈ ball 0 R, xi z / xi 0 =
        (diskProduct R z / diskProduct R 0) * H z) := by
  obtain ⟨g,hg,hgn,he⟩ := xi_disk_factorization R
  have hzero : (0 : ℂ) ∈ ball 0 R := by simpa using hR
  have hg0 : g 0 ≠ 0 := hgn 0 hzero
  have hp0 : diskProduct R 0 ≠ 0 := by
    intro h
    have hh := he 0 hzero
    rw [h,zero_mul,XiZeroGeometry.xi_zero_value] at hh
    norm_num at hh
  refine ⟨hp0, fun z => g z/g 0, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hg z hz).div_const
  · exact div_self hg0
  · intro z hz
    exact div_ne_zero (hgn z hz) hg0
  · intro z hz
    rw [he z hz,he 0 hzero]
    field_simp

theorem disk_divisor_is_multiplicity (R : ℝ) (z : ℂ) (hz : z ∈ ball 0 R) :
    divisor xi (ball 0 R) z = (analyticOrderNatAt xi z : ℤ) := by
  rw [divisor_apply (fun s _ => (xi_analytic s).meromorphicAt) hz,xi_meromorphic_order]
  simp

theorem disk_divisor_support (R : ℝ) :
    (divisor xi (ball 0 R)).support = ball 0 R ∩ {z | xi z = 0} := by
  ext z
  constructor
  · intro hz
    have hu := (divisor xi (ball 0 R)).supportWithinDomain hz
    refine ⟨hu,?_⟩
    have hn : divisor xi (ball 0 R) z ≠ 0 := hz
    rw [disk_divisor_is_multiplicity R z hu] at hn
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    exact_mod_cast hn
  · rintro ⟨hu,hz⟩
    change divisor xi (ball 0 R) z ≠ 0
    rw [disk_divisor_is_multiplicity R z hu]
    exact_mod_cast (ne_of_gt (xi_multiplicity_pos z hz))

theorem concrete_normalized_factorization (R : ℝ) (hR : 0 < R) :
    (divisor xi (ball 0 R)).support = ball 0 R ∩ {z | xi z = 0} ∧
    (∀ z ∈ ball 0 R, divisor xi (ball 0 R) z = (analyticOrderNatAt xi z : ℤ)) ∧
    diskProduct R 0 ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 R) ∧ H 0 = 1 ∧
      (∀ z ∈ ball 0 R, H z ≠ 0) ∧
      (∀ z ∈ ball 0 R, xi z / xi 0 =
        (diskProduct R z / diskProduct R 0) * H z) := by
  exact ⟨disk_divisor_support R, disk_divisor_is_multiplicity R,
    xi_normalized_disk_factorization R hR⟩

end XiFiniteFactor

theorem solution  :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    ∀ s : ℂ, f s = 0 → analyticOrderAt f s ≠ ⊤ ∧
      0 < analyticOrderNatAt f s ∧ analyticOrderAt f s = analyticOrderAt riemannZeta s := by
  dsimp only
  intro s hs
  have h := (XiZeroGeometry.xi_zero_iff s).mp hs
  have h1 : s ≠ 1 := by intro he; simp [he] at h
  exact ⟨XiMultiplicity.xi_order_finite s, XiMultiplicity.xi_multiplicity_pos s hs,
    XiMultiplicity.xi_zeta_order_eq s h.2.1 h1⟩
