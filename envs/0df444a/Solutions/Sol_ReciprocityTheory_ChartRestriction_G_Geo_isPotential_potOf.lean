-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isPotential_potOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:00.462582+00:00
-- url     : https://prove2.me/submissions/5cf66bee-2ca4-45d2-8537-f64970d56363

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_continuousOn_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}
private theorem smoothOn_potOf_of_isSmoothHerm (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L)
    (x : R.X) : R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := by
  intro j
  have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
    refine contDiffOn_pi.mpr fun p => ?_
    exact ((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm
      (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ
  have hcomp := (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)
  exact hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'
private theorem exists_holo_re_eq_potOf_sub_on_overlap (R : AnLogRes P J e) (L : HermLine ι) (x x' y : R.X)
    (hy : y ∈ R.U x ∩ R.U x') : ∃ W : Set R.X, IsOpen W ∧ y ∈ W ∧ ∃ G : R.X → ℂ,
      R.A.HoloOn W G ∧ ∀ z ∈ W ∩ R.U x ∩ R.U x',
        (potOf R L).φ x z - (potOf R L).φ x' z = (G z).re := by
  classical
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  choose i hi using (R.mem x' y hy.2).1
  have hVo : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')
  have hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x p).mono Set.inter_subset_left
  have hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x' p).mono Set.inter_subset_right
  let r : K → R.X → ℂ := fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k
  let D : K → Set R.X := fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hD : ∀ k, IsOpen (D k) := fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton
  have hr : ∀ k, ContinuousOn (r k) (D k) := fun k =>
    (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left)
      (fun z hz => hz.2)).div_const _
  let W : Set R.X := (R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)
  have hW : IsOpen W :=
    hVo.inter (isOpen_iInter_of_finite fun k =>
      (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)
  have hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩ := fun k => congrFun hxy _
  have hyW : y ∈ W := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩
    have : r k y = 1 := by
      simp only [r, hlk k]
      field_simp [hi k, hc k]
    simp only [Set.mem_preimage, this]
    exact Complex.one_mem_slitPlane
  refine ⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)),
    ?_, ?_⟩
  · intro j w hw
    have hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x' := hw.2.1
    have hzk := fun k => Set.mem_iInter.mp hw.2.2 k
    have ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x p j w ⟨hw.1, hzV.1⟩
    have ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x' p j w ⟨hw.1, hzV.2⟩
    have hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w := fun k =>
      ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)
    show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) *
      (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_
    exact analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c', hc', hz⟩ := R.compat x x' z ⟨hzx, hzx'⟩
    have hzk := fun k => Set.mem_iInter.mp hzW.2 k
    have h2 := L.pos _ (R.mem x' z hzx').1
    have hsm := L.smul c' (R.lift x' z) hc'
    rw [← hz] at hsm
    have hrz : ∀ k, r k z = c' k / c k := by
      intro k
      have hne : R.lift x' z ⟨k, i k⟩ ≠ 0 := (hzk k).1.2
      simp only [r, congrFun hz ⟨k, i k⟩]
      field_simp [hne, hc k]
    have hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    simp only [potOf]
    rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right,
      Real.log_prod hP, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrz k, Real.log_zpow]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]
    ring
end ReciprocityTheory.ChartRestriction.G.Geo
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  ⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩
end ReciprocityTheory.ChartRestriction.G.Geo
