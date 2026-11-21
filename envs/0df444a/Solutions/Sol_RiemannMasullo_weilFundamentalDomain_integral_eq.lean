-- Prove2me | solution 1 for RiemannMasullo.weilFundamentalDomain_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:33:13.686891+00:00
-- url     : https://prove2.me/submissions/fc804f84-d598-4816-a1a6-2a9e4c12578d

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L244-L248
import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _
variable (hH : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable [DiscreteTopology H] [SecondCountableTopology G]
variable {Δ Δ' : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))
include hH hΔ hbij
theorem solution (hΔ' : MeasurableSet Δ')
    (hbij' : Function.Bijective (fun x : Δ' ↦ (QuotientGroup.mk x.val : G ⧸ H)))
    {f : G → ℂ} (hf : Measurable f) (hinv : ∀ (x : G) (h : H), f (x * (h : G)) = f x)
    (hint : IntegrableOn f Δ μ) :
    IntegrableOn f Δ' μ ∧ (∫ x in Δ, f x ∂μ) = ∫ x in Δ', f x ∂μ := by
  classical
  haveI : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have domain (D : Set G) (hm : MeasurableSet D)
      (hb : Function.Bijective (fun x : D ↦ (QuotientGroup.mk x.val : G ⧸ H))) :
      IsFundamentalDomain H D μ := by
    apply IsFundamentalDomain.mk' hm.nullMeasurableSet
    intro x
    obtain ⟨y, hy⟩ := hb.2 (QuotientGroup.mk x)
    have hmem : x⁻¹ * y.val ∈ H := QuotientGroup.eq.mp hy.symm
    let a : H := ⟨x⁻¹ * y.val, hmem⟩
    have ha : (a : G) * x = y.val := by
      change (x⁻¹ * y.val) * x = y.val
      rw [mul_comm _ x, mul_inv_cancel_left]
    refine ⟨a, ?_, ?_⟩
    · change (a : G) * x ∈ D
      simpa [ha] using y.property
    intro b hbx
    change (b : G) * x ∈ D at hbx
    have hbq : (QuotientGroup.mk' H) (b : G) = 1 := (QuotientGroup.eq_one_iff _).2 b.property
    have hz : (⟨(b : G) * x, hbx⟩ : D) = y := hb.1 (by
      apply Eq.trans _ hy.symm
      change (QuotientGroup.mk' H) ((b : G) * x) = (QuotientGroup.mk' H) x
      rw [map_mul, hbq, one_mul])
    exact Subtype.ext (mul_right_cancel ((congrArg Subtype.val hz).trans ha.symm))
  have s := domain Δ hΔ hbij
  have t := domain Δ' hΔ' hbij'
  have hfi (h : H) (x : G) : f (h • x) = f x := by
    change f ((h : G) * x) = f x
    rw [mul_comm]
    exact hinv x h
  exact ⟨(s.integrableOn_iff t hfi).mp hint, s.setIntegral_eq t hfi⟩
