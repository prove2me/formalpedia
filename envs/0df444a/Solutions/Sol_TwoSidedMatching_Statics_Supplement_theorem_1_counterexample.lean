-- Prove2me | solution 1 for TwoSidedMatching.Statics.Supplement.theorem_1_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:45.451998+00:00
-- url     : https://prove2.me/submissions/8ab1f18a-c597-4bda-b274-93baf5cbaf03

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Deviation

open MeasureTheory

open TwoSidedMatching
open TwoSidedMatching.Statics
open TwoSidedMatching.Statics.Supplement

/-- Counterexample to both threshold-tie assertions in Theorem 1 on its full printed domain.
The tagged types v=c=1 belong to their closed supports. Both constant actions are adapted.
No assumption about a general equilibrium or conditional compensation is used. -/
theorem solution :
    touchingMarket.Regular ∧ touchingMarket.loS = touchingMarket.hiB ∧
    ContinuousOn touchingMarket.fB (Set.Icc touchingMarket.loB touchingMarket.hiB) ∧
    ContinuousOn touchingMarket.fS (Set.Icc touchingMarket.loS touchingMarket.hiS) ∧
    TwoSidedMatching.Guarantee.muStar touchingMarket 1 1 1 = 0 ∧
    TwoSidedMatching.Guarantee.pStar touchingMarket 1 1 1 = 1 ∧
    TwoSidedMatching.Guarantee.wStar touchingMarket 1 1 1 = 1 ∧
    IsProbabilityMeasure (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) ∧
    (∀ᵐ ω ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1,
      TwoSidedMatching.Guarantee.reqB touchingMarket 1 1 1 ω = ∅ ∧
      TwoSidedMatching.Guarantee.reqS touchingMarket 1 1 1 ω = ∅) ∧
    (∀ a : Bool,
      Integrable (buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
        (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) ∧
      Integrable (sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
        (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1)) ∧
    (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 ∧
    (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 ∧
    (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 ∧
    (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
      ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 := by
        have hcdfB : ∀ y, touchingMarket.cdfB y = y := by
          intro y; simp [MechanismDesign.BilateralTrade.Environment.cdfB, touchingMarket]
        have hcdfS : ∀ x, touchingMarket.cdfS x = x - 1 := by
          intro x; simp [MechanismDesign.BilateralTrade.Environment.cdfS, touchingMarket]
        have hpsiB : ∀ y, touchingMarket.psiB y = 2 * y - 1 := by
          intro y; simp only [MechanismDesign.BilateralTrade.Environment.psiB, hcdfB]
          simp [touchingMarket]; ring
        have hpsiS : ∀ x, touchingMarket.psiS x = 2 * x - 1 := by
          intro x; simp only [MechanismDesign.BilateralTrade.Environment.psiS, hcdfS]
          simp [touchingMarket]; ring
        have hFdBar : ∀ p, TwoSidedMatching.Guarantee.FdBar touchingMarket p = 1 - max 0 (min p 1) := by
          intro p; simp only [TwoSidedMatching.Guarantee.FdBar, TwoSidedMatching.Guarantee.Fd, hcdfB]
          simp [touchingMarket]
        have hFs : ∀ w, TwoSidedMatching.Guarantee.Fs touchingMarket w = max 1 (min w 2) - 1 := by
          intro w; simp only [TwoSidedMatching.Guarantee.Fs, hcdfS]
          simp [touchingMarket]
        have hFdBarInv : ∀ q ∈ Set.Icc (0:ℝ) 1, TwoSidedMatching.Guarantee.FdBarInv touchingMarket q = 1 - q := by
          intro q hq
          have hex : ∃ a ∈ Set.Icc touchingMarket.loB touchingMarket.hiB,
              TwoSidedMatching.Guarantee.FdBar touchingMarket a = q := by
            refine ⟨1 - q, ?_, ?_⟩
            · simp [touchingMarket]; constructor <;> linarith [hq.1, hq.2]
            · rw [hFdBar]; rw [min_eq_left (by linarith [hq.1]), max_eq_right (by linarith [hq.2])]; ring
          have h1 := Function.invFunOn_eq hex
          have h2 := Function.invFunOn_mem hex
          simp only [TwoSidedMatching.Guarantee.FdBarInv] at *
          set x := Function.invFunOn (TwoSidedMatching.Guarantee.FdBar touchingMarket)
            (Set.Icc touchingMarket.loB touchingMarket.hiB) q
          simp [touchingMarket] at h2
          rw [hFdBar, min_eq_left h2.2, max_eq_right h2.1] at h1
          linarith
        have hFsInv : ∀ q ∈ Set.Icc (0:ℝ) 1, TwoSidedMatching.Guarantee.FsInv touchingMarket q = 1 + q := by
          intro q hq
          have hex : ∃ a ∈ Set.Icc touchingMarket.loS touchingMarket.hiS,
              TwoSidedMatching.Guarantee.Fs touchingMarket a = q := by
            refine ⟨1 + q, ?_, ?_⟩
            · simp [touchingMarket]; constructor <;> linarith [hq.1, hq.2]
            · rw [hFs]; rw [min_eq_left (by linarith [hq.2]), max_eq_right (by linarith [hq.1])]; ring
          have h1 := Function.invFunOn_eq hex
          have h2 := Function.invFunOn_mem hex
          simp only [TwoSidedMatching.Guarantee.FsInv] at *
          set x := Function.invFunOn (TwoSidedMatching.Guarantee.Fs touchingMarket)
            (Set.Icc touchingMarket.loS touchingMarket.hiS) q
          simp [touchingMarket] at h2
          rw [hFs, min_eq_left h2.2, max_eq_right h2.1] at h1
          linarith
        have hadm : TwoSidedMatching.Guarantee.admissibleVolume touchingMarket 1 1 1 = {0} := by
          ext μ
          simp only [TwoSidedMatching.Guarantee.admissibleVolume, Set.mem_ofPred_eq, Set.mem_singleton_iff,
            TwoSidedMatching.Guarantee.V, mul_one, min_self, div_one]
          constructor
          · rintro ⟨hμ, hV⟩
            rw [hFdBarInv μ hμ, hFsInv μ hμ, hpsiB, hpsiS] at hV
            linarith [hμ.1]
          · rintro rfl
            refine ⟨⟨le_refl _, zero_le_one⟩, ?_⟩
            rw [hFdBarInv 0 ⟨le_refl _, zero_le_one⟩, hFsInv 0 ⟨le_refl _, zero_le_one⟩, hpsiB, hpsiS]
            norm_num
        have hmu : TwoSidedMatching.Guarantee.muStar touchingMarket 1 1 1 = 0 := by
          rw [TwoSidedMatching.Guarantee.muStar, hadm, csSup_singleton]
        have hp : TwoSidedMatching.Guarantee.pStar touchingMarket 1 1 1 = 1 := by
          rw [TwoSidedMatching.Guarantee.pStar, hmu, zero_div, hFdBarInv 0 ⟨le_refl _, zero_le_one⟩]; norm_num
        have hw : TwoSidedMatching.Guarantee.wStar touchingMarket 1 1 1 = 1 := by
          rw [TwoSidedMatching.Guarantee.wStar, hmu, zero_div, hFsInv 0 ⟨le_refl _, zero_le_one⟩]; norm_num
        have hreg : touchingMarket.Regular := by
          constructor
          · intro x _ y _ hxy; rw [hpsiS, hpsiS]; linarith
          · intro x _ y _ hxy; rw [hpsiB, hpsiB]; linarith
        have iT : IsProbabilityMeasure (TwoSidedMatching.Guarantee.timeLaw 1) :=
          ⟨by simp [TwoSidedMatching.Guarantee.timeLaw]⟩
        have iV : IsProbabilityMeasure (TwoSidedMatching.Guarantee.valLaw touchingMarket) :=
          ⟨by simp [TwoSidedMatching.Guarantee.valLaw, touchingMarket]⟩
        have iC : IsProbabilityMeasure (TwoSidedMatching.Guarantee.costLaw touchingMarket) :=
          ⟨by simp [TwoSidedMatching.Guarantee.costLaw, touchingMarket]; norm_num⟩
        have iBM : IsProbabilityMeasure (TwoSidedMatching.Guarantee.buyerMark touchingMarket 1) := by
          unfold TwoSidedMatching.Guarantee.buyerMark; infer_instance
        have iSM : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sellerMark touchingMarket 1) := by
          unfold TwoSidedMatching.Guarantee.sellerMark; infer_instance
        have hpo : ∀ r, ProbabilityTheory.poissonMeasure r Set.univ = 1 := fun r => by
          unfold ProbabilityTheory.poissonMeasure
          exact ((ProbabilityTheory.hasSum_one_poissonMeasure r).isProbabilityMeasure_sum_dirac (fun _ ↦ by positivity)).measure_univ
        have iSB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw 1 1
            (TwoSidedMatching.Guarantee.buyerMark touchingMarket 1)) := by
          unfold TwoSidedMatching.Guarantee.sideLaw
          have h2 : IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => TwoSidedMatching.Guarantee.buyerMark touchingMarket 1) := inferInstance
          exact ⟨by rw [← Set.univ_prod_univ, Measure.prod_prod, h2.measure_univ, mul_one]; exact hpo _⟩
        have iSS : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw 1 1
            (TwoSidedMatching.Guarantee.sellerMark touchingMarket 1)) := by
          unfold TwoSidedMatching.Guarantee.sideLaw
          have h2 : IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => TwoSidedMatching.Guarantee.sellerMark touchingMarket 1) := inferInstance
          exact ⟨by rw [← Set.univ_prod_univ, Measure.prod_prod, h2.measure_univ, mul_one]; exact hpo _⟩
        have iP : IsProbabilityMeasure (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) := by
          unfold TwoSidedMatching.Guarantee.P; infer_instance
        have hV : ∀ᵐ v ∂TwoSidedMatching.Guarantee.valLaw touchingMarket, v < 1 := by
          apply (withDensity_absolutelyContinuous _ _).ae_le
          refine (ae_restrict_iff' measurableSet_Icc).2 ?_
          have : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by
            simp [ae_iff, measure_singleton]
          filter_upwards [this] with v hv hmem
          simp [touchingMarket] at hmem
          exact lt_of_le_of_ne hmem.2 hv
        have hC : ∀ᵐ c ∂TwoSidedMatching.Guarantee.costLaw touchingMarket, 1 < c := by
          apply (withDensity_absolutelyContinuous _ _).ae_le
          refine (ae_restrict_iff' measurableSet_Icc).2 ?_
          have : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by
            simp [ae_iff, measure_singleton]
          filter_upwards [this] with v hv hmem
          simp [touchingMarket] at hmem
          exact lt_of_le_of_ne hmem.1 (Ne.symm hv)
        have hBn : ∀ n : ℕ, ∀ᵐ ω ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1, (ω.1.2 n).2 < 1 := by
          intro n
          have h1 : ∀ᵐ x ∂TwoSidedMatching.Guarantee.buyerMark touchingMarket 1, x.2 < 1 :=
            Measure.quasiMeasurePreserving_snd.ae hV
          have h2 : ∀ᵐ y ∂Measure.infinitePi (fun _ : ℕ => TwoSidedMatching.Guarantee.buyerMark touchingMarket 1),
              (y n).2 < 1 :=
            (measurePreserving_eval_infinitePi (fun _ : ℕ => TwoSidedMatching.Guarantee.buyerMark touchingMarket 1) n).quasiMeasurePreserving.ae (p := fun x : ℝ × ℝ => x.2 < 1) h1
          have h3 : ∀ᵐ x ∂TwoSidedMatching.Guarantee.sideLaw 1 1
              (TwoSidedMatching.Guarantee.buyerMark touchingMarket 1), (x.2 n).2 < 1 :=
            Measure.quasiMeasurePreserving_snd.ae h2
          exact Measure.quasiMeasurePreserving_fst.ae h3
        have hSn : ∀ n : ℕ, ∀ᵐ ω ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1, 1 < (ω.2.2 n).2 := by
          intro n
          have h1 : ∀ᵐ x ∂TwoSidedMatching.Guarantee.sellerMark touchingMarket 1, 1 < x.2 :=
            Measure.quasiMeasurePreserving_snd.ae hC
          have h2 : ∀ᵐ y ∂Measure.infinitePi (fun _ : ℕ => TwoSidedMatching.Guarantee.sellerMark touchingMarket 1),
              1 < (y n).2 :=
            (measurePreserving_eval_infinitePi (fun _ : ℕ => TwoSidedMatching.Guarantee.sellerMark touchingMarket 1) n).quasiMeasurePreserving.ae (p := fun x : ℝ × ℝ => 1 < x.2) h1
          have h3 : ∀ᵐ x ∂TwoSidedMatching.Guarantee.sideLaw 1 1
              (TwoSidedMatching.Guarantee.sellerMark touchingMarket 1), 1 < (x.2 n).2 :=
            Measure.quasiMeasurePreserving_snd.ae h2
          exact Measure.quasiMeasurePreserving_snd.ae h3
        have hreq : ∀ᵐ ω ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1,
            TwoSidedMatching.Guarantee.reqB touchingMarket 1 1 1 ω = ∅ ∧
            TwoSidedMatching.Guarantee.reqS touchingMarket 1 1 1 ω = ∅ := by
          filter_upwards [ae_all_iff.2 hBn, ae_all_iff.2 hSn] with ω hb hs
          constructor
          · simp only [TwoSidedMatching.Guarantee.reqB, hp, Finset.filter_eq_empty_iff]
            intro i _ hi
            exact absurd (hb i) (not_lt.2 hi)
          · simp only [TwoSidedMatching.Guarantee.reqS, hw, Finset.filter_eq_empty_iff]
            intro i _ hi
            exact absurd (hs i) (not_lt.2 hi)
        have hBU : ∀ a : Bool, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a)
            =ᵐ[TwoSidedMatching.Guarantee.P touchingMarket 1 1 1] fun _ => if a then -1 else 0 := by
          intro a
          filter_upwards [hreq] with ω h
          have hs : TwoSidedMatching.Guarantee.sortedS touchingMarket 1 1 1 ω = [] := by
            simp [TwoSidedMatching.Guarantee.sortedS, h.2]
          cases a <;> simp [buyerUtility, buyerMatch, immediate, hs] <;> norm_num
        have hSU : ∀ a : Bool, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a)
            =ᵐ[TwoSidedMatching.Guarantee.P touchingMarket 1 1 1] fun _ => if a then -1 else 0 := by
          intro a
          filter_upwards [hreq] with ω h
          have hs : TwoSidedMatching.Guarantee.sortedB touchingMarket 1 1 1 ω = [] := by
            simp [TwoSidedMatching.Guarantee.sortedB, h.1]
          cases a <;> simp [sellerUtility, sellerMatch, immediate, hs] <;> norm_num
        have hint : ∀ a : Bool,
            Integrable (buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
              (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) ∧
            Integrable (sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) a))
              (TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) := fun a =>
          ⟨(integrable_const _).congr (hBU a).symm, (integrable_const _).congr (hSU a).symm⟩
        have e1 : (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
            ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 := by
          rw [integral_congr_ae (hBU true)]; simp
        have e2 : (∫ ω, buyerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
            ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 := by
          rw [integral_congr_ae (hBU false)]; simp
        have e3 : (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) true) ω
            ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = -1 := by
          rw [integral_congr_ae (hSU true)]; simp
        have e4 : (∫ ω, sellerUtility touchingMarket 1 1 1 2 (1 / 2) 1 (immediate (1 / 2) false) ω
            ∂TwoSidedMatching.Guarantee.P touchingMarket 1 1 1) = 0 := by
          rw [integral_congr_ae (hSU false)]; simp
        exact ⟨hreg, rfl, continuousOn_const, continuousOn_const, hmu, hp, hw, iP, hreq, hint,
          e1, e2, e3, e4⟩
