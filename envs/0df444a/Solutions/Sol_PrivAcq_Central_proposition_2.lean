-- Prove2me | solution 1 for PrivAcq.Central.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T12:24:35.296479+00:00
-- url     : https://prove2.me/submissions/28f1b480-485d-4a5a-91cc-1aee56b19353

import Mathlib
import Definitions.Def_PrivAcq_Central_Model
open MeasureTheory
namespace Queelius.PrivateTypeLaw
lemma compact_density_mass (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hn : ∀ x ∈ Set.Icc a b,0 ≤ f x)
    (hI : ∫ x in a..b,f x=1) :
    ((volume.restrict (Set.Icc a b)).withDensity (fun x => ENNReal.ofReal (f x))) Set.univ=1 := by
  have hi : Integrable f (volume.restrict (Set.Icc a b)) := hf.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hn x hx
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,hI]
  norm_num
lemma compact_density_support (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hn : ∀ x ∈ Set.Icc a b,0 ≤ f x)
    (hI : ∫ x in a..b,f x=1) :
    ((volume.restrict (Set.Icc a b)).withDensity (fun x => ENNReal.ofReal (f x))) (Set.Icc a b)=1 := by
  have hmass := compact_density_mass a b hab f hf hn hI
  rw [withDensity_apply _ measurableSet_Icc]
  rw [withDensity_apply _ MeasurableSet.univ] at hmass
  simpa only [Measure.restrict_restrict measurableSet_Icc,Set.inter_self,Measure.restrict_univ] using hmass
open PrivAcq.Central
lemma typeLaw_probability {n : ℕ} (S : Setting n) (hS : S.Standing) : IsProbabilityMeasure S.typeLaw := by
  let ν := fun i : Fin n => (volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity
    (fun x => ENNReal.ofReal (S.f i x))
  have hp (i : Fin n) : IsProbabilityMeasure (ν i) := by
    obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
    exact ⟨compact_density_mass (S.a i) (S.b i) hab.le (S.f i) hf (fun x hx => (hpos x hx).le) hI⟩
  letI : ∀ i : Fin n,IsProbabilityMeasure (ν i) := hp
  change IsProbabilityMeasure (Measure.pi ν)
  infer_instance
lemma typeLaw_support {n : ℕ} (S : Setting n) (hS : S.Standing) : S.typeLaw S.types=1 := by
  let ν := fun i : Fin n => (volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity
    (fun x => ENNReal.ofReal (S.f i x))
  have hp (i : Fin n) : IsProbabilityMeasure (ν i) := by
    obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
    exact ⟨compact_density_mass (S.a i) (S.b i) hab.le (S.f i) hf (fun x hx => (hpos x hx).le) hI⟩
  letI : ∀ i : Fin n,IsProbabilityMeasure (ν i) := hp
  change (Measure.pi ν) (Set.univ.pi (fun i => Set.Icc (S.a i) (S.b i)))=1
  rw [Measure.pi_pi]
  have he (i : Fin n) : ν i (Set.Icc (S.a i) (S.b i))=1 := by
    obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
    exact compact_density_support (S.a i) (S.b i) hab.le (S.f i) hf (fun x hx => (hpos x hx).le) hI
  simp only [he,Finset.prod_const_one]
lemma update_types {n : ℕ} (S : Setting n) (c : Fin n → ℝ) (hc : c ∈ S.types)
    (i : Fin n) (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    Function.update c i r ∈ S.types := by
  intro j _
  by_cases hj : j=i
  · subst j;simpa using hr
  · simpa only [Function.update_of_ne hj] using hc j (Set.mem_univ j)
lemma types_measurable {n : ℕ} (S : Setting n) : MeasurableSet S.types := by
  unfold Setting.types
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
lemma ae_types {n : ℕ} (S : Setting n) (hS : S.Standing) :
    ∀ᵐ c ∂S.typeLaw,c ∈ S.types := by
  letI := typeLaw_probability S hS
  rw [ae_iff]
  change S.typeLaw S.typesᶜ=0
  rw [prob_compl_eq_one_sub (types_measurable S),typeLaw_support S hS,tsub_self]
lemma privacy_integrable {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) (i : Fin n) (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    Integrable (fun c => M.ε (Function.update c i r) i) S.typeLaw := by
  letI := typeLaw_probability S hS
  obtain ⟨hw,hη,hε,halloc,⟨B,hB⟩,hmse,hmsefix⟩ := hM.1
  have hm : Measurable (fun c => M.ε (Function.update c i r) i) := by fun_prop
  apply Integrable.of_mem_Icc 0 B hm.aemeasurable
  filter_upwards [ae_types S hS] with c hc
  have hcu := update_types S c hc i r hr
  obtain ⟨hp,hw0,hsum,hpriv⟩ := halloc _ hcu
  exact ⟨(mul_nonneg hp.le (hw0 i)).trans (hpriv i),hB _ hcu i⟩
lemma interim_cost_affine {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) (i : Fin n) (r ci : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    interimCost S M i r ci=interimMse S M i r+ci*interimEps S M i r-interimPay S M i r := by
  have hI := privacy_integrable S hS M hM i r hr
  have hm := hM.1.2.2.2.2.2.2 i r hr
  have ht := hM.2.2.2 i r hr
  unfold interimCost interimMse interimEps interimPay
  have hs : (∫ c,mse S M (Function.update c i r)+ci*M.ε (Function.update c i r) i-
      M.t (Function.update c i r) i ∂S.typeLaw)=
      (∫ c,mse S M (Function.update c i r)+ci*M.ε (Function.update c i r) i ∂S.typeLaw)-
      (∫ c,M.t (Function.update c i r) i ∂S.typeLaw) := by
    simpa only [Pi.add_apply] using integral_sub (hm.add (hI.const_mul ci)) ht
  have ha : (∫ c,mse S M (Function.update c i r)+ci*M.ε (Function.update c i r) i ∂S.typeLaw)=
      (∫ c,mse S M (Function.update c i r) ∂S.typeLaw)+
      (∫ c,ci*M.ε (Function.update c i r) i ∂S.typeLaw) := by
    simpa only [Pi.add_apply] using integral_add hm (hI.const_mul ci)
  rw [hs,ha,integral_const_mul]
lemma ic_antitone {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) (hIC : IC S M) (i : Fin n) :
    AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i)) := by
  intro a ha b hb hab
  by_cases he : a=b
  · subst b;exact le_rfl
  have hab' : a < b := lt_of_le_of_ne hab he
  have h1 := hIC i a ha b hb
  have h2 := hIC i b hb a ha
  rw [interim_cost_affine S hS M hM i a a ha,interim_cost_affine S hS M hM i b a hb] at h1
  rw [interim_cost_affine S hS M hM i b b hb,interim_cost_affine S hS M hM i a b ha] at h2
  have hp : (b-a)*(interimEps S M i a-interimEps S M i b) ≥ 0 := by nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp (sub_pos.mpr hab'))
end Queelius.PrivateTypeLaw

namespace Queelius.PrivateTypeLaw
open PrivAcq.Central
lemma privacy_nonneg {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) (i : Fin n) (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    0 ≤ interimEps S M i r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_types S hS] with c hc
  obtain ⟨hp,hw,hs,hpriv⟩ := hM.1.2.2.2.1 _ (update_types S c hc i r hr)
  exact (mul_nonneg hp.le (hw i)).trans (hpriv i)
lemma antitone_integrable (a b : ℝ) (q : ℝ → ℝ) (hq : AntitoneOn q (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    IntervalIntegrable q volume x r :=
  (hq.mono (Set.uIcc_subset_Icc hx hr)).intervalIntegrable
lemma antitone_integral_bounds (a b : ℝ) (q : ℝ → ℝ) (hq : AntitoneOn q (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) (r : ℝ) (hr : r ∈ Set.Icc a b) (hxr : x ≤ r) :
    (r-x)*q r ≤ (∫ z in x..r,q z) ∧ (∫ z in x..r,q z) ≤ (r-x)*q x := by
  have hi := antitone_integrable a b q hq x hx r hr
  constructor
  · have h := intervalIntegral.integral_mono_on hxr (intervalIntegrable_const) hi
      (fun z hz => hq ⟨hx.1.trans hz.1,hz.2.trans hr.2⟩ hr hz.2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using h
  · have h := intervalIntegral.integral_mono_on hxr hi (intervalIntegrable_const)
      (fun z hz => hq hx ⟨hx.1.trans hz.1,hz.2.trans hr.2⟩ hz.1)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using h
lemma tail_support (a b : ℝ) (q : ℝ → ℝ) (hq : AntitoneOn q (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    (∫ z in r..b,q z)-(∫ z in x..b,q z) ≤ (x-r)*q r := by
  have hab : a ≤ b := hx.1.trans hx.2
  have he := intervalIntegral.integral_add_adjacent_intervals
    (antitone_integrable a b q hq r hr x hx)
    (antitone_integrable a b q hq x hx b ⟨hab,le_rfl⟩)
  rcases le_total r x with h | h
  · have hb := (antitone_integral_bounds a b q hq r hr x hx h).2
    linarith
  · have hb := (antitone_integral_bounds a b q hq x hx r hr h).1
    rw [intervalIntegral.integral_symm x r] at he
    nlinarith
lemma payment_implies_ic_ir {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M)
    (hp : ∀ i : Fin n, AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i)) ∧
      ∃ d : ℝ, 0 ≤ d ∧ ∀ ci ∈ Set.Icc (S.a i) (S.b i),
        interimPay S M i ci=interimMse S M i ci-S.var+ci*interimEps S M i ci+
          (∫ z in ci..S.b i,interimEps S M i z)+d) : IC S M ∧ IR S M := by
  constructor
  · intro i ci hci r hr
    obtain ⟨hq,d,hd,hpay⟩ := hp i
    rw [interim_cost_affine S hS M hM i ci ci hci,
      interim_cost_affine S hS M hM i r ci hr,hpay ci hci,hpay r hr]
    have ht := tail_support (S.a i) (S.b i) (interimEps S M i) hq ci hci r hr
    nlinarith
  · intro i ci hci
    obtain ⟨hq,d,hd,hpay⟩ := hp i
    rw [interim_cost_affine S hS M hM i ci ci hci,hpay ci hci]
    have hab : S.a i ≤ S.b i := hci.1.trans hci.2
    have hb := (antitone_integral_bounds (S.a i) (S.b i) (interimEps S M i) hq
      ci hci (S.b i) ⟨hab,le_rfl⟩ hci.2).1
    have hn := privacy_nonneg S hS M hM i (S.b i) ⟨hab,le_rfl⟩
    have hm := mul_nonneg (sub_nonneg.mpr hci.2) hn
    linarith
end Queelius.PrivateTypeLaw
namespace Queelius.PrivateTypeLaw
open PrivAcq.Central
lemma support_lipschitz (a b : ℝ) (hab : a ≤ b) (q U : ℝ → ℝ)
    (hq : AntitoneOn q (Set.Icc a b)) (hn : ∀ x ∈ Set.Icc a b,0 ≤ q x)
    (hs : ∀ x ∈ Set.Icc a b,∀ y ∈ Set.Icc a b,U y ≤ U x+(y-x)*q x) :
    LipschitzOnWith ⟨q a,hn a ⟨le_rfl,hab⟩⟩ U (Set.Icc a b) := by
  have bound (x : ℝ) (hx : x ∈ Set.Icc a b) (y : ℝ) (hy : y ∈ Set.Icc a b) :
      U y-U x ≤ |y-x| * q a := by
    calc
      U y-U x ≤ (y-x)*q x := by linarith [hs x hx y hy]
      _ ≤ |y-x| * q x := mul_le_mul_of_nonneg_right (le_abs_self _) (hn x hx)
      _ ≤ |y-x| * q a := mul_le_mul_of_nonneg_left (hq ⟨le_rfl,hab⟩ hx hx.1) (abs_nonneg _)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |U x-U y| ≤ q a * |x-y|
  apply abs_le.mpr
  have h1 := bound x hx y hy
  have h2 := bound y hy x hx
  rw [abs_sub_comm y x] at h1
  constructor <;> nlinarith
lemma support_derivative (a b : ℝ) (q U : ℝ → ℝ)
    (hs : ∀ x ∈ Set.Icc a b,∀ y ∈ Set.Icc a b,U y ≤ U x+(y-x)*q x)
    (x : ℝ) (hx : x ∈ Set.Ioo a b) (hd : DifferentiableAt ℝ U x) : deriv U x=q x := by
  have hm : IsLocalMax (fun y => U y-y*q x) x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have h := hs x ⟨hx.1.le,hx.2.le⟩ y ⟨hy.1.le,hy.2.le⟩
    linarith
  have he := hm.hasDerivAt_eq_zero (hd.hasDerivAt.sub ((hasDerivAt_id x).mul_const (q x)))
  linarith
lemma support_envelope (a b : ℝ) (hab : a ≤ b) (q U : ℝ → ℝ)
    (hq : AntitoneOn q (Set.Icc a b)) (hn : ∀ x ∈ Set.Icc a b,0 ≤ q x)
    (hs : ∀ x ∈ Set.Icc a b,∀ y ∈ Set.Icc a b,U y ≤ U x+(y-x)*q x)
    (x : ℝ) (hx : x ∈ Set.Icc a b) : (∫ z in x..b,q z)=U b-U x := by
  have hl := support_lipschitz a b hab q U hq hn hs
  have hc := (hl.mono (Set.uIcc_subset_Icc hx ⟨hab,le_rfl⟩)).absolutelyContinuousOnInterval
  have he : (∫ z in x..b,q z)=(∫ z in x..b,deriv U z) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hc.ae_differentiableAt,volume.ae_ne b] with z hd hzb hz
    have hz' : z ∈ Set.Ioc x b := by simpa only [Set.uIoc_of_le hx.2] using hz
    have hi : z ∈ Set.Ioo a b := ⟨hx.1.trans_lt hz'.1,lt_of_le_of_ne hz'.2 hzb⟩
    exact (support_derivative a b q U hs z hi (hd (Set.uIcc_of_le hx.2 ▸ ⟨hz'.1.le,hz'.2⟩))).symm
  rw [he,hc.integral_deriv_eq_sub]
lemma ic_payment_identity {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) (hIC : IC S M) (hIR : IR S M) (i : Fin n) :
    ∃ d : ℝ,0 ≤ d ∧ ∀ ci ∈ Set.Icc (S.a i) (S.b i),
      interimPay S M i ci=interimMse S M i ci-S.var+ci*interimEps S M i ci+
        (∫ z in ci..S.b i,interimEps S M i z)+d := by
  let U := fun t => interimCost S M i t t
  have hab : S.a i ≤ S.b i := (hS.2.2 i).2.1.le
  have hb : S.b i ∈ Set.Icc (S.a i) (S.b i) := ⟨hab,le_rfl⟩
  have hs : ∀ x ∈ Set.Icc (S.a i) (S.b i),∀ y ∈ Set.Icc (S.a i) (S.b i),
      U y ≤ U x+(y-x)*interimEps S M i x := by
    intro x hx y hy
    have h := hIC i y hy x hx
    dsimp [U]
    rw [interim_cost_affine S hS M hM i y y hy,
      interim_cost_affine S hS M hM i x y hx,
      interim_cost_affine S hS M hM i x x hx] at *
    linarith
  refine ⟨S.var-U (S.b i),sub_nonneg.mpr (hIR i (S.b i) hb),?_⟩
  intro ci hci
  have he := support_envelope (S.a i) (S.b i) hab (interimEps S M i) U
    (ic_antitone S hS M hM hIC i) (fun x hx => privacy_nonneg S hS M hM i x hx) hs ci hci
  dsimp [U] at *
  rw [interim_cost_affine S hS M hM i ci ci hci] at he
  linarith
end Queelius.PrivateTypeLaw
namespace PrivAcq.Central
 theorem _root_.prior_characterization {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : Admissible S M) :
    IC S M ∧ IR S M ↔
      ∀ i : Fin n, AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i)) ∧
        ∃ d : ℝ,0 ≤ d ∧ ∀ ci ∈ Set.Icc (S.a i) (S.b i),
          interimPay S M i ci=interimMse S M i ci-S.var+ci*interimEps S M i ci+
            (∫ z in ci..S.b i,interimEps S M i z)+d := by
  constructor
  · intro h i
    exact ⟨Queelius.PrivateTypeLaw.ic_antitone S hS M hM h.1 i,
      Queelius.PrivateTypeLaw.ic_payment_identity S hS M hM h.1 h.2 i⟩
  · exact Queelius.PrivateTypeLaw.payment_implies_ic_ir S hS M hM
end PrivAcq.Central

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma virtual_lower {n : ℕ} (S : Setting n) (hS : S.Standing) (i : Fin n)
    (c : ℝ) (hc : c ∈ Set.Icc (S.a i) (S.b i)) : S.a i ≤ S.ψ i c := by
  obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
  have hi : 0 ≤ S.cdf i c := by
    apply intervalIntegral.integral_nonneg hc.1
    intro x hx
    exact (hpos x ⟨hx.1,hx.2.trans hc.2⟩).le
  unfold Setting.ψ
  have hd := div_nonneg hi (hpos c hc).le
  linarith [hc.1]
lemma virtual_continuous {n : ℕ} (S : Setting n) (hS : S.Standing) (i : Fin n) :
    ContinuousOn (S.ψ i) (Set.Icc (S.a i) (S.b i)) := by
  obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
  have hint : IntegrableOn (S.f i) (Set.uIcc (S.a i) (S.b i)) := by
    simpa only [Set.uIcc_of_le hab.le] using hf.integrableOn_Icc
  have hc : ContinuousOn (S.cdf i) (Set.Icc (S.a i) (S.b i)) := by
    unfold Setting.cdf
    simpa only [Set.uIcc_of_le hab.le] using intervalIntegral.continuousOn_primitive_interval hint
  exact continuousOn_id.add (hc.div hf (fun x hx => (hpos x hx).ne'))
lemma types_compact {n : ℕ} (S : Setting n) : IsCompact S.types := by
  have he : S.types=Set.Icc S.a S.b := by
    ext c
    simp [Setting.types,Set.mem_pi,Set.mem_Icc,Pi.le_def,forall_and]
  rw [he]
  exact isCompact_Icc
lemma objective_cap {n : ℕ} (S : Setting n) (hS : S.Standing) :
    ∃ K : ℝ,0 < K ∧ ∀ c ∈ S.types,∀ y : Fin n → ℝ,IsOpt23 S c y → obj23 S c y ≤ K := by
  have ha : S.a ∈ S.types := fun i _ => ⟨le_rfl,(hS.2.2 i).2.1.le⟩
  have hs : ContinuousOn (fun c : Fin n → ℝ => ∑ i,S.ψ i (c i)) S.types := by
    apply continuousOn_finset_sum
    intro i _
    exact (virtual_continuous S hS i).comp (continuous_apply i).continuousOn
      (fun c hc => hc i (Set.mem_univ i))
  have hf : ContinuousOn (fun c => obj23 S c (fun _ => 1)) S.types := by
    unfold obj23
    apply ContinuousOn.add continuousOn_const
    simpa only [mul_one] using hs
  obtain ⟨cbar,hcbar,hmax⟩ := (types_compact S).exists_isMaxOn ⟨S.a,ha⟩ hf
  let K := max 1 (obj23 S cbar (fun _ => 1))
  refine ⟨K,lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left _ _),?_⟩
  intro c hc y hy
  have hone : (fun _ : Fin n => (1:ℝ)) ∈ feas23 := by
    refine ⟨fun _ => by norm_num,?_⟩
    simpa using (Nat.cast_pos.mpr hS.1 : (0:ℝ) < n)
  exact (hy.2 _ hone).trans ((hmax hc).trans (le_max_right _ _))
noncomputable def pointMse {n : ℕ} (S : Setting n) (y : Fin n → ℝ) : ℝ :=
  2/(∑ i,y i)^2+∑ i,(y i/(∑ j,y j))^2*S.var
lemma objective_decomposition {n : ℕ} (S : Setting n) (c y : Fin n → ℝ)
    (hy : y ∈ (feas23 : Set (Fin n → ℝ))) :
    obj23 S c y=((n:ℝ)+1)*pointMse S y+∑ i,S.ψ i (c i)*y i := by
  have hn : (∑ i,y i) ≠ 0 := hy.2.ne'
  unfold obj23 pointMse
  have he : ∑ i,(y i/(∑ j,y j))^2*S.var=
      (∑ i,y i^2*S.var)/(∑ j,y j)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [he]
  ring
lemma optimizer_bounds {n : ℕ} (S : Setting n) (hS : S.Standing) :
    ∃ B K : ℝ,0 < B ∧ 0 < K ∧ ∀ c ∈ S.types,∀ y : Fin n → ℝ,IsOpt23 S c y →
      (∀ i,0 ≤ y i ∧ y i ≤ B) ∧ 0 ≤ pointMse S y ∧ pointMse S y ≤ K := by
  classical
  obtain ⟨K,hK,hcap⟩ := objective_cap S hS
  obtain ⟨i0,_,hmin⟩ := Finset.exists_min_image Finset.univ S.a ⟨⟨0,hS.1⟩,Finset.mem_univ _⟩
  have hA : 0 < S.a i0 := (hS.2.2 i0).1
  refine ⟨K/S.a i0,K,div_pos hK hA,hK,?_⟩
  intro c hc y hy
  have hp (i : Fin n) : 0 ≤ S.ψ i (c i)*y i :=
    mul_nonneg ((hS.2.2 i).1.le.trans (virtual_lower S hS i (c i) (hc i (Set.mem_univ i)))) (hy.1.1 i)
  have hsum : 0 ≤ ∑ i,S.ψ i (c i)*y i := Finset.sum_nonneg (fun i _ => hp i)
  have hvar : 0 < S.var := hS.2.1
  have hm : 0 ≤ pointMse S y := by
    unfold pointMse
    positivity
  have hdec := objective_decomposition S c y hy.1
  have hobj := hcap c hc y hy
  have hnm := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) hm
  refine ⟨?_,hm,by nlinarith⟩
  intro i
  refine ⟨hy.1.1 i,?_⟩
  have hterm := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have hai : S.a i0 ≤ S.ψ i (c i) :=
    (hmin i (Finset.mem_univ i)).trans (virtual_lower S hS i (c i) (hc i (Set.mem_univ i)))
  have hb := mul_le_mul_of_nonneg_right hai (hy.1.1 i)
  apply (le_div_iff₀ hA).mpr
  nlinarith
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma optimal_allocation_admissible {n : ℕ} (S : Setting n) (hS : S.Standing)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) :
    AdmissibleAlloc S (optMech S ystar) := by
  classical
  let M := optMech S ystar
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨B,K,hB,hK,hbound⟩ := optimizer_bounds S hS
  have heps : Measurable M.ε := by simpa only [M,optMech,withPayments] using hmeas
  have heta : Measurable M.η := by dsimp [M,optMech,withPayments];fun_prop
  have hw : Measurable M.w := by dsimp [M,optMech,withPayments];fun_prop
  have hmse : Measurable (mse S M) := by unfold mse;fun_prop
  have hmse_eq (c : Fin n → ℝ) : mse S M c=pointMse S (ystar c) := rfl
  change AdmissibleAlloc S M
  refine ⟨hw,heta,heps,?_,⟨B,?_⟩,?_,?_⟩
  · intro c hc
    have hy := (hopt c hc).1
    change 0 < ∑ j,ystar c j ∧ (∀ i,0 ≤ ystar c i/(∑ j,ystar c j)) ∧
      (∑ i,ystar c i/(∑ j,ystar c j))=1 ∧
      ∀ i,(∑ j,ystar c j)*(ystar c i/(∑ j,ystar c j)) ≤ ystar c i
    refine ⟨hy.2,fun i => div_nonneg (hy.1 i) hy.2.le,?_,?_⟩
    · rw [← Finset.sum_div,div_self hy.2.ne']
    · intro i;exact le_of_eq (mul_div_cancel₀ _ hy.2.ne')
  · intro c hc i
    exact (hbound c hc (ystar c) (hopt c hc)).1 i |>.2
  · apply Integrable.of_mem_Icc 0 K hmse.aemeasurable
    filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
    rw [hmse_eq]
    exact (hbound c hc (ystar c) (hopt c hc)).2
  · intro i r hr
    have hfix : Measurable (fun c : Fin n → ℝ => mse S M (Function.update c i r)) :=
      hmse.comp (by fun_prop)
    apply Integrable.of_mem_Icc 0 K hfix.aemeasurable
    filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
    rw [hmse_eq]
    have hu := Queelius.PrivateTypeLaw.update_types S c hc i r hr
    exact (hbound _ hu _ (hopt _ hu)).2
end Queelius.PrivateOptimizer
namespace PrivAcq.Central
 theorem _root_.prior_allocation {n : ℕ} (S : Setting n) (hS : S.Standing) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) :
    AdmissibleAlloc S (optMech S ystar) := by
  exact Queelius.PrivateOptimizer.optimal_allocation_admissible S hS ystar hmeas hopt
end PrivAcq.Central



open PrivAcq.Central in
theorem _root_.shivm_monotone {n : ℕ} (S : Setting n) (hA1 : S.Assumption1)
    (c c' y y' : Fin n → ℝ) (hc : c ∈ S.types) (hc' : c' ∈ S.types) (i : Fin n)
    (hcc' : ∀ j : Fin n, j ≠ i → c j = c' j)
    (hy : IsOpt23 S c y) (hy' : IsOpt23 S c' y') :
    (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) ≤ 0 ∧ (c i < c' i → y' i ≤ y i) := by
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  unfold obj23 at h1 h2
  have expand : ∑ j, (S.ψ j (c j) - S.ψ j (c' j)) * (y j - y' j) =
      (∑ j, S.ψ j (c j) * y j) - (∑ j, S.ψ j (c j) * y' j)
        - (∑ j, S.ψ j (c' j) * y j) + (∑ j, S.ψ j (c' j) * y' j) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have single : ∑ j, (S.ψ j (c j) - S.ψ j (c' j)) * (y j - y' j) =
      (S.ψ i (c i) - S.ψ i (c' i)) * (y i - y' i) := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      rw [hcc' j hj, sub_self, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) ≤ 0 := by
    rw [mul_comm, ← single, expand]
    linarith
  refine ⟨key, fun hlt => ?_⟩
  have hci : c i ∈ Set.Icc (S.a i) (S.b i) := hc i (Set.mem_univ i)
  have hci' : c' i ∈ Set.Icc (S.a i) (S.b i) := hc' i (Set.mem_univ i)
  have hψ : S.ψ i (c i) < S.ψ i (c' i) := hA1 i hci hci' hlt
  by_contra hne
  push_neg at hne
  have : 0 < (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma selected_antitone {n : ℕ} (S : Setting n) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c))
    (c : Fin n → ℝ) (hc : c ∈ S.types) (i : Fin n) :
    AntitoneOn (fun r => ystar (Function.update c i r) i) (Set.Icc (S.a i) (S.b i)) := by
  intro a ha b hb hab
  by_cases he : a=b
  · subst b;exact le_rfl
  have hca := Queelius.PrivateTypeLaw.update_types S c hc i a ha
  have hcb := Queelius.PrivateTypeLaw.update_types S c hc i b hb
  have hsame : ∀ j : Fin n,j ≠ i → Function.update c i a j=Function.update c i b j := by
    intro j hj;simp [Function.update_of_ne hj]
  have h := shivm_monotone S hA1 (Function.update c i a) (Function.update c i b)
    (ystar (Function.update c i a)) (ystar (Function.update c i b)) hca hcb i hsame
    (hopt _ hca) (hopt _ hcb)
  exact h.2 (by simpa using lt_of_le_of_ne hab he)
lemma allocation_privacy_integrable {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : AdmissibleAlloc S M) (i : Fin n) (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    Integrable (fun c => M.ε (Function.update c i r) i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨hw,hη,hε,halloc,⟨B,hB⟩,hmse,hmsefix⟩ := hM
  have hm : Measurable (fun c => M.ε (Function.update c i r) i) := by fun_prop
  apply Integrable.of_mem_Icc 0 B hm.aemeasurable
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  have hcu := Queelius.PrivateTypeLaw.update_types S c hc i r hr
  obtain ⟨hp,hw0,hsum,hpriv⟩ := halloc _ hcu
  exact ⟨(mul_nonneg hp.le (hw0 i)).trans (hpriv i),hB _ hcu i⟩
lemma selected_interim_antitone {n : ℕ} (S : Setting n) (hS : S.Standing) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) (i : Fin n) :
    AntitoneOn (interimEps S (optMech S ystar) i) (Set.Icc (S.a i) (S.b i)) := by
  have halloc := optimal_allocation_admissible S hS ystar hmeas hopt
  intro a ha b hb hab
  change (∫ c,(optMech S ystar).ε (Function.update c i b) i ∂S.typeLaw) ≤
    ∫ c,(optMech S ystar).ε (Function.update c i a) i ∂S.typeLaw
  apply integral_mono_ae (allocation_privacy_integrable S hS _ halloc i b hb)
    (allocation_privacy_integrable S hS _ halloc i a ha)
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  exact selected_antitone S hA1 ystar hopt c hc i ha hb hab
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma parameter_interval_measurable {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ) (hf : Measurable f) (a b : A → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun c => ∫ z in a c..b c,f (c,z)) := by
  classical
  let F : A × ℝ → ℝ := fun x => if a x.1 < x.2 ∧ x.2 ≤ b x.1 then f x else 0
  let G : A × ℝ → ℝ := fun x => if b x.1 < x.2 ∧ x.2 ≤ a x.1 then f x else 0
  have hF : Measurable F := hf.ite
    ((measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))) measurable_const
  have hG : Measurable G := hf.ite
    ((measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst))) measurable_const
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub
    (hG.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert h using 1
  ext c
  change (∫ z in a c..b c,f (c,z))=(∫ z,F (c,z))-(∫ z,G (c,z))
  rw [intervalIntegral]
  congr 1
  · rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by simp [F,Set.indicator,Set.mem_Ioc])
  · rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by simp [G,Set.indicator,Set.mem_Ioc])
lemma allocation_tail_measurable {n : ℕ} (S : Setting n) (M : Mech n)
    (hM : AdmissibleAlloc S M) (i : Fin n) :
    Measurable (fun c => ∫ z in c i..S.b i,M.ε (Function.update c i z) i) := by
  have hup : Measurable (fun x : (Fin n → ℝ) × ℝ => Function.update x.1 i x.2) := by fun_prop
  have hf := (measurable_pi_apply i).comp (hM.2.2.1.comp hup)
  exact parameter_interval_measurable _ hf (fun c => c i) (fun _ => S.b i)
    (by fun_prop) (by fun_prop)
lemma payments_measurable {n : ℕ} (S : Setting n) (M : Mech n)
    (hM : AdmissibleAlloc S M) : Measurable (withPayments S M).t := by
  have hw := hM.1
  have heta := hM.2.1
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (mse S M) := by unfold mse; fun_prop
  exact ((hm.sub measurable_const).add
    ((measurable_pi_apply i).mul ((measurable_pi_apply i).comp hM.2.2.1))).add
      (allocation_tail_measurable S M hM i)
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma allocation_uniform_bounds {n : ℕ} (S : Setting n) (M : Mech n)
    (hM : AdmissibleAlloc S M) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ c ∈ S.types,∀ i,0 ≤ M.ε c i ∧ M.ε c i ≤ B := by
  obtain ⟨B,hB⟩ := hM.2.2.2.2.1
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro c hc i
  obtain ⟨heta,hw,hsum,hpriv⟩ := hM.2.2.2.1 c hc
  exact ⟨(mul_nonneg heta.le (hw i)).trans (hpriv i),(hB c hc i).trans (le_max_right _ _)⟩
lemma allocation_tail_bound {n : ℕ} (S : Setting n) (M : Mech n)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ c ∈ S.types,∀ i,0 ≤ M.ε c i ∧ M.ε c i ≤ B)
    (c : Fin n → ℝ) (hc : c ∈ S.types) (i : Fin n) :
    ‖∫ z in c i..S.b i,M.ε (Function.update c i z) i‖ ≤ B*(S.b i-S.a i) := by
  have hci : S.a i ≤ c i ∧ c i ≤ S.b i := hc i (Set.mem_univ i)
  apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans
  · rw [abs_of_nonneg (sub_nonneg.mpr hci.2)]
    exact mul_le_mul_of_nonneg_left (by linarith) hB
  · intro z hz
    rw [Set.uIoc_of_le hci.2] at hz
    have hu := Queelius.PrivateTypeLaw.update_types S c hc i z ⟨hci.1.trans hz.1.le,hz.2⟩
    obtain ⟨h0,h1⟩ := hb _ hu i
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0] using h1
lemma allocation_tail_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    Integrable (fun c => ∫ z in c i..S.b i,M.ε (Function.update c i z) i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨B,hB,hb⟩ := allocation_uniform_bounds S M hM
  apply Integrable.of_bound (allocation_tail_measurable S M hM i).aestronglyMeasurable
    (B*(S.b i-S.a i))
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  exact allocation_tail_bound S M B hB hb c hc i
lemma allocation_tail_fixed_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n)
    (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    Integrable (fun c => ∫ z in r..S.b i,M.ε (Function.update c i z) i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨B,hB,hb⟩ := allocation_uniform_bounds S M hM
  have hm := (allocation_tail_measurable S M hM i).comp
    (show Measurable (fun c : Fin n → ℝ => Function.update c i r) by fun_prop)
  have he : (fun c => ∫ z in (Function.update c i r) i..S.b i,
      M.ε (Function.update (Function.update c i r) i z) i)=
      (fun c => ∫ z in r..S.b i,M.ε (Function.update c i z) i) := by
    funext c;simp only [Function.update_self,Function.update_idem]
  change Measurable (fun c => ∫ z in (Function.update c i r) i..S.b i, M.ε (Function.update (Function.update c i r) i z) i) at hm
  rw [he] at hm
  apply Integrable.of_bound hm.aestronglyMeasurable (B*(S.b i-S.a i))
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  simpa only [Function.update_self,Function.update_idem] using
    allocation_tail_bound S M B hB hb (Function.update c i r)
      (Queelius.PrivateTypeLaw.update_types S c hc i r hr) i
lemma allocation_weighted_privacy_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    Integrable (fun c => c i*M.ε c i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨B,hB,hb⟩ := allocation_uniform_bounds S M hM
  have hm := (measurable_pi_apply i).mul ((measurable_pi_apply i).comp hM.2.2.1)
  apply Integrable.of_mem_Icc 0 (S.b i*B) hm.aemeasurable
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  have hci : S.a i ≤ c i ∧ c i ≤ S.b i := hc i (Set.mem_univ i)
  have h0 : 0 ≤ c i := (hS.2.2 i).1.le.trans hci.1
  obtain ⟨he0,heB⟩ := hb c hc i
  exact ⟨mul_nonneg h0 he0,mul_le_mul hci.2 heB he0 (h0.trans hci.2)⟩
lemma payments_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    Integrable (fun c => (withPayments S M).t c i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  exact ((hM.2.2.2.2.2.1.sub (integrable_const S.var)).add
    (allocation_weighted_privacy_integrable S hS M hM i)).add
      (allocation_tail_integrable S hS M hM i)
lemma payments_fixed_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n)
    (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    Integrable (fun c => (withPayments S M).t (Function.update c i r) i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  have hi := ((hM.2.2.2.2.2.2 i r hr).sub (integrable_const S.var)).add
    ((allocation_privacy_integrable S hS M hM i r hr).const_mul r)
  have hh := hi.add (allocation_tail_fixed_integrable S hS M hM i r hr)
  convert! hh using 1 <;> (ext c; simp [withPayments])
lemma withPayments_admissible {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) : Admissible S (withPayments S M) := by
  exact ⟨hM,payments_measurable S M hM,payments_integrable S hS M hM,
    payments_fixed_integrable S hS M hM⟩
lemma optimal_mechanism_admissible {n : ℕ} (S : Setting n) (hS : S.Standing)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) : Admissible S (optMech S ystar) := by
  have h := withPayments_admissible S hS (optMech S ystar)
    (optimal_allocation_admissible S hS ystar hmeas hopt)
  exact h
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma allocation_tail_fubini {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n)
    (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    (∫ c,(∫ z in r..S.b i,M.ε (Function.update c i z) i) ∂S.typeLaw)=
      ∫ z in r..S.b i,interimEps S M i z := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  let ν := volume.restrict (Set.Ioc r (S.b i))
  obtain ⟨B,hB,hb⟩ := allocation_uniform_bounds S M hM
  have hup : Measurable (fun x : (Fin n → ℝ) × ℝ => Function.update x.1 i x.2) := by fun_prop
  have hf := (measurable_pi_apply i).comp (hM.2.2.1.comp hup)
  have hi : Integrable (fun x : (Fin n → ℝ) × ℝ => M.ε (Function.update x.1 i x.2) i)
      (S.typeLaw.prod ν) := by
    apply Integrable.of_mem_Icc 0 B hf.aemeasurable
    have hs : ∀ᵐ x ∂S.typeLaw.prod ν,x ∈ S.types ×ˢ Set.Ioc r (S.b i) := by
      apply (Measure.ae_prod_mem_iff_ae_ae_mem
        ((Queelius.PrivateTypeLaw.types_measurable S).prod measurableSet_Ioc)).mpr
      filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      exact ⟨hc,hz⟩
    filter_upwards [hs] with x hx
    exact hb _ (Queelius.PrivateTypeLaw.update_types S x.1 hx.1 i x.2
      ⟨hr.1.trans hx.2.1.le,hx.2.2⟩) i
  simp_rw [intervalIntegral.integral_of_le hr.2]
  exact integral_integral_swap hi
lemma interim_payment_identity {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n)
    (r : ℝ) (hr : r ∈ Set.Icc (S.a i) (S.b i)) :
    interimPay S (withPayments S M) i r =
      interimMse S M i r-S.var+r*interimEps S M i r+
        ∫ z in r..S.b i,interimEps S M i z := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  have hm := hM.2.2.2.2.2.2 i r hr
  have he := (allocation_privacy_integrable S hS M hM i r hr).const_mul r
  have ht := allocation_tail_fixed_integrable S hS M hM i r hr
  change (∫ c, (withPayments S M).t (Function.update c i r) i ∂S.typeLaw)=_
  simp only [withPayments,Function.update_self,Function.update_idem]
  rw [integral_add (f := fun c => mse S M (Function.update c i r)-S.var+r*M.ε (Function.update c i r) i) (g := fun c => ∫ z in r..S.b i,M.ε (Function.update c i z) i) (by convert! (hm.sub (integrable_const S.var)).add he using 1) ht,
    integral_add (f := fun c => mse S M (Function.update c i r)-S.var) (g := fun c => r*M.ε (Function.update c i r) i) (by convert! hm.sub (integrable_const S.var) using 1) he,
    integral_sub hm (integrable_const S.var),integral_const_mul,
    integral_const,allocation_tail_fubini S hS M hM i r hr]
  simp [interimMse,interimEps]
lemma withPayments_ic_ir {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M)
    (hq : ∀ i,AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i))) :
    IC S (withPayments S M) ∧ IR S (withPayments S M) := by
  apply Queelius.PrivateTypeLaw.payment_implies_ic_ir S hS _
    (withPayments_admissible S hS M hM)
  intro i
  refine ⟨hq i,0,le_rfl,?_⟩
  intro r hr
  simpa only [interimMse,interimEps,withPayments,mse,add_zero] using interim_payment_identity S hS M hM i r hr
lemma optimal_mechanism_ic_ir {n : ℕ} (S : Setting n) (hS : S.Standing)
    (hA1 : S.Assumption1) (ystar : (Fin n → ℝ) → Fin n → ℝ)
    (hmeas : Measurable ystar) (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) :
    IC S (optMech S ystar) ∧ IR S (optMech S ystar) := by
  exact withPayments_ic_ir S hS (optMech S ystar)
    (optimal_allocation_admissible S hS ystar hmeas hopt)
    (selected_interim_antitone S hS hA1 ystar hmeas hopt)
end Queelius.PrivateOptimizer

namespace PrivAcq.Central
theorem _root_.prior_mechanism {n : ℕ} (S : Setting n) (hS : S.Standing) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c)) :
    Admissible S (optMech S ystar) ∧ IC S (optMech S ystar) ∧ IR S (optMech S ystar) := by
  exact ⟨Queelius.PrivateOptimizer.optimal_mechanism_admissible S hS ystar hmeas hopt,
    Queelius.PrivateOptimizer.optimal_mechanism_ic_ir S hS hA1 ystar hmeas hopt⟩
end PrivAcq.Central

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
noncomputable def allocationY {n : ℕ} (M : Mech n) (c : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.η c*M.w c i
noncomputable def virtualPoint {n : ℕ} (S : Setting n) (M : Mech n) (c : Fin n → ℝ) : ℝ :=
  ((n:ℝ)+1)*mse S M c+∑ i,S.ψ i (c i)*M.ε c i
noncomputable def virtualObjective {n : ℕ} (S : Setting n) (M : Mech n) : ℝ :=
  ∫ c,virtualPoint S M c ∂S.typeLaw
lemma allocationY_feasible {n : ℕ} (S : Setting n) (M : Mech n) (hM : AdmissibleAlloc S M)
    (c : Fin n → ℝ) (hc : c ∈ S.types) :
    allocationY M c ∈ (feas23 : Set (Fin n → ℝ)) ∧ ∑ i,allocationY M c i=M.η c := by
  obtain ⟨heta,hw,hsum,hpriv⟩ := hM.2.2.2.1 c hc
  have he : (∑ i,allocationY M c i)=M.η c := by
    unfold allocationY;rw [← Finset.mul_sum,hsum,mul_one]
  exact ⟨⟨fun i => mul_nonneg heta.le (hw i),by rw [he];exact heta⟩,he⟩
lemma allocationY_mse {n : ℕ} (S : Setting n) (M : Mech n) (hM : AdmissibleAlloc S M)
    (c : Fin n → ℝ) (hc : c ∈ S.types) : pointMse S (allocationY M c)=mse S M c := by
  have he := (allocationY_feasible S M hM c hc).2
  have heta := (hM.2.2.2.1 c hc).1
  unfold pointMse mse
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [allocationY,mul_div_cancel_left₀ _ heta.ne']
lemma pointwise_virtual_optimal {n : ℕ} (S : Setting n) (hS : S.Standing)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c))
    (M : Mech n) (hM : AdmissibleAlloc S M) (c : Fin n → ℝ) (hc : c ∈ S.types) :
    virtualPoint S (optMech S ystar) c ≤ virtualPoint S M c := by
  have hy := allocationY_feasible S M hM c hc
  have hoptc := hopt c hc
  have hm : mse S (optMech S ystar) c=pointMse S (ystar c) := rfl
  have hε : (optMech S ystar).ε c=ystar c := rfl
  unfold virtualPoint
  rw [hm,hε,← objective_decomposition S c (ystar c) hoptc.1]
  apply (hoptc.2 _ hy.1).trans
  rw [objective_decomposition S c (allocationY M c) hy.1,allocationY_mse S M hM c hc]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left ((hM.2.2.2.1 c hc).2.2.2 i)
  exact (hS.2.2 i).1.le.trans (virtual_lower S hS i (c i) (hc i (Set.mem_univ i)))
lemma weighted_virtual_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    Integrable (fun c => S.ψ i (c i)*M.ε c i) S.typeLaw := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  obtain ⟨B,hB,hbounds⟩ := allocation_uniform_bounds S M hM
  have hψ : ContinuousOn (fun c : Fin n → ℝ => S.ψ i (c i)) S.types :=
    (virtual_continuous S hS i).comp (continuous_apply i).continuousOn
      (fun c hc => hc i (Set.mem_univ i))
  have hψm := hψ.aemeasurable (μ := S.typeLaw) (Queelius.PrivateTypeLaw.types_measurable S)
  rw [Measure.restrict_eq_self_of_ae_mem (Queelius.PrivateTypeLaw.ae_types S hS)] at hψm
  have he := ((measurable_pi_apply i).comp hM.2.2.1).aemeasurable (μ := S.typeLaw)
  have hab := (hS.2.2 i).2.1
  obtain ⟨r,hr,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (S.a i) (S.b i)).Nonempty from ⟨S.a i,le_rfl,hab.le⟩)
    (virtual_continuous S hS i)
  apply Integrable.of_mem_Icc 0 (S.ψ i r*B) (hψm.mul he)
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  have hci := hc i (Set.mem_univ i)
  have hψ0 : 0 ≤ S.ψ i (c i) := (hS.2.2 i).1.le.trans (virtual_lower S hS i (c i) hci)
  obtain ⟨he0,heB⟩ := hbounds c hc i
  exact ⟨mul_nonneg hψ0 he0,mul_le_mul (hmax hci) heB he0 (hψ0.trans (hmax hci))⟩
lemma virtualPoint_integrable {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) : Integrable (virtualPoint S M) S.typeLaw := by
  have hs : Integrable (fun c => ∑ i,S.ψ i (c i)*M.ε c i) S.typeLaw :=
    integrable_finset_sum _ (fun i _ => weighted_virtual_integrable S hS M hM i)
  exact ((hM.2.2.2.2.2.1.const_mul ((n:ℝ)+1)).add hs)
lemma virtual_global_optimal {n : ℕ} (S : Setting n) (hS : S.Standing)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types,IsOpt23 S c (ystar c))
    (M : Mech n) (hM : AdmissibleAlloc S M) :
    virtualObjective S (optMech S ystar) ≤ virtualObjective S M := by
  apply integral_mono_ae
    (virtualPoint_integrable S hS _ (optimal_allocation_admissible S hS ystar hmeas hopt))
    (virtualPoint_integrable S hS M hM)
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  exact pointwise_virtual_optimal S hS ystar hopt M hM c hc
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open MeasureTheory Set
lemma cumulative_tail_fubini (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : IntegrableOn f (Icc a b)) (hg : IntegrableOn g (Icc a b)) :
    (∫ r in a..b,f r*(∫ z in r..b,g z))=
      ∫ z in a..b,(∫ r in a..z,f r)*g z := by
  classical
  let μ := volume.restrict (Icc a b)
  let F : ℝ × ℝ → ℝ := fun x => if x.1 ≤ x.2 then f x.1*g x.2 else 0
  have hF : Integrable F (μ.prod μ) := by
    exact (hf.mul_prod hg).indicator (measurableSet_le measurable_fst measurable_snd)
  have hrow (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ z,F (r,z) ∂μ)=f r*(∫ z in r..b,g z) := by
    calc
      _ = f r*(∫ z,(Ici r).indicator g z ∂μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by simp [F,Set.indicator_apply])
      _ = f r*(∫ z in Icc r b,g z) := by
        rw [integral_indicator measurableSet_Ici]
        change f r*(∫ z,g z ∂(volume.restrict (Icc a b)).restrict (Ici r))=_
        rw [Measure.restrict_restrict measurableSet_Ici]
        rw [show Ici r ∩ Icc a b=Icc r b by
          ext z
          simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc]
          constructor
          · intro hz;exact ⟨hz.1,hz.2.2⟩
          · intro hz;exact ⟨hz.1,hr.1.trans hz.1,hz.2⟩]
      _ = _ := by rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hr.2]
  have hcol (z : ℝ) (hz : z ∈ Icc a b) :
      (∫ r,F (r,z) ∂μ)=(∫ r in a..z,f r)*g z := by
    calc
      _ = (∫ r,(Iic z).indicator f r ∂μ)*g z := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ (fun r => by simp [F,Set.indicator_apply])
      _ = (∫ r in Icc a z,f r)*g z := by
        rw [integral_indicator measurableSet_Iic]
        change (∫ r,f r ∂(volume.restrict (Icc a b)).restrict (Iic z))*g z=_
        rw [Measure.restrict_restrict measurableSet_Iic]
        rw [show Iic z ∩ Icc a b=Icc a z by
          ext r
          simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
          constructor
          · intro hr;exact ⟨hr.2.1,hr.1⟩
          · intro hr;exact ⟨hr.2,hr.1,hr.2.trans hz.2⟩]
      _ = _ := by rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hz.1]
  rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc]
  change (∫ r,f r*(∫ z in r..b,g z) ∂μ)=(∫ z,(∫ r in a..z,f r)*g z ∂μ)
  calc
    _ = ∫ r,∫ z,F (r,z) ∂μ ∂μ := integral_congr_ae
      ((ae_restrict_mem measurableSet_Icc).mono (fun r hr => (hrow r hr).symm))
    _ = ∫ z,∫ r,F (r,z) ∂μ ∂μ := integral_integral_swap hF
    _ = _ := integral_congr_ae
      ((ae_restrict_mem measurableSet_Icc).mono (fun z hz => hcol z hz))
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open MeasureTheory Set PrivAcq.Central
lemma density_tail_identity (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hfpos : ∀ r ∈ Icc a b,0 < f r)
    (hg : IntegrableOn g (Icc a b)) :
    (∫ r,(∫ z in r..b,g z) ∂(volume.restrict (Icc a b)).withDensity (fun r => ENNReal.ofReal (f r)))=
      ∫ r,((∫ x in a..r,f x)/f r)*g r
        ∂(volume.restrict (Icc a b)).withDensity (fun r => ENNReal.ofReal (f r)) := by
  have hfm := (hf.aemeasurable (μ := volume) measurableSet_Icc).ennreal_ofReal
  have hfinite : ∀ᵐ r ∂volume.restrict (Icc a b),ENNReal.ofReal (f r) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hfm hfinite,
    integral_withDensity_eq_integral_toReal_smul₀ hfm hfinite]
  have heL : (∫ r,(ENNReal.ofReal (f r)).toReal • (∫ z in r..b,g z) ∂volume.restrict (Icc a b))=
      ∫ r in a..b,f r*(∫ z in r..b,g z) := by
    rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [ENNReal.toReal_ofReal (hfpos r hr).le,smul_eq_mul]
  have heR : (∫ r,(ENNReal.ofReal (f r)).toReal • (((∫ x in a..r,f x)/f r)*g r)
      ∂volume.restrict (Icc a b))=∫ r in a..b,(∫ x in a..r,f x)*g r := by
    rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [ENNReal.toReal_ofReal (hfpos r hr).le,smul_eq_mul]
    field_simp [(hfpos r hr).ne']
  rw [heL,heR]
  exact cumulative_tail_fubini a b hab f g hf.integrableOn_Icc hg
lemma sensitivity_tail_identity {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (c : Fin n → ℝ) (hc : c ∈ S.types)
    (i : Fin n) :
    (∫ r,(∫ z in r..S.b i,M.ε (Function.update c i z) i)
      ∂(volume.restrict (Icc (S.a i) (S.b i))).withDensity (fun r => ENNReal.ofReal (S.f i r)))=
      ∫ r,(S.cdf i r/S.f i r)*M.ε (Function.update c i r) i
        ∂(volume.restrict (Icc (S.a i) (S.b i))).withDensity (fun r => ENNReal.ofReal (S.f i r)) := by
  have hmeas : Measurable (fun z => M.ε (Function.update c i z) i) :=
    (measurable_pi_apply i).comp (hM.2.2.1.comp (by fun_prop))
  obtain ⟨B,hB,hbound⟩ := allocation_uniform_bounds S M hM
  have hg : IntegrableOn (fun z => M.ε (Function.update c i z) i) (Icc (S.a i) (S.b i)) := by
    apply Integrable.of_mem_Icc 0 B hmeas.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hbound _ (Queelius.PrivateTypeLaw.update_types S c hc i z hz) i
  exact density_tail_identity (S.a i) (S.b i) (hS.2.2 i).2.1.le
    (S.f i) (fun z => M.ε (Function.update c i z) i) (hS.2.2 i).2.2.1 (hS.2.2 i).2.2.2.1 hg
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open MeasureTheory
lemma product_resampling (n : ℕ) (ν : Fin (n+1) → Measure ℝ) [∀ i,IsProbabilityMeasure (ν i)]
    (F : (Fin (n+1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi ν)) (i : Fin (n+1)) :
    (∫ c,(∫ r,F (Function.update c i r) ∂ν i) ∂Measure.pi ν)=∫ c,F c ∂Measure.pi ν := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := measurePreserving_piFinSuccAbove ν i
  have hs := MeasurePreserving.symm e hp
  let G := fun v : ℝ × (Fin n → ℝ) => F (e.symm v)
  have hG : Integrable G ((ν i).prod (Measure.pi fun j => ν (i.succAbove j))) :=
    hs.integrable_comp_of_integrable hF
  have he (a : ℝ) (x : Fin n → ℝ) (r : ℝ) :
      Function.update (e.symm (a,x)) i r=e.symm (r,x) := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    exact Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i a r x
  calc
    _ = ∫ v,(∫ r,F (Function.update (e.symm v) i r) ∂ν i)
        ∂(ν i).prod (Measure.pi fun j => ν (i.succAbove j)) :=
      (hs.integral_comp' (fun c => ∫ r,F (Function.update c i r) ∂ν i)).symm
    _ = ∫ v,(∫ r,G (r,v.2) ∂ν i)
        ∂(ν i).prod (Measure.pi fun j => ν (i.succAbove j)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by simp only [he,G])
    _ = ∫ x,∫ r,G (r,x) ∂ν i ∂Measure.pi fun j => ν (i.succAbove j) := by
      simpa using (integral_fun_snd (μ := ν i)
        (ν := Measure.pi fun j => ν (i.succAbove j)) (fun x => ∫ r,G (r,x) ∂ν i))
    _ = ∫ v,G v ∂(ν i).prod (Measure.pi fun j => ν (i.succAbove j)) :=
      (integral_prod_symm G hG).symm
    _ = _ := hs.integral_comp' F
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open MeasureTheory PrivAcq.Central
lemma typeLaw_resampling {n : ℕ} (S : Setting n) (hS : S.Standing)
    (F : (Fin n → ℝ) → ℝ) (hF : Integrable F S.typeLaw) (i : Fin n) :
    (∫ c,(∫ r,F (Function.update c i r)
      ∂(volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity (fun r => ENNReal.ofReal (S.f i r)))
        ∂S.typeLaw)=∫ c,F c ∂S.typeLaw := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let ν := fun j : Fin (n+1) => (volume.restrict (Set.Icc (S.a j) (S.b j))).withDensity
      (fun r => ENNReal.ofReal (S.f j r))
    have hp (j : Fin (n+1)) : IsProbabilityMeasure (ν j) := by
      obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 j
      exact ⟨Queelius.PrivateTypeLaw.compact_density_mass (S.a j) (S.b j) hab.le
        (S.f j) hf (fun r hr => (hpos r hr).le) hI⟩
    letI : ∀ j,IsProbabilityMeasure (ν j) := hp
    exact product_resampling n ν F hF i
lemma expected_tail_virtual_ratio {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    (∫ c,(∫ z in c i..S.b i,M.ε (Function.update c i z) i) ∂S.typeLaw)=
      ∫ c,(S.cdf i (c i)/S.f i (c i))*M.ε c i ∂S.typeLaw := by
  let T := fun c : Fin n → ℝ => ∫ z in c i..S.b i,M.ε (Function.update c i z) i
  let R := fun c : Fin n → ℝ => (S.cdf i (c i)/S.f i (c i))*M.ε c i
  have hT : Integrable T S.typeLaw := allocation_tail_integrable S hS M hM i
  have hR : Integrable R S.typeLaw := by
    have hh := (weighted_virtual_integrable S hS M hM i).sub
      (allocation_weighted_privacy_integrable S hS M hM i)
    convert! hh using 1
    ext c
    unfold R Setting.ψ
    simp only [Pi.sub_apply]
    ring
  have ht := typeLaw_resampling S hS T hT i
  have hr := typeLaw_resampling S hS R hR i
  change (∫ c,T c ∂S.typeLaw)=(∫ c,R c ∂S.typeLaw)
  rw [← ht,← hr]
  apply integral_congr_ae
  filter_upwards [Queelius.PrivateTypeLaw.ae_types S hS] with c hc
  simpa only [T,R,Function.update_self,Function.update_idem] using
    sensitivity_tail_identity S hS M hM c hc i
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open MeasureTheory PrivAcq.Central
lemma expected_payment_virtual {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) (i : Fin n) :
    (∫ c,(withPayments S M).t c i ∂S.typeLaw)=
      (∫ c,mse S M c ∂S.typeLaw)-S.var+(∫ c,S.ψ i (c i)*M.ε c i ∂S.typeLaw) := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  have hm := hM.2.2.2.2.2.1
  have hc := allocation_weighted_privacy_integrable S hS M hM i
  have ht := allocation_tail_integrable S hS M hM i
  have hr : Integrable (fun c => (S.cdf i (c i)/S.f i (c i))*M.ε c i) S.typeLaw := by
    convert! (weighted_virtual_integrable S hS M hM i).sub hc using 1
    ext c;unfold Setting.ψ;simp only [Pi.sub_apply];ring
  have he : (∫ c,S.ψ i (c i)*M.ε c i ∂S.typeLaw)=
      (∫ c,c i*M.ε c i ∂S.typeLaw)+
        (∫ c,(S.cdf i (c i)/S.f i (c i))*M.ε c i ∂S.typeLaw) := by
    rw [← integral_add hc hr]
    apply integral_congr_ae
    exact ae_of_all _ (fun c => by unfold Setting.ψ;ring)
  change (∫ c,mse S M c-S.var+c i*M.ε c i+
    (∫ z in c i..S.b i,M.ε (Function.update c i z) i) ∂S.typeLaw)=_
  rw [integral_add (f := fun c => mse S M c-S.var+c i*M.ε c i)
    (g := fun c => ∫ z in c i..S.b i,M.ε (Function.update c i z) i)
    (by convert! (hm.sub (integrable_const S.var)).add hc using 1) ht,
    integral_add (f := fun c => mse S M c-S.var) (g := fun c => c i*M.ε c i)
      (by convert! hm.sub (integrable_const S.var) using 1) hc,
    integral_sub hm (integrable_const S.var),integral_const,
    expected_tail_virtual_ratio S hS M hM i,he]
  simp
  <;> ring
lemma objective_withPayments {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : AdmissibleAlloc S M) :
    objective S (withPayments S M)=virtualObjective S M-(n:ℝ)*S.var := by
  letI := Queelius.PrivateTypeLaw.typeLaw_probability S hS
  have hm := hM.2.2.2.2.2.1
  have hp := integrable_finset_sum Finset.univ (fun i _ => payments_integrable S hS M hM i)
  have hv := integrable_finset_sum Finset.univ (fun i _ => weighted_virtual_integrable S hS M hM i)
  unfold objective virtualObjective virtualPoint
  change (∫ c,mse S M c+∑ i,(withPayments S M).t c i ∂S.typeLaw)=_
  rw [integral_add hm hp,integral_finset_sum _ (fun i _ => payments_integrable S hS M hM i)]
  simp_rw [expected_payment_virtual S hS M hM]
  rw [integral_add (hm.const_mul ((n:ℝ)+1)) hv,
    integral_const_mul,integral_finset_sum _ (fun i _ => weighted_virtual_integrable S hS M hM i),
    Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
end Queelius.PrivateOptimizer

namespace Queelius.PrivateOptimizer
open PrivAcq.Central MeasureTheory
lemma payment_objective_reduction {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
    (hM : AdmissibleAlloc S M)
    (hq : ∀ i : Fin n,AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i))) :
    Admissible S (withPayments S M) ∧ IC S (withPayments S M) ∧ IR S (withPayments S M) ∧
      objective S (withPayments S M)=
        (∫ c,(((n:ℝ)+1)*mse S M c+∑ i,M.ε c i*S.ψ i (c i)) ∂S.typeLaw)-(n:ℝ)*S.var := by
  refine ⟨withPayments_admissible S hS M hM,(withPayments_ic_ir S hS M hM hq).1,
    (withPayments_ic_ir S hS M hM hq).2,?_⟩
  simpa only [virtualObjective,virtualPoint,mul_comm] using objective_withPayments S hS M hM
end Queelius.PrivateOptimizer
namespace PrivAcq.Central
open MeasureTheory
theorem _root_.prior_constructive {n : ℕ} (S : Setting n) (hS : S.Standing) :
    ∀ M : Mech n,AdmissibleAlloc S M →
      (∀ i : Fin n,AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i))) →
      Admissible S (withPayments S M) ∧ IC S (withPayments S M) ∧ IR S (withPayments S M) ∧
        objective S (withPayments S M)=
          (∫ c,(((n:ℝ)+1)*mse S M c+∑ i,M.ε c i*S.ψ i (c i)) ∂S.typeLaw)-(n:ℝ)*S.var := by
  exact Queelius.PrivateOptimizer.payment_objective_reduction S hS
end PrivAcq.Central

namespace Queelius.PrivateOptimizer
open MeasureTheory PrivAcq.Central
lemma product_interim (n : ℕ) (ν : Fin (n+1) → Measure ℝ) [∀ i,IsProbabilityMeasure (ν i)]
    (F : (Fin (n+1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi ν)) (i : Fin (n+1)) :
    Integrable (fun r => ∫ c,F (Function.update c i r) ∂Measure.pi ν) (ν i) ∧
    (∫ r,(∫ c,F (Function.update c i r) ∂Measure.pi ν) ∂ν i)=∫ c,F c ∂Measure.pi ν := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := measurePreserving_piFinSuccAbove ν i
  have hs := MeasurePreserving.symm e hp
  let G := fun v : ℝ × (Fin n → ℝ) => F (e.symm v)
  have hG : Integrable G ((ν i).prod (Measure.pi fun j => ν (i.succAbove j))) :=
    hs.integrable_comp_of_integrable hF
  have he (a : ℝ) (x : Fin n → ℝ) (r : ℝ) :
      Function.update (e.symm (a,x)) i r=e.symm (r,x) := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    exact Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i a r x
  have hinter (r : ℝ) : (∫ c,F (Function.update c i r) ∂Measure.pi ν)=
      ∫ x,G (r,x) ∂Measure.pi fun j => ν (i.succAbove j) := by
    calc
      _ = ∫ v,F (Function.update (e.symm v) i r)
          ∂(ν i).prod (Measure.pi fun j => ν (i.succAbove j)) :=
        (hs.integral_comp' (fun c => F (Function.update c i r))).symm
      _ = ∫ v,G (r,v.2) ∂(ν i).prod (Measure.pi fun j => ν (i.succAbove j)) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun v => by simpa only [G,he] using (congrArg F (he v.1 v.2 r)))
      _ = _ := by simpa using (integral_fun_snd (μ := ν i)
        (ν := Measure.pi fun j => ν (i.succAbove j)) (fun x => G (r,x)))
  simp_rw [hinter]
  exact ⟨hG.integral_prod_left,(integral_prod G hG).symm.trans (hs.integral_comp' F)⟩
lemma typeLaw_interim {n : ℕ} (S : Setting n) (hS : S.Standing)
    (F : (Fin n → ℝ) → ℝ) (hF : Integrable F S.typeLaw) (i : Fin n) :
    let ν := (volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity
      (fun r => ENNReal.ofReal (S.f i r))
    Integrable (fun r => ∫ c,F (Function.update c i r) ∂S.typeLaw) ν ∧
    (∫ r,(∫ c,F (Function.update c i r) ∂S.typeLaw) ∂ν)=∫ c,F c ∂S.typeLaw := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let ν := fun j : Fin (n+1) => (volume.restrict (Set.Icc (S.a j) (S.b j))).withDensity
      (fun r => ENNReal.ofReal (S.f j r))
    have hp (j : Fin (n+1)) : IsProbabilityMeasure (ν j) := by
      obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 j
      exact ⟨Queelius.PrivateTypeLaw.compact_density_mass (S.a j) (S.b j) hab.le
        (S.f j) hf (fun r hr => (hpos r hr).le) hI⟩
    letI : ∀ j,IsProbabilityMeasure (ν j) := hp
    exact product_interim n ν F hF i
lemma expected_payment_minimal {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : Admissible S M) (hIC : IC S M) (hIR : IR S M) (i : Fin n) :
    (∫ c,(withPayments S M).t c i ∂S.typeLaw) ≤ ∫ c,M.t c i ∂S.typeLaw := by
  obtain ⟨d,hd,hid⟩ := Queelius.PrivateTypeLaw.ic_payment_identity S hS M hM hIC hIR i
  let ν := (volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity
    (fun r => ENNReal.ofReal (S.f i r))
  obtain ⟨ha,hab,hf,hpos,hI⟩ := hS.2.2 i
  letI : IsProbabilityMeasure ν := ⟨Queelius.PrivateTypeLaw.compact_density_mass
    (S.a i) (S.b i) hab.le (S.f i) hf (fun r hr => (hpos r hr).le) hI⟩
  have hsupp : ∀ᵐ r ∂ν,r ∈ Set.Icc (S.a i) (S.b i) := by
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
  have hpay := typeLaw_interim S hS (fun c => M.t c i) (hM.2.2.1 i) i
  have hzero := typeLaw_interim S hS (fun c => (withPayments S M).t c i)
    (payments_integrable S hS M hM.1 i) i
  have he : (fun r => interimPay S M i r)=ᵐ[ν]
      (fun r => interimPay S (withPayments S M) i r+d) := by
    filter_upwards [hsupp] with r hr
    rw [hid r hr,interim_payment_identity S hS M hM.1 i r hr]
  have heq := integral_congr_ae he
  change (∫ r,interimPay S M i r ∂ν)=(∫ r,interimPay S (withPayments S M) i r+d ∂ν) at heq
  have hzint : Integrable (interimPay S (withPayments S M) i) ν := hzero.1
  rw [integral_add hzint (integrable_const d),integral_const] at heq
  simp only [probReal_univ,one_smul] at heq
  change (∫ r,interimPay S M i r ∂ν)=(∫ r,interimPay S (withPayments S M) i r ∂ν)+d at heq
  change (∫ r,(∫ c,M.t (Function.update c i r) i ∂S.typeLaw) ∂ν)=(∫ r,(∫ c,(withPayments S M).t (Function.update c i r) i ∂S.typeLaw) ∂ν)+d at heq
  rw [hpay.2,hzero.2] at heq
  linarith
lemma objective_minimal_payments {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : Admissible S M) (hIC : IC S M) (hIR : IR S M) :
    objective S (withPayments S M) ≤ objective S M := by
  have hm := hM.1.2.2.2.2.2.1
  have hp := integrable_finset_sum Finset.univ (fun i _ => hM.2.2.1 i)
  have hz := integrable_finset_sum Finset.univ (fun i _ => payments_integrable S hS M hM.1 i)
  unfold objective
  change (∫ c,mse S M c+∑ i,(withPayments S M).t c i ∂S.typeLaw) ≤ _
  rw [integral_add hm hz,integral_add hm hp,
    integral_finset_sum _ (fun i _ => payments_integrable S hS M hM.1 i),
    integral_finset_sum _ (fun i _ => hM.2.2.1 i)]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => expected_payment_minimal S hS M hM hIC hIR i)
  linarith
lemma virtual_objective_lower {n : ℕ} (S : Setting n) (hS : S.Standing)
    (M : Mech n) (hM : Admissible S M) (hIC : IC S M) (hIR : IR S M) :
    virtualObjective S M-(n:ℝ)*S.var ≤ objective S M := by
  rw [← objective_withPayments S hS M hM.1]
  exact objective_minimal_payments S hS M hM hIC hIR
end Queelius.PrivateOptimizer

namespace PrivAcq.Central
open MeasureTheory
theorem _root_.solution {n : ℕ} (S : Setting n) (hS : S.Standing) :
    (∀ M : Mech n, Admissible S M → IC S M → IR S M →
      (∫ c, (((n : ℝ) + 1) * mse S M c + ∑ i, M.ε c i * S.ψ i (c i)) ∂S.typeLaw)
          - (n : ℝ) * S.var ≤ objective S M) ∧
    (∀ M : Mech n, AdmissibleAlloc S M →
      (∀ i : Fin n, AntitoneOn (interimEps S M i) (Set.Icc (S.a i) (S.b i))) →
      Admissible S (withPayments S M) ∧ IC S (withPayments S M) ∧ IR S (withPayments S M) ∧
        objective S (withPayments S M) =
          (∫ c, (((n : ℝ) + 1) * mse S M c + ∑ i, M.ε c i * S.ψ i (c i)) ∂S.typeLaw)
            - (n : ℝ) * S.var) := by
  refine ⟨?_,Queelius.PrivateOptimizer.payment_objective_reduction S hS⟩
  intro M hM hIC hIR
  simpa only [Queelius.PrivateOptimizer.virtualObjective,Queelius.PrivateOptimizer.virtualPoint,mul_comm]
    using Queelius.PrivateOptimizer.virtual_objective_lower S hS M hM hIC hIR
theorem _root_.complete_optimum {n : ℕ} (S : Setting n) (hS : S.Standing) (hA1 : S.Assumption1)
    (ystar : (Fin n → ℝ) → Fin n → ℝ) (hmeas : Measurable ystar)
    (hopt : ∀ c ∈ S.types, IsOpt23 S c (ystar c)) :
    Admissible S (optMech S ystar) ∧ IC S (optMech S ystar) ∧ IR S (optMech S ystar) ∧
      ∀ M : Mech n, Admissible S M → IC S M → IR S M →
        objective S (optMech S ystar) ≤ objective S M := by
  refine ⟨Queelius.PrivateOptimizer.optimal_mechanism_admissible S hS ystar hmeas hopt,
    (Queelius.PrivateOptimizer.optimal_mechanism_ic_ir S hS hA1 ystar hmeas hopt).1,
    (Queelius.PrivateOptimizer.optimal_mechanism_ic_ir S hS hA1 ystar hmeas hopt).2,?_⟩
  intro M hM hIC hIR
  have hid := Queelius.PrivateOptimizer.objective_withPayments S hS (optMech S ystar)
    (Queelius.PrivateOptimizer.optimal_allocation_admissible S hS ystar hmeas hopt)
  change objective S (optMech S ystar)=_ at hid
  rw [hid]
  have hv := Queelius.PrivateOptimizer.virtual_global_optimal S hS ystar hmeas hopt M hM.1
  have hl := Queelius.PrivateOptimizer.virtual_objective_lower S hS M hM hIC hIR
  linarith
end PrivAcq.Central
