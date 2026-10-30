-- Prove2me | solution 1 for PrivAcq.Central.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T09:39:00.295521+00:00
-- url     : https://prove2.me/submissions/87d187da-60bb-418a-a07d-3b44396daf51

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
 theorem _root_.solution {n : ℕ} (S : Setting n) (hS : S.Standing) (M : Mech n)
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
