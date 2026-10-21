-- Prove2me | solution 1 for RegMT.Regress.theorem_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T05:43:22.180215+00:00
-- url     : https://prove2.me/submissions/c137b972-b60a-4d9e-9e5f-2c13f3596d16

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_RegMT_Regress_Model

open WassersteinDRO.Duality
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal BigOperators Topology Classical

namespace RegMTProof
end RegMTProof

open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal BigOperators Topology Classical

namespace RegMTProof
variable {E : Type*} [NormedAddCommGroup E]

theorem modulus_le (f : E → ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    lipschitzModulus f ≤ K := by
  refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h := hK.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at h
  calc
    ENNReal.ofReal (|f x-f y| / ‖x-y‖) ≤ ENNReal.ofReal K :=
      ENNReal.ofReal_le_ofReal ((div_le_iff₀ hd).mpr h)
    _ = K := by simp

theorem modulus_ne_top (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) :
    lipschitzModulus f ≠ ⊤ := by
  obtain ⟨K,hK⟩ := hLip
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (modulus_le f hK)

theorem modulus_bound (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) (x y : E) :
    |f x-f y| ≤ (lipschitzModulus f).toReal * ‖x-y‖ := by
  by_cases hxy : x=y
  · subst y; simp
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h : ENNReal.ofReal (|f x-f y| / ‖x-y‖) ≤ lipschitzModulus f :=
    le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  have hr := ENNReal.toReal_mono (modulus_ne_top f hLip) h
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hd.le)] at hr
  exact (div_le_iff₀ hd).mp hr

theorem modulus_lipschitz (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) :
    LipschitzWith ⟨(lipschitzModulus f).toReal, ENNReal.toReal_nonneg⟩ f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change |f x-f y| ≤ (lipschitzModulus f).toReal * ‖x-y‖
  exact modulus_bound f hLip x y

variable [NormedSpace ℝ E]

theorem comp_lipschitz (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L)
    (beta : E →L[ℝ] ℝ) : ∃ K, LipschitzWith K (fun x => L (beta x)) := by
  obtain ⟨K,hK⟩ := hLip
  exact ⟨K * ‖beta‖₊, hK.comp beta.lipschitz⟩

theorem modulus_comp (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L)
    (beta : E →L[ℝ] ℝ) :
    lipschitzModulus (fun x => L (beta x)) = lipschitzModulus L * ENNReal.ofReal ‖beta‖ := by
  let F : E → ℝ := fun x => L (beta x)
  have hF : ∃ K, LipschitzWith K F := comp_lipschitz L hLip beta
  have hfin := modulus_ne_top F hF
  apply le_antisymm
  · have h := modulus_le F ((modulus_lipschitz L hLip).comp beta.lipschitz)
    rw [ENNReal.coe_nnreal_eq] at h
    change lipschitzModulus F ≤ ENNReal.ofReal ((lipschitzModulus L).toReal * ‖beta‖) at h
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (modulus_ne_top L hLip)] at h
    exact h
  · unfold lipschitzModulus
    simp only [ENNReal.iSup_mul]
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    let s : ℝ := |L a-L b| / ‖a-b‖
    have hs : 0 ≤ s := div_nonneg (abs_nonneg _) (norm_nonneg _)
    have habpos : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hbnd : ∀ v : E, ‖(s • beta) v‖ ≤ (lipschitzModulus F).toReal * ‖v‖ := by
      intro v
      by_cases hv : beta v=0
      · simp [hv, mul_nonneg ENNReal.toReal_nonneg (norm_nonneg v)]
      have hvpos : 0 < |beta v| := abs_pos.mpr hv
      have hh := modulus_bound F hF ((a / beta v) • v) ((b / beta v) • v)
      have hleft : F ((a / beta v) • v) = L a := by simp [F, hv]
      have hright : F ((b / beta v) • v) = L b := by simp [F, hv]
      rw [hleft, hright, ← sub_smul, norm_smul, Real.norm_eq_abs,
        ← sub_div, abs_div] at hh
      have hh' : |L a-L b| * |beta v| ≤
          (lipschitzModulus F).toReal * |a-b| * ‖v‖ := by
        apply (le_div_iff₀ hvpos).mp
        calc
          |L a-L b| ≤ (lipschitzModulus F).toReal * (|a-b| / |beta v| * ‖v‖) := hh
          _ = ((lipschitzModulus F).toReal * |a-b| * ‖v‖) / |beta v| := by ring
      rw [smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs, Real.norm_eq_abs]
      change (|L a-L b| / |a-b|) * |beta v| ≤ _
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ habpos).mpr (by nlinarith [hh'])
    have ho := (s • beta).opNorm_le_bound ENNReal.toReal_nonneg hbnd
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at ho
    change ENNReal.ofReal s * ENNReal.ofReal ‖beta‖ ≤ _
    rw [← ENNReal.ofReal_mul hs]
    exact (ENNReal.ofReal_le_ofReal ho).trans_eq (ENNReal.ofReal_toReal hfin)

end RegMTProof

open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal BigOperators Topology Classical

namespace RegMTProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ray_growth (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (x y : E) (T : ℝ) (hT : 1 ≤ T) :
    f y + T * (f x-f y) ≤ f (y+T • (x-y)) := by
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hi : 1 / T ≤ 1 := (div_le_one ht).mpr hT
  have h := hconv.2 (Set.mem_univ y) (Set.mem_univ (y+T • (x-y)))
    (sub_nonneg.mpr hi) (div_nonneg zero_le_one ht.le) (by ring : 1-1/T+1/T=1)
  have he : (1-1/T) • y + (1/T) • (y+T • (x-y)) = x := by
    rw [smul_add, smul_smul, one_div_mul_cancel ht.ne', one_smul]
    module
  rw [he] at h
  simp only [smul_eq_mul] at h
  have hh : f x ≤ ((T-1)*f y+f (y+T • (x-y)))/T := by
    calc
      f x ≤ (1-1/T)*f y+(1/T)*f (y+T • (x-y)) := h
      _ = _ := by field_simp
  have := (le_div_iff₀ ht).mp hh
  nlinarith

theorem translated_ray_growth (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hLip : ∃ K, LipschitzWith K f) (x y z : E) (T : ℝ) (hT : 1 ≤ T) :
    f y+T*(f x-f y)-(lipschitzModulus f).toReal*‖z-y‖ ≤
      f (z+T • (x-y)) := by
  have hg := ray_growth f hconv x y T hT
  have hl := modulus_bound f hLip (y+T • (x-y)) (z+T • (x-y))
  rw [add_sub_add_right_eq_sub, norm_sub_rev] at hl
  have ha := le_abs_self (f (y+T • (x-y))-f (z+T • (x-y)))
  linarith

end RegMTProof

open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal BigOperators

namespace RegMTProof

noncomputable def avg {E : Type*} {N : ℕ} (f : E → ℝ) (z : Fin N → E) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, f (z i)

theorem avg_nonneg {E : Type*} {N : ℕ} (f : E → ℝ) (z : Fin N → E)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg f z := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _ => hf (z i))

theorem nominalRisk_nonnegative {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) :
    nominalRisk Q f = ((∫⁻ x, ENNReal.ofReal (f x) ∂Q : ENNReal) : EReal) := by
  have hn (x : E) : (-(f x : EReal)).toENNReal = 0 := by
    apply EReal.toENNReal_of_nonpos
    rw [← EReal.coe_neg]
    exact EReal.coe_nonpos.mpr (neg_nonpos.mpr (hf x))
  simp only [nominalRisk, erealExpectation, hn]
  simp only [EReal.toENNReal, EReal.coe_ne_top, ↓reduceIte, EReal.toReal_coe,
    lintegral_zero, EReal.coe_ennreal_zero, sub_zero]
  split_ifs with h
  · rw [h, EReal.coe_ennreal_top]
  · rfl

theorem empirical_probability {E : Type*} [MeasurableSpace E] {N : ℕ}
    (z : Fin N → E) (hN : 0 < N) : IsProbabilityMeasure (empiricalDistribution z) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply,
    hN.ne', ENNReal.inv_mul_cancel]

theorem empirical_lintegral {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (z : Fin N → E) (hN : 0 < N) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂empiricalDistribution z = ENNReal.ofReal (avg f z) := by
  rw [empiricalDistribution, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  rw [avg, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf (z i))]

theorem empirical_risk {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (z : Fin N → E) (hN : 0 < N) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) :
    nominalRisk (empiricalDistribution z) f = ((avg f z : ℝ) : EReal) := by
  rw [nominalRisk_nonnegative _ _ hf, empirical_lintegral z hN f hf,
    EReal.coe_ennreal_ofReal, max_eq_left]
  exact_mod_cast avg_nonneg f z hf

theorem empirical_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {N : ℕ} (z : Fin N → E) (g : E → F) (hg : Measurable g) :
    (empiricalDistribution z).map g = empiricalDistribution (fun i => g (z i)) := by
  rw [empiricalDistribution, Measure.map_smul]
  congr 1
  induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Measure.map_add _ _ hg, Measure.map_dirac' hg, ih]

end RegMTProof

open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal BigOperators

namespace RegMTProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N : ℕ}

noncomputable def translatedMixture (z : Fin N → E) (p : ℝ) (h : E) : Measure E :=
  ENNReal.ofReal (1-p) • empiricalDistribution z +
    ENNReal.ofReal p • empiricalDistribution (fun i => z i + h)

noncomputable def translatedCoupling (z : Fin N → E) (p : ℝ) (h : E) : Measure (E × E) :=
  ENNReal.ofReal (1-p) • empiricalDistribution (fun i => (z i, z i)) +
    ENNReal.ofReal p • empiricalDistribution (fun i => (z i + h, z i))

theorem mixture_feasible (z : Fin N → E) (hN : 0 < N)
    (p ρ : ℝ) (h : E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcost : p * ‖h‖ ≤ ρ) :
    translatedMixture z p h ∈ ambiguitySet ρ 1 Set.univ (empiricalDistribution z) := by
  have hp : ENNReal.ofReal (1-p) + ENNReal.ofReal p = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]
    simp
  let P := empiricalDistribution z
  let π := translatedCoupling z p h
  have hm : π.map Prod.fst = translatedMixture z p h ∧ π.map Prod.snd = P := by
    constructor
    · simp only [π, translatedCoupling, Measure.map_add _ _ measurable_fst,
        Measure.map_smul, empirical_map _ _ measurable_fst, translatedMixture]
    · simp only [π, translatedCoupling, Measure.map_add _ _ measurable_snd,
        Measure.map_smul, empirical_map _ _ measurable_snd, P]
      rw [← add_smul, hp, one_smul]
  have hπ : ∫⁻ x : E × E, ENNReal.ofReal ‖x.1-x.2‖ ∂π =
      ENNReal.ofReal (p * ‖h‖) := by
    simp only [π, translatedCoupling, lintegral_add_measure, lintegral_smul_measure,
      smul_eq_mul]
    rw [empirical_lintegral _ hN _ (fun _ => norm_nonneg _),
      empirical_lintegral _ hN _ (fun _ => norm_nonneg _)]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [avg, hn, ENNReal.ofReal_mul hp0]
  have hP := empirical_probability z hN
  have hPh := empirical_probability (fun i => z i + h) hN
  refine ⟨?_, by simp, ?_⟩
  · simpa only [translatedMixture, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one] using hp
  · change wassersteinDistance 1 (translatedMixture z p h) P ≤ ENNReal.ofReal ρ
    simp only [wassersteinDistance, Real.rpow_one, one_div_one, ENNReal.rpow_one]
    exact (iInf_le_of_le π (iInf_le_of_le hm (le_of_eq hπ))).trans
      (ENNReal.ofReal_le_ofReal hcost)

theorem mixture_risk (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (p : ℝ) (h : E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    nominalRisk (translatedMixture z p h) f =
      (((1-p) * avg f z + p * avg f (fun i => z i + h) : ℝ) : EReal) := by
  rw [nominalRisk_nonnegative _ _ hf]
  simp only [translatedMixture, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
  rw [empirical_lintegral _ hN _ hf, empirical_lintegral _ hN _ hf,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hp1), ← ENNReal.ofReal_mul hp0,
    ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hp1) (avg_nonneg _ _ hf))
      (mul_nonneg hp0 (avg_nonneg _ _ hf)), EReal.coe_ennreal_ofReal, max_eq_left]
  exact_mod_cast add_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (avg_nonneg _ _ hf))
    (mul_nonneg hp0 (avg_nonneg _ _ hf))

theorem empirical_feasible (z : Fin N → E) (hN : 0 < N)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    empiricalDistribution z ∈ ambiguitySet ρ 1 Set.univ (empiricalDistribution z) := by
  simpa [translatedMixture] using mixture_feasible z hN 0 ρ 0 le_rfl zero_le_one (by simpa)

end RegMTProof

open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal BigOperators

namespace RegMTProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N : ℕ}

theorem coupling_upper (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (k : ℝ≥0) (hLip : LipschitzWith k f)
    (Q : Measure E) (π : Measure (E × E))
    (hm : π.map Prod.fst = Q ∧ π.map Prod.snd = empiricalDistribution z) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂Q ≤ ENNReal.ofReal (avg f z) +
      (k : ENNReal) * ∫⁻ x : E × E, ENNReal.ofReal ‖x.1-x.2‖ ∂π := by
  have hfm : Measurable (fun x => ENNReal.ofReal (f x)) :=
    hLip.continuous.measurable.ennreal_ofReal
  calc
    ∫⁻ x, ENNReal.ofReal (f x) ∂Q = ∫⁻ x : E × E, ENNReal.ofReal (f x.1) ∂π := by
      rw [← hm.1, lintegral_map hfm measurable_fst]
    _ ≤ ∫⁻ x : E × E, (ENNReal.ofReal (f x.2) +
        (k : ENNReal) * ENNReal.ofReal ‖x.1-x.2‖) ∂π := by
      apply lintegral_mono
      intro x
      have hb : f x.1 ≤ f x.2 + (k : ℝ) * ‖x.1-x.2‖ := by
        have ht := hLip.dist_le_mul x.1 x.2
        rw [Real.dist_eq, dist_eq_norm] at ht
        linarith [le_abs_self (f x.1-f x.2)]
      simpa only [ENNReal.ofReal_add (hf x.2) (mul_nonneg k.coe_nonneg (norm_nonneg _)),
        ENNReal.ofReal_mul k.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hb
    _ ≤ (∫⁻ x : E × E, ENNReal.ofReal (f x.2) ∂π) +
        ∫⁻ x : E × E, (k : ENNReal) * ENNReal.ofReal ‖x.1-x.2‖ ∂π :=
      le_of_eq (lintegral_add_left (hfm.comp measurable_snd) _)
    _ = _ := by
      rw [← lintegral_map hfm measurable_snd, hm.2, empirical_lintegral z hN f hf,
        lintegral_const_mul' _ _ (ENNReal.coe_ne_top)]

theorem transport_upper (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (k : ℝ≥0) (hLip : LipschitzWith k f)
    (Q : Measure E) (hQ : IsProbabilityMeasure Q) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂Q ≤ ENNReal.ofReal (avg f z) +
      (k : ENNReal) * wassersteinDistance 1 Q (empiricalDistribution z) := by
  let P := empiricalDistribution z
  let C := {π : Measure (E × E) // π.map Prod.fst = Q ∧ π.map Prod.snd = P}
  let _ : IsProbabilityMeasure Q := hQ
  let _ : IsProbabilityMeasure P := empirical_probability z hN
  have hc : (Q.prod P).map Prod.fst = Q ∧ (Q.prod P).map Prod.snd = P := by
    simp
  let _ : Nonempty C := ⟨⟨Q.prod P, hc⟩⟩
  have hw : wassersteinDistance 1 Q P =
      ⨅ π : C, ∫⁻ x : E × E, ENNReal.ofReal ‖x.1-x.2‖ ∂π.1 := by
    simp only [wassersteinDistance, Real.rpow_one, one_div_one, ENNReal.rpow_one,
      C, iInf_subtype]
  change _ ≤ ENNReal.ofReal (avg f z) + (k : ENNReal) * wassersteinDistance 1 Q P
  rw [hw, ENNReal.mul_iInf (by simp), ENNReal.add_iInf]
  exact le_iInf fun π => coupling_upper z hN f hf k hLip Q π.1 π.2

theorem worst_upper (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hLip : ∃ K, LipschitzWith K f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f ≤
      ((avg f z + ρ * (lipschitzModulus f).toReal : ℝ) : EReal) := by
  let k : ℝ≥0 := ⟨(lipschitzModulus f).toReal, ENNReal.toReal_nonneg⟩
  have hk : LipschitzWith k f := modulus_lipschitz f hLip
  refine iSup_le fun Q => iSup_le fun hQ => ?_
  have hprob : IsProbabilityMeasure Q := ⟨hQ.1⟩
  have hb := (transport_upper z hN f hf k hk Q hprob).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl hQ.2.2))
  rw [nominalRisk_nonnegative Q f hf]
  have he : ENNReal.ofReal (avg f z) + (k : ENNReal) * ENNReal.ofReal ρ =
      ENNReal.ofReal (avg f z + ρ * (lipschitzModulus f).toReal) := by
    rw [ENNReal.ofReal_add (avg_nonneg f z hf)
      (mul_nonneg hρ ENNReal.toReal_nonneg), ENNReal.ofReal_mul hρ]
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (avg f z) + ENNReal.ofReal (lipschitzModulus f).toReal * ENNReal.ofReal ρ =
      ENNReal.ofReal (avg f z) + ENNReal.ofReal ρ * ENNReal.ofReal (lipschitzModulus f).toReal
    rw [mul_comm]
  rw [he] at hb
  have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hb
  have hn : 0 ≤ avg f z + ρ * (lipschitzModulus f).toReal :=
    add_nonneg (avg_nonneg f z hf) (mul_nonneg hρ ENNReal.toReal_nonneg)
  simpa only [EReal.coe_ennreal_ofReal, max_eq_left hn] using hh

end RegMTProof

open MeasureTheory WassersteinDRO.Duality Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace RegMTProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N : ℕ}

theorem empirical_lower (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((avg f z : ℝ) : EReal) ≤ worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f := by
  rw [← empirical_risk z hN f hf]
  exact le_iSup_of_le (empiricalDistribution z)
    (le_iSup_of_le (empirical_feasible z hN ρ hρ) le_rfl)

theorem oriented_secant_lower (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hconv : ConvexOn ℝ Set.univ f)
    (hLip : ∃ K, LipschitzWith K f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (x y : E) (hxy : x ≠ y) :
    ((avg f z + ρ * ((f x-f y)/‖x-y‖) : ℝ) : EReal) ≤
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f := by
  let a := avg f z
  let k := (lipschitzModulus f).toReal
  let C := a-f y+(N:ℝ)⁻¹ * ∑ i, k*‖z i-y‖
  have hv : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbound (T : ℝ) (ht1 : 1 ≤ T) (htρ : ρ/‖x-y‖ ≤ T) :
      ((a+ρ*((f x-f y)/‖x-y‖)-ρ*C/(T*‖x-y‖) : ℝ) : EReal) ≤
        worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f := by
    have ht : 0 < T := lt_of_lt_of_le zero_lt_one ht1
    have hd : 0 < T*‖x-y‖ := mul_pos ht hv
    let p := ρ/(T*‖x-y‖)
    have hp0 : 0 ≤ p := div_nonneg hρ hd.le
    have hp1 : p ≤ 1 := (div_le_one hd).mpr ((div_le_iff₀ hv).mp htρ)
    have hcost : p*‖T • (x-y)‖ ≤ ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact le_of_eq (div_mul_cancel₀ ρ hd.ne')
    have hq := mixture_feasible z hN p ρ (T • (x-y)) hp0 hp1 hcost
    have hsum : a+T*(f x-f y)-C ≤ avg f (fun i => z i+T • (x-y)) := by
      calc
        a+T*(f x-f y)-C = (N:ℝ)⁻¹ * ∑ i,
            (f y+T*(f x-f y)-k*‖z i-y‖) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          dsimp [C]
          field_simp
          ring
        _ ≤ avg f (fun i => z i+T • (x-y)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
          exact Finset.sum_le_sum fun i _ => translated_ray_growth f hconv hLip x y (z i) T ht1
    have hr : a+ρ*((f x-f y)/‖x-y‖)-ρ*C/(T*‖x-y‖) ≤
        (1-p)*avg f z+p*avg f (fun i => z i+T • (x-y)) := by
      have hm := mul_le_mul_of_nonneg_left hsum hp0
      have he : a+ρ*((f x-f y)/‖x-y‖)-ρ*C/(T*‖x-y‖) =
          (1-p)*a+p*(a+T*(f x-f y)-C) := by
        dsimp [p]
        field_simp
        ring
      rw [he]
      dsimp [a] at *
      linarith
    calc
      _ ≤ (((1-p)*avg f z+p*avg f (fun i => z i+T • (x-y)) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hr
      _ = nominalRisk (translatedMixture z p (T • (x-y))) f :=
        (mixture_risk z hN f hf p (T • (x-y)) hp0 hp1).symm
      _ ≤ _ := by
        unfold worstCaseRisk
        apply le_iSup_of_le (translatedMixture z p (T • (x-y)))
        exact le_iSup_of_le hq le_rfl
  have hz : Tendsto (fun T : ℝ => ρ*C/(T*‖x-y‖)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0))
    convert h.const_mul (ρ*C/‖x-y‖) using 1 <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hl : Tendsto (fun T : ℝ =>
      ((a+ρ*((f x-f y)/‖x-y‖)-ρ*C/(T*‖x-y‖) : ℝ) : EReal)) atTop
      (𝓝 ((a+ρ*((f x-f y)/‖x-y‖) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (by simpa using tendsto_const_nhds.sub hz)
  apply le_of_tendsto hl
  filter_upwards [eventually_ge_atTop (max 1 (ρ/‖x-y‖))] with T hT
  exact hbound T ((le_max_left _ _).trans hT) ((le_max_right _ _).trans hT)

theorem secant_lower (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hconv : ConvexOn ℝ Set.univ f)
    (hLip : ∃ K, LipschitzWith K f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (x y : E) (hxy : x ≠ y) :
    ((avg f z+ρ*(|f x-f y|/‖x-y‖) : ℝ) : EReal) ≤
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f := by
  by_cases h : 0 ≤ f x-f y
  · simpa only [abs_of_nonneg h] using oriented_secant_lower z hN f hf hconv hLip ρ hρ x y hxy
  · have hr := oriented_secant_lower z hN f hf hconv hLip ρ hρ y x hxy.symm
    simpa only [abs_of_neg (lt_of_not_ge h), neg_sub, norm_sub_rev] using hr

theorem worst_lower (z : Fin N → E) (hN : 0 < N) (f : E → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hconv : ConvexOn ℝ Set.univ f)
    (hLip : ∃ K, LipschitzWith K f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((avg f z+ρ*(lipschitzModulus f).toReal : ℝ) : EReal) ≤
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) f := by
  by_cases hr0 : ρ=0
  · simpa [hr0] using empirical_lower z hN f hf ρ hρ
  have hr : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hr0)
  by_contra hn
  obtain ⟨r,hr1,hr2⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  have ha : avg f z < r := EReal.coe_lt_coe_iff.mp ((empirical_lower z hN f hf ρ hρ).trans_lt hr1)
  have hk : lipschitzModulus f ≤ ENNReal.ofReal ((r-avg f z)/ρ) := by
    refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
    have hh := EReal.coe_lt_coe_iff.mp ((secant_lower z hN f hf hconv hLip ρ hρ x y hxy).trans_lt hr1)
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hr).mpr
    nlinarith
  have hkreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
  rw [ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr ha.le) hr.le)] at hkreal
  have hh := (le_div_iff₀ hr).mp hkreal
  have hh2 := EReal.coe_lt_coe_iff.mp hr2
  nlinarith

end RegMTProof

open WassersteinDRO.Duality
open scoped ENNReal BigOperators Classical

namespace RegMT.Regress

/-- Theorem 3.1(ii) (Distributionally robust linear regression), Shafieezadeh-Abadeh, Kuhn &
Mohajerin Esfahani, *Regularization via Mass Transportation*, arXiv:1710.10016v3, p. 8, (6).

Setting (§3.1, p. 8): the input-output space `ℝ^{n+1}` carries an arbitrary norm and is modelled
as `E` with input/output coordinates `e : E ≃L[ℝ] ℝⁿ × ℝ`; the transport cost is `‖ξ − ξ'‖` and
`Ξ = E`; `L : ℝ → ℝ` is nonnegative, convex and Lipschitz continuous; the samples are `(xhat i, yhat i)`,
`i < N`, `N ≥ 1`; `ρ ≥ 0` is the radius of the Wasserstein ball (3) around the empirical
distribution `P̂_N`. The worst case `sup_{Q ∈ B_ρ(P̂_N)} E^Q[L(⟨w, x⟩ − y)]` of (4) is
`worstCaseRisk ρ 1 Set.univ P̂_N (L ∘ pairing e w)`.

Conclusion ("(4) is equivalent to (6)"): (1) for every `w` the worst-case expected loss equals the
objective of (6), `(1/N) Σᵢ L(⟨w, xhat i⟩ − yhat i) + ρ · lip(L) · ‖(w, −1)‖_*`, with `lip(L)` the
Lipschitz modulus of `L` and `‖(w, −1)‖_*` the operator norm of `pairing e w`; (2) consequently the
optimal values of (4) and (6) agree. -/
theorem theorem_3_1_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hN : 0 < N)
    (xhat : Fin N → Fin n → ℝ) (yhat : Fin N → ℝ)
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L) :
    (∀ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ)) =
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal)) ∧
    (⨅ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ))) =
      ⨅ w : Fin n → ℝ,
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal)  := by
  let z : Fin N → E := fun i => e.symm (xhat i, yhat i)
  have hw (w : Fin n → ℝ) :
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution z) (fun ξ => L (pairing e w ξ)) =
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) : EReal) := by
    let f : E → ℝ := fun ξ => L (pairing e w ξ)
    have hf : ∀ ξ, 0 ≤ f ξ := fun ξ => h_nonneg _
    have hl : ∃ K, LipschitzWith K f := RegMTProof.comp_lipschitz L hLip (pairing e w)
    have hc : ConvexOn ℝ Set.univ f := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      simpa only [f, map_add, map_smul, smul_eq_mul] using hconv.2 (Set.mem_univ (pairing e w x))
        (Set.mem_univ (pairing e w y)) ha hb hab
    have he := le_antisymm (RegMTProof.worst_upper z hN f hf hl ρ hρ)
      (RegMTProof.worst_lower z hN f hf hc hl ρ hρ)
    have hm := RegMTProof.modulus_comp L hLip (pairing e w)
    have ha : RegMTProof.avg f z = (N : ℝ)⁻¹ * ∑ i, L (∑ j, w j*xhat i j-yhat i) := by
      simp [RegMTProof.avg, f, z]
    have hp : ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ =
        ENNReal.ofReal (ρ * (lipschitzModulus f).toReal) := by
      rw [ENNReal.ofReal_mul hρ, ENNReal.ofReal_toReal (RegMTProof.modulus_ne_top f hl)]
      rw [show lipschitzModulus f = _ from hm, mul_assoc]
    rw [hp, EReal.coe_ennreal_ofReal, max_eq_left]
    · simpa only [EReal.coe_add, ha] using he
    · exact_mod_cast mul_nonneg hρ (ENNReal.toReal_nonneg : 0 ≤ (lipschitzModulus f).toReal)
  exact ⟨hw, iInf_congr hw⟩

end RegMT.Regress

open RegMT.Regress

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hN : 0 < N)
    (xhat : Fin N → Fin n → ℝ) (yhat : Fin N → ℝ)
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L) :
    (∀ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ)) =
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal)) ∧
    (⨅ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ))) =
      ⨅ w : Fin n → ℝ,
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal) := by
  exact RegMT.Regress.theorem_3_1_ii e ρ hρ hN xhat yhat L hconv h_nonneg hLip
